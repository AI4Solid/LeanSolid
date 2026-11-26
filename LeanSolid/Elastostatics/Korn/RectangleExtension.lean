module

public import LeanSolid.Elastostatics.Korn.Reflection
import LeanSolid.Elastostatics.Korn.Theorems
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace LeanSolid.Elastostatics.Korn

/-- Turn the upper side of a strip into a lower side, reversing its normal coordinate. -/
def flipNormal (L : ℝ) (p : Plane) : Plane := (p.1, L - p.2)

/-- Extend through both horizontal sides. The upper reflection reverses the normal component
as well as the coordinate before applying the lower reflection. -/
noncomputable def extendVertical (L : ℝ) (u v : Plane → ℝ) :
    (Plane → ℝ) × (Plane → ℝ) :=
  let U := glueFace u (reflectedTangent u)
  let V := glueFace v (reflectedNormal v)
  let f := U ∘ flipNormal L
  let g := fun p => -V (flipNormal L p)
  (glueFace f (reflectedTangent f) ∘ flipNormal L,
    fun p => -glueFace g (reflectedNormal g) (flipNormal L p))

private theorem flipNormal_involutive (L : ℝ) (p : Plane) :
    flipNormal L (flipNormal L p) = p := by
  apply Prod.ext
  · rfl
  · change L - (L - p.2) = p.2
    ring

private theorem flip_normal_hasFDeriv (L : ℝ) (p : Plane) :
    HasFDerivAt (flipNormal L) (reflectionSample 1) p := by
  have h := ((reflectionSample 1).hasFDerivAt (x := p)).add
    (hasFDerivAt_const ((0, L) : Plane) p)
  have hf : ((reflectionSample 1 : Plane → Plane) + fun _ => (0, L)) = flipNormal L := by
    funext q
    simp only [Pi.add_apply, reflectionSample_apply, flipNormal]
    apply Prod.ext
    · simp
    · change -1 * q.2 + L = L - q.2
      ring
  rw [hf, add_zero] at h
  exact h

/-- Reversing both the normal component and the normal coordinate preserves strain energy. -/
theorem flipNormal_strain_sq (L : ℝ) {u v : Plane → ℝ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (p : Plane) :
    strainComponentSq (strainComponents (u ∘ flipNormal L) (fun z => -v (flipNormal L z)) p) =
      strainComponentSq (strainComponents u v (flipNormal L p)) := by
  have hu' := ((hu (flipNormal L p)).hasFDerivAt.comp p (flip_normal_hasFDeriv L p)).fderiv
  have hv' := (((hv (flipNormal L p)).hasFDerivAt.comp p (flip_normal_hasFDeriv L p)).neg).fderiv
  change fderiv ℝ (fun z => -v (flipNormal L z)) p = _ at hv'
  have h1 : reflectionSample 1 (1, 0) = (1, 0) := by
    rw [reflectionSample_apply]
    norm_num
  have h2 : reflectionSample 1 (0, 1) = -((0, 1) : Plane) := by
    rw [reflectionSample_apply]
    apply Prod.ext <;> norm_num
  unfold strainComponentSq strainComponents
  rw [hu', hv']
  simp only [ContinuousLinearMap.comp_apply, h1, h2, neg_apply, map_neg]
  ring

theorem extendVertical_contDiff (L : ℝ) {u v : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (extendVertical L u v).1 ∧ ContDiff ℝ 1 (extendVertical L u v).2 := by
  obtain ⟨hU, hV⟩ := reflection_contDiff hu hv
  have hflip : ContDiff ℝ 1 (flipNormal L) := by
    unfold flipNormal
    fun_prop
  have hF := hU.comp hflip
  have hG := (hV.comp hflip).neg
  obtain ⟨hf, hg⟩ := reflection_contDiff hF hG
  exact ⟨hf.comp hflip, (hg.comp hflip).neg⟩

theorem extendVertical_eq_on (L : ℝ) (u v : Plane → ℝ) (p : Plane)
    (hb : 0 ≤ p.2) (ht : p.2 ≤ L) :
    (extendVertical L u v).1 p = u p ∧ (extendVertical L u v).2 p = v p := by
  have hflip : 0 ≤ (flipNormal L p).2 := sub_nonneg.mpr ht
  simp [extendVertical, glueFace, hflip, hb, flipNormal_involutive]

private theorem interval_congr_open {s t : ℝ} {F G : ℝ → ℝ} (hst : s ≤ t)
    (h : ∀ y ∈ Ioo s t, F y = G y) :
    (∫ y in s..t, F y) = ∫ y in s..t, G y := by
  apply intervalIntegral.integral_congr_ae'
  · have hne : ∀ᵐ y : ℝ ∂volume, y ≠ t := by simp [ae_iff]
    filter_upwards [hne] with y hy hmem
    exact h y ⟨hmem.1, lt_of_le_of_ne hmem.2 hy⟩
  · exact Eventually.of_forall fun y hy => (not_lt_of_ge (hy.2.trans hst) hy.1).elim

private theorem continuous_line_strain {u v : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (x : ℝ) :
    Continuous (fun y => strainComponentSq (strainComponents u v (x, y))) := by
  have hU := hu.continuous_fderiv one_ne_zero
  have hV := hv.continuous_fderiv one_ne_zero
  unfold strainComponentSq strainComponents
  dsimp
  fun_prop

/-- The two-sided extension has a normal-slice strain bound on the entire enlarged interval.
Both reflected sides sample only within the original interval when `3*d ≤ L`. -/
theorem extendVertical_strain_integral_le {L d : ℝ} (hd : 0 ≤ d) (hdL : 3 * d ≤ L)
    {u v : Plane → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (x : ℝ) :
    (∫ y in -d..L + d, strainComponentSq (strainComponents
        (extendVertical L u v).1 (extendVertical L u v).2 (x, y))) ≤
      18433 * ∫ y in (0 : ℝ)..L, strainComponentSq (strainComponents u v (x, y)) := by
  let U := glueFace u (reflectedTangent u)
  let V := glueFace v (reflectedNormal v)
  let f := U ∘ flipNormal L
  let g := fun p => -V (flipNormal L p)
  let T := fun y => strainComponentSq (strainComponents (extendVertical L u v).1
    (extendVertical L u v).2 (x, y))
  let P := fun y => strainComponentSq (strainComponents u v (x, y))
  let B := fun y => strainComponentSq (strainComponents (reflectedTangent u) (reflectedNormal v) (x, y))
  let A := fun y => strainComponentSq (strainComponents (reflectedTangent f) (reflectedNormal g) (x, y))
  have hL : 0 ≤ L := (mul_nonneg (by norm_num) hd).trans hdL
  obtain ⟨hU, hV⟩ := reflection_contDiff hu hv
  have hflip : ContDiff ℝ 1 (flipNormal L) := by unfold flipNormal; fun_prop
  have hf : ContDiff ℝ 1 f := hU.comp hflip
  have hg : ContDiff ℝ 1 g := (hV.comp hflip).neg
  obtain ⟨hF, hG⟩ := reflection_contDiff hf hg
  obtain ⟨heU, heV⟩ := extendVertical_contDiff L hu hv
  have hT : Continuous T := continuous_line_strain heU heV x
  have hP : Continuous P := continuous_line_strain hu hv x
  have hn (y : ℝ) : 0 ≤ P y := by unfold P strainComponentSq; positivity
  have lower_eq (y : ℝ) (hy : y < L) :
      T y = strainComponentSq (strainComponents U V (x, y)) := by
    have he (p : Plane) (hp : p.2 < L) :
        (extendVertical L u v).1 p = U p ∧ (extendVertical L u v).2 p = V p := by
      have hp' : 0 ≤ (flipNormal L p).2 := sub_nonneg.mpr hp.le
      simp [extendVertical, U, V, glueFace, hp', flipNormal_involutive]
    have h := (isOpen_lt continuous_snd continuous_const).mem_nhds
      (show (x, y) ∈ {p : Plane | p.2 < L} from hy)
    have h₁ : (extendVertical L u v).1 =ᶠ[𝓝 (x, y)] U := by
      filter_upwards [h] with p hp using (he p hp).1
    have h₂ : (extendVertical L u v).2 =ᶠ[𝓝 (x, y)] V := by
      filter_upwards [h] with p hp using (he p hp).2
    unfold T strainComponents
    rw [h₁.fderiv_eq, h₂.fderiv_eq]
  have middle_eq (y : ℝ) (hy : 0 < y) :
      strainComponentSq (strainComponents U V (x, y)) = P y := by
    have hd₁ {w z : Plane → ℝ} :
        fderiv ℝ (glueFace w z) (x, y) = fderiv ℝ w (x, y) := by
      apply EventuallyEq.fderiv_eq
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hy] with p hp
      exact ite_eq_left hp.le
    simp only [P, U, V, strainComponents, hd₁]
  have hlow : (∫ y in -d..(0 : ℝ), T y) = ∫ y in -d..(0 : ℝ), B y := by
    apply interval_congr_open (neg_nonpos.mpr hd)
    intro y hy
    rw [lower_eq y (hy.2.trans_le hL)]
    exact congrArg strainComponentSq (glued_strain_below u v (x, y) hy.2)
  have hmid : (∫ y in (0 : ℝ)..L, T y) = ∫ y in (0 : ℝ)..L, P y := by
    apply interval_congr_open hL
    exact fun y hy => (lower_eq y hy.2).trans (middle_eq y hy.1)
  have hhigh : (∫ y in L..L + d, T y) = ∫ y in -d..(0 : ℝ), A y := by
    calc
      _ = ∫ y in L..L + d, A (L - y) := by
        apply interval_congr_open (by linarith)
        intro y hy
        have h := flipNormal_strain_sq L (hF.differentiable one_ne_zero)
          (hG.differentiable one_ne_zero) (x, y)
        change T y = _ at h
        rw [h]
        exact congrArg strainComponentSq (glued_strain_below f g (x, L - y)
          (sub_neg.mpr hy.1))
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left, sub_add_eq_sub_sub, sub_self,
        zero_sub]
  have hfar : (∫ y in (0 : ℝ)..3 * d, strainComponentSq (strainComponents f g (x, y))) =
      ∫ y in L - 3 * d..L, P y := by
    calc
      _ = ∫ y in (0 : ℝ)..3 * d, P (L - y) := by
        apply interval_congr_open (by positivity)
        intro y hy
        rw [show strainComponentSq (strainComponents f g (x, y)) =
          strainComponentSq (strainComponents U V (x, L - y)) from
          flipNormal_strain_sq L (hU.differentiable one_ne_zero) (hV.differentiable one_ne_zero) _]
        exact middle_eq _ (sub_pos.mpr (hy.2.trans_le hdL))
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left, sub_zero]
  have hh := reflected_slice_strain_integral_le hf hg x hd
  change (∫ y in -d..(0 : ℝ), A y) ≤ _ at hh
  rw [hfar] at hh
  have hbnd := reflected_slice_strain_integral_le hu hv x hd
  change (∫ y in -d..(0 : ℝ), B y) ≤ 9216 * ∫ y in (0 : ℝ)..3 * d, P y at hbnd
  have hh' := intervalIntegral.integral_mono_interval (μ := volume)
    (sub_nonneg.mpr hdL) (sub_le_self _ (by positivity)) le_rfl
    (Eventually.of_forall hn) (hP.intervalIntegrable 0 L)
  have hb' := intervalIntegral.integral_mono_interval (μ := volume)
    le_rfl (show (0 : ℝ) ≤ 3 * d by positivity) hdL
    (Eventually.of_forall hn) (hP.intervalIntegrable 0 L)
  change (∫ y in -d..L + d, T y) ≤ 18433 * ∫ y in (0 : ℝ)..L, P y
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hT.intervalIntegrable (-d) 0) (hT.intervalIntegrable 0 (L + d)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hT.intervalIntegrable 0 L) (hT.intervalIntegrable L (L + d)), hlow, hmid, hhigh]
  linarith only [hbnd, hh, hh', hb']

/-- The two reflected faces preserve a uniform squared displacement integral bound. -/
theorem extendVertical_displacement_integral_le {L d : ℝ} (hd : 0 ≤ d) (hdL : 3 * d ≤ L)
    {u v : Plane → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (x : ℝ) :
    (∫ y in -d..L + d, (extendVertical L u v).1 (x, y) ^ 2 +
        (extendVertical L u v).2 (x, y) ^ 2) ≤
      4609 * ∫ y in (0 : ℝ)..L, u (x, y) ^ 2 + v (x, y) ^ 2 := by
  let U := glueFace u (reflectedTangent u)
  let V := glueFace v (reflectedNormal v)
  let f := U ∘ flipNormal L
  let g := fun p => -V (flipNormal L p)
  let T := fun y => (extendVertical L u v).1 (x, y) ^ 2 + (extendVertical L u v).2 (x, y) ^ 2
  let P := fun y => u (x, y) ^ 2 + v (x, y) ^ 2
  let B := fun y => reflectedTangent u (x, y) ^ 2 + reflectedNormal v (x, y) ^ 2
  let A := fun y => reflectedTangent f (x, y) ^ 2 + reflectedNormal g (x, y) ^ 2
  have hL : 0 ≤ L := (mul_nonneg (by norm_num) hd).trans hdL
  obtain ⟨hU, hV⟩ := reflection_contDiff hu hv
  have hflip : ContDiff ℝ 1 (flipNormal L) := by unfold flipNormal; fun_prop
  have hf : ContDiff ℝ 1 f := hU.comp hflip
  have hg : ContDiff ℝ 1 g := (hV.comp hflip).neg
  obtain ⟨heU, heV⟩ := extendVertical_contDiff L hu hv
  have hT : Continuous T := by unfold T; fun_prop
  have hP : Continuous P := by unfold P; fun_prop
  have hn (y : ℝ) : 0 ≤ P y := by unfold P; positivity
  have lower_eq (y : ℝ) (hy : y < L) : T y = U (x, y) ^ 2 + V (x, y) ^ 2 := by
    have hp' : 0 ≤ (flipNormal L (x, y)).2 := sub_nonneg.mpr hy.le
    simp [T, extendVertical, U, V, glueFace, hp', flipNormal_involutive]
  have hlow : (∫ y in -d..(0 : ℝ), T y) = ∫ y in -d..(0 : ℝ), B y := by
    apply interval_congr_open (neg_nonpos.mpr hd)
    intro y hy
    rw [lower_eq y (hy.2.trans_le hL)]
    simp [U, V, B, glueFace, not_le.mpr hy.2]
  have hmid : (∫ y in (0 : ℝ)..L, T y) = ∫ y in (0 : ℝ)..L, P y := by
    apply interval_congr_open hL
    intro y hy
    rw [lower_eq y hy.2]
    simp [U, V, P, glueFace, hy.1.le]
  have hhigh : (∫ y in L..L + d, T y) = ∫ y in -d..(0 : ℝ), A y := by
    calc
      _ = ∫ y in L..L + d, A (L - y) := by
        apply interval_congr_open (by linarith)
        intro y hy
        simp [T, A, extendVertical, f, g, U, V, glueFace, flipNormal, not_le.mpr hy.1]
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left, sub_add_eq_sub_sub, sub_self,
        zero_sub]
  have hfar : (∫ y in (0 : ℝ)..3 * d, f (x, y) ^ 2 + g (x, y) ^ 2) =
      ∫ y in L - 3 * d..L, P y := by
    calc
      _ = ∫ y in (0 : ℝ)..3 * d, P (L - y) := by
        apply interval_congr_open (by positivity)
        intro y hy
        simp [f, g, U, V, P, flipNormal, glueFace, hy.2.le.trans hdL]
      _ = _ := by rw [intervalIntegral.integral_comp_sub_left, sub_zero]
  have hh := reflected_slice_displacement_integral_le hf.continuous hg.continuous x hd
  change (∫ y in -d..(0 : ℝ), A y) ≤ _ at hh
  rw [hfar] at hh
  have hbnd := reflected_slice_displacement_integral_le hu.continuous hv.continuous x hd
  change (∫ y in -d..(0 : ℝ), B y) ≤ 2304 * ∫ y in (0 : ℝ)..3 * d, P y at hbnd
  have hh' := intervalIntegral.integral_mono_interval (μ := volume)
    (sub_nonneg.mpr hdL) (sub_le_self _ (by positivity)) le_rfl
    (Eventually.of_forall hn) (hP.intervalIntegrable 0 L)
  have hb' := intervalIntegral.integral_mono_interval (μ := volume)
    le_rfl (show (0 : ℝ) ≤ 3 * d by positivity) hdL
    (Eventually.of_forall hn) (hP.intervalIntegrable 0 L)
  change (∫ y in -d..L + d, T y) ≤ 4609 * ∫ y in (0 : ℝ)..L, P y
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hT.intervalIntegrable (-d) 0) (hT.intervalIntegrable 0 (L + d)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hT.intervalIntegrable 0 L) (hT.intervalIntegrable L (L + d)), hlow, hmid, hhigh]
  linarith only [hbnd, hh, hh', hb']

/-- Place the horizontal coordinate in the normal slot, with the left edge sent to zero. -/
def toHorizontalFace (a : ℝ) (p : Plane) : Plane := (p.2, p.1 - a)

def fromHorizontalFace (a : ℝ) (p : Plane) : Plane := (p.2 + a, p.1)

private noncomputable def swapLinear : Plane →L[ℝ] Plane :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

private theorem fromHorizontal_hasFDeriv (a : ℝ) (p : Plane) :
    HasFDerivAt (fromHorizontalFace a) swapLinear p := by
  have hh := (swapLinear.hasFDerivAt (x := p)).add (hasFDerivAt_const ((a, 0) : Plane) p)
  have he : ((swapLinear : Plane → Plane) + fun _ => (a, 0)) = fromHorizontalFace a := by
    funext q
    change (q.2 + a, q.1 + 0) = (q.2 + a, q.1)
    rw [add_zero]
  rw [he, add_zero] at hh
  exact hh

/-- Exchanging the coordinate and displacement axes preserves the squared strain. -/
theorem fromHorizontal_strain_sq (a : ℝ) {u v : Plane → ℝ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (p : Plane) :
    strainComponentSq (strainComponents (v ∘ fromHorizontalFace a) (u ∘ fromHorizontalFace a) p) =
      strainComponentSq (strainComponents u v (fromHorizontalFace a p)) := by
  have hu' := ((hu (fromHorizontalFace a p)).hasFDerivAt.comp p
    (fromHorizontal_hasFDeriv a p)).fderiv
  have hv' := ((hv (fromHorizontalFace a p)).hasFDerivAt.comp p
    (fromHorizontal_hasFDeriv a p)).fderiv
  have h1 : swapLinear (1, 0) = (0, 1) := rfl
  have h2 : swapLinear (0, 1) = (1, 0) := rfl
  unfold strainComponentSq strainComponents
  rw [hu', hv']
  simp only [ContinuousLinearMap.comp_apply, h1, h2]
  ring

private theorem from_to_horizontal (a : ℝ) (p : Plane) :
    fromHorizontalFace a (toHorizontalFace a p) = p := by
  apply Prod.ext
  · exact sub_add_cancel _ _
  · rfl

/-- Apply the same two-sided construction in the other coordinate direction. -/
noncomputable def extendRectangle (a b L : ℝ) (u v : Plane → ℝ) :
    (Plane → ℝ) × (Plane → ℝ) :=
  let V := extendVertical L u v
  let H := extendVertical (b - a) (V.2 ∘ fromHorizontalFace a) (V.1 ∘ fromHorizontalFace a)
  (H.2 ∘ toHorizontalFace a, H.1 ∘ toHorizontalFace a)

theorem extendRectangle_contDiff (a b L : ℝ) {u v : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (extendRectangle a b L u v).1 ∧
      ContDiff ℝ 1 (extendRectangle a b L u v).2 := by
  obtain ⟨hU, hV⟩ := extendVertical_contDiff L hu hv
  have hfrom : ContDiff ℝ 1 (fromHorizontalFace a) := by unfold fromHorizontalFace; fun_prop
  have hto : ContDiff ℝ 1 (toHorizontalFace a) := by unfold toHorizontalFace; fun_prop
  obtain ⟨hT, hN⟩ := extendVertical_contDiff (b - a) (hV.comp hfrom) (hU.comp hfrom)
  exact ⟨hN.comp hto, hT.comp hto⟩

theorem extendRectangle_eq_on (a b L : ℝ) (u v : Plane → ℝ) (p : Plane)
    (hl : a ≤ p.1) (hr : p.1 ≤ b) (hb : 0 ≤ p.2) (ht : p.2 ≤ L) :
    (extendRectangle a b L u v).1 p = u p ∧ (extendRectangle a b L u v).2 p = v p := by
  have hh := extendVertical_eq_on (b - a)
    ((extendVertical L u v).2 ∘ fromHorizontalFace a)
    ((extendVertical L u v).1 ∘ fromHorizontalFace a)
    (toHorizontalFace a p) (sub_nonneg.mpr hl) (sub_le_sub_right hr a)
  have hv := extendVertical_eq_on L u v p hb ht
  dsimp only [extendRectangle, Function.comp_apply]
  exact ⟨hh.2.trans (by rw [Function.comp_apply, from_to_horizontal]; exact hv.1),
    hh.1.trans (by rw [Function.comp_apply, from_to_horizontal]; exact hv.2)⟩

private theorem to_from_horizontal (a : ℝ) (p : Plane) :
    toHorizontalFace a (fromHorizontalFace a p) = p := by
  apply Prod.ext
  · rfl
  · exact add_sub_cancel_right _ _

/-- After the vertical extension, the same strip bound controls the extra horizontal sides. -/
theorem extendRectangle_horizontal_strain_integral_le {a b L d : ℝ}
    (hd : 0 ≤ d) (hdb : 3 * d ≤ b - a)
    {u v : Plane → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (y : ℝ) :
    (∫ x in a - d..b + d, strainComponentSq (strainComponents
      (extendRectangle a b L u v).1 (extendRectangle a b L u v).2 (x, y))) ≤
    18433 * ∫ x in a..b, strainComponentSq
      (strainComponents (extendVertical L u v).1 (extendVertical L u v).2 (x, y)) := by
  let V := extendVertical L u v
  let f := V.2 ∘ fromHorizontalFace a
  let g := V.1 ∘ fromHorizontalFace a
  let H := extendVertical (b - a) f g
  let R := extendRectangle a b L u v
  obtain ⟨hV1, hV2⟩ := extendVertical_contDiff L hu hv
  obtain ⟨hR1, hR2⟩ := extendRectangle_contDiff a b L hu hv
  have hfrom : ContDiff ℝ 1 (fromHorizontalFace a) := by unfold fromHorizontalFace; fun_prop
  have hf : ContDiff ℝ 1 f := hV2.comp hfrom
  have hg : ContDiff ℝ 1 g := hV1.comp hfrom
  have hc1 : R.2 ∘ fromHorizontalFace a = H.1 := by
    funext p
    change H.1 (toHorizontalFace a (fromHorizontalFace a p)) = H.1 p
    rw [to_from_horizontal]
  have hc2 : R.1 ∘ fromHorizontalFace a = H.2 := by
    funext p
    change H.2 (toHorizontalFace a (fromHorizontalFace a p)) = H.2 p
    rw [to_from_horizontal]
  have hl (x : ℝ) : strainComponentSq (strainComponents H.1 H.2 (y, x)) =
      strainComponentSq (strainComponents R.1 R.2 (x + a, y)) := by
    rw [← hc1, ← hc2]
    exact fromHorizontal_strain_sq a (hR1.differentiable one_ne_zero)
      (hR2.differentiable one_ne_zero) (y, x)
  have hr (x : ℝ) : strainComponentSq (strainComponents f g (y, x)) =
      strainComponentSq (strainComponents V.1 V.2 (x + a, y)) :=
    fromHorizontal_strain_sq a (hV1.differentiable one_ne_zero) (hV2.differentiable one_ne_zero) (y, x)
  have h := extendVertical_strain_integral_le hd hdb hf hg y
  change (∫ x in -d..(b - a) + d, strainComponentSq (strainComponents H.1 H.2 (y, x))) ≤
    18433 * ∫ x in (0 : ℝ)..b - a, strainComponentSq (strainComponents f g (y, x)) at h
  simp_rw [hl, hr] at h
  rw [intervalIntegral.integral_comp_add_right
      (f := fun z => strainComponentSq (strainComponents R.1 R.2 (z, y))) a,
    intervalIntegral.integral_comp_add_right
      (f := fun z => strainComponentSq (strainComponents V.1 V.2 (z, y))) a] at h
  rw [show -d + a = a - d by ring, show b - a + d + a = b + d by ring, zero_add,
    sub_add_cancel] at h
  exact h

/-- The strain energy of the four-edge extension on the enlarged rectangle is uniformly
controlled by its original strain energy. -/
theorem extendRectangle_strain_integral_le {a b L d : ℝ}
    (hd : 0 ≤ d) (hdx : 3 * d ≤ b - a) (hdy : 3 * d ≤ L)
    {u v : Plane → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    (∫ p : Plane, strainComponentSq (strainComponents
      (extendRectangle a b L u v).1 (extendRectangle a b L u v).2 p)
        ∂((volume.restrict (Ioc (a - d) (b + d))).prod (volume.restrict (Ioc (-d) (L + d))))) ≤
    18433 ^ 2 * ∫ p : Plane, strainComponentSq (strainComponents u v p)
      ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc 0 L))) := by
  let X := volume.restrict (Ioc a b)
  let Y := volume.restrict (Ioc 0 L)
  let X' := volume.restrict (Ioc (a - d) (b + d))
  let Y' := volume.restrict (Ioc (-d) (L + d))
  let P := fun p => strainComponentSq (strainComponents u v p)
  let V := fun p => strainComponentSq (strainComponents
    (extendVertical L u v).1 (extendVertical L u v).2 p)
  let T := fun p => strainComponentSq (strainComponents
    (extendRectangle a b L u v).1 (extendRectangle a b L u v).2 p)
  have hcont {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
      Continuous fun p => strainComponentSq (strainComponents f g p) := by
    have hF := hf.continuous_fderiv one_ne_zero
    have hG := hg.continuous_fderiv one_ne_zero
    unfold strainComponentSq strainComponents
    dsimp
    fun_prop
  have hInt (f : Plane → ℝ) (hf : Continuous f) (e₁ e₂ e₃ e₄ : ℝ) :
      Integrable f ((volume.restrict (Ioc e₁ e₂)).prod (volume.restrict (Ioc e₃ e₄))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  obtain ⟨hV1, hV2⟩ := extendVertical_contDiff L hu hv
  obtain ⟨hT1, hT2⟩ := extendRectangle_contDiff a b L hu hv
  have hP : Integrable P (X.prod Y) := hInt _ (hcont hu hv) _ _ _ _
  have hV : Integrable V (X.prod Y') := hInt _ (hcont hV1 hV2) _ _ _ _
  have hT : Integrable T (X'.prod Y') := hInt _ (hcont hT1 hT2) _ _ _ _
  have hab : a ≤ b := sub_nonneg.mp ((mul_nonneg (by norm_num) hd).trans hdx)
  have hL : 0 ≤ L := (mul_nonneg (by norm_num) hd).trans hdy
  have hh : (∫ p, T p ∂(X'.prod Y')) ≤ 18433 * ∫ p, V p ∂(X.prod Y') := by
    rw [integral_prod_symm _ hT, integral_prod_symm _ hV, ← integral_const_mul]
    refine integral_mono hT.integral_prod_right (hV.integral_prod_right.const_mul _) fun y => ?_
    change (∫ x in Ioc (a - d) (b + d), T (x, y)) ≤ 18433 * ∫ x in Ioc a b, V (x, y)
    rw [← intervalIntegral.integral_of_le (show a - d ≤ b + d by linarith),
      ← intervalIntegral.integral_of_le hab]
    exact extendRectangle_horizontal_strain_integral_le hd hdx hu hv y
  have hv' : (∫ p, V p ∂(X.prod Y')) ≤ 18433 * ∫ p, P p ∂(X.prod Y) := by
    rw [integral_prod _ hV, integral_prod _ hP, ← integral_const_mul]
    refine integral_mono hV.integral_prod_left (hP.integral_prod_left.const_mul _) fun x => ?_
    change (∫ y in Ioc (-d) (L + d), V (x, y)) ≤ 18433 * ∫ y in Ioc 0 L, P (x, y)
    rw [← intervalIntegral.integral_of_le (show -d ≤ L + d by linarith),
      ← intervalIntegral.integral_of_le hL]
    exact extendVertical_strain_integral_le hd hdy hu hv x
  change (∫ p, T p ∂(X'.prod Y')) ≤ 18433 ^ 2 * ∫ p, P p ∂(X.prod Y)
  exact hh.trans (by simpa only [pow_two, mul_assoc] using
    mul_le_mul_of_nonneg_left hv' (show (0 : ℝ) ≤ 18433 by norm_num))

/-- The horizontal extension controls squared displacement on each tangential slice. -/
theorem extendRectangle_horizontal_displacement_integral_le {a b L d : ℝ}
    (hd : 0 ≤ d) (hdb : 3 * d ≤ b - a)
    {u v : Plane → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (y : ℝ) :
    (∫ x in a - d..b + d, ((extendRectangle a b L u v).1 (x, y) ^ 2 + (extendRectangle a b L u v).2 (x, y) ^ 2)) ≤
    4609 * ∫ x in a..b, ((extendVertical L u v).1 (x, y) ^ 2 + (extendVertical L u v).2 (x, y) ^ 2) := by
  let V := extendVertical L u v
  let f := V.2 ∘ fromHorizontalFace a
  let g := V.1 ∘ fromHorizontalFace a
  let H := extendVertical (b - a) f g
  let R := extendRectangle a b L u v
  obtain ⟨hV1, hV2⟩ := extendVertical_contDiff L hu hv
  have hfrom : ContDiff ℝ 1 (fromHorizontalFace a) := by unfold fromHorizontalFace; fun_prop
  have hf : ContDiff ℝ 1 f := hV2.comp hfrom
  have hg : ContDiff ℝ 1 g := hV1.comp hfrom
  have hc1 : R.2 ∘ fromHorizontalFace a = H.1 := by
    funext p
    change H.1 (toHorizontalFace a (fromHorizontalFace a p)) = H.1 p
    rw [to_from_horizontal]
  have hc2 : R.1 ∘ fromHorizontalFace a = H.2 := by
    funext p
    change H.2 (toHorizontalFace a (fromHorizontalFace a p)) = H.2 p
    rw [to_from_horizontal]
  have hl (x : ℝ) : (H.1 (y, x) ^ 2 + H.2 (y, x) ^ 2) =
      (R.1 (x + a, y) ^ 2 + R.2 (x + a, y) ^ 2) := by
    rw [← hc1, ← hc2]
    exact add_comm _ _
  have hr (x : ℝ) : (f (y, x) ^ 2 + g (y, x) ^ 2) =
      (V.1 (x + a, y) ^ 2 + V.2 (x + a, y) ^ 2) :=
    add_comm _ _
  have h := extendVertical_displacement_integral_le hd hdb hf hg y
  change (∫ x in -d..(b - a) + d, (H.1 (y, x) ^ 2 + H.2 (y, x) ^ 2)) ≤
    4609 * ∫ x in (0 : ℝ)..b - a, (f (y, x) ^ 2 + g (y, x) ^ 2) at h
  simp_rw [hl, hr] at h
  rw [intervalIntegral.integral_comp_add_right
      (f := fun z => (R.1 (z, y) ^ 2 + R.2 (z, y) ^ 2)) a,
    intervalIntegral.integral_comp_add_right
      (f := fun z => (V.1 (z, y) ^ 2 + V.2 (z, y) ^ 2)) a] at h
  rw [show -d + a = a - d by ring, show b - a + d + a = b + d by ring, zero_add,
    sub_add_cancel] at h
  exact h

/-- The squared displacement of the four-edge extension on the enlarged rectangle is uniformly
controlled by its original squared displacement. -/
theorem extendRectangle_displacement_integral_le {a b L d : ℝ}
    (hd : 0 ≤ d) (hdx : 3 * d ≤ b - a) (hdy : 3 * d ≤ L)
    {u v : Plane → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    (∫ p : Plane, ((extendRectangle a b L u v).1 p ^ 2 + (extendRectangle a b L u v).2 p ^ 2)
        ∂((volume.restrict (Ioc (a - d) (b + d))).prod (volume.restrict (Ioc (-d) (L + d))))) ≤
    4609 ^ 2 * ∫ p : Plane, (u p ^ 2 + v p ^ 2)
      ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc 0 L))) := by
  let X := volume.restrict (Ioc a b)
  let Y := volume.restrict (Ioc 0 L)
  let X' := volume.restrict (Ioc (a - d) (b + d))
  let Y' := volume.restrict (Ioc (-d) (L + d))
  let P := fun p => (u p ^ 2 + v p ^ 2)
  let V := fun p => ((extendVertical L u v).1 p ^ 2 + (extendVertical L u v).2 p ^ 2)
  let T := fun p => ((extendRectangle a b L u v).1 p ^ 2 + (extendRectangle a b L u v).2 p ^ 2)
  have hcont {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
      Continuous fun p => (f p ^ 2 + g p ^ 2) := by
    have hfC := hf.continuous
    have hgC := hg.continuous
    fun_prop
  have hInt (f : Plane → ℝ) (hf : Continuous f) (e₁ e₂ e₃ e₄ : ℝ) :
      Integrable f ((volume.restrict (Ioc e₁ e₂)).prod (volume.restrict (Ioc e₃ e₄))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  obtain ⟨hV1, hV2⟩ := extendVertical_contDiff L hu hv
  obtain ⟨hT1, hT2⟩ := extendRectangle_contDiff a b L hu hv
  have hP : Integrable P (X.prod Y) := hInt _ (hcont hu hv) _ _ _ _
  have hV : Integrable V (X.prod Y') := hInt _ (hcont hV1 hV2) _ _ _ _
  have hT : Integrable T (X'.prod Y') := hInt _ (hcont hT1 hT2) _ _ _ _
  have hab : a ≤ b := sub_nonneg.mp ((mul_nonneg (by norm_num) hd).trans hdx)
  have hL : 0 ≤ L := (mul_nonneg (by norm_num) hd).trans hdy
  have hh : (∫ p, T p ∂(X'.prod Y')) ≤ 4609 * ∫ p, V p ∂(X.prod Y') := by
    rw [integral_prod_symm _ hT, integral_prod_symm _ hV, ← integral_const_mul]
    refine integral_mono hT.integral_prod_right (hV.integral_prod_right.const_mul _) fun y => ?_
    change (∫ x in Ioc (a - d) (b + d), T (x, y)) ≤ 4609 * ∫ x in Ioc a b, V (x, y)
    rw [← intervalIntegral.integral_of_le (show a - d ≤ b + d by linarith),
      ← intervalIntegral.integral_of_le hab]
    exact extendRectangle_horizontal_displacement_integral_le hd hdx hu hv y
  have hv' : (∫ p, V p ∂(X.prod Y')) ≤ 4609 * ∫ p, P p ∂(X.prod Y) := by
    rw [integral_prod _ hV, integral_prod _ hP, ← integral_const_mul]
    refine integral_mono hV.integral_prod_left (hP.integral_prod_left.const_mul _) fun x => ?_
    change (∫ y in Ioc (-d) (L + d), V (x, y)) ≤ 4609 * ∫ y in Ioc 0 L, P (x, y)
    rw [← intervalIntegral.integral_of_le (show -d ≤ L + d by linarith),
      ← intervalIntegral.integral_of_le hL]
    exact extendVertical_displacement_integral_le hd hdy hu hv x
  change (∫ p, T p ∂(X'.prod Y')) ≤ 4609 ^ 2 * ∫ p, P p ∂(X.prod Y)
  exact hh.trans (by simpa only [pow_two, mul_assoc] using
    mul_le_mul_of_nonneg_left hv' (show (0 : ℝ) ≤ 4609 by norm_num))

/-- The extended field has the original full gradient throughout the open rectangle. -/
theorem extendRectangle_fderiv_eq_on (a b L : ℝ) (u v : Plane → ℝ) (p : Plane)
    (hp : p ∈ Ioo a b ×ˢ Ioo 0 L) :
    fderiv ℝ (extendRectangle a b L u v).1 p = fderiv ℝ u p ∧
      fderiv ℝ (extendRectangle a b L u v).2 p = fderiv ℝ v p := by
  have he : ∀ᶠ q in 𝓝 p, (extendRectangle a b L u v).1 q = u q ∧
      (extendRectangle a b L u v).2 q = v q := by
    filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp] with q hq
    exact extendRectangle_eq_on a b L u v q hq.1.1.le hq.1.2.le hq.2.1.le hq.2.2.le
  exact ⟨Filter.EventuallyEq.fderiv_eq (he.mono fun _ h => h.1), Filter.EventuallyEq.fderiv_eq (he.mono fun _ h => h.2)⟩

/-- A smooth cutoff equals one on the closed rectangle and is supported in its enlargement.
The collar width may be chosen arbitrarily small. -/
theorem exists_rectangle_cutoff (a b L : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ χ : Plane → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      EqOn χ (fun _ => 1) (Icc a b ×ˢ Icc 0 L) ∧
      tsupport χ ⊆ Icc (a - d) (b + d) ×ˢ Icc (-d) (L + d) := by
  have hsub : Icc a b ×ˢ Icc 0 L ⊆ Ioo (a - d) (b + d) ×ˢ Ioo (-d) (L + d) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  obtain ⟨χ, hχ, _, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_Ioo.prod isOpen_Ioo) (isClosed_Icc.prod isClosed_Icc) hsub
  have hts : tsupport χ ⊆ Icc (a - d) (b + d) ×ˢ Icc (-d) (L + d) := by
    rw [tsupport, hsupp]
    exact closure_minimal (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
      (isClosed_Icc.prod isClosed_Icc)
  exact ⟨χ, hχ, (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    isClosed_closure hts, fun p hp => (hone p).mp hp, hts⟩

/-- A rectangular C¹ displacement has a compactly supported C¹ extension preserving the
field and its full derivative in the open rectangle. -/
theorem exists_compact_rectangle_extension (a b L : ℝ) {u v : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) {d : ℝ} (hd : 0 < d) :
    ∃ U V : Plane → ℝ, ContDiff ℝ 1 U ∧ ContDiff ℝ 1 V ∧
      HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ p ∈ Ioo a b ×ˢ Ioo 0 L, U p = u p ∧ V p = v p ∧
        fderiv ℝ U p = fderiv ℝ u p ∧ fderiv ℝ V p = fderiv ℝ v p) := by
  obtain ⟨χ, hχ, hc, hone, _⟩ := exists_rectangle_cutoff a b L hd
  obtain ⟨hU, hV⟩ := extendRectangle_contDiff a b L hu hv
  let U := χ * (extendRectangle a b L u v).1
  let V := χ * (extendRectangle a b L u v).2
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  refine ⟨U, V, hχ1.mul hU, hχ1.mul hV, hc.mul_right, hc.mul_right, fun p hp => ?_⟩
  have he : ∀ᶠ q in 𝓝 p, U q = u q ∧ V q = v q := by
    filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp] with q hq
    have hs : χ q = 1 := hone (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hq)
    obtain ⟨hu', hv'⟩ :=
      extendRectangle_eq_on a b L u v q hq.1.1.le hq.1.2.le hq.2.1.le hq.2.2.le
    simp [U, V, hs, hu', hv']
  obtain ⟨hpU, hpV⟩ := he.self_of_nhds
  exact ⟨hpU, hpV, Filter.EventuallyEq.fderiv_eq (he.mono fun _ h => h.1), Filter.EventuallyEq.fderiv_eq (he.mono fun _ h => h.2)⟩

/-- A fixed cutoff on the enlarged rectangle has a uniform strain bound for every field.
Its constant depends on the chosen cutoff, and is independent of the displacement. -/
theorem exists_rectangle_cutoff_with_strain_bound (a b L : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ (χ : Plane → ℝ) (C : ℝ), 0 < C ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      EqOn χ (fun _ => 1) (Icc a b ×ˢ Icc 0 L) ∧
      tsupport χ ⊆ Icc (a - d) (b + d) ×ˢ Icc (-d) (L + d) ∧
      ∀ (u v : Plane → ℝ) (p : Plane), DifferentiableAt ℝ u p → DifferentiableAt ℝ v p →
        strainComponentSq (strainComponents (fun z => χ z * u z) (fun z => χ z * v z) p) ≤
          C * (strainComponentSq (strainComponents u v p) + u p ^ 2 + v p ^ 2) := by
  obtain ⟨χ, hχ, hs, ho, hts⟩ := exists_rectangle_cutoff a b L hd
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hD := hχ1.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hχ1.continuous
  obtain ⟨X, hX⟩ := (hs.fderiv_apply ℝ (1, 0)).exists_bound_of_continuous
    (hD.clm_apply continuous_const)
  obtain ⟨Y, hY⟩ := (hs.fderiv_apply ℝ (0, 1)).exists_bound_of_continuous
    (hD.clm_apply continuous_const)
  let C := 1 + 2 * (M ^ 2 + X ^ 2 + Y ^ 2)
  refine ⟨χ, C, by dsimp [C]; positivity, hχ, hs, ho, hts, fun u v p hu hv => ?_⟩
  have hχp := hχ1.differentiable one_ne_zero p
  have hm : (χ p) ^ 2 ≤ M ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg (χ p)) (hM p) 2
  have hx : (fderiv ℝ χ p (1, 0)) ^ 2 ≤ X ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg (fderiv ℝ χ p (1, 0))) (hX p) 2
  have hy : (fderiv ℝ χ p (0, 1)) ^ 2 ≤ Y ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg (fderiv ℝ χ p (0, 1))) (hY p) 2
  let E := strainComponentSq (strainComponents u v p)
  have hE : 0 ≤ E := by unfold E strainComponentSq; positivity
  have h1 := mul_le_mul_of_nonneg_right hm hE
  have h2 := mul_le_mul_of_nonneg_right (add_le_add hx hy)
    (add_nonneg (sq_nonneg (u p)) (sq_nonneg (v p)))
  refine (cutoff_strain_sq_le hχp hu hv).trans ?_
  change 2 * (χ p) ^ 2 * E +
    2 * ((fderiv ℝ χ p (1, 0)) ^ 2 + (fderiv ℝ χ p (0, 1)) ^ 2) * (u p ^ 2 + v p ^ 2) ≤
    C * (E + u p ^ 2 + v p ^ 2)
  dsimp only [C]
  nlinarith only [h1, h2, hE, sq_nonneg (u p), sq_nonneg (v p),
    mul_nonneg (sq_nonneg M) (add_nonneg (sq_nonneg (u p)) (sq_nonneg (v p))),
    mul_nonneg (add_nonneg (sq_nonneg X) (sq_nonneg Y)) hE]

/-- The cutoff extension controls the whole-plane strain integral by the original
strain and displacement integrals, with a constant fixed by the rectangle. -/
theorem exists_compact_rectangle_extension_integral_le {a b L : ℝ}
    (hab : a < b) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u v : Plane → ℝ}, ContDiff ℝ 1 u → ContDiff ℝ 1 v →
      ∃ U V : Plane → ℝ, ContDiff ℝ 1 U ∧ ContDiff ℝ 1 V ∧
        HasCompactSupport U ∧ HasCompactSupport V ∧
        (∀ p ∈ Ioo a b ×ˢ Ioo 0 L, fderiv ℝ U p = fderiv ℝ u p ∧
          fderiv ℝ V p = fderiv ℝ v p) ∧
        (∫ p, strainComponentSq (strainComponents U V p) ∂((volume : Measure ℝ).prod volume)) ≤
          C * (∫ p, strainComponentSq (strainComponents u v p) + (u p ^ 2 + v p ^ 2)
            ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc 0 L)))) := by
  let d := min (b - a) L / 3
  have hd : 0 < d := div_pos (lt_min (sub_pos.mpr hab) hL) (by norm_num)
  have hdx : 3 * d ≤ b - a := by
    dsimp [d]
    linarith [min_le_left (b - a) L]
  have hdy : 3 * d ≤ L := by
    dsimp [d]
    linarith [min_le_right (b - a) L]
  obtain ⟨χ, K, hK, hχ, hs, ho, hts, hbound⟩ :=
    exists_rectangle_cutoff_with_strain_bound a b L (show 0 < d / 2 by positivity)
  refine ⟨K * 18433 ^ 2, by positivity, ?_⟩
  intro u v hu hv
  let R := extendRectangle a b L u v
  let U := χ * R.1
  let V := χ * R.2
  obtain ⟨hR1, hR2⟩ := extendRectangle_contDiff a b L hu hv
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hU : ContDiff ℝ 1 U := hχ1.mul hR1
  have hV : ContDiff ℝ 1 V := hχ1.mul hR2
  refine ⟨U, V, hU, hV, hs.mul_right, hs.mul_right, ?_, ?_⟩
  · intro p hp
    have he : ∀ᶠ q in 𝓝 p, U q = u q ∧ V q = v q := by
      filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp] with q hq
      have hqχ := ho (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hq)
      obtain ⟨hqU, hqV⟩ :=
        extendRectangle_eq_on a b L u v q hq.1.1.le hq.1.2.le hq.2.1.le hq.2.2.le
      simp [U, V, R, hqχ, hqU, hqV]
    exact ⟨EventuallyEq.fderiv_eq (he.mono fun _ h => h.1),
      EventuallyEq.fderiv_eq (he.mono fun _ h => h.2)⟩
  let μ := (volume.restrict (Ioc a b)).prod (volume.restrict (Ioc 0 L))
  let ν := (volume.restrict (Ioc (a - d) (b + d))).prod (volume.restrict (Ioc (-d) (L + d)))
  let E := fun p => strainComponentSq (strainComponents u v p)
  let D := fun p => u p ^ 2 + v p ^ 2
  let F := fun p => strainComponentSq (strainComponents R.1 R.2 p)
  let G := fun p => R.1 p ^ 2 + R.2 p ^ 2
  let T := fun p => strainComponentSq (strainComponents U V p)
  have hIc (f : Plane → ℝ) (hf : Continuous f) (w x y z : ℝ) :
      Integrable f ((volume.restrict (Ioc w x)).prod (volume.restrict (Ioc y z))) := by
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hEc {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
      Continuous (fun p => strainComponentSq (strainComponents f g p)) := by
    have hdf := hf.continuous_fderiv one_ne_zero
    have hdg := hg.continuous_fderiv one_ne_zero
    unfold strainComponentSq strainComponents
    dsimp
    fun_prop
  have hEi : Integrable E μ := hIc _ (hEc hu hv) _ _ _ _
  have hDi : Integrable D μ := hIc _ (by unfold D; fun_prop) _ _ _ _
  have hFi : Integrable F ν := hIc _ (hEc hR1 hR2) _ _ _ _
  have hGi : Integrable G ν := hIc _ (by
    have h₁ := hR1.continuous
    have h₂ := hR2.continuous
    unfold G
    fun_prop) _ _ _ _
  have hTi : Integrable T ν := hIc _ (hEc hU hV) _ _ _ _
  have hsupport : tsupport χ ⊆ Ioc (a - d) (b + d) ×ˢ Ioc (-d) (L + d) := by
    intro p hp
    have h := hts hp
    exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩,
      ⟨by linarith [h.2.1], by linarith [h.2.2]⟩⟩
  have hrestrict : (∫ p, T p ∂ν) = ∫ p, T p ∂((volume : Measure ℝ).prod volume) := by
    unfold ν
    rw [Measure.prod_restrict]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    have hx : p ∉ tsupport χ := fun h => hp (hsupport h)
    have he : ∀ᶠ q in 𝓝 p, χ q = 0 := by
      filter_upwards [(isClosed_closure : IsClosed (tsupport χ)).isOpen_compl.mem_nhds hx] with q hq
      exact image_eq_zero_of_notMem_tsupport hq
    have heU : U =ᶠ[𝓝 p] (fun _ => 0) := he.mono fun q hq => by simp [U, hq]
    have heV : V =ᶠ[𝓝 p] (fun _ => 0) := he.mono fun q hq => by simp [V, hq]
    simp [T, strainComponentSq, strainComponents, heU.fderiv_eq, heV.fderiv_eq]
  have hmono : (∫ p, T p ∂ν) ≤ ∫ p, K * (F p + G p) ∂ν := by
    refine integral_mono hTi ((hFi.add hGi).const_mul K) fun p => ?_
    have h := hbound R.1 R.2 p (hR1.differentiable one_ne_zero p)
      (hR2.differentiable one_ne_zero p)
    change strainComponentSq (strainComponents (fun z => χ z * R.1 z)
      (fun z => χ z * R.2 z) p) ≤ K * (F p + G p)
    simpa only [F, G, add_assoc] using h
  have hF := extendRectangle_strain_integral_le hd.le hdx hdy hu hv
  have hG := extendRectangle_displacement_integral_le hd.le hdx hdy hu hv
  change (∫ p, F p ∂ν) ≤ 18433 ^ 2 * ∫ p, E p ∂μ at hF
  change (∫ p, G p ∂ν) ≤ 4609 ^ 2 * ∫ p, D p ∂μ at hG
  have hD : 0 ≤ ∫ p, D p ∂μ := integral_nonneg fun p => by unfold D; positivity
  change (∫ p, T p ∂((volume : Measure ℝ).prod volume)) ≤ K * 18433 ^ 2 * ∫ p, E p + D p ∂μ
  rw [← hrestrict, integral_add hEi hDi]
  rw [integral_const_mul, integral_add hFi hGi] at hmono
  refine hmono.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hK.le
  linarith only [hF, hG, hD]

/-- Squared Frobenius norm of the planar displacement gradient. -/
noncomputable def planeGradSq (u v : Plane → ℝ) (p : Plane) : ℝ :=
  (fderiv ℝ u p (1, 0)) ^ 2 + (fderiv ℝ u p (0, 1)) ^ 2 +
    (fderiv ℝ v p (1, 0)) ^ 2 + (fderiv ℝ v p (0, 1)) ^ 2

/-- Whole-space Korn in Cartesian product coordinates. -/
theorem plane_korn_first_c1 {u v : Plane → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hcu : HasCompactSupport u) (hcv : HasCompactSupport v) :
    (∫ p, planeGradSq u v p ∂((volume : Measure ℝ).prod volume)) ≤
      2 * ∫ p, strainComponentSq (strainComponents u v p) ∂((volume : Measure ℝ).prod volume) := by
  let e := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let w : Fin 2 → (Fin 2 → ℝ) → ℝ := ![u ∘ e, v ∘ e]
  have hw : ∀ i, ContDiff ℝ 1 (w i) := by
    intro i
    fin_cases i
    · exact hu.comp e.contDiff
    · exact hv.comp e.contDiff
  have hs : ∀ i, HasCompactSupport (w i) := by
    intro i
    fin_cases i
    · exact hcu.comp_homeomorph e.toHomeomorph
    · exact hcv.comp_homeomorph e.toHomeomorph
  have hx (x : Fin 2 → ℝ) (f : Plane → ℝ) (hf : ContDiff ℝ 1 f) (j : Fin 2) :
      LeanSolid.Math.partialDeriv (f ∘ e) j x =
        fderiv ℝ f (e x) (e (Pi.single j 1)) := by
    unfold LeanSolid.Math.partialDeriv
    rw [fderiv_comp x (hf.differentiable one_ne_zero (e x)) e.differentiableAt,
      e.fderiv]
    rfl
  have e0 : e (Pi.single 0 1) = (1, 0) := by
    change ((Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) 0, (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) 1) = _
    simp [Pi.single]
  have e1 : e (Pi.single 1 1) = (0, 1) := by
    change ((Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) 0, (Pi.single 1 (1 : ℝ) : Fin 2 → ℝ) 1) = _
    simp [Pi.single]
  have hg : gradSq w = planeGradSq u v ∘ e := by
    funext x
    simp only [gradSq, Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one,
      hx _ _ hu, hx _ _ hv, e0, e1, Function.comp_apply, planeGradSq]
    ring
  have he : strainSq w = (fun p => strainComponentSq (strainComponents u v p)) ∘ e := by
    funext x
    simp only [strainSq, Fin.sum_univ_two, w, Matrix.cons_val_zero, Matrix.cons_val_one,
      hx _ _ hu, hx _ _ hv, e0, e1, Function.comp_apply,
      strainComponentSq, strainComponents]
    ring
  have hm := volume_preserving_finTwoArrow ℝ
  have h := korn_first_c1 hw hs
  rw [hg, he] at h
  change (∫ x, planeGradSq u v (MeasurableEquiv.finTwoArrow x)) ≤
    2 * ∫ x, strainComponentSq (strainComponents u v (MeasurableEquiv.finTwoArrow x)) at h
  rw [hm.integral_comp MeasurableEquiv.finTwoArrow.measurableEmbedding (planeGradSq u v),
    hm.integral_comp MeasurableEquiv.finTwoArrow.measurableEmbedding
      (fun p => strainComponentSq (strainComponents u v p))] at h
  exact h

/-- Second Korn inequality on a nondegenerate planar rectangle for C¹ displacement fields. -/
theorem rectangle_second_korn_integral {a b L : ℝ} (hab : a < b) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u v : Plane → ℝ}, ContDiff ℝ 1 u → ContDiff ℝ 1 v →
      (∫ p, planeGradSq u v p ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo 0 L)))) ≤
        C * (∫ p, strainComponentSq (strainComponents u v p) + (u p ^ 2 + v p ^ 2)
          ∂((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo 0 L)))) := by
  obtain ⟨K, hK, h⟩ := exists_compact_rectangle_extension_integral_le hab hL
  refine ⟨2 * K, by positivity, ?_⟩
  intro u v hu hv
  obtain ⟨U, V, hU, hV, hcU, hcV, he, hE⟩ := h hu hv
  let S := Ioo a b ×ˢ Ioo 0 L
  let μ : Measure Plane := (volume : Measure ℝ).prod volume
  have hs : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hgrad : Continuous (planeGradSq U V) := by
    have hdu := hU.continuous_fderiv one_ne_zero
    have hdv := hV.continuous_fderiv one_ne_zero
    unfold planeGradSq
    fun_prop
  have hcs : HasCompactSupport (planeGradSq U V) := by
    unfold planeGradSq
    have hsq {f : Plane → ℝ} (hf : HasCompactSupport f) :
        HasCompactSupport (fun p => f p ^ 2) := by
      refine hf.mono' fun p hp => subset_tsupport _ ?_
      rw [Function.mem_support] at hp ⊢
      exact fun h => hp (by simp [h])
    exact (((hsq (hcU.fderiv_apply ℝ (1, 0))).add
      (hsq (hcU.fderiv_apply ℝ (0, 1)))).add
      (hsq (hcV.fderiv_apply ℝ (1, 0)))).add
      (hsq (hcV.fderiv_apply ℝ (0, 1)))
  have hmono : (∫ p in S, planeGradSq U V p ∂μ) ≤ ∫ p, planeGradSq U V p ∂μ :=
    setIntegral_le_integral (hgrad.integrable_of_hasCompactSupport hcs)
      (Filter.Eventually.of_forall fun p => by unfold planeGradSq; positivity)
  have heq : (∫ p in S, planeGradSq u v p ∂μ) = ∫ p in S, planeGradSq U V p ∂μ := by
    apply setIntegral_congr_fun hs
    intro p hp
    obtain ⟨h₁, h₂⟩ := he p hp
    simp only [planeGradSq, h₁, h₂]
  rw [← restrict_Ioo_eq_restrict_Ioc, ← restrict_Ioo_eq_restrict_Ioc] at hE
  rw [Measure.prod_restrict] at hE
  rw [Measure.prod_restrict]
  change (∫ p in S, planeGradSq u v p ∂μ) ≤ _
  rw [heq, mul_assoc]
  exact hmono.trans ((plane_korn_first_c1 hU hV hcU hcV).trans
    (mul_le_mul_of_nonneg_left hE (by norm_num)))

end LeanSolid.Elastostatics.Korn
