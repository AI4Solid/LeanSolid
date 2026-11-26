module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open scoped Topology

@[expose] public section

namespace LeanSolid.Elastostatics.Korn

open MeasureTheory

abbrev Plane := ℝ × ℝ

/-- Across a horizontal face, sample at depth `-c * y` while retaining the tangential coordinate. -/
noncomputable def reflectionSample (c : ℝ) : Plane →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((-c) • ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem reflectionSample_apply (c : ℝ) (p : Plane) :
    reflectionSample c p = (p.1, -c * p.2) := rfl

/-- The reflected tangential component before gluing it to the interior field. -/
noncomputable def reflectedTangent (u : Plane → ℝ) (p : Plane) : ℝ :=
  6 * u (reflectionSample 1 p) - 8 * u (reflectionSample 2 p) + 3 * u (reflectionSample 3 p)

/-- The reflected normal component uses coefficients that match the reflected shear terms. -/
noncomputable def reflectedNormal (v : Plane → ℝ) (p : Plane) : ℝ :=
  -6 * v (reflectionSample 1 p) + 16 * v (reflectionSample 2 p) - 9 * v (reflectionSample 3 p)

/-- Two-dimensional symmetric gradient components, storing twice the shear strain. -/
noncomputable def strainComponents (u v : Plane → ℝ) (p : Plane) : ℝ × ℝ × ℝ :=
  (fderiv ℝ u p (1, 0), fderiv ℝ v p (0, 1),
    fderiv ℝ u p (0, 1) + fderiv ℝ v p (1, 0))

private theorem reflect_fderiv {f : Plane → ℝ} (hf : Differentiable ℝ f)
    (c : ℝ) (p : Plane) :
    fderiv ℝ (fun z => f (reflectionSample c z)) p =
      (fderiv ℝ f (reflectionSample c p)).comp (reflectionSample c) :=
  ((hf _).hasFDerivAt.comp p (reflectionSample c).hasFDerivAt).fderiv

private theorem reflect_dirs (c : ℝ) :
    reflectionSample c (1, 0) = (1, 0) ∧
    reflectionSample c (0, 1) = (-c) • ((0, 1) : Plane) := by
  constructor <;> ext <;> simp [reflectionSample]

private theorem tangent_fderiv {u : Plane → ℝ} (hu : Differentiable ℝ u) (p : Plane) :
    fderiv ℝ (reflectedTangent u) p =
      (6 : ℝ) • (fderiv ℝ u (reflectionSample 1 p)).comp (reflectionSample 1) -
      (8 : ℝ) • (fderiv ℝ u (reflectionSample 2 p)).comp (reflectionSample 2) +
      (3 : ℝ) • (fderiv ℝ u (reflectionSample 3 p)).comp (reflectionSample 3) := by
  have hd (c : ℝ) : Differentiable ℝ (fun z => u (reflectionSample c z)) :=
    hu.comp (reflectionSample c).differentiable
  have h1 := ((hd 1 p).hasFDerivAt.const_mul 6).sub ((hd 2 p).hasFDerivAt.const_mul 8)
  have h := (h1.add ((hd 3 p).hasFDerivAt.const_mul 3)).fderiv
  change fderiv ℝ (reflectedTangent u) p = _ at h
  simpa only [reflect_fderiv hu] using h

private theorem normal_fderiv {v : Plane → ℝ} (hv : Differentiable ℝ v) (p : Plane) :
    fderiv ℝ (reflectedNormal v) p =
      (-6 : ℝ) • (fderiv ℝ v (reflectionSample 1 p)).comp (reflectionSample 1) +
      (16 : ℝ) • (fderiv ℝ v (reflectionSample 2 p)).comp (reflectionSample 2) -
      (9 : ℝ) • (fderiv ℝ v (reflectionSample 3 p)).comp (reflectionSample 3) := by
  have hd (c : ℝ) : Differentiable ℝ (fun z => v (reflectionSample c z)) :=
    hv.comp (reflectionSample c).differentiable
  have h1 := ((hd 1 p).hasFDerivAt.const_mul (-6)).add ((hd 2 p).hasFDerivAt.const_mul 16)
  have h := (h1.sub ((hd 3 p).hasFDerivAt.const_mul 9)).fderiv
  change fderiv ℝ (reflectedNormal v) p = _ at h
  simpa only [reflect_fderiv hv] using h

/-- Every component of the reflected strain depends only on the corresponding original
strain component at the three samples, with no contribution from the skew gradient. -/
theorem reflected_strain_components {u v : Plane → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (p : Plane) :
    let e₁ := strainComponents u v (reflectionSample 1 p)
    let e₂ := strainComponents u v (reflectionSample 2 p)
    let e₃ := strainComponents u v (reflectionSample 3 p)
    strainComponents (reflectedTangent u) (reflectedNormal v) p =
      (6 * e₁.1 - 8 * e₂.1 + 3 * e₃.1,
       6 * e₁.2.1 - 32 * e₂.2.1 + 27 * e₃.2.1,
       -6 * e₁.2.2 + 16 * e₂.2.2 - 9 * e₃.2.2) := by
  dsimp only [strainComponents]
  rw [tangent_fderiv hu, normal_fderiv hv]
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    (reflect_dirs _).1, (reflect_dirs _).2, map_smul, smul_eq_mul]
  apply Prod.ext
  · ring
  · apply Prod.ext <;> ring

private theorem reflectionSample_on_face (c x : ℝ) : reflectionSample c (x, 0) = (x, 0) := by
  ext <;> simp [reflectionSample]

/-- Both reflected displacement components agree with the original on the gluing line. -/
theorem reflection_on_face (u v : Plane → ℝ) (x : ℝ) :
    reflectedTangent u (x, 0) = u (x, 0) ∧ reflectedNormal v (x, 0) = v (x, 0) := by
  simp only [reflectedTangent, reflectedNormal, reflectionSample_on_face]
  constructor <;> ring

private theorem reflectionSample_split (c : ℝ) (p : Plane) :
    reflectionSample c p = p.1 • ((1, 0) : Plane) + (-c * p.2) • ((0, 1) : Plane) := by
  ext <;> simp [reflectionSample]

/-- The coefficients additionally match the entire first derivative at the gluing line. -/
theorem reflection_fderiv_on_face {u v : Plane → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (x : ℝ) :
    fderiv ℝ (reflectedTangent u) (x, 0) = fderiv ℝ u (x, 0) ∧
    fderiv ℝ (reflectedNormal v) (x, 0) = fderiv ℝ v (x, 0) := by
  rw [tangent_fderiv hu, normal_fderiv hv]
  simp only [reflectionSample_on_face]
  constructor
  all_goals
    apply ContinuousLinearMap.ext
    intro p
    simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      reflectionSample_split, map_add, map_smul, smul_eq_mul]
    conv_rhs =>
      rw [show p = p.1 • ((1, 0) : Plane) + p.2 • ((0, 1) : Plane) by
        ext <;> simp]
    simp only [map_add, map_smul, smul_eq_mul]
    ring

/-- Glue the original field above the face to a reflected expression below it. -/
noncomputable def glueFace {F : Type*} (f g : Plane → F) (p : Plane) : F :=
  if 0 ≤ p.2 then f p else g p

private theorem glueFace_contDiff {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hval : ∀ x : ℝ, f (x, 0) = g (x, 0))
    (hder : ∀ x : ℝ, fderiv ℝ f (x, 0) = fderiv ℝ g (x, 0)) :
    ContDiff ℝ 1 (glueFace f g) := by
  let upper := {p : Plane | 0 ≤ p.2}
  let lower := {p : Plane | p.2 ≤ 0}
  let D := glueFace (fderiv ℝ f) (fderiv ℝ g)
  have hcover : upper ∪ lower = Set.univ := by
    ext p
    simp only [upper, lower, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_total 0 p.2
  have hEqUpper {F : Type} (a b : Plane → F) : Set.EqOn (glueFace a b) a upper :=
    fun p hp => ite_eq_left hp
  have hEqLower {F : Type} (a b : Plane → F) (h : ∀ x : ℝ, a (x, 0) = b (x, 0)) :
      Set.EqOn (glueFace a b) b lower := by
    intro p hp
    by_cases hpos : 0 ≤ p.2
    · have hzero : p.2 = 0 := le_antisymm hp hpos
      rw [glueFace, ite_eq_left hpos]
      exact (show p = (p.1, 0) from Prod.ext rfl hzero) ▸ h p.1
    · exact ite_eq_right hpos
  have hDu : ContinuousOn D upper :=
    (hf.continuous_fderiv one_ne_zero).continuousOn.congr (hEqUpper _ _)
  have hDl : ContinuousOn D lower :=
    (hg.continuous_fderiv one_ne_zero).continuousOn.congr (hEqLower _ _ hder)
  have hD := hDu.union_of_isClosed hDl (isClosed_le continuous_const continuous_snd)
    (isClosed_le continuous_snd continuous_const)
  rw [hcover, continuousOn_univ] at hD
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨D, hD, fun p => ?_⟩
  rcases lt_trichotomy p.2 0 with hneg | hzero | hpos
  · have h := (hg.differentiable one_ne_zero p).hasFDerivAt
    rw [show D p = fderiv ℝ g p from ite_eq_right (not_le.mpr hneg)]
    apply h.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hneg] with z hz
    exact ite_eq_right (not_le.mpr hz)
  · have hp : p = (p.1, 0) := Prod.ext rfl hzero
    have he : fderiv ℝ f p = fderiv ℝ g p := by rw [hp]; exact hder _
    have hu : p ∈ upper := by simp [upper, hzero]
    have hl : p ∈ lower := by simp [lower, hzero]
    rw [show D p = fderiv ℝ f p from ite_eq_left hu]
    have h1 := (hf.differentiable one_ne_zero p).hasFDerivAt.hasFDerivWithinAt
      (s := upper)
    have h2 := (hg.differentiable one_ne_zero p).hasFDerivAt.hasFDerivWithinAt
      (s := lower)
    rw [← he] at h2
    have h := (h1.congr' (hEqUpper _ _) hu).union (h2.congr' (hEqLower _ _ hval) hl)
    rwa [hcover, hasFDerivWithinAt_univ] at h
  · have h := (hf.differentiable one_ne_zero p).hasFDerivAt
    rw [show D p = fderiv ℝ f p from ite_eq_left hpos.le]
    apply h.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hpos] with z hz
    exact ite_eq_left (le_of_lt hz)

/-- The single-face elastic reflection preserves C¹ regularity across the interface. -/
theorem reflection_contDiff {u v : Plane → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (glueFace u (reflectedTangent u)) ∧
      ContDiff ℝ 1 (glueFace v (reflectedNormal v)) := by
  have hdu := hu.differentiable one_ne_zero
  have hdv := hv.differentiable one_ne_zero
  constructor
  · apply glueFace_contDiff hu
    · unfold reflectedTangent
      fun_prop
    · exact fun x => (reflection_on_face u v x).1.symm
    · exact fun x => (reflection_fderiv_on_face hdu hdv x).1.symm
  · apply glueFace_contDiff hv
    · unfold reflectedNormal
      fun_prop
    · exact fun x => (reflection_on_face u v x).2.symm
    · exact fun x => (reflection_fderiv_on_face hdu hdv x).2.symm

/-- Frobenius strain energy, using a tuple whose last entry stores twice the shear. -/
noncomputable def strainComponentSq (E : ℝ × ℝ × ℝ) : ℝ :=
  E.1 ^ 2 + E.2.1 ^ 2 + E.2.2 ^ 2 / 2

private theorem three_term_sq (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith only [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- The reflected elastic energy density is bounded by the reflected samples of the
original strain energy density. This estimate is uniform in the field and point. -/
theorem reflected_strain_sq_le {u v : Plane → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (p : Plane) :
    strainComponentSq (strainComponents (reflectedTangent u) (reflectedNormal v) p) ≤
      3072 * (strainComponentSq (strainComponents u v (reflectionSample 1 p)) +
        strainComponentSq (strainComponents u v (reflectionSample 2 p)) +
        strainComponentSq (strainComponents u v (reflectionSample 3 p))) := by
  rw [reflected_strain_components hu hv]
  let A := strainComponents u v (reflectionSample 1 p)
  let B := strainComponents u v (reflectionSample 2 p)
  let C := strainComponents u v (reflectionSample 3 p)
  change (6 * A.1 - 8 * B.1 + 3 * C.1) ^ 2 +
    (6 * A.2.1 - 32 * B.2.1 + 27 * C.2.1) ^ 2 +
    (-6 * A.2.2 + 16 * B.2.2 - 9 * C.2.2) ^ 2 / 2 ≤
    3072 * (strainComponentSq A + strainComponentSq B + strainComponentSq C)
  unfold strainComponentSq
  nlinarith only [three_term_sq (6 * A.1) (-8 * B.1) (3 * C.1),
    three_term_sq (6 * A.2.1) (-32 * B.2.1) (27 * C.2.1),
    three_term_sq (-6 * A.2.2) (16 * B.2.2) (-9 * C.2.2),
    sq_nonneg A.1, sq_nonneg B.1, sq_nonneg C.1,
    sq_nonneg A.2.1, sq_nonneg B.2.1, sq_nonneg C.2.1,
    sq_nonneg A.2.2, sq_nonneg B.2.2, sq_nonneg C.2.2]

/-- Below the gluing line the actual extension has the reflected strain. -/
theorem glued_strain_below (u v : Plane → ℝ) (p : Plane) (hp : p.2 < 0) :
    strainComponents (glueFace u (reflectedTangent u)) (glueFace v (reflectedNormal v)) p =
      strainComponents (reflectedTangent u) (reflectedNormal v) p := by
  have hd {f g : Plane → ℝ} :
      fderiv ℝ (glueFace f g) p = fderiv ℝ g p := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hp] with z hz
    exact ite_eq_right (not_le.mpr hz)
  simp only [strainComponents, hd]

/-- The product rule identifies the lower-order displacement term introduced by a cutoff. -/
theorem cutoff_strain_components {χ u v : Plane → ℝ} {p : Plane}
    (hχ : DifferentiableAt ℝ χ p) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    let E := strainComponents u v p
    let χx := fderiv ℝ χ p (1, 0)
    let χy := fderiv ℝ χ p (0, 1)
    strainComponents (fun z => χ z * u z) (fun z => χ z * v z) p =
      (χ p * E.1 + χx * u p, χ p * E.2.1 + χy * v p,
       χ p * E.2.2 + χy * u p + χx * v p) := by
  dsimp only [strainComponents]
  have h1 := (hχ.hasFDerivAt.mul hu.hasFDerivAt).fderiv
  have h2 := (hχ.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  change fderiv ℝ (fun z => χ z * u z) p = _ at h1
  change fderiv ℝ (fun z => χ z * v z) p = _ at h2
  rw [h1, h2]
  simp only [add_apply, smul_apply, smul_eq_mul]
  apply Prod.ext
  · ring
  · apply Prod.ext <;> ring

/-- The strain of a cutoff field is controlled by the original strain and displacement. -/
theorem cutoff_strain_sq_le {χ u v : Plane → ℝ} {p : Plane}
    (hχ : DifferentiableAt ℝ χ p) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    strainComponentSq (strainComponents (fun z => χ z * u z) (fun z => χ z * v z) p) ≤
      2 * (χ p) ^ 2 * strainComponentSq (strainComponents u v p) +
      2 * ((fderiv ℝ χ p (1, 0)) ^ 2 + (fderiv ℝ χ p (0, 1)) ^ 2) * (u p ^ 2 + v p ^ 2) := by
  rw [cutoff_strain_components hχ hu hv]
  let E := strainComponents u v p
  let x := fderiv ℝ χ p (1, 0)
  let y := fderiv ℝ χ p (0, 1)
  change (χ p * E.1 + x * u p) ^ 2 + (χ p * E.2.1 + y * v p) ^ 2 +
    (χ p * E.2.2 + y * u p + x * v p) ^ 2 / 2 ≤
    2 * χ p ^ 2 * strainComponentSq E + 2 * (x ^ 2 + y ^ 2) * (u p ^ 2 + v p ^ 2)
  unfold strainComponentSq
  nlinarith only [sq_nonneg (χ p * E.1 - x * u p), sq_nonneg (χ p * E.2.1 - y * v p),
    sq_nonneg (χ p * E.2.2 - (y * u p + x * v p)), sq_nonneg (y * u p - x * v p)]

private theorem reflected_sample_integral_le {F : ℝ → ℝ} (hF : Continuous F)
    (hn : ∀ y, 0 ≤ F y) {d : ℝ} (hd : 0 ≤ d) {c : ℝ} (hc : 1 ≤ c) (hc' : c ≤ 3) :
    (∫ y in -d..(0 : ℝ), F (-c * y)) ≤ ∫ y in (0 : ℝ)..3 * d, F y := by
  have hp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rw [intervalIntegral.integral_comp_mul_left F (neg_ne_zero.mpr hp.ne'),
    neg_mul_neg, mul_zero, intervalIntegral.integral_symm 0 (c * d),
    inv_neg, smul_eq_mul, neg_mul_neg]
  have h := intervalIntegral.integral_mono_interval (μ := volume)
    (show (0 : ℝ) ≤ 0 from le_rfl) (mul_nonneg hp.le hd)
    (mul_le_mul_of_nonneg_right hc' hd) (Filter.Eventually.of_forall hn)
    (hF.intervalIntegrable 0 (3 * d))
  calc
    c⁻¹ * (∫ y in (0 : ℝ)..c * d, F y) ≤ 1 * ∫ y in (0 : ℝ)..c * d, F y :=
      mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hc)
        (intervalIntegral.integral_nonneg_of_forall (mul_nonneg hp.le hd) hn)
    _ ≤ _ := by simpa only [one_mul] using h

private theorem continuous_strain_sq {u v : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    Continuous (fun p => strainComponentSq (strainComponents u v p)) := by
  have hdu := hu.continuous_fderiv one_ne_zero
  have hdv := hv.continuous_fderiv one_ne_zero
  unfold strainComponentSq strainComponents
  dsimp
  fun_prop

private theorem reflected_contDiff_branches {u v : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (reflectedTangent u) ∧ ContDiff ℝ 1 (reflectedNormal v) := by
  constructor
  · unfold reflectedTangent
    fun_prop
  · unfold reflectedNormal
    fun_prop

/-- The reflected strip's strain integral is controlled by the original normal slice.
The strip reaches depth `d` outside and samples at most depth `3*d` inside. -/
theorem reflected_slice_strain_integral_le {u v : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (x : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (∫ y in -d..(0 : ℝ), strainComponentSq
      (strainComponents (reflectedTangent u) (reflectedNormal v) (x, y))) ≤
      9216 * ∫ y in (0 : ℝ)..3 * d, strainComponentSq (strainComponents u v (x, y)) := by
  let F := fun y => strainComponentSq (strainComponents u v (x, y))
  let T := fun y => strainComponentSq (strainComponents (reflectedTangent u) (reflectedNormal v) (x, y))
  have hF : Continuous F := (continuous_strain_sq hu hv).comp
    (continuous_const.prodMk continuous_id)
  obtain ⟨hU, hV⟩ := reflected_contDiff_branches hu hv
  have hT : Continuous T := (continuous_strain_sq hU hV).comp
    (continuous_const.prodMk continuous_id)
  have G (c : ℝ) : Continuous (fun y => F (-c * y)) := hF.comp (continuous_const.mul continuous_id)
  have hG : Continuous (fun y => 3072 * (F (-1 * y) + F (-2 * y) + F (-3 * y))) :=
    continuous_const.mul (((G 1).add (G 2)).add (G 3))
  have h := intervalIntegral.integral_mono_on (μ := volume) (neg_nonpos.mpr hd)
    (hT.intervalIntegrable (-d) 0)
    (hG.intervalIntegrable (-d) 0) fun y _ => by
      have he := reflected_strain_sq_le (hu.differentiable one_ne_zero)
        (hv.differentiable one_ne_zero) (x, y)
      simpa only [T, F, reflectionSample_apply] using he
  have hG12 : Continuous (fun y => F (-1 * y) + F (-2 * y)) := (G 1).add (G 2)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hG12.intervalIntegrable (-d) 0)
      ((G 3).intervalIntegrable (-d) 0),
    intervalIntegral.integral_add ((G 1).intervalIntegrable (-d) 0)
      ((G 2).intervalIntegrable (-d) 0)] at h
  have hn (y : ℝ) : 0 ≤ F y := by unfold F strainComponentSq; positivity
  have h1 := reflected_sample_integral_le hF hn hd (c := 1) (by norm_num) (by norm_num)
  have h2 := reflected_sample_integral_le hF hn hd (c := 2) (by norm_num) (by norm_num)
  have h3 := reflected_sample_integral_le hF hn hd (c := 3) (by norm_num) (by norm_num)
  change (∫ y in -d..(0 : ℝ), T y) ≤ 9216 * ∫ y in (0 : ℝ)..3 * d, F y
  linarith only [h, h1, h2, h3]

/-- The reflected strip controls the squared displacement without derivative assumptions. -/
theorem reflected_slice_displacement_integral_le {u v : Plane → ℝ}
    (hu : Continuous u) (hv : Continuous v) (x : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (∫ y in -d..(0 : ℝ), reflectedTangent u (x, y) ^ 2 + reflectedNormal v (x, y) ^ 2) ≤
      2304 * ∫ y in (0 : ℝ)..3 * d, u (x, y) ^ 2 + v (x, y) ^ 2 := by
  let F := fun y => u (x, y) ^ 2 + v (x, y) ^ 2
  let T := fun y => reflectedTangent u (x, y) ^ 2 + reflectedNormal v (x, y) ^ 2
  have hF : Continuous F := by unfold F; fun_prop
  have hT : Continuous T := by unfold T reflectedTangent reflectedNormal; fun_prop
  have G (c : ℝ) : Continuous (fun y => F (-c * y)) := hF.comp (continuous_const.mul continuous_id)
  have hG : Continuous (fun y => 768 * (F (-1 * y) + F (-2 * y) + F (-3 * y))) :=
    continuous_const.mul (((G 1).add (G 2)).add (G 3))
  have h := intervalIntegral.integral_mono_on (μ := volume) (neg_nonpos.mpr hd)
    (hT.intervalIntegrable (-d) 0)
    (hG.intervalIntegrable (-d) 0) fun y _ => by
      unfold T F reflectedTangent reflectedNormal
      simp only [reflectionSample_apply]
      let a := u (x, -1 * y)
      let b := u (x, -2 * y)
      let c := u (x, -3 * y)
      let e := v (x, -1 * y)
      let f := v (x, -2 * y)
      let g := v (x, -3 * y)
      change (6 * a - 8 * b + 3 * c) ^ 2 + (-6 * e + 16 * f - 9 * g) ^ 2 ≤
        768 * (a ^ 2 + e ^ 2 + (b ^ 2 + f ^ 2) + (c ^ 2 + g ^ 2))
      nlinarith only [three_term_sq (6 * a) (-8 * b) (3 * c),
        three_term_sq (-6 * e) (16 * f) (-9 * g),
        sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg e, sq_nonneg g]
  have hG12 : Continuous (fun y => F (-1 * y) + F (-2 * y)) := (G 1).add (G 2)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hG12.intervalIntegrable (-d) 0)
      ((G 3).intervalIntegrable (-d) 0),
    intervalIntegral.integral_add ((G 1).intervalIntegrable (-d) 0)
      ((G 2).intervalIntegrable (-d) 0)] at h
  have hn (y : ℝ) : 0 ≤ F y := by unfold F; positivity
  have h1 := reflected_sample_integral_le hF hn hd (c := 1) (by norm_num) (by norm_num)
  have h2 := reflected_sample_integral_le hF hn hd (c := 2) (by norm_num) (by norm_num)
  have h3 := reflected_sample_integral_le hF hn hd (c := 3) (by norm_num) (by norm_num)
  change (∫ y in -d..(0 : ℝ), T y) ≤ 2304 * ∫ y in (0 : ℝ)..3 * d, F y
  linarith only [h, h1, h2, h3]

/-- Fubini turns the slice estimate into an L² strain estimate on a rectangular reflected strip. -/
theorem reflected_strip_strain_integral_le {u v : Plane → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) (a b : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (∫ p : Plane, strainComponentSq (strainComponents (reflectedTangent u) (reflectedNormal v) p)
      ∂((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc (-d) 0)))) ≤
    9216 * ∫ p : Plane, strainComponentSq (strainComponents u v p)
      ∂((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 (3 * d)))) := by
  let μ := volume.restrict (Set.Ioc a b)
  let F := fun p => strainComponentSq (strainComponents u v p)
  let T := fun p => strainComponentSq (strainComponents (reflectedTangent u) (reflectedNormal v) p)
  have hInt (f : Plane → ℝ) (h : Continuous f) (s t : ℝ) :
      Integrable f (μ.prod (volume.restrict (Set.Ioc s t))) := by
    rw [show μ = volume.restrict (Set.Ioc a b) from rfl, Measure.prod_restrict]
    exact (h.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  obtain ⟨hU, hV⟩ := reflected_contDiff_branches hu hv
  have hT := hInt T (continuous_strain_sq hU hV) (-d) 0
  have hF := hInt F (continuous_strain_sq hu hv) 0 (3 * d)
  change (∫ p, T p ∂(μ.prod (volume.restrict (Set.Ioc (-d) 0)))) ≤
    9216 * ∫ p, F p ∂(μ.prod (volume.restrict (Set.Ioc 0 (3 * d))))
  rw [integral_prod _ hT, integral_prod _ hF, ← integral_const_mul]
  refine integral_mono hT.integral_prod_left (hF.integral_prod_left.const_mul _) fun x => ?_
  change (∫ y in Set.Ioc (-d) 0, T (x, y)) ≤ 9216 * ∫ y in Set.Ioc 0 (3 * d), F (x, y)
  rw [← intervalIntegral.integral_of_le (neg_nonpos.mpr hd),
    ← intervalIntegral.integral_of_le (mul_nonneg (by norm_num) hd)]
  exact reflected_slice_strain_integral_le hu hv x hd

end LeanSolid.Elastostatics.Korn
