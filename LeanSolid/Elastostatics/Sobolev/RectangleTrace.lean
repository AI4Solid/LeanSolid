module

public import LeanSolid.Math.Calculus.FaceTraceL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic.Positivity

public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace LeanSolid.Elastostatics.Rectangle

open LeanSolid.Math

/-- Smooth scalar trial functions fixed along the bottom edge. -/
@[expose] def smoothFixed (a b : ℝ) : Submodule ℝ (ℝ × ℝ → ℝ) where
  carrier := {f | ContDiff ℝ 1 f ∧ ∀ x ∈ Icc a b, f (x, 0) = 0}
  zero_mem' := ⟨contDiff_const, by simp⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  smul_mem' c f hf := ⟨contDiff_const.smul hf.1, fun x hx => by simp [hf.2 x hx]⟩

abbrev Trials (a b : ℝ) := Fin 2 → smoothFixed a b

@[expose] noncomputable def bulkMeasure (a b L : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L))

abbrev Interior (a b L : ℝ) := Lp ℝ 2 (bulkMeasure a b L)
abbrev Edge (a b : ℝ) := Lp ℝ 2 (volume.restrict (Icc a b))
abbrev Vec (X : Type) := PiLp 2 (fun _ : Fin 2 => X)
abbrev Graph (a b L : ℝ) :=
  WithLp 2 (Vec (Interior a b L) × WithLp 2 (Vec (Interior a b L) × Vec (Interior a b L)))

private theorem interior_memLp {a b L : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (bulkMeasure a b L) := by
  rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable, bulkMeasure, Measure.prod_restrict]
  exact ((hf.pow 2).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Subset.rfl Ioc_subset_Icc_self)

private noncomputable def toLpLinear {S X : Type} [AddCommGroup S] [Module ℝ S]
    [MeasurableSpace X] (ν : Measure X) (f : S →ₗ[ℝ] (X → ℝ))
    (hf : ∀ s, MemLp (f s) 2 ν) : S →ₗ[ℝ] Lp ℝ 2 ν where
  toFun s := (hf s).toLp (f s)
  map_add' u v := by
    simp only [map_add]
    exact MemLp.toLp_add (hf u) (hf v)
  map_smul' c u := by
    simp only [map_smul, RingHom.id_apply]
    exact MemLp.toLp_const_smul c (hf u)

private theorem toLp_congr {X : Type} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (h : f = g) :
    hf.toLp f = hg.toLp g := by
  subst g
  rfl

/-- Scalar displacement as a bulk L² equivalence class. -/
noncomputable def valueMap (a b L : ℝ) : smoothFixed a b →ₗ[ℝ] Interior a b L :=
  toLpLinear _ (smoothFixed a b).subtype fun f => interior_memLp f.property.1.continuous

/-- Scalar directional derivative as a bulk L² equivalence class. -/
noncomputable def derivativeMap (a b L : ℝ) (v : ℝ × ℝ) :
    smoothFixed a b →ₗ[ℝ] Interior a b L := by
  let D : smoothFixed a b →ₗ[ℝ] (ℝ × ℝ → ℝ) :=
    { toFun := fun f p => fderiv ℝ f.val p v
      map_add' := by
        intro f g
        funext p
        exact congrArg (fun M : (ℝ × ℝ) →L[ℝ] ℝ => M v)
          (fderiv_add (f.property.1.differentiable one_ne_zero p)
            (g.property.1.differentiable one_ne_zero p))
      map_smul' := by
        intro c f
        funext p
        exact congrArg (fun M : (ℝ × ℝ) →L[ℝ] ℝ => M v)
          (fderiv_const_smul (f.property.1.differentiable one_ne_zero p) c) }
  exact toLpLinear _ D fun f =>
    interior_memLp ((f.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const)

private noncomputable def topMap (a b L : ℝ) : smoothFixed a b →ₗ[ℝ] Edge a b := by
  let ev : smoothFixed a b →ₗ[ℝ] (ℝ → ℝ) :=
    { toFun := fun f x => f.val (x, L)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine toLpLinear _ ev fun f => ?_
  have h : Continuous (ev f) := f.property.1.continuous.comp
    (continuous_id.prodMk continuous_const)
  exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).2
    ((h.pow 2).continuousOn.integrableOn_compact isCompact_Icc)

private noncomputable def components {S X : Type} [AddCommGroup S] [Module ℝ S]
    [AddCommGroup X] [Module ℝ X] (f : S →ₗ[ℝ] X) : (Fin 2 → S) →ₗ[ℝ] Vec X :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp
    (LinearMap.pi fun i => f.comp (LinearMap.proj i))

/-- The displacement and the tangential and normal derivatives as a bulk L² graph. -/
noncomputable def trialGraph (a b L : ℝ) : Trials a b →ₗ[ℝ] Graph a b L :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
    (components (valueMap a b L)).prod <|
      (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp <|
        (components (derivativeMap a b L (1, 0))).prod
          (components (derivativeMap a b L (0, 1)))

theorem trialGraph_components (a b L : ℝ) (u : Trials a b) (i : Fin 2) :
    (trialGraph a b L u).fst i = valueMap a b L (u i) ∧
    (trialGraph a b L u).snd.fst i = derivativeMap a b L (1, 0) (u i) ∧
    (trialGraph a b L u).snd.snd i = derivativeMap a b L (0, 1) (u i) :=
  ⟨rfl, rfl, rfl⟩

theorem valueMap_ae {a b L : ℝ} (u : smoothFixed a b) :
    ⇑(valueMap a b L u) =ᵐ[bulkMeasure a b L] u.val :=
  (interior_memLp u.property.1.continuous).coeFn_toLp

theorem derivativeMap_ae {a b L : ℝ} (u : smoothFixed a b) (v : ℝ × ℝ) :
    ⇑(derivativeMap a b L v u) =ᵐ[bulkMeasure a b L] fun p => fderiv ℝ u.val p v :=
  (interior_memLp ((u.property.1.continuous_fderiv one_ne_zero).clm_apply
    continuous_const)).coeFn_toLp

/-- Top edge values of both displacement components. -/
noncomputable def topEvaluation (a b L : ℝ) : Trials a b →ₗ[ℝ] Vec (Edge a b) :=
  components (topMap a b L)

/-- Completed bulk graph of the smooth bottom-fixed trial functions. -/
@[expose] noncomputable def bottomFixedSpace (a b L : ℝ) : Submodule ℝ (Graph a b L) :=
  (LinearMap.range (trialGraph a b L)).topologicalClosure

/-- Continuous top trace on the concrete bottom-fixed rectangular graph space. -/
theorem existsUnique_topTrace {a b L : ℝ} (hL : 0 < L) :
    ∃! trace : bottomFixedSpace a b L →L[ℝ] Vec (Edge a b),
      ∀ u, trace ⟨trialGraph a b L u,
        Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)⟩ =
        topEvaluation a b L u := by
  let bulk := components (valueMap a b L)
  let normal := components (derivativeMap a b L (0, 1))
  apply existsUnique_vector_top_trace_on_graph_closure hL (trialGraph a b L)
    (topEvaluation a b L) bulk normal
  · intro u
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖bulk u‖ ^ 2 + ‖normal u‖ ^ 2 ≤ ‖bulk u‖ ^ 2 +
      ‖(trialGraph a b L u).snd‖ ^ 2
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖bulk u‖ ^ 2 + ‖normal u‖ ^ 2 ≤ ‖bulk u‖ ^ 2 +
      (‖components (derivativeMap a b L (1, 0)) u‖ ^ 2 + ‖normal u‖ ^ 2)
    gcongr
    exact le_add_of_nonneg_left (sq_nonneg _)
  · intro u i
    let f := u i
    let w := fun x y : ℝ => f.val (x, y)
    have hw (x : ℝ) : ContDiff ℝ 1 (w x) :=
      f.property.1.comp (contDiff_const.prodMk contDiff_id)
    have hn (p : ℝ × ℝ) : deriv (w p.1) p.2 = fderiv ℝ f.val p (0, 1) := by
      have hline : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
        (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
      exact ((f.property.1.differentiable one_ne_zero p).hasFDerivAt.comp_hasDerivAt
        p.2 hline).deriv
    obtain ⟨ht, hv, hd⟩ := rectangle_top_memLp_of_contDiff (a := a) (b := b) (L := L)
      (u := w) f.property.1
    have h := top_face_norm_sq_bound hL hw ht hv hd
    have heq : (fun p => deriv (w p.1) p.2) = fun p => fderiv ℝ f.val p (0, 1) := funext hn
    have hm : MemLp (fun p => fderiv ℝ f.val p (0, 1)) 2 (bulkMeasure a b L) :=
      interior_memLp ((f.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    rw [toLp_congr hd hm heq] at h
    exact h

/-- The continuous trace obtained from the specified smooth trial functions. -/
noncomputable def topTrace {a b L : ℝ} (hL : 0 < L) :
    bottomFixedSpace a b L →L[ℝ] Vec (Edge a b) :=
  (existsUnique_topTrace (a := a) (b := b) hL).exists.choose

theorem topTrace_trialGraph {a b L : ℝ} (hL : 0 < L) (u : Trials a b) :
    topTrace hL ⟨trialGraph a b L u,
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)⟩ =
        topEvaluation a b L u :=
  (existsUnique_topTrace (a := a) (b := b) hL).exists.choose_spec u

/-- A square-integrable top traction defines a continuous virtual-work load on the
bottom-fixed rectangular space. -/
noncomputable def topTractionLoad {a b L : ℝ} (hL : 0 < L) (t : Vec (Edge a b)) :
    bottomFixedSpace a b L →L[ℝ] ℝ :=
  (innerSL ℝ t).comp (topTrace hL)

/-- The normal derivative controls both displacement components on smooth bottom-fixed trials. -/
theorem trial_normal_poincare {a b L : ℝ} (hL : 0 < L) (u : Trials a b) :
    ‖(trialGraph a b L u).fst‖ ^ 2 ≤ (4 * L ^ 2) * ‖(trialGraph a b L u).snd.snd‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  let f := u i
  let w := fun x y : ℝ => f.val (x, y)
  have hw (x : ℝ) : ContDiff ℝ 1 (w x) :=
    f.property.1.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨_, hv, hd⟩ := rectangle_top_memLp_of_contDiff (a := a) (b := b) (L := L)
    (u := w) f.property.1
  have hn : (fun p : ℝ × ℝ => deriv (w p.1) p.2) = fun p => fderiv ℝ f.val p (0, 1) := by
    funext p
    have hline : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
    exact ((f.property.1.differentiable one_ne_zero p).hasFDerivAt.comp_hasDerivAt
      p.2 hline).deriv
  have hm : MemLp (fun p => fderiv ℝ f.val p (0, 1)) 2 (bulkMeasure a b L) :=
    interior_memLp ((f.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have h := rectangle_bottom_fixed_poincare hL hw f.property.2 hv hd
  rw [toLp_congr hd hm hn] at h
  exact h

/-- Bottom Poincaré holds for each displacement component on the completed graph. -/
theorem component_normal_poincare {a b L : ℝ} (hL : 0 < L) (U : bottomFixedSpace a b L)
    (i : Fin 2) :
    ‖(U : Graph a b L).fst i‖ ^ 2 ≤ (4 * L ^ 2) * ‖(U : Graph a b L).snd.snd i‖ ^ 2 := by
  let p := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 2 => Interior a b L) i
  let disp := p.comp (WithLp.fstL 2 ℝ (Vec (Interior a b L))
    (WithLp 2 (Vec (Interior a b L) × Vec (Interior a b L))))
  let normal := (p.comp (WithLp.sndL 2 ℝ (Vec (Interior a b L)) (Vec (Interior a b L)))).comp
    (WithLp.sndL 2 ℝ (Vec (Interior a b L))
      (WithLp 2 (Vec (Interior a b L) × Vec (Interior a b L))))
  let Q := {W : Graph a b L | ‖disp W‖ ^ 2 ≤ (4 * L ^ 2) * ‖normal W‖ ^ 2}
  have hQ : IsClosed Q :=
    isClosed_le (disp.continuous.norm.pow 2)
      (continuous_const.mul (normal.continuous.norm.pow 2))
  have hsub : Set.range (trialGraph a b L) ⊆ Q := by
    rintro _ ⟨u, rfl⟩
    let f := u i
    let w := fun x y : ℝ => f.val (x, y)
    have hw (x : ℝ) : ContDiff ℝ 1 (w x) :=
      f.property.1.comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨_, hv, hd⟩ := rectangle_top_memLp_of_contDiff (a := a) (b := b) (L := L)
      (u := w) f.property.1
    have hn : (fun p : ℝ × ℝ => deriv (w p.1) p.2) = fun p => fderiv ℝ f.val p (0, 1) := by
      funext p
      have hline : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
        (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
      exact ((f.property.1.differentiable one_ne_zero p).hasFDerivAt.comp_hasDerivAt
        p.2 hline).deriv
    have hm : MemLp (fun p => fderiv ℝ f.val p (0, 1)) 2 (bulkMeasure a b L) :=
      interior_memLp ((f.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    have h := rectangle_bottom_fixed_poincare hL hw f.property.2 hv hd
    rw [toLp_congr hd hm hn] at h
    exact h
  have hmem : (U : Graph a b L) ∈ closure (Set.range (trialGraph a b L)) := by
    rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
    exact U.property
  exact closure_minimal hsub hQ hmem

private theorem integral_bulk_continuous {a b L : ℝ} {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Integrable f (bulkMeasure a b L) := by
  rw [bulkMeasure, Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Subset.rfl Ioc_subset_Icc_self)

private theorem pairing_toLp {X : Type} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ p, f p * g p ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  exact real_inner_comm _ _

private theorem trial_normal_integration_by_parts {a b L : ℝ} (hL : 0 < L)
    (f ψ : smoothFixed a b) (ht : ∀ x ∈ Icc a b, ψ.val (x, L) = 0) :
    ⟪derivativeMap a b L (0, 1) f, valueMap a b L ψ⟫_ℝ +
      ⟪valueMap a b L f, derivativeMap a b L (0, 1) ψ⟫_ℝ = 0 := by
  let D := fun p : ℝ × ℝ => fderiv ℝ f.val p (0, 1)
  let DP := fun p : ℝ × ℝ => fderiv ℝ ψ.val p (0, 1)
  have hD : Continuous D :=
    (f.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDP : Continuous DP :=
    (ψ.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hmemD : MemLp D 2 (bulkMeasure a b L) := interior_memLp hD
  have hmemDP : MemLp DP 2 (bulkMeasure a b L) := interior_memLp hDP
  have hmemF : MemLp f.val 2 (bulkMeasure a b L) := interior_memLp f.property.1.continuous
  have hmemP : MemLp ψ.val 2 (bulkMeasure a b L) := interior_memLp ψ.property.1.continuous
  change ⟪hmemD.toLp D, hmemP.toLp ψ.val⟫_ℝ +
    ⟪hmemF.toLp f.val, hmemDP.toLp DP⟫_ℝ = 0
  rw [pairing_toLp, pairing_toLp]
  have h1 : Integrable (fun p => D p * ψ.val p) (bulkMeasure a b L) :=
    integral_bulk_continuous
    (hD.mul ψ.property.1.continuous)
  have h2 : Integrable (fun p => f.val p * DP p) (bulkMeasure a b L) :=
    integral_bulk_continuous
    (f.property.1.continuous.mul hDP)
  have hsum : Integrable (fun p => D p * ψ.val p + f.val p * DP p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L))) := h1.add h2
  rw [← integral_add h1 h2, bulkMeasure, integral_prod _ hsum]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
  change (∫ y in Ioc 0 L, D (x, y) * ψ.val (x, y) + f.val (x, y) * DP (x, y)) = 0
  rw [← intervalIntegral.integral_of_le hL.le]
  have hder (y : ℝ) : HasDerivAt (fun t => f.val (x, t) * ψ.val (x, t))
      (D (x, y) * ψ.val (x, y) + f.val (x, y) * DP (x, y)) y := by
    have hline : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
      (hasDerivAt_const y x).prodMk (hasDerivAt_id' y)
    exact ((f.property.1.differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt
      y hline).mul ((ψ.property.1.differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt
        y hline)
  have hcont : Continuous (fun y => D (x, y) * ψ.val (x, y) +
      f.val (x, y) * DP (x, y)) :=
    ((hD.mul ψ.property.1.continuous).add (f.property.1.continuous.mul hDP)).comp
      (continuous_const.prodMk continuous_id)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hder y)
    (hcont.intervalIntegrable 0 L)]
  simp [ht x hx, ψ.property.2 x hx]

/-- On the completed graph, the normal column satisfies the weak derivative identity
against smooth tests vanishing on the top and bottom edges. -/
theorem weak_normal_derivative {a b L : ℝ} (hL : 0 < L) (U : bottomFixedSpace a b L)
    (i : Fin 2) (ψ : smoothFixed a b) (ht : ∀ x ∈ Icc a b, ψ.val (x, L) = 0) :
    ⟪(U : Graph a b L).snd.snd i, valueMap a b L ψ⟫_ℝ +
      ⟪(U : Graph a b L).fst i, derivativeMap a b L (0, 1) ψ⟫_ℝ = 0 := by
  let p := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 2 => Interior a b L) i
  let disp := p.comp (WithLp.fstL 2 ℝ (Vec (Interior a b L))
    (WithLp 2 (Vec (Interior a b L) × Vec (Interior a b L))))
  let normal := (p.comp (WithLp.sndL 2 ℝ (Vec (Interior a b L)) (Vec (Interior a b L)))).comp
    (WithLp.sndL 2 ℝ (Vec (Interior a b L))
      (WithLp 2 (Vec (Interior a b L) × Vec (Interior a b L))))
  let Q := {W : Graph a b L | ⟪normal W, valueMap a b L ψ⟫_ℝ +
    ⟪disp W, derivativeMap a b L (0, 1) ψ⟫_ℝ = 0}
  have hQ : IsClosed Q :=
    isClosed_eq ((normal.continuous.inner continuous_const).add
      (disp.continuous.inner continuous_const)) continuous_const
  have hsub : Set.range (trialGraph a b L) ⊆ Q := by
    rintro _ ⟨u, rfl⟩
    exact trial_normal_integration_by_parts hL (u i) ψ ht
  have hmem : (U : Graph a b L) ∈ closure (Set.range (trialGraph a b L)) := by
    rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
    exact U.property
  exact closure_minimal hsub hQ hmem

private theorem trial_tangential_integration_by_parts {a b L : ℝ} (hab : a ≤ b)
    (f ψ : smoothFixed a b) (ht : ∀ y ∈ Ioc 0 L, ψ.val (a, y) = 0 ∧ ψ.val (b, y) = 0) :
    ⟪derivativeMap a b L (1, 0) f, valueMap a b L ψ⟫_ℝ +
      ⟪valueMap a b L f, derivativeMap a b L (1, 0) ψ⟫_ℝ = 0 := by
  let D := fun p : ℝ × ℝ => fderiv ℝ f.val p (1, 0)
  let DP := fun p : ℝ × ℝ => fderiv ℝ ψ.val p (1, 0)
  have hD : Continuous D :=
    (f.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDP : Continuous DP :=
    (ψ.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hmemD : MemLp D 2 (bulkMeasure a b L) := interior_memLp hD
  have hmemDP : MemLp DP 2 (bulkMeasure a b L) := interior_memLp hDP
  have hmemF : MemLp f.val 2 (bulkMeasure a b L) := interior_memLp f.property.1.continuous
  have hmemP : MemLp ψ.val 2 (bulkMeasure a b L) := interior_memLp ψ.property.1.continuous
  change ⟪hmemD.toLp D, hmemP.toLp ψ.val⟫_ℝ +
    ⟪hmemF.toLp f.val, hmemDP.toLp DP⟫_ℝ = 0
  rw [pairing_toLp, pairing_toLp]
  have h1 : Integrable (fun p => D p * ψ.val p) (bulkMeasure a b L) :=
    integral_bulk_continuous
    (hD.mul ψ.property.1.continuous)
  have h2 : Integrable (fun p => f.val p * DP p) (bulkMeasure a b L) :=
    integral_bulk_continuous
    (f.property.1.continuous.mul hDP)
  have hsum : Integrable (fun p => D p * ψ.val p + f.val p * DP p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L))) := h1.add h2
  rw [← integral_add h1 h2, bulkMeasure, integral_prod_symm _ hsum]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with y hy
  change (∫ x in Icc a b, D (x, y) * ψ.val (x, y) + f.val (x, y) * DP (x, y)) = 0
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hder (x : ℝ) : HasDerivAt (fun t => f.val (t, y) * ψ.val (t, y))
      (D (x, y) * ψ.val (x, y) + f.val (x, y) * DP (x, y)) x := by
    have hline : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id' x).prodMk (hasDerivAt_const x y)
    exact ((f.property.1.differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt
      x hline).mul ((ψ.property.1.differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt
        x hline)
  have hcont : Continuous (fun x => D (x, y) * ψ.val (x, y) +
      f.val (x, y) * DP (x, y)) :=
    ((hD.mul ψ.property.1.continuous).add (f.property.1.continuous.mul hDP)).comp
      (continuous_id.prodMk continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    (hcont.intervalIntegrable a b)]
  simp [(ht y hy).1, (ht y hy).2]

/-- On the completed graph, the tangential column satisfies the weak derivative identity
against smooth tests vanishing on the two lateral edges. -/
theorem weak_tangential_derivative {a b L : ℝ} (hab : a ≤ b) (U : bottomFixedSpace a b L)
    (i : Fin 2) (ψ : smoothFixed a b) (ht : ∀ y ∈ Ioc 0 L, ψ.val (a, y) = 0 ∧ ψ.val (b, y) = 0) :
    ⟪(U : Graph a b L).snd.fst i, valueMap a b L ψ⟫_ℝ +
      ⟪(U : Graph a b L).fst i, derivativeMap a b L (1, 0) ψ⟫_ℝ = 0 := by
  let p := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 2 => Interior a b L) i
  let disp := p.comp (WithLp.fstL 2 ℝ (Vec (Interior a b L))
    (WithLp 2 (Vec (Interior a b L) × Vec (Interior a b L))))
  let tangent := (p.comp (WithLp.fstL 2 ℝ (Vec (Interior a b L)) (Vec (Interior a b L)))).comp
    (WithLp.sndL 2 ℝ (Vec (Interior a b L))
      (WithLp 2 (Vec (Interior a b L) × Vec (Interior a b L))))
  let Q := {W : Graph a b L | ⟪tangent W, valueMap a b L ψ⟫_ℝ +
    ⟪disp W, derivativeMap a b L (1, 0) ψ⟫_ℝ = 0}
  have hQ : IsClosed Q :=
    isClosed_eq ((tangent.continuous.inner continuous_const).add
      (disp.continuous.inner continuous_const)) continuous_const
  have hsub : Set.range (trialGraph a b L) ⊆ Q := by
    rintro _ ⟨u, rfl⟩
    exact trial_tangential_integration_by_parts hab (u i) ψ ht
  have hmem : (U : Graph a b L) ∈ closure (Set.range (trialGraph a b L)) := by
    rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
    exact U.property
  exact closure_minimal hsub hQ hmem

/-- Interior smooth tests separate bulk L² classes on the rectangle. -/
theorem eq_zero_of_interior_pairings {a b L : ℝ} (F : Interior a b L)
    (h : ∀ ψ : smoothFixed a b,
      (∀ y ∈ Ioc 0 L, ψ.val (a, y) = 0 ∧ ψ.val (b, y) = 0) →
      ⟪F, valueMap a b L ψ⟫_ℝ = 0) : F = 0 := by
  let Ω := Ioo a b ×ˢ Ioo 0 L
  have hopen : IsOpen Ω := isOpen_Ioo.prod isOpen_Ioo
  have hm : bulkMeasure a b L = (volume : Measure (ℝ × ℝ)).restrict Ω := by
    rw [bulkMeasure, Measure.prod_restrict, Measure.volume_eq_prod]
    exact Measure.restrict_congr_set
      (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Ioc).symm
  have hint : Integrable (F : ℝ × ℝ → ℝ) (bulkMeasure a b L) := by
    let : IsFiniteMeasure (bulkMeasure a b L) := by rw [bulkMeasure]; infer_instance
    exact (Lp.memLp F).integrable (by norm_num)
  have hlocal : LocallyIntegrableOn (F : ℝ × ℝ → ℝ) Ω volume := by
    apply IntegrableOn.locallyIntegrableOn
    rwa [IntegrableOn, ← hm]
  have hae := hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    (fun g hg _ hs => by
      have hout (p : ℝ × ℝ) (hp : p ∉ Ω) : g p = 0 := by
        by_contra hn
        exact hp (hs (subset_tsupport _ hn))
      let ψ : smoothFixed a b := ⟨g, hg.of_le (by simp), fun x _ =>
        hout (x, 0) (by simp [Ω])⟩
      have hz := h ψ (fun y _ => ⟨hout (a, y) (by simp [Ω]), hout (b, y) (by simp [Ω])⟩)
      have hgmem : MemLp g 2 (bulkMeasure a b L) := interior_memLp hg.continuous
      change ⟪F, hgmem.toLp g⟫_ℝ = 0 at hz
      rw [L2.inner_def] at hz
      have heq : (∫ p, ⟪F p, hgmem.toLp g p⟫_ℝ ∂bulkMeasure a b L) =
          ∫ p, g p • F p ∂bulkMeasure a b L := by
        apply integral_congr_ae
        filter_upwards [hgmem.coeFn_toLp] with p hp
        rw [hp]
        rfl
      rw [heq] at hz
      have hvol := (congrArg (fun m : Measure (ℝ × ℝ) =>
        ∫ p, g p • F p ∂m) hm).symm.trans hz
      rw [← integral_indicator hopen.measurableSet] at hvol
      convert hvol using 1
      apply integral_congr_ae
      filter_upwards with p
      by_cases hp : p ∈ Ω
      · simp [hp]
      · simp [hp, hout p hp])
  apply Lp.ext
  have hf : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)).restrict Ω, F p = 0 :=
    (ae_restrict_iff' hopen.measurableSet).2 hae
  have hz := Lp.coeFn_zero (E := ℝ) (p := 2) (μ := bulkMeasure a b L)
  rw [← hm] at hf
  filter_upwards [hf, hz] with p hp hz
  exact hp.trans hz.symm

end LeanSolid.Elastostatics.Rectangle
