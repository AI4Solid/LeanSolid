module

public import LeanSolid.Math.Calculus.FaceTrace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace LeanSolid.Math

private theorem norm_toLp_two_sq {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → ℝ} (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- A displacement component vanishing on the bottom edge is controlled by its normal
derivative in the bulk L² norm of the rectangle. -/
theorem rectangle_bottom_fixed_poincare {a b L : ℝ} (hL : 0 < L) {u : ℝ → ℝ → ℝ}
    (hu : ∀ y, ContDiff ℝ 1 (u y)) (h₀ : ∀ y ∈ Icc a b, u y 0 = 0)
    (hv : MemLp (Function.uncurry u) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L))))
    (hd : MemLp (fun p : ℝ × ℝ => deriv (u p.1) p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L)))) :
    ‖hv.toLp (Function.uncurry u)‖ ^ 2 ≤
      (4 * L ^ 2) * ‖hd.toLp (fun p : ℝ × ℝ => deriv (u p.1) p.2)‖ ^ 2 := by
  rw [norm_toLp_two_sq hv, norm_toLp_two_sq hd]
  rw [integral_prod _ hv.integrable_sq, integral_prod _ hd.integrable_sq, ← integral_const_mul]
  refine integral_mono_ae hv.integrable_sq.integral_prod_left
    (hd.integrable_sq.integral_prod_left.const_mul _) ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with y hy
  change (∫ x in Ioc 0 L, u y x ^ 2) ≤
    (4 * L ^ 2) * ∫ x in Ioc 0 L, deriv (u y) x ^ 2
  rw [← intervalIntegral.integral_of_le hL.le, ← intervalIntegral.integral_of_le hL.le]
  exact bottom_fixed_slice_poincare hL (hu y) (h₀ y hy)

/-- The squared top trace norm is controlled by the bulk displacement and normal derivative
norms for a smooth scalar field on a product domain. -/
theorem top_face_norm_sq_bound {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [SFinite ν] {L : ℝ} (hL : 0 < L) {u : X → ℝ → ℝ}
    (hu : ∀ y, ContDiff ℝ 1 (u y))
    (ht : MemLp (fun y => u y L) 2 ν)
    (hv : MemLp (Function.uncurry u) 2 (ν.prod (volume.restrict (Ioc 0 L))))
    (hd : MemLp (fun p : X × ℝ => deriv (u p.1) p.2) 2
      (ν.prod (volume.restrict (Ioc 0 L)))) :
    L * ‖ht.toLp (fun y => u y L)‖ ^ 2 ≤
      (1 + L) * ‖hv.toLp (Function.uncurry u)‖ ^ 2 +
        L * ‖hd.toLp (fun p : X × ℝ => deriv (u p.1) p.2)‖ ^ 2 := by
  have hv' : Integrable (fun p : X × ℝ => u p.1 p.2 ^ 2)
      (ν.prod (volume.restrict (Ioc 0 L))) := hv.integrable_sq
  have hb := top_face_trace_bound hL hu ht.integrable_sq
    ((hv'.const_mul (1 + L)).add (hd.integrable_sq.const_mul L))
  rw [integral_add (hv'.const_mul (1 + L)) (hd.integrable_sq.const_mul L),
    integral_const_mul, integral_const_mul] at hb
  rw [norm_toLp_two_sq ht, norm_toLp_two_sq hv, norm_toLp_two_sq hd]
  exact hb

/-- Summing componentwise trace estimates gives the trace bound for a finite vector of
displacement components, with the same constant. -/
theorem vector_top_face_norm_sq_bound {ι T V D : Type*} [Fintype ι]
    [SeminormedAddCommGroup T] [SeminormedAddCommGroup V] [SeminormedAddCommGroup D]
    {L : ℝ} (top : PiLp 2 (fun _ : ι => T)) (bulk : PiLp 2 (fun _ : ι => V))
    (normal : PiLp 2 (fun _ : ι => D))
    (h : ∀ i, L * ‖top i‖ ^ 2 ≤ (1 + L) * ‖bulk i‖ ^ 2 + L * ‖normal i‖ ^ 2) :
    L * ‖top‖ ^ 2 ≤ (1 + L) * ‖bulk‖ ^ 2 + L * ‖normal‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => h i

/-- Componentwise estimates extend top evaluation to the bulk completion. The bulk norm
controls the displacement and its normal derivative, as it does for the full gradient norm. -/
theorem existsUnique_vector_top_trace {ι S V T U D : Type*} [Fintype ι]
    [AddCommGroup S] [Module ℝ S] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    [SeminormedAddCommGroup U] [SeminormedAddCommGroup D]
    {L : ℝ} (hL : 0 < L)
    (embed : S →ₗ[ℝ] V) (eval : S →ₗ[ℝ] PiLp 2 (fun _ : ι => T))
    (bulk : S → PiLp 2 (fun _ : ι => U)) (normal : S → PiLp 2 (fun _ : ι => D))
    (hdense : DenseRange embed)
    (hbulk : ∀ s, ‖bulk s‖ ^ 2 + ‖normal s‖ ^ 2 ≤ ‖embed s‖ ^ 2)
    (hface : ∀ s i, L * ‖eval s i‖ ^ 2 ≤
      (1 + L) * ‖bulk s i‖ ^ 2 + L * ‖normal s i‖ ^ 2) :
    ∃! trace : V →L[ℝ] PiLp 2 (fun _ : ι => T), ∀ s, trace (embed s) = eval s := by
  apply existsUnique_continuous_trace embed eval hdense
  let C := Real.sqrt ((1 + L) / L)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hc : C ^ 2 = (1 + L) / L := Real.sq_sqrt (by positivity)
  refine ⟨C, fun s => ?_⟩
  have h := vector_top_face_norm_sq_bound (eval s) (bulk s) (normal s) (hface s)
  have hmul := mul_le_mul_of_nonneg_left (hbulk s) (show 0 ≤ 1 + L by positivity)
  have hs : L * ‖eval s‖ ^ 2 ≤ (1 + L) * ‖embed s‖ ^ 2 := by
    nlinarith only [h, hmul, sq_nonneg ‖normal s‖]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, hc, div_mul_eq_mul_div, le_div_iff₀ hL]
  simpa only [mul_comm L] using hs

/-- The restriction of a smooth scalar field and its normal derivative to a bounded
rectangle, and the evaluation on its top edge, all belong to their respective L² spaces. -/
theorem rectangle_top_memLp {a b L : ℝ} {u : ℝ → ℝ → ℝ}
    (hc : Continuous (Function.uncurry u))
    (hd : Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2)) :
    MemLp (fun y => u y L) 2 (volume.restrict (Icc a b)) ∧
    MemLp (Function.uncurry u) 2 ((volume.restrict (Icc a b)).prod
      (volume.restrict (Ioc 0 L))) ∧
    MemLp (fun p : ℝ × ℝ => deriv (u p.1) p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L))) := by
  have htop : Continuous (fun y => u y L) := hc.comp (continuous_id.prodMk continuous_const)
  have hbulk (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
      MemLp f 2 ((volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L))) := by
    rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable, Measure.prod_restrict]
    exact ((hf.pow 2).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Subset.rfl Ioc_subset_Icc_self)
  exact ⟨(memLp_two_iff_integrable_sq htop.aestronglyMeasurable).2
    ((htop.pow 2).continuousOn.integrableOn_compact isCompact_Icc), hbulk _ hc, hbulk _ hd⟩

/-- A jointly C¹ rectangular displacement component provides square-integrable top values,
bulk values and normal derivatives. -/
theorem rectangle_top_memLp_of_contDiff {a b L : ℝ} {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) :
    MemLp (fun y => u y L) 2 (volume.restrict (Icc a b)) ∧
    MemLp (Function.uncurry u) 2 ((volume.restrict (Icc a b)).prod
      (volume.restrict (Ioc 0 L))) ∧
    MemLp (fun p : ℝ × ℝ => deriv (u p.1) p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L))) := by
  apply rectangle_top_memLp hu.continuous
  have hd : (fun p : ℝ × ℝ => deriv (u p.1) p.2) =
      fun p => fderiv ℝ (Function.uncurry u) p (0, 1) := by
    funext p
    have hline : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
    have h := (hu.differentiable one_ne_zero p).hasFDerivAt.comp_hasDerivAt p.2
      hline
    exact h.deriv
  rw [hd]
  exact (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Top evaluation extends to the closed range of a smooth displacement–gradient graph.
Density is a consequence of the chosen completion. -/
theorem existsUnique_vector_top_trace_on_graph_closure {ι S V T U D : Type*} [Fintype ι]
    [AddCommGroup S] [Module ℝ S] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    [SeminormedAddCommGroup U] [SeminormedAddCommGroup D]
    {L : ℝ} (hL : 0 < L)
    (graph : S →ₗ[ℝ] V) (eval : S →ₗ[ℝ] PiLp 2 (fun _ : ι => T))
    (bulk : S → PiLp 2 (fun _ : ι => U)) (normal : S → PiLp 2 (fun _ : ι => D))
    (hbulk : ∀ s, ‖bulk s‖ ^ 2 + ‖normal s‖ ^ 2 ≤ ‖graph s‖ ^ 2)
    (hface : ∀ s i, L * ‖eval s i‖ ^ 2 ≤
      (1 + L) * ‖bulk s i‖ ^ 2 + L * ‖normal s i‖ ^ 2) :
    ∃! trace : (LinearMap.range graph).topologicalClosure →L[ℝ] PiLp 2 (fun _ : ι => T),
      ∀ s, trace ⟨graph s, Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ s)⟩ =
        eval s := by
  let R := LinearMap.range graph
  let embed : S →ₗ[ℝ] R.topologicalClosure :=
    graph.codRestrict R.topologicalClosure fun s =>
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ s)
  have hdense : DenseRange embed := by
    have hi : DenseRange (Set.inclusion (show (R : Set V) ⊆ R.topologicalClosure from
        Submodule.le_topologicalClosure R)) := by
      apply (denseRange_inclusion_iff (Submodule.le_topologicalClosure R)).2
      rw [Submodule.topologicalClosure_coe]
    have hs : Function.Surjective graph.rangeRestrict := by
      rintro ⟨_, s, rfl⟩
      exact ⟨s, rfl⟩
    exact hi.comp hs.denseRange (continuous_inclusion _)
  exact existsUnique_vector_top_trace hL embed eval bulk normal hdense hbulk hface

end LeanSolid.Math
