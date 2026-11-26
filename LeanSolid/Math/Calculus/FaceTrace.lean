module

public import LeanSolid.Math.Calculus.EndpointTrace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Normed.Operator.Extend

public section

open MeasureTheory Set

namespace LeanSolid.Math

/-- Integrating the normal-slice estimate gives a bound on the whole top face of a
product domain. The transverse measure can be volume restricted to a rectangle. -/
theorem top_face_trace_bound {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [SFinite ν] {L : ℝ} (hL : 0 < L) {u : X → ℝ → ℝ}
    (hu : ∀ y, ContDiff ℝ 1 (u y))
    (htop : Integrable (fun y => u y L ^ 2) ν)
    (hbulk : Integrable (fun p : X × ℝ =>
      (1 + L) * u p.1 p.2 ^ 2 + L * deriv (u p.1) p.2 ^ 2)
      (ν.prod (volume.restrict (Ioc 0 L)))) :
    L * (∫ y, u y L ^ 2 ∂ν) ≤
      ∫ p : X × ℝ, (1 + L) * u p.1 p.2 ^ 2 + L * deriv (u p.1) p.2 ^ 2
        ∂(ν.prod (volume.restrict (Ioc 0 L))) := by
  rw [← integral_const_mul, integral_prod _ hbulk]
  apply integral_mono (htop.const_mul L) hbulk.integral_prod_left
  intro y
  change L * u y L ^ 2 ≤ ∫ x in Ioc 0 L, (1 + L) * u y x ^ 2 + L * deriv (u y) x ^ 2
  rw [← intervalIntegral.integral_of_le hL.le]
  exact endpoint_trace_bound hL (hu y)

/-- The face bound for a smooth scalar field on a planar rectangle. Joint continuity of the
field and its normal derivative supplies the integrability conditions. -/
theorem rectangle_top_trace_bound {a b L : ℝ} (hL : 0 < L) {u : ℝ → ℝ → ℝ}
    (hu : ∀ y, ContDiff ℝ 1 (u y))
    (hc : Continuous (Function.uncurry u))
    (hd : Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2)) :
    L * (∫ y in Icc a b, u y L ^ 2) ≤
      ∫ p : ℝ × ℝ, (1 + L) * u p.1 p.2 ^ 2 + L * deriv (u p.1) p.2 ^ 2
        ∂((volume.restrict (Icc a b)).prod (volume.restrict (Ioc 0 L))) := by
  apply top_face_trace_bound hL hu
  · have htop : Continuous (fun y => u y L ^ 2) :=
      (hc.comp (continuous_id.prodMk continuous_const)).pow 2
    exact htop.continuousOn.integrableOn_compact isCompact_Icc
  · have hbulk : Continuous (fun p : ℝ × ℝ =>
        (1 + L) * u p.1 p.2 ^ 2 + L * deriv (u p.1) p.2 ^ 2) :=
      (continuous_const.mul (hc.pow 2)).add (continuous_const.mul (hd.pow 2))
    rw [Measure.prod_restrict]
    exact (hbulk.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Subset.rfl Ioc_subset_Icc_self)

section Extension

variable {S V B : Type*} [AddCommGroup S] [Module ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- A face evaluation on a dense family of smooth fields extends uniquely when its norm is
bounded by the bulk norm. The bulk embedding may represent displacement–gradient pairs. -/
theorem existsUnique_continuous_trace (embed : S →ₗ[ℝ] V) (eval : S →ₗ[ℝ] B)
    (hdense : DenseRange embed) (hbound : ∃ C : ℝ, ∀ s, ‖eval s‖ ≤ C * ‖embed s‖) :
    ∃! trace : V →L[ℝ] B, ∀ s, trace (embed s) = eval s := by
  refine ⟨eval.extendOfNorm embed, LinearMap.extendOfNorm_eq hdense hbound, ?_⟩
  intro trace htrace
  apply ContinuousLinearMap.ext
  intro v
  exact hdense.induction
    (fun _ ⟨s, hs⟩ => by
      rw [← hs, htrace, LinearMap.extendOfNorm_eq hdense hbound])
    (isClosed_eq trace.continuous (eval.extendOfNorm embed).continuous) v

end Extension

end LeanSolid.Math
