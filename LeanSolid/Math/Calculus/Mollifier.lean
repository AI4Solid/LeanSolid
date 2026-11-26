module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

import Mathlib.Tactic.Ring

public section

open ContinuousLinearMap MeasureTheory Filter Set
open scoped ContDiff Convolution Topology Pointwise

namespace LeanSolid.Math

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Differentiating a mollified scalar field mollifies its continuous derivative. -/
theorem fderiv_normed_convolution {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x =
      (φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x := by
  rw [(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
    (φ.continuous_normed.locallyIntegrable (μ := μ)) hf x).fderiv]
  rfl

/-- A family of shrinking mollifiers approximates the full first derivative pointwise. -/
theorem tendsto_fderiv_normed_convolution {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)}
    (hr : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (x : E) :
    Tendsto (fun i => fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
      l (𝓝 (fderiv ℝ f x)) := by
  simpa only [fderiv_normed_convolution hf hc] using
    (ContDiffBump.convolution_tendsto_right_of_continuous (μ := μ) hr
      (hf.continuous_fderiv one_ne_zero) x)

/-- For radii bounded by `r`, the mollified fields have a common compact support. -/
theorem tsupport_normed_convolution_subset {f : E → ℝ} (hc : HasCompactSupport f)
    (φ : ContDiffBump (0 : E)) {r : ℝ} (hr : φ.rOut ≤ r) :
    tsupport (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) ⊆ Metric.closedBall 0 r + tsupport f := by
  have hk : IsCompact (Metric.closedBall (0 : E) r + tsupport f) :=
    (isCompact_closedBall _ _).add hc.isCompact
  refine closure_minimal ((support_convolution_subset _).trans ?_) hk.isClosed
  rw [φ.support_normed_eq]
  exact add_subset_add (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr))
    subset_closure

/-- A bounded continuous derivative gives a uniform derivative bound for every mollifier. -/
theorem norm_fderiv_normed_convolution_le {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (φ : ContDiffBump (0 : E)) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (x : E) :
    ‖fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ ≤ 3 * M := by
  rw [fderiv_normed_convolution hf hc]
  have hclose := φ.dist_normed_convolution_le (μ := μ)
    (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
    (x₀ := x) (ε := 2 * M) (fun y _ => by
      calc
        dist (fderiv ℝ f y) (fderiv ℝ f x) ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ f x‖ := by
          rw [dist_eq_norm]
          exact norm_sub_le _ _
        _ ≤ 2 * M := by simpa [two_mul] using add_le_add (hM y) (hM x))
  calc
    _ ≤ dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x) (fderiv ℝ f x) +
        ‖fderiv ℝ f x‖ := by
      rw [dist_eq_norm]
      exact norm_le_norm_sub_add _ _
    _ ≤ 3 * M := by
      calc
        _ ≤ 2 * M + M := add_le_add hclose (hM x)
        _ = 3 * M := by ring

end LeanSolid.Math
