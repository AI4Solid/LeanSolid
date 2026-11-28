module

public import LeanSolid.ContinuumMechanics.Rates
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Ring

public section

open MeasureTheory MeasureTheory.Measure Filter Set LeanSolid.Math
open scoped Topology

namespace LeanSolid.ContinuumMechanics

/-- Chain rule for a spatial scalar along a material path. The two terms are the
time derivative at fixed position and the directional derivative along the velocity. -/
theorem hasDerivAt_materialScalar {n : ℕ} {φ : ℝ × Vector n → ℝ}
    {x : ℝ → Vector n} {v : Vector n} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (t, x t)) (hx : HasDerivAt x v t) :
    HasDerivAt (fun s => φ (s, x s))
      (fderiv ℝ φ (t, x t) (1, 0) + fderiv ℝ φ (t, x t) (0, v)) t := by
  have h := hφ.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hx)
  have he : ((1 : ℝ), v) = (1, 0) + (0, v) := by simp
  change HasDerivAt (fun s => φ (s, x s)) (fderiv ℝ φ (t, x t) (1, v)) t at h
  rw [he, map_add] at h
  exact h

/-- Volume change of variables in a positively oriented Cartesian placement. -/
theorem integral_image_placement {n : ℕ} (μ : Measure (Vector n)) [IsAddHaarMeasure μ]
    {Ω : Set (Vector n)} (hΩ : MeasurableSet Ω) (χ : Vector n → Vector n)
    (hχ : ∀ X ∈ Ω, DifferentiableAt ℝ χ X) (hInj : InjOn χ Ω)
    (hJ : ∀ X ∈ Ω, 0 < jacobian (deformationGradient χ X)) (g : Vector n → ℝ) :
    (∫ x in χ '' Ω, g x ∂μ) =
      ∫ X in Ω, jacobian (deformationGradient χ X) * g (χ X) ∂μ := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hΩ
    (fun X hX => (hχ X hX).hasFDerivAt.hasFDerivWithinAt) hInj g]
  apply setIntegral_congr_fun hΩ
  intro X hX
  have hd : jacobian (deformationGradient χ X) = (fderiv ℝ χ X).det := by
    rw [deformationGradient_eq_toMatrix (hχ X hX)]
    exact LinearMap.det_toMatrix' _
  change |(fderiv ℝ χ X).det| • g (χ X) = jacobian (deformationGradient χ X) * g (χ X)
  rw [← hd, abs_of_pos (hJ X hX), smul_eq_mul]

/-- Reference-coordinate Reynolds integrand for a scalar field pulled back to a material point. -/
@[expose]
noncomputable def transportIntegrand (F H : Tensor 3) (g gdot : ℝ) : ℝ :=
  jacobian F * (gdot + g * (velocityGradient F H).trace)

/-- Time derivative of the pulled-back, volume-weighted quantity. -/
theorem hasDerivAt_referenceVolumeWeight {F : ℝ → Tensor 3} {H : Tensor 3}
    {g : ℝ → ℝ} {gdot t : ℝ} (hF : HasTensorDerivAt F H t)
    (hg : HasDerivAt g gdot t) (hJ : jacobian (F t) ≠ 0) :
    HasDerivAt (fun s => jacobian (F s) * g s) (transportIntegrand (F t) H (g t) gdot) t := by
  have h := (hasDerivAt_jacobian_of_spatialRate hF hJ).mul hg
  have he : (fun s => jacobian (F s) * g s) = (fun s => jacobian (F s)) * g := rfl
  rw [he]
  convert h using 1
  unfold transportIntegrand
  ring

/-- Reynolds transport for a moving material region, proved by volume change of variables
and dominated differentiation on the fixed reference set. The scalar rate supplied by
`hRate` is measured along each material trajectory. -/
theorem hasDerivAt_integral_movingRegion
    (μ : Measure (Vector 3)) [IsAddHaarMeasure μ]
    {Ω : Set (Vector 3)} (hΩ : MeasurableSet Ω)
    (χ : ℝ → Vector 3 → Vector 3) (φ : ℝ → Vector 3 → ℝ)
    (Fdot : ℝ → Vector 3 → Tensor 3) (φdot : ℝ → Vector 3 → ℝ)
    {s : Set ℝ} {t : ℝ} (hs : s ∈ 𝓝 t)
    (hPlacement : ∀ τ ∈ s, ∀ X ∈ Ω, DifferentiableAt ℝ (χ τ) X)
    (hInj : ∀ τ ∈ s, InjOn (χ τ) Ω)
    (hJ : ∀ τ ∈ s, ∀ X ∈ Ω, 0 < jacobian (deformationGradient (χ τ) X))
    (hF : ∀ᵐ X ∂μ.restrict Ω, ∀ τ ∈ s,
      HasTensorDerivAt (fun r => deformationGradient (χ r) X) (Fdot τ X) τ)
    (hRate : ∀ᵐ X ∂μ.restrict Ω, ∀ τ ∈ s,
      HasDerivAt (fun r => φ r (χ r X)) (φdot τ X) τ)
    (hMeas : ∀ᶠ τ in 𝓝 t, AEStronglyMeasurable (fun X =>
      jacobian (deformationGradient (χ τ) X) * φ τ (χ τ X)) (μ.restrict Ω))
    (hInt : IntegrableOn (fun X => jacobian (deformationGradient (χ t) X) * φ t (χ t X)) Ω μ)
    (hRateMeas : AEStronglyMeasurable (fun X => transportIntegrand
      (deformationGradient (χ t) X) (Fdot t X) (φ t (χ t X)) (φdot t X)) (μ.restrict Ω))
    (bound : Vector 3 → ℝ) (hBoundInt : IntegrableOn bound Ω μ)
    (hBound : ∀ᵐ X ∂μ.restrict Ω, ∀ τ ∈ s, ‖transportIntegrand
      (deformationGradient (χ τ) X) (Fdot τ X) (φ τ (χ τ X)) (φdot τ X)‖ ≤ bound X) :
    HasDerivAt (fun τ => ∫ x in χ τ '' Ω, φ τ x ∂μ)
      (∫ X in Ω, transportIntegrand (deformationGradient (χ t) X) (Fdot t X)
        (φ t (χ t X)) (φdot t X) ∂μ) t := by
  have hPositive : ∀ᵐ X ∂μ.restrict Ω, X ∈ Ω := ae_restrict_mem hΩ
  have hDiff : ∀ᵐ X ∂μ.restrict Ω, ∀ τ ∈ s, HasDerivAt
      (fun r => jacobian (deformationGradient (χ r) X) * φ r (χ r X))
      (transportIntegrand (deformationGradient (χ τ) X) (Fdot τ X)
        (φ τ (χ τ X)) (φdot τ X)) τ := by
    filter_upwards [hF, hRate, hPositive] with X hxF hxRate hx
    intro τ hτ
    exact hasDerivAt_referenceVolumeWeight (hxF τ hτ) (hxRate τ hτ) (hJ τ hτ X hx).ne'
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hMeas hInt
    hRateMeas hBound hBoundInt hDiff).2
  apply h.congr_of_eventuallyEq
  filter_upwards [hs] with τ hτ
  exact integral_image_placement μ hΩ (χ τ) (hPlacement τ hτ) (hInj τ hτ) (hJ τ hτ) (φ τ)

end LeanSolid.ContinuumMechanics
