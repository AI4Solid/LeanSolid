module

public import LeanSolid.ContinuumMechanics.Area
public import LeanSolid.ContinuumMechanics.Theorems
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

open MeasureTheory Set LeanSolid.Math
open scoped Matrix

namespace LeanSolid.ContinuumMechanics

noncomputable section

/-- Oriented area density in a two-parameter chart. The parameter order fixes the orientation. -/
def chartAreaVector (r : Vector 2 → Vector 3) (u : Vector 2) : Vector 3 :=
  let Dr := fderiv ℝ r u
  Dr (Pi.single 0 1) ⨯₃ Dr (Pi.single 1 1)

/-- Surface integral in a supplied chart, with multiplicity if the chart overlaps itself. -/
def chartSurfaceIntegral (D : Set (Vector 2)) (r : Vector 2 → Vector 3)
    (g : Vector 3 → ℝ) : ℝ :=
  ∫ u in D, g (r u) * Real.sqrt (dotProduct (chartAreaVector r u) (chartAreaVector r u))

/-- Oriented flux integral in a supplied chart. -/
def chartFlux (D : Set (Vector 2)) (r : Vector 2 → Vector 3)
    (w : Vector 3 → Vector 3) : ℝ :=
  ∫ u in D, dotProduct (w (r u)) (chartAreaVector r u)

/-- Surface integral of a vector field, using the same area density as
the scalar chart integral. -/
def chartSurfaceForce (D : Set (Vector 2)) (r : Vector 2 → Vector 3)
    (traction : Vector 3 → Vector 3) : Vector 3 :=
  ∫ u in D, Real.sqrt (dotProduct (chartAreaVector r u) (chartAreaVector r u)) •
    traction (r u)

/-- For an affine face chart the force is its area times the normalized
parameter average. The normalization uses a finite, positive parameter area. -/
theorem chartSurfaceForce_affine (D : Set (Vector 2)) (p : Vector 3)
    (L : Vector 2 →L[ℝ] Vector 3) (traction : Vector 3 → Vector 3)
    (hD : volume.real D ≠ 0) :
    let r := fun u => L u + p
    chartSurfaceForce D r traction =
      chartSurfaceIntegral D r (fun _ => 1) •
        ((volume.real D)⁻¹ • ∫ u in D, traction (r u)) := by
  have harea (u : Vector 2) :
      chartAreaVector (fun v => L v + p) u = L (Pi.single 0 1) ⨯₃ L (Pi.single 1 1) := by
    rw [chartAreaVector, (L.hasFDerivAt.add_const p).fderiv]
  have hmeasure : (volume.restrict D).real univ = volume.real D := by
    simp only [measureReal_def, Measure.restrict_apply_univ]
  dsimp only
  simp only [chartSurfaceForce, chartSurfaceIntegral, harea, integral_smul, one_mul,
    integral_const, hmeasure, smul_eq_mul, smul_smul]
  rw [mul_comm (volume.real D), mul_assoc, mul_inv_cancel₀ hD, mul_one]

theorem chartAreaVector_comp {χ : Vector 3 → Vector 3} {r : Vector 2 → Vector 3}
    {u : Vector 2} (hr : DifferentiableAt ℝ r u) (hχ : DifferentiableAt ℝ χ (r u)) :
    chartAreaVector (χ ∘ r) u =
      (deformationGradient χ (r u)).adjugate.transpose *ᵥ chartAreaVector r u := by
  have hmul (v : Vector 3) :
      (fderiv ℝ χ (r u)) v = deformationGradient χ (r u) *ᵥ v := by
    rw [deformationGradient_eq_toMatrix hχ, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  unfold chartAreaVector
  rw [fderiv_comp u hχ hr]
  change (fderiv ℝ χ (r u)) ((fderiv ℝ r u) (Pi.single 0 1)) ⨯₃
      (fderiv ℝ χ (r u)) ((fderiv ℝ r u) (Pi.single 1 1)) = _
  rw [hmul, hmul, areaVector_transform]

theorem chartSurfaceIntegral_comp (D : Set (Vector 2)) (hD : MeasurableSet D)
    (χ : Vector 3 → Vector 3) (r : Vector 2 → Vector 3) (g : Vector 3 → ℝ)
    (hr : ∀ u ∈ D, DifferentiableAt ℝ r u)
    (hχ : ∀ u ∈ D, DifferentiableAt ℝ χ (r u)) :
    chartSurfaceIntegral D (χ ∘ r) g = ∫ u in D, g (χ (r u)) *
      Real.sqrt (dotProduct
        ((deformationGradient χ (r u)).adjugate.transpose *ᵥ chartAreaVector r u)
        ((deformationGradient χ (r u)).adjugate.transpose *ᵥ chartAreaVector r u)) := by
  apply setIntegral_congr_fun hD
  intro u hu
  simp only [Function.comp_apply, chartAreaVector_comp (hr u hu) (hχ u hu)]

theorem chartFlux_comp (D : Set (Vector 2)) (hD : MeasurableSet D)
    (χ : Vector 3 → Vector 3) (r : Vector 2 → Vector 3) (w : Vector 3 → Vector 3)
    (hr : ∀ u ∈ D, DifferentiableAt ℝ r u)
    (hχ : ∀ u ∈ D, DifferentiableAt ℝ χ (r u)) :
    chartFlux D (χ ∘ r) w = ∫ u in D, dotProduct (w (χ (r u)))
      ((deformationGradient χ (r u)).adjugate.transpose *ᵥ chartAreaVector r u) := by
  apply setIntegral_congr_fun hD
  intro u hu
  simp only [Function.comp_apply, chartAreaVector_comp (hr u hu) (hχ u hu)]

end

end LeanSolid.ContinuumMechanics
