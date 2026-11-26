module

public import LeanSolid.AntiPlane.Theorems
public import LeanSolid.Math.RadialIntegrability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum

public section

namespace LeanSolid.AntiPlane

open LeanSolid.Math

theorem antiPlane_balance_iff_harmonic (mu : ℝ) (hmu : mu ≠ 0)
    {w : Vector 2 → ℝ} (hw : ContDiff ℝ 2 w) (x : Vector 2) :
    balanceResidual mu w x = 0 ↔ laplacian w x = 0 := by
  rw [balanceResidual_eq_laplacian mu hw, mul_eq_zero]
  simp [hmu]

/-- The radius-dependent factor in the screw dislocation energy in an annulus. -/
theorem screw_radialEnergy_annulus {rc R : ℝ} (hc : 0 < rc) (hR : 0 < R) :
    (∫ r in rc..R, r⁻¹) = Real.log (R / rc) :=
  integral_inv_of_pos hc hR

theorem crack_radialEnergy_integrable {R : ℝ} (hR : 0 < R) :
    MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (2 * (-(1 / 2) : ℝ) + 1))
      (Set.Ioo 0 R) :=
  (radialEnergyIntegrable_iff _ hR).2 (by norm_num)

theorem dislocation_radialEnergy_not_integrable {R : ℝ} (hR : 0 < R) :
    ¬ MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (2 * (-1 : ℝ) + 1))
      (Set.Ioo 0 R) := by
  rw [radialEnergyIntegrable_iff _ hR]
  norm_num

end LeanSolid.AntiPlane
