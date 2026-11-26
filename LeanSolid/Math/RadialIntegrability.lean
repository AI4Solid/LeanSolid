module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.Linarith

public section

namespace LeanSolid.Math

/-- Integrability of the radial density after inserting the two-dimensional Jacobian.
The exponent `p` describes an exact power law; angular factors are not modeled here. -/
theorem radialEnergyIntegrable_iff (p : ℝ) {R : ℝ} (hR : 0 < R) :
    MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (2 * p + 1)) (Set.Ioo 0 R) ↔ -1 < p := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hR]
  constructor <;> intro h <;> linarith

end LeanSolid.Math
