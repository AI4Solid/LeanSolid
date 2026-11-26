module

public import LeanSolid.Constitutive.Uniaxial.Definitions
import Mathlib.Tactic.Ring

public section

namespace LeanSolid.Uniaxial

theorem energyDensity_eq_half_stress_mul_strain (E ε : ℝ) :
    energyDensity E ε = stress E ε * ε / 2 := by
  unfold energyDensity stress
  ring

theorem energyDensity_nonneg (E ε : ℝ) (hE : 0 ≤ E) :
    0 ≤ energyDensity E ε := by
  exact div_nonneg (mul_nonneg hE (sq_nonneg ε)) (by norm_num)

end LeanSolid.Uniaxial
