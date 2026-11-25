module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

@[expose] public section

namespace LeanSolid.Uniaxial

/-- Scalar Hooke's law for Young's modulus `E` and strain `ε`. -/
def stress (E ε : ℝ) : ℝ := E * ε

/-- Quadratic elastic strain energy per unit volume. -/
noncomputable def energyDensity (E ε : ℝ) : ℝ := E * ε ^ 2 / 2

theorem energyDensity_eq_half_stress_mul_strain (E ε : ℝ) :
    energyDensity E ε = stress E ε * ε / 2 := by
  unfold energyDensity stress
  ring

theorem energyDensity_nonneg (E ε : ℝ) (hE : 0 ≤ E) :
    0 ≤ energyDensity E ε := by
  exact div_nonneg (mul_nonneg hE (sq_nonneg ε)) (by norm_num)

end LeanSolid.Uniaxial
