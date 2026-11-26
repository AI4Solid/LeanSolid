module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace LeanSolid.Uniaxial

/-- Scalar Hooke's law for Young's modulus `E` and strain `ε`. -/
def stress (E ε : ℝ) : ℝ := E * ε

/-- Quadratic elastic strain energy per unit volume. -/
noncomputable def energyDensity (E ε : ℝ) : ℝ := E * ε ^ 2 / 2

end LeanSolid.Uniaxial
