module

public import LeanSolid.Constitutive.Uniaxial

public section

namespace LeanSolid.Examples

/-- Scalar strain recovery for a material with strictly positive modulus. -/
theorem strain_eq_of_stress_eq (E ε₁ ε₂ : ℝ) (hE : 0 < E)
    (hσ : Uniaxial.stress E ε₁ = Uniaxial.stress E ε₂) :
    ε₁ = ε₂ := by
  exact mul_left_cancel₀ (ne_of_gt hE) hσ

end LeanSolid.Examples
