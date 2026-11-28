module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Incompressible
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public section

open LeanSolid.Math
open scoped Matrix

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

/-- The deformation gradient of the homogeneous shear x₁ = X₁ + γ X₂. -/
def simpleShearGradient (γ : ℝ) : Tensor 3 := !![1, γ, 0; 0, 1, 0; 0, 0, 1]

theorem jacobian_simpleShearGradient (γ : ℝ) : jacobian (simpleShearGradient γ) = 1 := by
  simp [simpleShearGradient, jacobian, Matrix.det_fin_three]

/-- Rivlin's homogeneous incompressible simple shear for the two-invariant linear energy.
The columns of the first Piola stress give the tractions on the positive reference faces.
The multiplier convention is that of `constrainedEnergy`. -/
theorem rivlin_simpleShear_nominalStress (c₁ c₂ p γ : ℝ) :
    let F := simpleShearGradient γ
    let d := 2 * (c₁ + 2 * c₂) - p
    let τ := 2 * (c₁ + c₂) * γ
    firstPiolaStress
      (constrainedEnergy (fun A => mooneyRivlinEnergy c₁ c₂ (rightCauchyGreen A)) p) F =
      !![d, τ, 0; (p - 2 * c₂) * γ, d, 0; 0, 0, d + 2 * c₂ * γ^2] := by
  dsimp only
  rw [mooneyRivlin_firstPiola]
  have hC : rightCauchyGreen (simpleShearGradient γ) =
      !![1, γ, 0; γ, 1 + γ^2, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [simpleShearGradient, rightCauchyGreen, Matrix.mul_apply, Fin.sum_univ_three, pow_two,
        add_comm]
  have hAdj : (simpleShearGradient γ).adjugate.transpose =
      !![1, 0, 0; -γ, 1, 0; 0, 0, 1] := by
    rw [simpleShearGradient, Matrix.adjugate_fin_three_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hC, hAdj]
  unfold mooneyRivlinSecondPiola
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [simpleShearGradient, Matrix.one_apply] <;> ring

/-- Setting the normal stress on the shear plane to zero fixes the multiplier.
The remaining normal stresses are quadratic in the shear amplitude. -/
theorem rivlin_simpleShear_cauchyStress (c₁ c₂ γ : ℝ) :
    let F := simpleShearGradient γ
    let p := 2 * (c₁ + 2 * c₂)
    let τ := 2 * (c₁ + c₂) * γ
    cauchyFromPiola F (firstPiolaStress
      (constrainedEnergy (fun A => mooneyRivlinEnergy c₁ c₂ (rightCauchyGreen A)) p) F) =
      !![τ * γ, τ, 0; τ, 0, 0; 0, 0, 2 * c₂ * γ^2] := by
  dsimp only
  rw [rivlin_simpleShear_nominalStress, cauchyFromPiola, jacobian_simpleShearGradient,
    inv_one, one_smul]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [simpleShearGradient]
  ring_nf
  simp

/-- Nominal traction on either orientation of any Cartesian reference face. -/
theorem rivlin_simpleShear_faceTraction (c₁ c₂ p γ s : ℝ) (j : Fin 3) :
    let d := 2 * (c₁ + 2 * c₂) - p
    let τ := 2 * (c₁ + c₂) * γ
    let P := firstPiolaStress
      (constrainedEnergy (fun A => mooneyRivlinEnergy c₁ c₂ (rightCauchyGreen A)) p)
      (simpleShearGradient γ)
    nominalTraction P (s • Pi.single j 1) =
      s • (!![d, τ, 0; (p - 2 * c₂) * γ, d, 0; 0, 0, d + 2 * c₂ * γ^2]).col j := by
  dsimp only
  rw [rivlin_simpleShear_nominalStress, nominalTraction, Matrix.mulVec_smul,
    Matrix.mulVec_single_one]

end LeanSolid.ContinuumMechanics.Hyperelasticity
