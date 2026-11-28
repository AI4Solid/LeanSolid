module

public import LeanSolid.ContinuumMechanics.Definitions
public import LeanSolid.Math.Theorems
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic.Abel

public section

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

variable {n : ℕ}

theorem deformationGradient_eq_toMatrix {χ : Vector n → Vector n} {X : Vector n}
    (hχ : DifferentiableAt ℝ χ X) :
    deformationGradient χ X = LinearMap.toMatrix' (fderiv ℝ χ X).toLinearMap := by
  ext i j
  change partialDeriv (fun Y => χ Y i) j X = _
  rw [partialDeriv, fderiv_apply hχ, LinearMap.toMatrix'_apply]
  rfl

/-- Chain rule for successive placements, with the intermediate configuration evaluated at χ X. -/
theorem deformationGradient_comp {χ ψ : Vector n → Vector n} {X : Vector n}
    (hχ : DifferentiableAt ℝ χ X) (hψ : DifferentiableAt ℝ ψ (χ X)) :
    deformationGradient (ψ ∘ χ) X =
      deformationGradient ψ (χ X) * deformationGradient χ X := by
  rw [deformationGradient_eq_toMatrix (hψ.comp X hχ),
    deformationGradient_eq_toMatrix hψ, deformationGradient_eq_toMatrix hχ,
    fderiv_comp X hψ hχ]
  exact LinearMap.toMatrix'_comp _ _

/-- An affine placement has the same deformation gradient at every material point. -/
theorem deformationGradient_affine (L : Vector n →L[ℝ] Vector n) (c X : Vector n) :
    deformationGradient (fun Y => L Y + c) X = LinearMap.toMatrix' L.toLinearMap := by
  have h := L.hasFDerivAt (x := X) |>.add_const c
  rw [deformationGradient_eq_toMatrix h.differentiableAt, h.fderiv]

theorem deformationGradient_placement (u : Vector n → Vector n) (X : Vector n)
    (hu : DifferentiableAt ℝ u X) :
    deformationGradient (placement u) X = 1 + deformationGradient u X := by
  have hplaced : DifferentiableAt ℝ (placement u) X := differentiableAt_id.add hu
  rw [deformationGradient_eq_toMatrix hplaced, deformationGradient_eq_toMatrix hu]
  change LinearMap.toMatrix' (fderiv ℝ (fun Y => id Y + u Y) X).toLinearMap = _
  rw [fderiv_fun_add differentiableAt_id hu, fderiv_id]
  change LinearMap.toMatrix' (LinearMap.id + (fderiv ℝ u X).toLinearMap) = _
  rw [map_add, LinearMap.toMatrix'_id]

theorem deformationGradient_id (X : Vector n) : deformationGradient id X = 1 := by
  rw [deformationGradient_eq_toMatrix differentiableAt_id, fderiv_id]
  exact LinearMap.toMatrix'_id

theorem jacobian_mul (F G : Tensor n) : jacobian (F * G) = jacobian F * jacobian G :=
  Matrix.det_mul _ _

theorem rightCauchyGreen_transpose (F : Tensor n) :
    (rightCauchyGreen F).transpose = rightCauchyGreen F := by
  simp [rightCauchyGreen, Matrix.transpose_mul]

theorem leftCauchyGreen_transpose (F : Tensor n) :
    (leftCauchyGreen F).transpose = leftCauchyGreen F := by
  simp [leftCauchyGreen, Matrix.transpose_mul]

theorem greenStrain_transpose (F : Tensor n) : (greenStrain F).transpose = greenStrain F := by
  simp [greenStrain, Matrix.transpose_smul, Matrix.transpose_sub, rightCauchyGreen_transpose]

/-- An orthogonal change on the spatial side leaves the reference metric invariant. -/
theorem rightCauchyGreen_orthogonal_mul (Q F : Tensor n) (hQ : Q.transpose * Q = 1) :
    rightCauchyGreen (Q * F) = rightCauchyGreen F := by
  unfold rightCauchyGreen
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q.transpose, hQ, one_mul]

theorem greenStrain_orthogonal_mul (Q F : Tensor n) (hQ : Q.transpose * Q = 1) :
    greenStrain (Q * F) = greenStrain F := by
  simp only [greenStrain, rightCauchyGreen_orthogonal_mul Q F hQ]

theorem greenStrain_one : greenStrain (1 : Tensor n) = 0 := by
  simp [greenStrain, rightCauchyGreen]

/-- The symmetric gradient is the linear term of the exact finite strain. -/
theorem greenStrain_one_add (G : Tensor n) :
    greenStrain (1 + G) = symPart G + (1 / 2 : ℝ) • (G.transpose * G) := by
  have h : (1 + G).transpose * (1 + G) - 1 = (G + G.transpose) + G.transpose * G := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul]
    simp only [one_mul, Matrix.mul_add, mul_one]
    abel
  rw [greenStrain, rightCauchyGreen, h, smul_add]
  rfl

end LeanSolid.ContinuumMechanics
