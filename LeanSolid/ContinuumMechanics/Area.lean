module

public import LeanSolid.ContinuumMechanics.Statics
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

public section

open scoped Matrix

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

/-- Pointwise Nanson formula for oriented area vectors represented by tangent cross products.
The cofactor identity also holds for singular matrices. -/
theorem areaVector_transform (F : Tensor 3) (a b : Vector 3) :
    (F *ᵥ a) ⨯₃ (F *ᵥ b) = F.adjugate.transpose *ᵥ (a ⨯₃ b) := by
  funext i
  fin_cases i <;>
    simp [cross_apply, Matrix.mulVec, dotProduct, Matrix.adjugate_fin_three,
      Matrix.transpose_apply, Fin.sum_univ_succ] <;> ring

theorem cofactor_eq_jacobian_smul_invTranspose {n : ℕ} (F : Tensor n)
    (hJ : jacobian F ≠ 0) :
    F.adjugate.transpose = jacobian F • (F⁻¹).transpose := by
  have ha : F.adjugate = jacobian F • F⁻¹ := by
    calc
      F.adjugate = F⁻¹ * (F * F.adjugate) :=
        (Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hJ)).symm
      _ = _ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]; rfl
  rw [ha, Matrix.transpose_smul]

theorem areaVector_transform_inverse (F : Tensor 3) (a b : Vector 3)
    (hJ : jacobian F ≠ 0) :
    (F *ᵥ a) ⨯₃ (F *ᵥ b) =
      jacobian F • ((F⁻¹).transpose *ᵥ (a ⨯₃ b)) := by
  rw [areaVector_transform, cofactor_eq_jacobian_smul_invTranspose F hJ, Matrix.smul_mulVec]

/-- Cauchy traction paired with the spatial oriented area agrees with the nominal
traction paired with the reference oriented area. -/
theorem traction_area_transform (F σ : Tensor 3) (a b : Vector 3) :
    nominalTraction (firstPiola F σ) (a ⨯₃ b) =
      σ *ᵥ ((F *ᵥ a) ⨯₃ (F *ᵥ b)) := by
  rw [nominalTraction_firstPiola, areaVector_transform]

end LeanSolid.ContinuumMechanics
