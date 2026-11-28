module

public import LeanSolid.ContinuumMechanics.Theorems
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith

@[expose] public section

open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

variable {n : ℕ}

theorem stretch_sq_eq_rightCauchyGreen (F : Tensor n) (N : Vector n) :
    dotProduct (F.mulVec N) (F.mulVec N) = dotProduct N ((rightCauchyGreen F).mulVec N) := by
  rw [rightCauchyGreen, ← Matrix.mulVec_mulVec]
  exact (Matrix.dotProduct_transpose_mulVec F N (F.mulVec N)).symm

theorem rightCauchyGreen_posDef (F : Tensor n) (hJ : jacobian F ≠ 0) :
    (rightCauchyGreen F).PosDef := by
  have h : (rightCauchyGreen F).PosSemidef := by
    simpa only [rightCauchyGreen, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self F
  apply h.posDef_iff_det_ne_zero.mpr
  simpa only [jacobian, rightCauchyGreen, Matrix.det_mul, Matrix.det_transpose] using mul_ne_zero hJ hJ

theorem leftCauchyGreen_posDef (F : Tensor n) (hJ : jacobian F ≠ 0) :
    (leftCauchyGreen F).PosDef := by
  have ht : jacobian F.transpose ≠ 0 := by simpa only [jacobian, Matrix.det_transpose] using hJ
  simpa only [rightCauchyGreen, leftCauchyGreen, Matrix.transpose_transpose] using
    rightCauchyGreen_posDef F.transpose ht

/-- Principal stretches are the positive square roots of the eigenvalues of C. -/
def principalStretch (F : Tensor n) (i : Fin n) : ℝ :=
  Real.sqrt ((show (rightCauchyGreen F).IsHermitian by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact rightCauchyGreen_transpose F).eigenvalues i)

theorem principalStretch_pos (F : Tensor n) (hJ : jacobian F ≠ 0) (i : Fin n) :
    0 < principalStretch F i :=
  Real.sqrt_pos.mpr ((rightCauchyGreen_posDef F hJ).eigenvalues_pos i)

/-- Positive square root of C. -/
def rightStretch (F : Tensor n) : Tensor n := CFC.sqrt (rightCauchyGreen F)

/-- Positive square root of B. -/
def leftStretch (F : Tensor n) : Tensor n := CFC.sqrt (leftCauchyGreen F)

/-- Rotation in the right polar decomposition, for invertible F. -/
def polarRotation (F : Tensor n) : Tensor n := F * (rightStretch F)⁻¹

theorem rightStretch_sq (F : Tensor n) (hJ : jacobian F ≠ 0) :
    rightStretch F * rightStretch F = rightCauchyGreen F :=
  CFC.sqrt_mul_sqrt_self _ (rightCauchyGreen_posDef F hJ).posSemidef.nonneg

private theorem rightStretch_semidef (F : Tensor n) : (rightStretch F).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

theorem rightStretch_posDef (F : Tensor n) (hJ : jacobian F ≠ 0) : (rightStretch F).PosDef := by
  apply (rightStretch_semidef F).posDef_iff_det_ne_zero.mpr
  intro hz
  have h := congrArg Matrix.det (rightStretch_sq F hJ)
  rw [Matrix.det_mul, hz, zero_mul] at h
  exact (rightCauchyGreen_posDef F hJ).det_pos.ne' h.symm

theorem polarRotation_mul_rightStretch (F : Tensor n) (hJ : jacobian F ≠ 0) :
    polarRotation F * rightStretch F = F :=
  Matrix.nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.mpr (rightStretch_posDef F hJ).det_pos.ne')

theorem polarRotation_orthogonal (F : Tensor n) (hJ : jacobian F ≠ 0) :
    (polarRotation F).transpose * polarRotation F = 1 := by
  let U := rightStretch F
  have hU : U.transpose = U := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (rightStretch_semidef F).isHermitian
  have hi : IsUnit U.det := isUnit_iff_ne_zero.mpr (rightStretch_posDef F hJ).det_pos.ne'
  change (F * U⁻¹).transpose * (F * U⁻¹) = 1
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hU]
  calc
    _ = U⁻¹ * ((F.transpose * F) * U⁻¹) := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [show F.transpose * F = U * U from (rightStretch_sq F hJ).symm,
        Matrix.mul_nonsing_inv_cancel_right U U hi, Matrix.nonsing_inv_mul U hi]

theorem polarRotation_det (F : Tensor n) (hJ : 0 < jacobian F) :
    jacobian (polarRotation F) = 1 := by
  have h := congrArg Matrix.det (polarRotation_orthogonal F hJ.ne')
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have he := congrArg Matrix.det (polarRotation_mul_rightStretch F hJ.ne')
  rw [Matrix.det_mul] at he
  have hp : 0 < (polarRotation F).det := by
    apply pos_of_mul_pos_left (b := (rightStretch F).det)
    · rw [he]
      exact hJ
    · exact (rightStretch_posDef F hJ.ne').det_pos.le
  change (polarRotation F).det = 1
  nlinarith

theorem rightStretch_unique (F U : Tensor n) (hJ : jacobian F ≠ 0)
    (hU : U.PosSemidef) (hSq : U * U = rightCauchyGreen F) : rightStretch F = U :=
  (CFC.sqrt_eq_iff _ _ (rightCauchyGreen_posDef F hJ).posSemidef.nonneg hU.nonneg).mpr hSq

theorem rightPolar_unique (F R U : Tensor n) (hJ : jacobian F ≠ 0)
    (hR : R.transpose * R = 1) (hU : U.PosSemidef) (hF : R * U = F) :
    polarRotation F = R ∧ rightStretch F = U := by
  have hUt : U.transpose = U := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hU.isHermitian
  have hC : rightCauchyGreen F = U * U := by
    rw [rightCauchyGreen, ← hF, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc R.transpose, hR, one_mul, hUt]
  have he := rightStretch_unique F U hJ hU hC.symm
  have hp : 0 < U.det := by
    rw [← he]
    exact (rightStretch_posDef F hJ).det_pos
  have hi : IsUnit U.det := isUnit_iff_ne_zero.mpr hp.ne'
  exact ⟨by rw [polarRotation, he, ← hF, Matrix.mul_nonsing_inv_cancel_right U R hi], he⟩

/-- The spatial stretch is the material stretch conjugated by the polar rotation. -/
theorem leftStretch_eq_conjugate (F : Tensor n) (hJ : jacobian F ≠ 0) :
    leftStretch F = conjugate (polarRotation F) (rightStretch F) := by
  let R := polarRotation F
  let U := rightStretch F
  have hR : R.transpose * R = 1 := polarRotation_orthogonal F hJ
  have hF : R * U = F := polarRotation_mul_rightStretch F hJ
  have hU : U.transpose = U := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (rightStretch_semidef F).isHermitian
  have hP : (conjugate R U).PosSemidef := by
    simpa only [conjugate, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose, Matrix.mul_assoc] using
      (rightStretch_semidef F).conjTranspose_mul_mul_same R.transpose
  apply (CFC.sqrt_eq_iff _ _ (leftCauchyGreen_posDef F hJ).posSemidef.nonneg hP.nonneg).mpr
  unfold conjugate leftCauchyGreen
  rw [← hF, Matrix.transpose_mul, hU]
  calc
    _ = (R * U) * ((R.transpose * R) * (U * R.transpose)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hR, one_mul]

theorem leftStretch_mul_polarRotation (F : Tensor n) (hJ : jacobian F ≠ 0) :
    leftStretch F * polarRotation F = F := by
  rw [leftStretch_eq_conjugate F hJ, conjugate, Matrix.mul_assoc,
    polarRotation_orthogonal F hJ, mul_one, polarRotation_mul_rightStretch F hJ]

/-- Euler–Almansi strain on the spatial configuration of an invertible deformation. -/
def almansiStrain (F : Tensor n) : Tensor n :=
  (1 / 2 : ℝ) • (1 - (leftCauchyGreen F)⁻¹)

theorem almansiStrain_pullback (F : Tensor n) (hJ : jacobian F ≠ 0) :
    F.transpose * almansiStrain F * F = greenStrain F := by
  have hF : IsUnit F.det := isUnit_iff_ne_zero.mpr hJ
  have hi : F.transpose * (leftCauchyGreen F)⁻¹ * F = 1 := by
    rw [leftCauchyGreen, Matrix.mul_inv_rev,
      ← Matrix.mul_assoc F.transpose, Matrix.mul_nonsing_inv F.transpose (Matrix.isUnit_det_transpose F hF),
      one_mul, Matrix.nonsing_inv_mul F hF]
  rw [almansiStrain, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    mul_one, hi]
  rfl

end LeanSolid.ContinuumMechanics
