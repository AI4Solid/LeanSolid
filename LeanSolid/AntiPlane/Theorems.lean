module

public import LeanSolid.AntiPlane.Definitions
public import LeanSolid.Math.Calculus.Theorems
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul

public section

open scoped ContDiff

namespace LeanSolid.AntiPlane

open LeanSolid.Math LeanSolid.LinearElasticity

theorem constitutive_antiPlane (lam mu wx wy : ℝ) :
    stress lam mu (strain (gradient wx wy)) =
      Matrix.of ![![0, 0, mu * wx], ![0, 0, mu * wy], ![mu * wx, mu * wy, 0]] := by
  have hε : strain (gradient wx wy) =
      Matrix.of ![![0, 0, wx / 2], ![0, 0, wy / 2], ![wx / 2, wy / 2, 0]] := by
    ext i j
    simp only [strain, symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> norm_num [gradient, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hε]
  have ht : (Matrix.of ![![0, 0, wx / 2], ![0, 0, wy / 2], ![wx / 2, wy / 2, 0]] :
      Tensor 3).trace = 0 := by norm_num [Matrix.trace, Fin.sum_univ_succ]
  unfold stress
  rw [ht, mul_zero, zero_smul, zero_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [smul_eq_mul] <;> ring

theorem balanceResidual_eq_laplacian (mu : ℝ) {w : Vector 2 → ℝ}
    (hw : ContDiff ℝ 2 w) (x : Vector 2) :
    balanceResidual mu w x = mu * laplacian w x := by
  rw [balanceResidual, laplacian, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := (contDiff_partial hw (k := 1) (by norm_num) i).differentiable one_ne_zero
  simp [shear, partial_mul (differentiable_const mu) hi, partial_const]

theorem screwDisplacement_jump (b θ : ℝ) :
    screwDisplacement b (θ + 2 * Real.pi) - screwDisplacement b θ = b := by
  unfold screwDisplacement
  have hpi := Real.pi_ne_zero
  field_simp
  ring

theorem screwShear (mu b r θ : ℝ) (hr : r ≠ 0) :
    polarShear mu r (screwDisplacement b) θ = mu * b / (2 * Real.pi * r) := by
  have hd : deriv (screwDisplacement b) θ = b / (2 * Real.pi) := by
    change deriv (fun t : ℝ => b / (2 * Real.pi) * t) θ = _
    exact ((hasDerivAt_id θ).const_mul (b / (2 * Real.pi))).deriv.trans (mul_one _)
  rw [polarShear, hd]
  have hpi := Real.pi_ne_zero
  field_simp

end LeanSolid.AntiPlane
