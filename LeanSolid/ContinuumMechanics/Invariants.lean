module

public import LeanSolid.ContinuumMechanics.Definitions
public import LeanSolid.Math.Theorems
public import LeanSolid.Math.Calculus.TensorPath
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

variable {n : ℕ}

/-- First principal invariant of a second-order tensor. -/
def invariant₁ (A : Tensor n) : ℝ := A.trace

/-- Second principal invariant, the sum of the principal two-by-two minors. -/
def invariant₂ (A : Tensor n) : ℝ := (A.trace ^ 2 - (A * A).trace) / 2

/-- Third principal invariant in three dimensions. -/
def invariant₃ (A : Tensor 3) : ℝ := A.det

/-- The same invariants may be evaluated on Green–Lagrange strain or on Cauchy–Green tensors. -/
def principalInvariants (A : Tensor 3) : Vector 3 :=
  ![invariant₁ A, invariant₂ A, invariant₃ A]

theorem invariant₁_conjugate (Q A : Tensor n) (hQ : Q.transpose * Q = 1) :
    invariant₁ (conjugate Q A) = invariant₁ A :=
  trace_conjugate Q A hQ

theorem invariant₂_conjugate (Q A : Tensor n) (hQ : Q.transpose * Q = 1) :
    invariant₂ (conjugate Q A) = invariant₂ A := by
  have h : conjugate Q A * conjugate Q A = conjugate Q (A * A) := by
    unfold conjugate
    calc
      (Q * A * Q.transpose) * (Q * A * Q.transpose) =
          Q * A * (Q.transpose * Q) * A * Q.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by simp [hQ, Matrix.mul_assoc]
  rw [invariant₂, invariant₂, trace_conjugate Q A hQ, h, trace_conjugate Q (A * A) hQ]

theorem invariant₃_conjugate (Q A : Tensor 3) (hQ : Q.transpose * Q = 1) :
    invariant₃ (conjugate Q A) = invariant₃ A := by
  have hd := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_one] at hd
  unfold invariant₃ conjugate
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Q.det * A.det * Q.transpose.det = (Q.transpose.det * Q.det) * A.det := by ring
    _ = A.det := by rw [hd, one_mul]

theorem invariant₃_rightCauchyGreen (F : Tensor 3) :
    invariant₃ (rightCauchyGreen F) = jacobian F ^ 2 := by
  simp [invariant₃, rightCauchyGreen, jacobian, Matrix.det_mul, pow_two]

theorem principalInvariants_conjugate (Q A : Tensor 3) (hQ : Q.transpose * Q = 1) :
    principalInvariants (conjugate Q A) = principalInvariants A := by
  rw [principalInvariants, principalInvariants, invariant₁_conjugate Q A hQ,
    invariant₂_conjugate Q A hQ, invariant₃_conjugate Q A hQ]

/-- Jacobi's cofactor formula in three dimensions, valid also at singular tensors. -/
theorem hasDerivAt_invariant₃ {A : ℝ → Tensor 3} {H : Tensor 3} {t : ℝ}
    (hA : HasTensorDerivAt A H t) :
    HasDerivAt (fun s => invariant₃ (A s)) (contract (A t).adjugate.transpose H) t := by
  have m (i j k l p q : Fin 3) :
      HasDerivAt (fun s => A s i j * A s k l * A s p q)
        ((H i j * A t k l + A t i j * H k l) * A t p q + A t i j * A t k l * H p q) t :=
    ((hA i j).mul (hA k l)).mul (hA p q)
  have h := (((((m 0 0 1 1 2 2).sub (m 0 0 1 2 2 1)).sub (m 0 1 1 0 2 2)).add
    (m 0 1 1 2 2 0)).add (m 0 2 1 0 2 1)).sub (m 0 2 1 1 2 0)
  simp only [invariant₃, Matrix.det_fin_three, contract, Matrix.transpose_apply,
    Matrix.adjugate_fin_three, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  convert h using 1
  simp
  ring

end LeanSolid.ContinuumMechanics
