module

public import LeanSolid.Math.Definitions
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

public section

namespace LeanSolid.Math

variable {n : ℕ}

theorem symPart_transpose (A : Tensor n) : (symPart A).transpose = symPart A := by
  ext i j
  simp only [symPart, Matrix.transpose_apply, Matrix.smul_apply, Matrix.add_apply]
  rw [add_comm (A j i) (A i j)]

theorem symPart_add (A B : Tensor n) : symPart (A + B) = symPart A + symPart B := by
  ext i j
  simp [symPart, Matrix.transpose_apply, smul_eq_mul]
  ring

theorem contract_self_nonneg (A : Tensor n) : 0 ≤ contract A A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (A i j)

theorem contract_comm (A B : Tensor n) : contract A B = contract B A := by
  simp [contract, mul_comm]

theorem contract_eq_trace (A B : Tensor n) : contract A B = (A.transpose * B).trace := by
  unfold contract Matrix.trace
  rw [Finset.sum_comm]
  rfl

/-- Transposing either factor has the same effect on the Frobenius contraction. -/
theorem contract_transpose_left (A B : Tensor n) :
    contract A.transpose B = contract A B.transpose := by
  unfold contract
  rw [Finset.sum_comm]
  rfl

theorem symPart_add_skewPart (A : Tensor n) : symPart A + skewPart A = A := by
  ext i j
  simp [symPart, skewPart, smul_eq_mul]
  ring

theorem symPart_eq_zero_iff (A : Tensor n) :
    symPart A = 0 ↔ A.transpose = -A := by
  constructor
  · intro h
    ext i j
    have hij := congrArg (fun T : Tensor n => T i j) h
    simp [symPart, smul_eq_mul] at hij
    change A j i = -A i j
    linarith
  · intro h
    simp [symPart, h]

theorem contract_add_left (A B C : Tensor n) :
    contract (A + B) C = contract A C + contract B C := by
  simp [contract, add_mul, Finset.sum_add_distrib]

theorem contract_smul_left (c : ℝ) (A B : Tensor n) :
    contract (c • A) B = c * contract A B := by
  simp [contract, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem contract_add_right (A B C : Tensor n) :
    contract A (B + C) = contract A B + contract A C := by
  simp [contract, mul_add, Finset.sum_add_distrib]

theorem contract_smul_right (c : ℝ) (A B : Tensor n) :
    contract A (c • B) = c * contract A B := by
  rw [contract_comm A, contract_smul_left, contract_comm B]

theorem contract_symPart_of_symmetric (A B : Tensor n) (hB : B.transpose = B) :
    contract (symPart A) B = contract A B := by
  rw [symPart, contract_smul_left, contract_add_left, contract_transpose_left, hB]
  ring

theorem contract_skewPart_of_skew (A B : Tensor n) (hB : B.transpose = -B) :
    contract (skewPart A) B = contract A B := by
  have hneg (C : Tensor n) : contract C (-B) = -contract C B := by
    simp [contract, mul_neg]
  have hsub : contract (A - A.transpose) B =
      contract A B - contract A.transpose B := by
    simp [contract, sub_mul, Finset.sum_sub_distrib]
  rw [skewPart, contract_smul_left, hsub, contract_transpose_left, hB, hneg]
  ring

theorem contract_self_pos (A : Tensor n) (hA : A ≠ 0) : 0 < contract A A := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    apply hA
    ext i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  unfold contract
  refine Finset.sum_pos' (fun k _ => Finset.sum_nonneg fun l _ => mul_self_nonneg (A k l)) ?_
  refine ⟨i, Finset.mem_univ i, Finset.sum_pos' (fun l _ => mul_self_nonneg (A i l)) ?_⟩
  exact ⟨j, Finset.mem_univ j, mul_self_pos.mpr hij⟩

theorem contract_one_left (A : Tensor n) : contract 1 A = A.trace := by
  classical
  simp [contract, Matrix.one_apply, Matrix.trace, ite_mul]

theorem trace_deviator (A : Tensor n) (hn : n ≠ 0) : (deviator A).trace = 0 := by
  have hd : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [deviator, spherical, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    smul_eq_mul, div_mul_cancel₀ _ hd]

theorem deviator_add_spherical (A : Tensor n) : deviator A + spherical A = A :=
  sub_add_cancel A (spherical A)

theorem contract_spherical_deviator (A : Tensor n) (hn : n ≠ 0) :
    contract (spherical A) (deviator A) = 0 := by
  rw [spherical, contract_smul_left, contract_one_left, trace_deviator A hn, mul_zero]

theorem contract_self_split (A : Tensor n) (hn : n ≠ 0) :
    contract A A = contract (deviator A) (deviator A) + A.trace ^ 2 / (n : ℝ) := by
  have hd : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hs := contract_spherical_deviator A hn
  have ht : contract (deviator A) (spherical A) = 0 := by
    rw [contract_comm]
    exact hs
  have hss : contract (spherical A) (spherical A) = A.trace ^ 2 / (n : ℝ) := by
    simp only [spherical, contract_smul_left, contract_smul_right, contract_one_left,
      Matrix.trace_one, Fintype.card_fin]
    field_simp [hd]
  calc
    contract A A =
        contract (deviator A + spherical A) (deviator A + spherical A) := by
          rw [deviator_add_spherical]
    _ = _ := by simp [contract_add_left, contract_add_right, hs, ht, hss]

theorem trace_conjugate (Q A : Tensor n) (hQ : Q.transpose * Q = 1) :
    (conjugate Q A).trace = A.trace := by
  rw [conjugate, Matrix.trace_mul_cycle, hQ, one_mul]

theorem conjugate_transpose (Q A : Tensor n) :
    (conjugate Q A).transpose = conjugate Q A.transpose := by
  simp [conjugate, Matrix.transpose_mul, Matrix.mul_assoc]

theorem conjugate_undo (Q A : Tensor n) (hQ : Q.transpose * Q = 1) :
    conjugate Q.transpose (conjugate Q A) = A := by
  simp only [conjugate, Matrix.transpose_transpose]
  calc
    Q.transpose * (Q * A * Q.transpose) * Q =
        (Q.transpose * Q) * A * (Q.transpose * Q) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [hQ, one_mul, mul_one]

end LeanSolid.Math
