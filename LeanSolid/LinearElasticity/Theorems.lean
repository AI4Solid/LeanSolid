module

public import LeanSolid.LinearElasticity.Definitions
public import LeanSolid.Math.Theorems
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import LeanSolid.ContinuumMechanics.Theorems

public section

namespace LeanSolid.LinearElasticity

/-- Symmetric stress gives reciprocal normal components on two planes. -/
theorem traction_dot_comm {n : ℕ} (σ : LeanSolid.Math.Tensor n)
    (hσ : σ.transpose = σ) (a b : LeanSolid.Math.Vector n) :
    dotProduct (traction σ a) b = dotProduct (traction σ b) a := by
  unfold traction
  rw [dotProduct_comm (Matrix.mulVec σ a), dotProduct_comm (Matrix.mulVec σ b)]
  simpa only [hσ] using Matrix.dotProduct_transpose_mulVec σ b a

open LeanSolid.Math

variable {n : ℕ}

theorem strain_transpose (G : Tensor n) : (strain G).transpose = strain G :=
  symPart_transpose G

/-- Exact linear-plus-quadratic expansion about the undeformed state. -/
theorem greenStrain_one_add (G : Tensor n) :
    greenStrain (1 + G) = strain G + (1 / 2 : ℝ) • (G.transpose * G) :=
  ContinuumMechanics.greenStrain_one_add G

theorem stress_add (lam mu : ℝ) (A B : Tensor n) :
    stress lam mu (A + B) = stress lam mu A + stress lam mu B := by
  ext i j
  simp [stress, Matrix.trace_add, smul_eq_mul]
  ring

theorem stress_smul (lam mu c : ℝ) (A : Tensor n) :
    stress lam mu (c • A) = c • stress lam mu A := by
  ext i j
  simp [stress, Matrix.trace_smul, smul_eq_mul]
  ring

theorem trace_stress (lam mu : ℝ) (A : Tensor n) :
    (stress lam mu A).trace = ((n : ℝ) * lam + 2 * mu) * A.trace := by
  simp [stress, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  ring

theorem energyDensity_nonneg (lam mu : ℝ) (A : Tensor n) (hlam : 0 ≤ lam)
    (hmu : 0 ≤ mu) : 0 ≤ energyDensity lam mu A := by
  exact add_nonneg (div_nonneg (mul_nonneg hlam (sq_nonneg _)) (by norm_num))
    (mul_nonneg hmu (contract_self_nonneg A))

theorem stress_transpose (lam mu : ℝ) (A : Tensor n) (hA : A.transpose = A) :
    (stress lam mu A).transpose = stress lam mu A := by
  simp [stress, Matrix.transpose_add, Matrix.transpose_smul, hA]

theorem energyDensity_eq_half_stress_contract (lam mu : ℝ) (A : Tensor n) :
    energyDensity lam mu A = contract (stress lam mu A) A / 2 := by
  rw [energyDensity, stress, contract_add_left, contract_smul_left, contract_smul_left,
    contract_one_left]
  ring

/-- Major symmetry of the isotropic stiffness as a bilinear form on strains. -/
theorem stress_contract_comm (lam mu : ℝ) (A B : Tensor n) :
    contract (stress lam mu A) B = contract (stress lam mu B) A := by
  simp only [stress, contract_add_left, contract_smul_left, contract_one_left]
  rw [contract_comm B A]
  ring

/-- Exact energy increment along a strain perturbation. -/
theorem energyDensity_add_smul (lam mu t : ℝ) (A B : Tensor n) :
    energyDensity lam mu (A + t • B) =
      energyDensity lam mu A + t * contract (stress lam mu A) B +
        t ^ 2 * energyDensity lam mu B := by
  simp only [energyDensity_eq_half_stress_contract, stress_add, stress_smul,
    contract_add_left, contract_add_right, contract_smul_left, contract_smul_right]
  rw [stress_contract_comm lam mu B A]
  ring

/-- The directional derivative of elastic energy is stress paired with the strain increment. -/
theorem hasDerivAt_energyDensity (lam mu : ℝ) (A B : Tensor n) :
    HasDerivAt (fun t : ℝ => energyDensity lam mu (A + t • B))
      (contract (stress lam mu A) B) 0 := by
  let c := contract (stress lam mu A) B
  let W := energyDensity lam mu B
  have hlin := (hasDerivAt_id' (0 : ℝ)).mul_const c
  have hsq := ((hasDerivAt_id' (0 : ℝ)).pow 2).mul_const W
  have h := (HasDerivAt.add (hasDerivAt_const (0 : ℝ) (energyDensity lam mu A)) hlin).add hsq
  have hf : (fun t : ℝ => energyDensity lam mu (A + t • B)) =
      (fun _ : ℝ => energyDensity lam mu A) + (fun t => t * c) + (fun t => t ^ 2 * W) := by
    funext t
    simp only [Pi.add_apply, energyDensity_add_smul, c, W]
  rw [hf]
  simpa [c, W] using h

/-- The isotropic material law commutes with orthogonal changes of basis. -/
theorem stress_conjugate (lam mu : ℝ) (Q A : Tensor n)
    (hleft : Q.transpose * Q = 1) (hright : Q * Q.transpose = 1) :
    stress lam mu (conjugate Q A) = conjugate Q (stress lam mu A) := by
  rw [stress, trace_conjugate Q A hleft]
  simp only [conjugate, stress, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_one, hright]

theorem energyDensity_volumetric_deviatoric (lam mu : ℝ) (A : Tensor 3) :
    energyDensity lam mu A =
      (3 * lam + 2 * mu) / 6 * A.trace ^ 2 + mu * contract (deviator A) (deviator A) := by
  rw [energyDensity, contract_self_split A (by decide)]
  norm_num
  ring

theorem energyPosDef3_iff (lam mu : ℝ) :
    EnergyPosDef3 lam mu ↔ 0 < mu ∧ 0 < 3 * lam + 2 * mu := by
  constructor
  · intro h
    let D : Tensor 3 := Matrix.diagonal ![1, -1, 0]
    have hDsym : D.transpose = D := Matrix.diagonal_transpose _
    have hDne : D ≠ 0 := by
      intro he
      have h00 := congrArg (fun A : Tensor 3 => A 0 0) he
      norm_num [D] at h00
    have hDtrace : D.trace = 0 := by
      norm_num [D, Matrix.trace, Fin.sum_univ_succ]
    have hDpos := h D hDsym hDne
    rw [energyDensity, hDtrace] at hDpos
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div, zero_add] at hDpos
    have hI : (1 : Tensor 3) ≠ 0 := by
      intro he
      have h00 := congrArg (fun A : Tensor 3 => A 0 0) he
      norm_num at h00
    have hIpos := h 1 Matrix.transpose_one hI
    rw [energyDensity, contract_one_left, Matrix.trace_one] at hIpos
    norm_num at hIpos
    exact ⟨pos_of_mul_pos_left hDpos (contract_self_nonneg D), by linarith⟩
  · rintro ⟨hmu, hbulk⟩ A _ hA
    rw [energyDensity_volumetric_deviatoric]
    have hc : 0 < (3 * lam + 2 * mu) / 6 := div_pos hbulk (by norm_num)
    by_cases ht : A.trace = 0
    · have hdev : deviator A = A := by simp [deviator, spherical, ht]
      rw [hdev, ht]
      simpa using mul_pos hmu (contract_self_pos A hA)
    · exact add_pos_of_pos_of_nonneg
        (mul_pos hc (sq_pos_of_ne_zero ht)) (mul_nonneg hmu.le (contract_self_nonneg _))

end LeanSolid.LinearElasticity
