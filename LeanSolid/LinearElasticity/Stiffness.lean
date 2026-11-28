module

public import LeanSolid.LinearElasticity.Voigt.Theorems
public import LeanSolid.LinearElasticity.Theorems
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

namespace LeanSolid.LinearElasticity.StiffnessTensor

open LeanSolid.Math

/-- Cartesian components Cᵢⱼₖₗ of linear elastic stiffness. -/
abbrev Components (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

variable {n : ℕ}

/-- Symmetry of the output index pair, which gives symmetric stress. -/
def LeftMinor (C : Components n) : Prop := ∀ i j k l, C j i k l = C i j k l

/-- Symmetry of the input index pair, which makes the law depend on symmetric strain. -/
def RightMinor (C : Components n) : Prop := ∀ i j k l, C i j l k = C i j k l

/-- Reciprocity under exchange of the stress and strain index pairs. -/
def Major (C : Components n) : Prop := ∀ i j k l, C k l i j = C i j k l

def apply (C : Components n) (A : Tensor n) : Tensor n :=
  Matrix.of fun i j => ∑ k, ∑ l, C i j k l * A k l

def energy (C : Components n) (A : Tensor n) : ℝ := contract A (apply C A) / 2

/-- Strictly positive elastic energy on nonzero symmetric strains. -/
def EnergyPosDef (C : Components n) : Prop :=
  ∀ A : Tensor n, A.transpose = A → A ≠ 0 → 0 < energy C A

theorem apply_transpose (C : Components n) (hC : LeftMinor C) (A : Tensor n) :
    (apply C A).transpose = apply C A := by
  ext i j
  simp only [Matrix.transpose_apply, apply, Matrix.of_apply, hC i j]

theorem apply_of_transpose (C : Components n) (hC : RightMinor C) (A : Tensor n) :
    apply C A.transpose = apply C A := by
  ext i j
  simp only [apply, Matrix.of_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hC i j k l]

theorem apply_add (C : Components n) (A B : Tensor n) :
    apply C (A + B) = apply C A + apply C B := by
  ext i j
  simp only [apply, Matrix.of_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem apply_smul (C : Components n) (a : ℝ) (A : Tensor n) :
    apply C (a • A) = a • apply C A := by
  ext i j
  simp only [apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem apply_symPart (C : Components n) (hC : RightMinor C) (A : Tensor n) :
    apply C (symPart A) = apply C A := by
  rw [symPart, apply_smul, apply_add, apply_of_transpose C hC]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem rightMinor_of_leftMinor_major (C : Components n) (hL : LeftMinor C) (hM : Major C) :
    RightMinor C := by
  intro i j k l
  calc
    C i j l k = C l k i j := hM l k i j
    _ = C k l i j := hL k l i j
    _ = C i j k l := hM i j k l

theorem contract_apply_comm (C : Components n) (hC : Major C) (A B : Tensor n) :
    contract A (apply C B) = contract B (apply C A) := by
  have h : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
      A p.1 p.2 * (C p.1 p.2 q.1 q.2 * B q.1 q.2)) =
      ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n,
        B q.1 q.2 * (C q.1 q.2 p.1 p.2 * A p.1 p.2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro p _
    rw [hC p.1 p.2 q.1 q.2]
    ring
  simpa only [Fintype.sum_prod_type, contract, apply, Matrix.of_apply, Finset.mul_sum] using h

theorem energy_symPart (C : Components n) (hL : LeftMinor C) (hR : RightMinor C) (A : Tensor n) :
    energy C (symPart A) = energy C A := by
  rw [energy, apply_symPart C hR, contract_symPart_of_symmetric _ _ (apply_transpose C hL A)]
  rfl

/-- The independent unordered pairs in the library's engineering Voigt order. -/
def voigtPair : Fin 6 → Fin 3 × Fin 3 :=
  ![(0, 0), (1, 1), (2, 2), (1, 2), (0, 2), (0, 1)]

def voigtMatrix (C : Components 3) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun a b => C (voigtPair a).1 (voigtPair a).2 (voigtPair b).1 (voigtPair b).2

theorem voigtMatrix_transpose (C : Components 3) (hC : Major C) :
    (voigtMatrix C).transpose = voigtMatrix C := by
  ext i j
  exact hC _ _ _ _

private theorem pair_covered (i j : Fin 3) :
    ∃ a, voigtPair a = (i, j) ∨ voigtPair a = (j, i) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The six unordered pairs determine the full tensor under both minor symmetries. -/
theorem eq_of_voigtMatrix_eq {C D : Components 3}
    (hCL : LeftMinor C) (hCR : RightMinor C) (hDL : LeftMinor D) (hDR : RightMinor D)
    (h : voigtMatrix C = voigtMatrix D) : C = D := by
  funext i j k l
  obtain ⟨a, ha | ha⟩ := pair_covered i j <;>
    obtain ⟨b, hb | hb⟩ := pair_covered k l <;>
    have hh := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M a b) h <;>
    simpa only [voigtMatrix, Matrix.of_apply, ha, hb,
      hCL i j, hCR i j k l, hDL i j, hDR i j k l] using hh

/-- Inverse of the engineering strain vector on symmetric matrices. -/
def fromEngineeringStrain (v : Vector 6) : Tensor 3 :=
  !![v 0, v 5 / 2, v 4 / 2; v 5 / 2, v 1, v 3 / 2; v 4 / 2, v 3 / 2, v 2]

theorem fromEngineeringStrain_transpose (v : Vector 6) :
    (fromEngineeringStrain v).transpose = fromEngineeringStrain v := by
  ext i j
  simp only [Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem strainVector_fromEngineeringStrain (v : Vector 6) :
    Voigt.strainVector (fromEngineeringStrain v) = v := by
  funext i
  fin_cases i <;> simp [Voigt.strainVector, fromEngineeringStrain] <;> ring

theorem fromEngineeringStrain_strainVector (A : Tensor 3) (hA : A.transpose = A) :
    fromEngineeringStrain (Voigt.strainVector A) = A := by
  have hs (i j : Fin 3) : A j i = A i j :=
    congrArg (fun B : Tensor 3 => B i j) hA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Voigt.strainVector, fromEngineeringStrain,
    hs 0 1, hs 0 2, hs 1 2]

/-- The Voigt matrix gives the stress vector from the engineering strain vector. -/
theorem voigt_apply (C : Components 3) (hC : RightMinor C) (A : Tensor 3)
    (hA : A.transpose = A) :
    Voigt.stressVector (apply C A) = Matrix.mulVec (voigtMatrix C) (Voigt.strainVector A) := by
  have hs (i j : Fin 3) : A j i = A i j :=
    congrArg (fun B : Tensor 3 => B i j) hA
  have hrow (i j : Fin 3) :
      apply C A i j = ∑ a, C i j (voigtPair a).1 (voigtPair a).2 * Voigt.strainVector A a := by
    simp [apply, Voigt.strainVector, voigtPair, Fin.sum_univ_succ,
      hs 0 1, hs 0 2, hs 1 2, hC i j 0 1, hC i j 0 2, hC i j 1 2]
    ring
  funext i
  fin_cases i <;> exact hrow _ _

theorem energy_eq_voigt (C : Components 3) (hL : LeftMinor C) (hR : RightMinor C)
    (A : Tensor 3) (hA : A.transpose = A) :
    energy C A = dotProduct (Matrix.mulVec (voigtMatrix C) (Voigt.strainVector A))
      (Voigt.strainVector A) / 2 := by
  rw [energy, contract_comm A, ← Voigt.preserves_contract _ _ (apply_transpose C hL A) hA,
    voigt_apply C hR A hA]
  rfl

/-- Positive energy is equivalent to strict positive definiteness of the Voigt quadratic form. -/
theorem energyPosDef_iff_voigt (C : Components 3) (hL : LeftMinor C) (hR : RightMinor C) :
    EnergyPosDef C ↔ ∀ v : Vector 6, v ≠ 0 →
      0 < dotProduct (Matrix.mulVec (voigtMatrix C) v) v := by
  constructor
  · intro h v hv
    have hn : fromEngineeringStrain v ≠ 0 := by
      intro hz
      apply hv
      rw [← strainVector_fromEngineeringStrain v, hz]
      simp [Voigt.strainVector]
    have hp := h _ (fromEngineeringStrain_transpose v) hn
    rw [energy_eq_voigt C hL hR _ (fromEngineeringStrain_transpose v),
      strainVector_fromEngineeringStrain] at hp
    linarith
  · intro h A hA hn
    have hv : Voigt.strainVector A ≠ 0 := by
      intro hz
      apply hn
      rw [← fromEngineeringStrain_strainVector A hA, hz]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [fromEngineeringStrain]
    rw [energy_eq_voigt C hL hR A hA]
    exact div_pos (h _ hv) (by norm_num)



/-- With major symmetry, elastic energy positivity is Mathlib positive definiteness of the Voigt matrix. -/
theorem energyPosDef_iff_matrixPosDef (C : Components 3) (hL : LeftMinor C) (hM : Major C) :
    EnergyPosDef C ↔ (voigtMatrix C).PosDef := by
  rw [energyPosDef_iff_voigt C hL (rightMinor_of_leftMinor_major C hL hM),
    Matrix.posDef_iff_dotProduct_mulVec]
  have hH : (voigtMatrix C).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact voigtMatrix_transpose C hM
  constructor
  · intro h
    refine ⟨hH, ?_⟩
    intro v hv
    simpa only [star_trivial, dotProduct_comm v] using h v hv
  · rintro ⟨_, h⟩ v hv
    simpa only [star_trivial, dotProduct_comm v] using h hv

/-- Major symmetry makes the stress the first variation of the quadratic stored energy. -/
theorem hasDerivAt_energy (C : Components n) (hC : Major C) (A H : Tensor n) :
    HasDerivAt (fun t : ℝ => energy C (A + t • H)) (contract (apply C A) H) 0 := by
  let s := contract (apply C A) H
  let w := energy C H
  have hexpand (t : ℝ) : energy C (A + t • H) = energy C A + t * s + t ^ 2 * w := by
    dsimp only [s, w, energy]
    rw [apply_add, apply_smul, contract_add_left, contract_add_right, contract_add_right]
    simp only [contract_smul_left, contract_smul_right]
    rw [contract_apply_comm C hC A H, contract_comm (apply C A) H]
    ring
  have hlin := (hasDerivAt_id' (0 : ℝ)).mul_const s
  have hquad := ((hasDerivAt_id' (0 : ℝ)).pow 2).mul_const w
  have h := (HasDerivAt.add (hasDerivAt_const (0 : ℝ) (energy C A)) hlin).add hquad
  have hf : (fun t : ℝ => energy C (A + t • H)) =
      (fun _ : ℝ => energy C A) + (fun t => t * s) + (fun t => t ^ 2 * w) :=
    funext hexpand
  rw [hf]
  simpa [s] using h

/-- Kronecker-delta representation of the two-parameter Lamé stiffness. -/
def isotropicComponents (n : ℕ) (lam mu : ℝ) : Components n :=
  fun i j k l => lam * (1 : Tensor n) i j * (1 : Tensor n) k l +
    mu * ((1 : Tensor n) i k * (1 : Tensor n) j l +
      (1 : Tensor n) i l * (1 : Tensor n) j k)

theorem isotropicComponents_major (lam mu : ℝ) :
    Major (isotropicComponents n lam mu) := by
  intro i j k l
  have h (a b : Fin n) : (1 : Tensor n) a b = (1 : Tensor n) b a := by
    simp only [Matrix.one_apply, eq_comm]
  simp only [isotropicComponents, h k i, h l j, h k j, h l i]
  ring

theorem isotropicComponents_leftMinor (lam mu : ℝ) :
    LeftMinor (isotropicComponents n lam mu) := by
  intro i j k l
  have h : (1 : Tensor n) j i = (1 : Tensor n) i j := by simp only [Matrix.one_apply, eq_comm]
  simp only [isotropicComponents, h]
  ring

theorem isotropicComponents_apply (lam mu : ℝ) (A : Tensor n) :
    apply (isotropicComponents n lam mu) A = stress lam mu (symPart A) := by
  classical
  have htrace : (symPart A).trace = A.trace := by
    simp [symPart, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
    ring
  rw [stress, htrace]
  ext i j
  simp only [apply, Matrix.of_apply, isotropicComponents, symPart,
    Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  have h (k l : Fin n) :
      (lam * (1 : Tensor n) i j * (1 : Tensor n) k l +
      mu * ((1 : Tensor n) i k * (1 : Tensor n) j l + (1 : Tensor n) i l * (1 : Tensor n) j k)) *
          A k l =
      lam * (1 : Tensor n) i j * ((1 : Tensor n) k l * A k l) +
        mu * ((1 : Tensor n) i k * ((1 : Tensor n) j l * A k l)) +
        mu * ((1 : Tensor n) j k * ((1 : Tensor n) i l * A k l)) := by ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [Matrix.one_apply, ite_mul, Matrix.trace, Matrix.diag_apply]
  ring

theorem isotropicComponents_energyPosDef (lam mu : ℝ) :
    EnergyPosDef (isotropicComponents 3 lam mu) ↔ 0 < mu ∧ 0 < 3 * lam + 2 * mu := by
  have he (A : Tensor 3) (hA : A.transpose = A) :
      energy (isotropicComponents 3 lam mu) A = energyDensity lam mu A := by
    have hsym : symPart A = A := by
      ext i j
      simp only [symPart, hA, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      ring
    rw [energy, isotropicComponents_apply, hsym, contract_comm A,
      energyDensity_eq_half_stress_contract]
  rw [← energyPosDef3_iff]
  constructor <;> intro h A ha hn
  · rw [← he A ha]
    exact h A ha hn
  · rw [he A ha]
    exact h A ha hn

end LeanSolid.LinearElasticity.StiffnessTensor
