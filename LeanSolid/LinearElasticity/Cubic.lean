module

public import LeanSolid.LinearElasticity.Stiffness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace LeanSolid.LinearElasticity.StiffnessTensor

open LeanSolid.Math

/-- The cubic stiffness in engineering Voigt coordinates. -/
def cubicVoigt (c₁₁ c₁₂ c₄₄ : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![c₁₁, c₁₂, c₁₂, 0, 0, 0;
     c₁₂, c₁₁, c₁₂, 0, 0, 0;
     c₁₂, c₁₂, c₁₁, 0, 0, 0;
     0, 0, 0, c₄₄, 0, 0;
     0, 0, 0, 0, c₄₄, 0;
     0, 0, 0, 0, 0, c₄₄]

/-- Induced signs on engineering Voigt coordinates under reflection of axes one and two. -/
def reflectX : Vector 6 := ![1, 1, 1, 1, -1, -1]
def reflectY : Vector 6 := ![1, 1, 1, -1, 1, -1]

/-- Index permutation induced by cyclically permuting the three Cartesian axes. -/
def cycleAxes : Fin 6 → Fin 6 := ![1, 2, 0, 4, 5, 3]

/-- Material symmetry under reflection in the coordinate planes. The third reflection
has the same action on second-order tensors as the composition of the first two. -/
def HasOrthotropicSymmetry (A : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  (∀ i j, reflectX i * reflectX j * A i j = A i j) ∧
  (∀ i j, reflectY i * reflectY j * A i j = A i j)

/-- Reflection and cyclic-axis conditions in the engineering Voigt basis. -/
def HasCubicSymmetry (A : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  HasOrthotropicSymmetry A ∧
  (∀ i j, A (cycleAxes i) (cycleAxes j) = A i j)

theorem orthotropic_shear_offDiagonal (A : Matrix (Fin 6) (Fin 6) ℝ)
    (h : HasOrthotropicSymmetry A) (i j : Fin 6) (hij : i ≠ j)
    (hsh : 3 ≤ i.val ∨ 3 ≤ j.val) : A i j = 0 := by
  have hx := h.1 i j
  have hy := h.2 i j
  have hzero (x : ℝ) (hx' : -x = x) : x = 0 := by linarith
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num at hsh <;>
    norm_num [reflectX, reflectY] at hx hy <;>
    first | exact hzero _ hx | exact hzero _ hy

def orthotropicVoigt (c₁₁ c₂₂ c₃₃ c₁₂ c₁₃ c₂₃ c₄₄ c₅₅ c₆₆ : ℝ) :
    Matrix (Fin 6) (Fin 6) ℝ :=
  !![c₁₁, c₁₂, c₁₃, 0, 0, 0;
     c₁₂, c₂₂, c₂₃, 0, 0, 0;
     c₁₃, c₂₃, c₃₃, 0, 0, 0;
     0, 0, 0, c₄₄, 0, 0;
     0, 0, 0, 0, c₅₅, 0;
     0, 0, 0, 0, 0, c₆₆]

/-- Major symmetry and the reflections reduce the law to a nine-constant matrix. -/
theorem eq_orthotropicVoigt_of_symmetry (A : Matrix (Fin 6) (Fin 6) ℝ)
    (hA : A.transpose = A) (h : HasOrthotropicSymmetry A) :
    A = orthotropicVoigt (A 0 0) (A 1 1) (A 2 2) (A 0 1) (A 0 2) (A 1 2)
      (A 3 3) (A 4 4) (A 5 5) := by
  have ht (i j : Fin 6) : A j i = A i j :=
    congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M i j) hA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [orthotropicVoigt] <;>
    first
    | exact orthotropic_shear_offDiagonal A h _ _ (by decide) (by decide)
    | simp only [ht 0 1, ht 0 2, ht 1 2]

/-- The signed axis actions and major symmetry force the three-constant cubic form. -/
theorem eq_cubicVoigt_of_symmetry (A : Matrix (Fin 6) (Fin 6) ℝ)
    (hA : A.transpose = A) (h : HasCubicSymmetry A) :
    A = cubicVoigt (A 0 0) (A 0 1) (A 3 3) := by
  obtain ⟨hr, hc⟩ := h
  have ht (i j : Fin 6) : A j i = A i j :=
    congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M i j) hA
  have h₀₀ : A 1 1 = A 0 0 := hc 0 0
  have h₁₁ : A 2 2 = A 1 1 := hc 1 1
  have h₃₃ : A 4 4 = A 3 3 := hc 3 3
  have h₄₄ : A 5 5 = A 4 4 := hc 4 4
  have h₀₁ : A 1 2 = A 0 1 := hc 0 1
  have h₁₂ : A 2 0 = A 1 2 := hc 1 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubicVoigt] <;>
    first
    | exact orthotropic_shear_offDiagonal A hr _ _ (by decide) (by decide)
    | simp only [ht 0 1, ← ht 0 2, ht 1 2, h₀₀, h₁₁, h₃₃, h₄₄, h₀₁, h₁₂]

theorem cubicVoigt_hasCubicSymmetry (a b c : ℝ) : HasCubicSymmetry (cubicVoigt a b c) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [cubicVoigt, reflectX, reflectY, cycleAxes]

theorem cubicVoigt_transpose (a b c : ℝ) :
    (cubicVoigt a b c).transpose = cubicVoigt a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The Lamé tensor occupies the two-parameter subfamily of cubic stiffness matrices. -/
theorem voigtMatrix_isotropic (lam mu : ℝ) :
    voigtMatrix (isotropicComponents 3 lam mu) = cubicVoigt (lam + 2 * mu) lam mu := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [voigtMatrix, isotropicComponents, voigtPair, cubicVoigt, Matrix.one_apply] <;> ring

theorem cubicVoigt_quadratic (a b c : ℝ) (v : Vector 6) :
    dotProduct (Matrix.mulVec (cubicVoigt a b c) v) v =
      (a + 2 * b) / 3 * (v 0 + v 1 + v 2) ^ 2 +
      (a - b) / 3 * ((v 0 - v 1) ^ 2 + (v 1 - v 2) ^ 2 + (v 2 - v 0) ^ 2) +
      c * (v 3 ^ 2 + v 4 ^ 2 + v 5 ^ 2) := by
  simp [cubicVoigt, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

/-- Three sharp and independent positivity conditions for a cubic elastic solid. -/
theorem cubicVoigt_quadratic_pos_iff (a b c : ℝ) :
    (∀ v : Vector 6, v ≠ 0 → 0 < dotProduct (Matrix.mulVec (cubicVoigt a b c) v) v) ↔
      0 < a + 2 * b ∧ 0 < a - b ∧ 0 < c := by
  constructor
  · intro h
    have hbulk := h ![1, 1, 1, 0, 0, 0] (by
      intro hz
      have hh := congrFun hz (0 : Fin 6)
      norm_num at hh)
    have hdev := h ![1, -1, 0, 0, 0, 0] (by
      intro hz
      have hh := congrFun hz (0 : Fin 6)
      norm_num at hh)
    have hshear := h ![0, 0, 0, 1, 0, 0] (by
      intro hz
      have hh := congrFun hz (3 : Fin 6)
      norm_num at hh)
    rw [cubicVoigt_quadratic] at hbulk hdev hshear
    norm_num at hbulk hdev hshear
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hb, hd, hs⟩ v hv
    rw [cubicVoigt_quadratic]
    let B := (v 0 + v 1 + v 2) ^ 2
    let D := (v 0 - v 1) ^ 2 + (v 1 - v 2) ^ 2 + (v 2 - v 0) ^ 2
    let S := v 3 ^ 2 + v 4 ^ 2 + v 5 ^ 2
    change 0 < (a + 2 * b) / 3 * B + (a - b) / 3 * D + c * S
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hBp : 0 < (a + 2 * b) / 3 := by positivity
    have hDp : 0 < (a - b) / 3 := by positivity
    by_contra! hn
    have hb0 : B = 0 := by
      by_contra hne
      linarith only [hn, mul_pos hBp (lt_of_le_of_ne hB (Ne.symm hne)),
        mul_nonneg hDp.le hD, mul_nonneg hs.le hS]
    have hd0 : D = 0 := by
      by_contra hne
      linarith only [hn, mul_nonneg hBp.le hB, mul_pos hDp (lt_of_le_of_ne hD (Ne.symm hne)),
        mul_nonneg hs.le hS]
    have hs0 : S = 0 := by
      by_contra hne
      linarith only [hn, mul_nonneg hBp.le hB, mul_nonneg hDp.le hD,
        mul_pos hs (lt_of_le_of_ne hS (Ne.symm hne))]
    dsimp [B] at hb0
    dsimp [D] at hd0
    dsimp [S] at hs0
    have hsum : v 0 + v 1 + v 2 = 0 := sq_eq_zero_iff.mp hb0
    have h01 : v 0 - v 1 = 0 := by
      apply sq_eq_zero_iff.mp
      nlinarith only [hd0, sq_nonneg (v 1 - v 2), sq_nonneg (v 2 - v 0),
        sq_nonneg (v 0 - v 1)]
    have h12 : v 1 - v 2 = 0 := by
      apply sq_eq_zero_iff.mp
      nlinarith only [hd0, sq_nonneg (v 0 - v 1), sq_nonneg (v 2 - v 0),
        sq_nonneg (v 1 - v 2)]
    have h3 : v 3 = 0 := sq_eq_zero_iff.mp (by
      nlinarith only [hs0, sq_nonneg (v 3), sq_nonneg (v 4), sq_nonneg (v 5)])
    have h4 : v 4 = 0 := sq_eq_zero_iff.mp (by
      nlinarith only [hs0, sq_nonneg (v 3), sq_nonneg (v 4), sq_nonneg (v 5)])
    have h5 : v 5 = 0 := sq_eq_zero_iff.mp (by
      nlinarith only [hs0, sq_nonneg (v 3), sq_nonneg (v 4), sq_nonneg (v 5)])
    apply hv
    funext i
    change v i = 0
    fin_cases i
    · change v 0 = 0
      linarith only [hsum, h01, h12]
    · change v 1 = 0
      linarith only [hsum, h01, h12]
    · change v 2 = 0
      linarith only [hsum, h01, h12]
    · exact h3
    · exact h4
    · exact h5

theorem energyPosDef_iff_cubic (C : Components 3)
    (hL : LeftMinor C) (hM : Major C) (h : HasCubicSymmetry (voigtMatrix C)) :
    EnergyPosDef C ↔
      let A := voigtMatrix C
      0 < A 0 0 + 2 * A 0 1 ∧ 0 < A 0 0 - A 0 1 ∧ 0 < A 3 3 := by
  rw [energyPosDef_iff_voigt C hL (rightMinor_of_leftMinor_major C hL hM)]
  conv_lhs => rw [eq_cubicVoigt_of_symmetry _ (voigtMatrix_transpose C hM) h]
  exact cubicVoigt_quadratic_pos_iff _ _ _

end LeanSolid.LinearElasticity.StiffnessTensor
