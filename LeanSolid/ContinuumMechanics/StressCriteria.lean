/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Stress/Criteria.lean
at 7e41dfe (Apache-2.0). -/
module

public import LeanSolid.ContinuumMechanics.Invariants
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace LeanSolid.ContinuumMechanics.StressCriteria

open LeanSolid.Math

/-- The second deviatoric stress invariant. -/
noncomputable def J₂ (σ : Tensor 3) : ℝ := contract (deviator σ) (deviator σ) / 2

/-- The von Mises equivalent stress. -/
noncomputable def vonMises (σ : Tensor 3) : ℝ := Real.sqrt (3 * J₂ σ)

/-- The Tresca equivalent stress in decreasing principal stress coordinates. -/
def tresca (largest smallest : ℝ) : ℝ := largest - smallest

theorem J₂_nonneg (σ : Tensor 3) : 0 ≤ J₂ σ :=
  div_nonneg (contract_self_nonneg _) (by norm_num)

theorem J₂_eq (σ : Tensor 3) :
    J₂ σ = (contract σ σ - σ.trace ^ 2 / 3) / 2 := by
  have h := contract_self_split σ (by decide)
  unfold J₂
  norm_num at h
  linarith

private theorem contract_self_eq_trace_sq (σ : Tensor 3) (h : σ.transpose = σ) :
    contract σ σ = (σ * σ).trace := by
  unfold contract Matrix.trace
  congr 1
  funext i
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [show σ j i = σ i j from congrFun (congrFun h i) j]

theorem J₂_conjugate (Q σ : Tensor 3) (hQ : Q.transpose * Q = 1)
    (hσ : σ.transpose = σ) : J₂ (conjugate Q σ) = J₂ σ := by
  have hs : (conjugate Q σ).transpose = conjugate Q σ := by
    simp [conjugate, Matrix.transpose_mul, hσ, Matrix.mul_assoc]
  have hi := invariant₂_conjugate Q σ hQ
  rw [invariant₂, invariant₂, trace_conjugate Q σ hQ] at hi
  rw [J₂_eq, J₂_eq, contract_self_eq_trace_sq _ hs, contract_self_eq_trace_sq _ hσ,
    trace_conjugate Q σ hQ]
  linarith

theorem vonMises_conjugate (Q σ : Tensor 3) (hQ : Q.transpose * Q = 1)
    (hσ : σ.transpose = σ) : vonMises (conjugate Q σ) = vonMises σ := by
  rw [vonMises, vonMises, J₂_conjugate Q σ hQ hσ]

theorem J₂_principal (a b c : ℝ) :
    J₂ (Matrix.diagonal ![a,b,c]) = ((a-b)^2 + (a-c)^2 + (b-c)^2)/6 := by
  rw [J₂_eq]
  simp [contract, Matrix.trace, Fin.sum_univ_three, Matrix.diagonal_apply]
  ring

theorem vonMises_sq (σ : Tensor 3) : vonMises σ ^ 2 = 3 * J₂ σ :=
  Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (J₂_nonneg σ))

theorem compare_on_principal_stresses (a b c : ℝ) (hab : b ≤ a) (hbc : c ≤ b) :
    Real.sqrt 3 / 2 * tresca a c ≤ vonMises (Matrix.diagonal ![a,b,c]) ∧
    vonMises (Matrix.diagonal ![a,b,c]) ≤ tresca a c := by
  let v := vonMises (Matrix.diagonal ![a,b,c])
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hv₂ : v ^ 2 = ((a-b)^2 + (a-c)^2 + (b-c)^2)/2 := by
    dsimp only [v]
    rw [vonMises_sq, J₂_principal]
    ring
  have ht : 0 ≤ tresca a c := sub_nonneg.mpr (hbc.trans hab)
  change Real.sqrt 3 / 2 * tresca a c ≤ v ∧ v ≤ tresca a c
  constructor
  · have h₀ : 0 ≤ Real.sqrt 3 / 2 * tresca a c :=
      mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) ht
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) hv
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hv₂]
    unfold tresca
    nlinarith [sq_nonneg (a - 2*b + c)]
  · apply le_of_pow_le_pow_left₀ (n := 2) (by decide) ht
    rw [hv₂]
    unfold tresca
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc)]

theorem compare_of_principal_basis (Q σ : Tensor 3) (hQ : Q.transpose * Q = 1)
    (a b c : ℝ) (hab : b ≤ a) (hbc : c ≤ b)
    (hσ : σ = conjugate Q (Matrix.diagonal ![a,b,c])) :
    Real.sqrt 3 / 2 * tresca a c ≤ vonMises σ ∧ vonMises σ ≤ tresca a c := by
  have hd : (Matrix.diagonal ![a,b,c]).transpose = Matrix.diagonal ![a,b,c] := by
    ext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Ne.symm h]
  rw [hσ, vonMises_conjugate Q _ hQ hd]
  exact compare_on_principal_stresses a b c hab hbc

end LeanSolid.ContinuumMechanics.StressCriteria
