module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Definitions
public import LeanSolid.ContinuumMechanics.Rates
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

open scoped Matrix.Norms.Elementwise

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

open LeanSolid.Math

variable {n : ℕ}

theorem contract_eq_trace (A B : Tensor n) : contract A B = (A.transpose * B).trace := by
  exact LeanSolid.Math.contract_eq_trace A B

theorem contract_single_right (G : Tensor n) (i j : Fin n) :
    contract G (Matrix.single i j 1) = G i j := by
  classical
  simp [contract, Matrix.single, mul_ite, ite_and]

/-- A pathwise gradient agrees with the matrix of partial derivatives. -/
theorem HasEnergyGradient.eq_energyGradient {W : Tensor n → ℝ} {A G : Tensor n}
    (h : HasEnergyGradient W A G) : energyGradient W A = G := by
  ext i j
  change deriv (fun t : ℝ => W (A + t • Matrix.single i j 1)) 0 = _
  have hc : HasTensorDerivative (fun t : ℝ => A + t • Matrix.single i j 1)
      (Matrix.single i j 1) := by
    intro k l
    change HasDerivAt (fun t : ℝ => A k l + t * Matrix.single i j 1 k l) _ _
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Matrix.single i j (1 : ℝ) k l)).const_add (A k l)
  rw [(h _ _ (by simp) hc).deriv, contract_single_right]

private theorem apply_contract (L : Tensor n →L[ℝ] ℝ) (H : Tensor n) :
    L H = contract (Matrix.of fun i j => L (Matrix.single i j 1)) H := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single H]
  simp only [map_sum, contract, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : Matrix.single i j (H i j) = H i j • Matrix.single i j (1 : ℝ) := by
    ext k l
    by_cases hk : i = k <;> by_cases hl : j = l <;>
      simp [Matrix.single, hk, hl, smul_eq_mul]
  rw [h, map_smul, smul_eq_mul, mul_comm]

/-- A Fréchet differentiable stored energy has the pathwise Frobenius gradient. -/
theorem hasEnergyGradient_of_differentiable {W : Tensor n → ℝ} {A : Tensor n}
    (hW : DifferentiableAt ℝ W A) : HasEnergyGradient W A (energyGradient W A) := by
  let L := fderiv ℝ W A
  have h : HasEnergyGradient W A (Matrix.of fun i j => L (Matrix.single i j 1)) := by
    intro c H hc hd
    have hd' : HasDerivAt c H 0 := hasDerivAt_pi.mpr fun i =>
      hasDerivAt_pi.mpr fun j => hd i j
    rw [← apply_contract L H]
    exact (hW.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd' hc.symm)
  rw [h.eq_energyGradient]
  exact h

private theorem hasDerivAt_mul_entry {c d : ℝ → Tensor n} {A B H K : Tensor n}
    (hc : c 0 = A) (hd : d 0 = B)
    (hH : HasTensorDerivative c H) (hK : HasTensorDerivative d K) (i j : Fin n) :
    HasDerivAt (fun t => (c t * d t) i j) ((H * B + A * K) i j) 0 := by
  simpa only [hc, hd] using HasTensorDerivAt.mul hH hK i j

/-- Derivative of C = FᵀF along a deformation-gradient path. -/
theorem hasTensorDerivative_rightCauchyGreen {c : ℝ → Tensor n} {F H : Tensor n}
    (hc : c 0 = F) (hH : HasTensorDerivative c H) :
    HasTensorDerivative (fun t => rightCauchyGreen (c t)) (H.transpose * F + F.transpose * H) := by
  simpa only [HasTensorDerivative, hc] using hasTensorDerivAt_rightCauchyGreen hH

/-- Exact derivative of E = (FᵀF − I)/2. -/
theorem hasTensorDerivative_greenStrain {c : ℝ → Tensor n} {F H : Tensor n}
    (hc : c 0 = F) (hH : HasTensorDerivative c H) :
    HasTensorDerivative (fun t => greenStrain (c t))
      ((1 / 2 : ℝ) • (H.transpose * F + F.transpose * H)) := by
  simpa only [HasTensorDerivative, hc] using hasTensorDerivAt_greenStrain hH

private theorem contract_transpose_mul (S F H : Tensor n) :
    contract S (F.transpose * H) = contract (F * S) H := by
  simp only [contract_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Symmetric second Piola stress is work conjugate to Green–Lagrange strain. -/
theorem greenStrain_work (F S H : Tensor n) (hS : S.transpose = S) :
    contract S ((1 / 2 : ℝ) • (H.transpose * F + F.transpose * H)) = contract (F * S) H := by
  have h : contract S (H.transpose * F) = contract S (F.transpose * H) := by
    rw [← show (F.transpose * H).transpose = H.transpose * F by simp [Matrix.transpose_mul],
      ← contract_transpose_left, hS]
  rw [contract_smul_right, contract_add_right, h, contract_transpose_mul]
  ring

/-- If W is written in E, the first Piola stress is F times the symmetric E-gradient. -/
theorem hasEnergyGradient_greenStrain {W : Tensor n → ℝ} {F S : Tensor n}
    (hW : HasEnergyGradient W (greenStrain F) S) (hS : S.transpose = S) :
    HasEnergyGradient (fun A => W (greenStrain A)) F (F * S) := by
  intro c H hc hd
  rw [← greenStrain_work F S H hS]
  exact hW _ _ (congrArg greenStrain hc) (hasTensorDerivative_greenStrain hc hd)

theorem firstPiolaStress_greenStrain {W : Tensor n → ℝ} {F : Tensor n}
    (hW : DifferentiableAt ℝ W (greenStrain F))
    (hS : (secondPiolaStress W (greenStrain F)).transpose = secondPiolaStress W (greenStrain F)) :
    firstPiolaStress (fun A => W (greenStrain A)) F = F * secondPiolaStress W (greenStrain F) :=
  (hasEnergyGradient_greenStrain (hasEnergyGradient_of_differentiable hW) hS).eq_energyGradient

/-- If W is written in C, the second Piola stress is twice its symmetric C-gradient. -/
theorem hasEnergyGradient_rightCauchyGreen {W : Tensor n → ℝ} {F G : Tensor n}
    (hW : HasEnergyGradient W (rightCauchyGreen F) G) (hG : G.transpose = G) :
    HasEnergyGradient (fun A => W (rightCauchyGreen A)) F (F * ((2 : ℝ) • G)) := by
  intro c H hc hd
  have hw := greenStrain_work F G H hG
  rw [contract_smul_right] at hw
  have he : contract (F * ((2 : ℝ) • G)) H =
      contract G (H.transpose * F + F.transpose * H) := by
    rw [Matrix.mul_smul, contract_smul_left]
    linarith only [hw]
  rw [he]
  exact hW _ _ (congrArg rightCauchyGreen hc) (hasTensorDerivative_rightCauchyGreen hc hd)

theorem secondPiola_of_mul (F S : Tensor n) (hJ : jacobian F ≠ 0) :
    secondPiola F (F * S) = S :=
  Matrix.nonsing_inv_mul_cancel_left F S (isUnit_iff_ne_zero.mpr hJ)

theorem firstPiolaStress_rightCauchyGreen {W : Tensor n → ℝ} {F : Tensor n}
    (hW : DifferentiableAt ℝ W (rightCauchyGreen F))
    (hG : (energyGradient W (rightCauchyGreen F)).transpose = energyGradient W (rightCauchyGreen F)) :
    firstPiolaStress (fun A => W (rightCauchyGreen A)) F = F * secondPiolaFromC W (rightCauchyGreen F) :=
  (hasEnergyGradient_rightCauchyGreen (hasEnergyGradient_of_differentiable hW) hG).eq_energyGradient

theorem cauchy_of_secondPiola (F S : Tensor n) :
    cauchyFromPiola F (F * S) = (jacobian F)⁻¹ • (F * S * F.transpose) := rfl

theorem momentBalanced_of_secondPiola (F S : Tensor n) (hS : S.transpose = S) :
    IsMomentBalanced F (F * S) := by
  simp [IsMomentBalanced, Matrix.transpose_mul, Matrix.mul_assoc, hS]


private theorem hasDerivAt_trace {c : ℝ → Tensor n} {H : Tensor n}
    (hH : HasTensorDerivative c H) : HasDerivAt (fun t => (c t).trace) H.trace 0 :=
  HasDerivAt.fun_sum fun i _ => hH i i

theorem hasEnergyGradient_invariant₁ (A : Tensor n) :
    HasEnergyGradient invariant₁ A 1 := by
  intro c H _ hH
  rw [contract_one_left]
  exact hasDerivAt_trace hH

theorem hasEnergyGradient_invariant₂ (A : Tensor n) :
    HasEnergyGradient invariant₂ A (A.trace • (1 : Tensor n) - A.transpose) := by
  intro c H hc hH
  have ht := hasDerivAt_trace hH
  have hm := hasDerivAt_trace (fun i j => hasDerivAt_mul_entry hc hc hH hH i j)
  have h := ((ht.pow 2).sub hm).div_const 2
  change HasDerivAt (fun t => invariant₂ (c t)) _ 0 at h
  convert h using 1
  rw [show A.trace • (1 : Tensor n) - A.transpose =
      A.trace • (1 : Tensor n) + (-1 : ℝ) • A.transpose by simp [sub_eq_add_neg],
    contract_add_left, contract_smul_left, contract_smul_left, contract_one_left,
    contract_eq_trace A.transpose H, Matrix.transpose_transpose, Matrix.trace_add, hc,
    Matrix.trace_mul_comm H A]
  ring

/-- Cofactor derivative of the third invariant in dimension three, including singular tensors. -/
theorem hasEnergyGradient_invariant₃ (A : Tensor 3) :
    HasEnergyGradient invariant₃ A A.adjugate.transpose := by
  intro c H hc hH
  simpa only [hc] using hasDerivAt_invariant₃ hH

theorem hasEnergyGradient_invariantEnergy {W : Vector 3 → ℝ} {A : Tensor 3}
    (hW : DifferentiableAt ℝ W (principalInvariants A)) :
    HasEnergyGradient (invariantEnergy W) A
      (invariantGradient A (fun i => partialDeriv W i (principalInvariants A))) := by
  intro c H hc hH
  let d : Vector 3 := ![contract 1 H, contract (A.trace • (1 : Tensor 3) - A.transpose) H,
    contract A.adjugate.transpose H]
  have hd : HasDerivAt (fun t => principalInvariants (c t)) d 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasEnergyGradient_invariant₁ A c H hc hH
    · exact hasEnergyGradient_invariant₂ A c H hc hH
    · exact hasEnergyGradient_invariant₃ A c H hc hH
  let L := fderiv ℝ W (principalInvariants A)
  have h := hW.hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (congrArg principalInvariants hc.symm)
  have hsum : L d = ∑ i, partialDeriv W i (principalInvariants A) * d i := by
    have hb : d = ∑ i : Fin 3, d i • (Pi.single i (1 : ℝ) : Vector 3) := by
      funext i
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite]
    conv_lhs => rw [hb]
    simp [partialDeriv, L, smul_eq_mul, mul_comm]
  change HasDerivAt (fun t => invariantEnergy W (c t)) (L d) 0 at h
  rw [hsum] at h
  simpa [invariantGradient, contract_add_left, contract_smul_left, Fin.sum_univ_succ, d, add_assoc] using h

theorem secondPiola_invariantEnergy {W : Vector 3 → ℝ} {C : Tensor 3}
    (hW : DifferentiableAt ℝ W (principalInvariants C)) :
    secondPiolaFromC (invariantEnergy W) C =
      invariantSecondPiola C (fun i => partialDeriv W i (principalInvariants C)) := by
  rw [secondPiolaFromC, invariantSecondPiola,
    (hasEnergyGradient_invariantEnergy hW).eq_energyGradient]

/-- Orthogonal conjugation of the strain argument leaves an invariant energy unchanged. -/
theorem invariantEnergy_conjugate (W : Vector 3 → ℝ) (Q A : Tensor 3)
    (hQ : Q.transpose * Q = 1) : invariantEnergy W (conjugate Q A) = invariantEnergy W A :=
  congrArg W (principalInvariants_conjugate Q A hQ)

/-- For a symmetric argument the invariant energy gradient is symmetric. -/
theorem invariantGradient_transpose (A : Tensor 3) (dW : Vector 3) (hA : A.transpose = A) :
    (invariantGradient A dW).transpose = invariantGradient A dW := by
  have ha : A.adjugate.transpose = A.adjugate := by rw [Matrix.adjugate_transpose, hA]
  simp [invariantGradient, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul, hA, ha]

theorem firstPiola_invariantEnergy {W : Vector 3 → ℝ} {F : Tensor 3}
    (hW : DifferentiableAt ℝ W (principalInvariants (rightCauchyGreen F))) :
    firstPiolaStress (fun A => invariantEnergy W (rightCauchyGreen A)) F =
      F * invariantSecondPiola (rightCauchyGreen F)
        (fun i => partialDeriv W i (principalInvariants (rightCauchyGreen F))) :=
  (hasEnergyGradient_rightCauchyGreen (hasEnergyGradient_invariantEnergy hW)
    (invariantGradient_transpose _ _ (rightCauchyGreen_transpose F))).eq_energyGradient

end LeanSolid.ContinuumMechanics.Hyperelasticity
