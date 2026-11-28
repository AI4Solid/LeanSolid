module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Theorems
public import LeanSolid.ContinuumMechanics.Area
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

open LeanSolid.Math

/-- Pressure is the multiplier for the local constraint J = 1. -/
def constrainedEnergy (W : Tensor 3 → ℝ) (p : ℝ) (F : Tensor 3) : ℝ :=
  W F - p * (jacobian F - 1)

theorem hasEnergyGradient_constrainedEnergy {W : Tensor 3 → ℝ} {F P : Tensor 3}
    (hW : HasEnergyGradient W F P) (p : ℝ) :
    HasEnergyGradient (constrainedEnergy W p) F (P - p • F.adjugate.transpose) := by
  intro c H hc hH
  have hDet := hasDerivAt_invariant₃ hH
  rw [hc] at hDet
  have h := (hW c H hc hH).sub ((hDet.sub_const 1).const_mul p)
  have he : contract (P - p • F.adjugate.transpose) H =
      contract P H - p * contract F.adjugate.transpose H := by
    rw [sub_eq_add_neg, ← neg_smul, contract_add_left, contract_smul_left]
    ring
  rw [he]
  exact h

theorem cauchyFromPiola_pressure (F P : Tensor 3) (p : ℝ) (hJ : jacobian F ≠ 0) :
    cauchyFromPiola F (P - p • F.adjugate.transpose) =
      cauchyFromPiola F P - p • (1 : Tensor 3) := by
  have h : F.adjugate.transpose * F.transpose = jacobian F • (1 : Tensor 3) := by
    rw [← Matrix.transpose_mul, Matrix.mul_adjugate, Matrix.transpose_smul, Matrix.transpose_one]
    rfl
  rw [cauchyFromPiola, cauchyFromPiola, Matrix.sub_mul, Matrix.smul_mul, h, smul_sub,
    smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm p, ← mul_assoc, inv_mul_cancel₀ hJ, one_mul]

/-- Isochoric neo-Hookean energy before adding the pressure constraint. -/
def incompressibleNeoHookean (mu : ℝ) (C : Tensor 3) : ℝ :=
  mu / 2 * (invariant₁ C - 3)

theorem hasEnergyGradient_incompressibleNeoHookean (mu : ℝ) (F : Tensor 3) :
    HasEnergyGradient (fun A => incompressibleNeoHookean mu (rightCauchyGreen A)) F (mu • F) := by
  have hC : HasEnergyGradient (incompressibleNeoHookean mu) (rightCauchyGreen F)
      ((mu / 2) • (1 : Tensor 3)) := by
    intro c H hc hH
    rw [contract_smul_left]
    exact (((hasEnergyGradient_invariant₁ _ c H hc hH).sub_const 3).const_mul _)
  have hs : (((mu / 2) • (1 : Tensor 3))).transpose = (mu / 2) • (1 : Tensor 3) := by simp
  have hF := hasEnergyGradient_rightCauchyGreen hC hs
  have he : F * ((2 : ℝ) • ((mu / 2) • (1 : Tensor 3))) = mu • F := by
    rw [smul_smul, show (2 : ℝ) * (mu / 2) = mu by ring, Matrix.mul_smul, mul_one]
  rw [he] at hF
  exact hF

theorem incompressibleNeoHookean_firstPiola (mu p : ℝ) (F : Tensor 3) :
    firstPiolaStress (constrainedEnergy (fun A => incompressibleNeoHookean mu
      (rightCauchyGreen A)) p) F =
      mu • F - p • F.adjugate.transpose :=
  (hasEnergyGradient_constrainedEnergy (hasEnergyGradient_incompressibleNeoHookean mu F) p).eq_energyGradient

/-- Neo-Hookean Cauchy stress at an isochoric state, including its multiplier. -/
def incompressibleNeoHookeanCauchy (mu p : ℝ) (F : Tensor 3) : Tensor 3 :=
  mu • leftCauchyGreen F - p • (1 : Tensor 3)

theorem incompressibleNeoHookean_cauchy (mu p : ℝ) (F : Tensor 3) (hJ : jacobian F = 1) :
    cauchyFromPiola F (firstPiolaStress
      (constrainedEnergy (fun A => incompressibleNeoHookean mu (rightCauchyGreen A)) p) F) =
      incompressibleNeoHookeanCauchy mu p F := by
  rw [incompressibleNeoHookean_firstPiola, cauchyFromPiola_pressure _ _ _ (by rw [hJ]; exact one_ne_zero)]
  simp only [cauchyFromPiola, hJ, inv_one, one_smul, Matrix.smul_mul,
    incompressibleNeoHookeanCauchy, leftCauchyGreen]

/-- Isochoric uniaxial stretching. Equal transverse stretches and zero lateral
traction determine the multiplier and the axial Cauchy stress. -/
theorem neoHookean_uniaxial (mu stretch r p : ℝ) (hstretch : stretch ≠ 0) (hJ : stretch * r ^ 2 = 1) :
    let F : Tensor 3 := Matrix.diagonal ![stretch, r, r]
    let σ := incompressibleNeoHookeanCauchy mu p F
    jacobian F = 1 ∧ (σ 1 1 = 0 ↔ p = mu / stretch) ∧
      (σ 1 1 = 0 → σ 0 0 = mu * (stretch ^ 2 - stretch⁻¹) ∧ σ 2 2 = 0) := by
  have hr : r ^ 2 = stretch⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hstretch).mpr
    rwa [mul_comm]
  have hdet : jacobian (Matrix.diagonal (![stretch, r, r] : Vector 3)) = 1 := by
    simpa [jacobian, Matrix.det_diagonal, Fin.prod_univ_succ, pow_two, mul_assoc] using hJ
  have hlat : incompressibleNeoHookeanCauchy mu p (Matrix.diagonal ![stretch, r, r]) 1 1 =
      mu * r ^ 2 - p := by
    simp [incompressibleNeoHookeanCauchy, leftCauchyGreen, Matrix.diagonal_mul_diagonal, pow_two]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hlat, hr, div_eq_mul_inv]
    exact sub_eq_zero.trans eq_comm
  · intro hz
    have hp : p = mu * stretch⁻¹ := by rw [hlat, hr] at hz; exact (sub_eq_zero.mp hz).symm
    simp [incompressibleNeoHookeanCauchy, leftCauchyGreen, Matrix.diagonal_mul_diagonal,
      hp, ← hr, pow_two]
    ring

/-- Simple shear with vanishing transverse normal stress. The longitudinal
normal stress is quadratic in the shear amplitude. -/
theorem neoHookean_simpleShear (mu γ : ℝ) :
    let F : Tensor 3 := !![1, γ, 0; 0, 1, 0; 0, 0, 1]
    jacobian F = 1 ∧
      incompressibleNeoHookeanCauchy mu mu F =
        !![mu * γ ^ 2, mu * γ, 0; mu * γ, 0, 0; 0, 0, 0] := by
  dsimp only
  constructor
  · simp [jacobian, Matrix.det_fin_three]
  · unfold incompressibleNeoHookeanCauchy leftCauchyGreen
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    fin_cases i <;> fin_cases j <;> simp
    ring

/-- Incompressible Mooney–Rivlin energy in the first two invariants of C. -/
def mooneyRivlinEnergy (c₁ c₂ : ℝ) (C : Tensor 3) : ℝ :=
  c₁ * (invariant₁ C - 3) + c₂ * (invariant₂ C - 3)

/-- Unconstrained part of the Mooney–Rivlin second Piola stress. -/
def mooneyRivlinSecondPiola (c₁ c₂ : ℝ) (C : Tensor 3) : Tensor 3 :=
  (2 : ℝ) • (c₁ • (1 : Tensor 3) + c₂ • (C.trace • (1 : Tensor 3) - C.transpose))

theorem mooneyRivlin_firstPiola (c₁ c₂ p : ℝ) (F : Tensor 3) :
    firstPiolaStress
      (constrainedEnergy (fun A => mooneyRivlinEnergy c₁ c₂ (rightCauchyGreen A)) p) F =
      F * mooneyRivlinSecondPiola c₁ c₂ (rightCauchyGreen F) - p • F.adjugate.transpose := by
  let C := rightCauchyGreen F
  let G := c₁ • (1 : Tensor 3) + c₂ • (C.trace • (1 : Tensor 3) - C.transpose)
  have hG : HasEnergyGradient (mooneyRivlinEnergy c₁ c₂) C G := by
    intro c H hc hH
    have h₁ := ((hasEnergyGradient_invariant₁ C c H hc hH).sub_const 3).const_mul c₁
    have h₂ := ((hasEnergyGradient_invariant₂ C c H hc hH).sub_const 3).const_mul c₂
    rw [show contract G H = c₁ * contract 1 H +
        c₂ * contract (C.trace • (1 : Tensor 3) - C.transpose) H by
      dsimp only [G]
      rw [contract_add_left, contract_smul_left, contract_smul_left]]
    exact h₁.add h₂
  have hC : C.transpose = C := rightCauchyGreen_transpose F
  have hs : G.transpose = G := by
    simp only [G, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_sub, hC]
  exact (hasEnergyGradient_constrainedEnergy (hasEnergyGradient_rightCauchyGreen hG hs) p).eq_energyGradient

/-- Spatial Mooney–Rivlin stress at J=1, written directly in the left Cauchy–Green tensor. -/
theorem mooneyRivlin_cauchy (c₁ c₂ p : ℝ) (F : Tensor 3) (hJ : jacobian F = 1) :
    let B := leftCauchyGreen F
    cauchyFromPiola F (firstPiolaStress
      (constrainedEnergy (fun A => mooneyRivlinEnergy c₁ c₂ (rightCauchyGreen A)) p) F) =
      (2 : ℝ) • (c₁ • B + c₂ • (B.trace • B - B * B)) - p • (1 : Tensor 3) := by
  dsimp only
  have hJ' : jacobian F ≠ 0 := by rw [hJ]; exact one_ne_zero
  rw [mooneyRivlin_firstPiola, cauchyFromPiola_pressure _ _ _ hJ']
  have hTrace : (rightCauchyGreen F).trace = (leftCauchyGreen F).trace :=
    Matrix.trace_mul_comm _ _
  simp only [cauchyFromPiola, hJ, inv_one, one_smul, mooneyRivlinSecondPiola,
    rightCauchyGreen_transpose, hTrace, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, mul_one]
  simp only [leftCauchyGreen, rightCauchyGreen, Matrix.mul_assoc]

/-- The Yeoh energy is cubic in the offset of the first invariant. -/
def yeohEnergy (c₁ c₂ c₃ : ℝ) (C : Tensor 3) : ℝ :=
  let x := invariant₁ C - 3
  c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3

theorem yeoh_firstPiola (c₁ c₂ c₃ p : ℝ) (F : Tensor 3) :
    let x := invariant₁ (rightCauchyGreen F) - 3
    firstPiolaStress (constrainedEnergy (fun A => yeohEnergy c₁ c₂ c₃ (rightCauchyGreen A)) p) F =
      F * ((2 : ℝ) • ((c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2) • (1 : Tensor 3))) -
        p • F.adjugate.transpose := by
  let C := rightCauchyGreen F
  let x := invariant₁ C - 3
  let k := c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2
  have h : HasEnergyGradient (yeohEnergy c₁ c₂ c₃) C (k • (1 : Tensor 3)) := by
    intro c H hc hH
    have hd : HasDerivAt (fun t => invariant₁ (c t) - 3) (contract 1 H) 0 :=
      (hasEnergyGradient_invariant₁ C c H hc hH).sub_const 3
    have hp := ((hd.const_mul c₁).add ((hd.pow 2).const_mul c₂)).add
      ((hd.pow 3).const_mul c₃)
    convert hp using 1
    · rfl
    · rw [contract_smul_left]
      norm_num [k, x, hc]
      ring
  have hs : (k • (1 : Tensor 3)).transpose = k • (1 : Tensor 3) := by
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  exact (hasEnergyGradient_constrainedEnergy (hasEnergyGradient_rightCauchyGreen h hs) p).eq_energyGradient

/-- Spatial Yeoh stress under the isochoric constraint. -/
theorem yeoh_cauchy (c₁ c₂ c₃ p : ℝ) (F : Tensor 3) (hJ : jacobian F = 1) :
    let x := invariant₁ (rightCauchyGreen F) - 3
    cauchyFromPiola F (firstPiolaStress
      (constrainedEnergy (fun A => yeohEnergy c₁ c₂ c₃ (rightCauchyGreen A)) p) F) =
      (2 * (c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2)) • leftCauchyGreen F - p • (1 : Tensor 3) := by
  dsimp only
  have hJ' : jacobian F ≠ 0 := by rw [hJ]; exact one_ne_zero
  rw [yeoh_firstPiola, cauchyFromPiola_pressure _ _ _ hJ']
  simp only [cauchyFromPiola, hJ, inv_one, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, smul_smul, one_mul, leftCauchyGreen]

end LeanSolid.ContinuumMechanics.Hyperelasticity
