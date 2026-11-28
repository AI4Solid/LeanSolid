module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Incompressible
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

open LeanSolid.Math
open scoped Matrix

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

noncomputable section

/-- The volume-free factor of a three-dimensional deformation gradient. -/
def isochoricGradient (F : Tensor 3) : Tensor 3 :=
  (jacobian F ^ (-(1 / 3) : ℝ)) • F

theorem jacobian_isochoricGradient (F : Tensor 3) (hJ : 0 < jacobian F) :
    jacobian (isochoricGradient F) = 1 := by
  let J := jacobian F
  have h : (J ^ (-(1 / 3) : ℝ)) ^ (3 : ℕ) = J⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hJ.le]
    norm_num [Real.rpow_neg_one, J]
  change ((J ^ (-(1 / 3) : ℝ)) • F).det = 1
  rw [Matrix.det_smul, Fintype.card_fin, h]
  exact inv_mul_cancel₀ hJ.ne'

/-- The right and left Cauchy–Green tensors of the isochoric factor
both carry the normalization J^(-2/3). -/
theorem cauchyGreen_isochoricGradient (F : Tensor 3) (hJ : 0 < jacobian F) :
    rightCauchyGreen (isochoricGradient F) =
        (jacobian F ^ (-(2 / 3) : ℝ)) • rightCauchyGreen F ∧
      leftCauchyGreen (isochoricGradient F) =
        (jacobian F ^ (-(2 / 3) : ℝ)) • leftCauchyGreen F := by
  have h : jacobian F ^ (-(1 / 3) : ℝ) * jacobian F ^ (-(1 / 3) : ℝ) =
      jacobian F ^ (-(2 / 3) : ℝ) := by
    rw [← Real.rpow_add hJ]
    congr 1
    ring
  simp only [isochoricGradient, rightCauchyGreen, leftCauchyGreen, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, and_self]

/-- Split energy with a scalar volumetric law and a deformation-dependent
isochoric law. Both terms are measured per unit reference volume. -/
def splitEnergy (V : ℝ → ℝ) (W : Tensor 3 → ℝ) (F : Tensor 3) : ℝ :=
  V (jacobian F) + W (isochoricGradient F)

/-- Rate of the isochoric factor along a differentiable tensor path. -/
theorem hasTensorDerivative_isochoricGradient {c : ℝ → Tensor 3} {F H : Tensor 3}
    (hc : c 0 = F) (hH : HasTensorDerivative c H) (hJ : 0 < jacobian F) :
    let α := jacobian F ^ (-(1 / 3) : ℝ)
    HasTensorDerivative (fun s => isochoricGradient (c s))
      (α • H + ((-α / (3 * jacobian F)) * contract F.adjugate.transpose H) • F) := by
  let J := jacobian F
  let α := J ^ (-(1 / 3) : ℝ)
  have hDet := hasDerivAt_invariant₃ hH
  rw [hc] at hDet
  have hd : HasDerivAt (fun s => jacobian (c s) ^ (-(1 / 3) : ℝ))
      ((-α / (3 * J)) * contract F.adjugate.transpose H) 0 := by
    have hp : HasDerivAt (fun y : ℝ => y ^ (-(1 / 3) : ℝ))
        ((-(1 / 3) : ℝ) * J ^ (-(1 / 3) - 1 : ℝ)) (jacobian (c 0)) := by
      rw [hc]
      exact Real.hasDerivAt_rpow_const (Or.inl hJ.ne')
    have hh := hp.comp 0 hDet
    change HasDerivAt (fun s => jacobian (c s) ^ (-(1 / 3) : ℝ)) _ 0 at hh
    have he : (-(1 / 3) : ℝ) * J ^ (-(1 / 3) - 1 : ℝ) = -α / (3 * J) := by
      rw [Real.rpow_sub_one hJ.ne']
      dsimp only [α]
      field_simp [show J ≠ 0 from hJ.ne']
      dsimp only [J]
      ring
    simpa only [he] using hh
  intro _ i j
  have h := hd.mul (hH i j)
  change HasDerivAt (fun s => jacobian (c s) ^ (-(1 / 3) : ℝ) * c s i j)
    (((-α / (3 * J)) * contract F.adjugate.transpose H) * c 0 i j +
      (jacobian (c 0) ^ (-(1 / 3) : ℝ)) * H i j) 0 at h
  rw [hc, add_comm] at h
  exact h

/-- First Piola stress of a volumetric–isochoric split. The determinant
correction removes the dilatational part of the isochoric variation. -/
theorem hasEnergyGradient_splitEnergy {V : ℝ → ℝ} {W : Tensor 3 → ℝ}
    {F G : Tensor 3} {pressure : ℝ} (hJ : 0 < jacobian F)
    (hV : HasDerivAt V pressure (jacobian F))
    (hW : HasEnergyGradient W (isochoricGradient F) G) :
    let α := jacobian F ^ (-(1 / 3) : ℝ)
    HasEnergyGradient (splitEnergy V W) F
      (α • G + (pressure - contract G (isochoricGradient F) / (3 * jacobian F)) •
        F.adjugate.transpose) := by
  intro α c H hc hH
  have hDet := hasDerivAt_invariant₃ hH
  rw [hc] at hDet
  have hw := hW _ _ (congrArg isochoricGradient hc) (hasTensorDerivative_isochoricGradient hc hH hJ)
  have hV' : HasDerivAt V pressure (jacobian (c 0)) := by rwa [hc]
  have h := (hV'.comp 0 hDet).add hw
  change HasDerivAt (fun s => splitEnergy V W (c s)) _ 0 at h
  convert h using 1
  simp only [contract_add_left, contract_smul_left, contract_add_right, contract_smul_right,
    isochoricGradient]
  change _ = pressure * contract F.adjugate.transpose H +
    (α * contract G H + (-α / (3 * jacobian F) * contract F.adjugate.transpose H) * contract G F)
  ring

/-- The volumetric Cauchy stress is spherical and the isochoric
contribution is the deviator of its Kirchhoff stress divided by J. -/
theorem cauchy_splitEnergy {V : ℝ → ℝ} {W : Tensor 3 → ℝ}
    {F G : Tensor 3} {pressure : ℝ} (hJ : 0 < jacobian F)
    (hV : HasDerivAt V pressure (jacobian F))
    (hW : HasEnergyGradient W (isochoricGradient F) G) :
    cauchyFromPiola F (firstPiolaStress (splitEnergy V W) F) =
      pressure • (1 : Tensor 3) + (jacobian F)⁻¹ • deviator (G * (isochoricGradient F).transpose) := by
  let α := jacobian F ^ (-(1 / 3) : ℝ)
  let T := G * (isochoricGradient F).transpose
  have hP := (hasEnergyGradient_splitEnergy hJ hV hW).eq_energyGradient
  have hCof : F.adjugate.transpose * F.transpose = jacobian F • (1 : Tensor 3) := by
    rw [← Matrix.transpose_mul, Matrix.mul_adjugate, Matrix.transpose_smul, Matrix.transpose_one]
    rfl
  have hT : (α • G) * F.transpose = T := by
    simp only [T, isochoricGradient, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, α]
  have hTrace : T.trace = contract G (isochoricGradient F) := by
    rw [contract_eq_trace]
    calc
      T.trace = T.transpose.trace := (Matrix.trace_transpose T).symm
      _ = (G.transpose * isochoricGradient F).trace := by
        rw [show T.transpose = isochoricGradient F * G.transpose by
          simp only [T, Matrix.transpose_mul, Matrix.transpose_transpose], Matrix.trace_mul_comm]
  change firstPiolaStress (splitEnergy V W) F = _ at hP
  rw [hP, cauchyFromPiola, Matrix.add_mul, Matrix.smul_mul _ F.adjugate.transpose,
    hCof, hT, ← hTrace]
  ext i j
  simp only [deviator, spherical, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  norm_num
  field_simp
  ring

/-- One compressible neo-Hookean model uses a quadratic volume penalty
and the neo-Hookean law on the isochoric factor. -/
def splitNeoHookean (bulk mu : ℝ) (F : Tensor 3) : ℝ :=
  splitEnergy (fun J => (bulk / 2) * (J - 1) ^ 2)
    (fun A => incompressibleNeoHookean mu (rightCauchyGreen A)) F

theorem cauchy_splitNeoHookean (bulk mu : ℝ) (F : Tensor 3) (hJ : 0 < jacobian F) :
    cauchyFromPiola F (firstPiolaStress (splitNeoHookean bulk mu) F) =
      (bulk * (jacobian F - 1)) • (1 : Tensor 3) +
        (jacobian F)⁻¹ • deviator (mu • leftCauchyGreen (isochoricGradient F)) := by
  have hv : HasDerivAt (fun J => (bulk / 2) * (J - 1) ^ 2)
      (bulk * (jacobian F - 1)) (jacobian F) := by
    have h := (((hasDerivAt_id (jacobian F)).sub_const 1).pow 2).const_mul (bulk / 2)
    convert h using 1
    · rfl
    · dsimp only [id]
      norm_num
      ring
  have h := cauchy_splitEnergy hJ hv (hasEnergyGradient_incompressibleNeoHookean mu (isochoricGradient F))
  have he : splitNeoHookean bulk mu = splitEnergy (fun J => (bulk / 2) * (J - 1) ^ 2)
      (fun A => incompressibleNeoHookean mu (rightCauchyGreen A)) := rfl
  rw [he]
  simpa only [Matrix.smul_mul, leftCauchyGreen] using h

/-- An isotropic dilation has identity as its isochoric factor. -/
theorem isochoricGradient_uniformDilation (s : ℝ) (hs : 0 < s) :
    isochoricGradient (s • (1 : Tensor 3)) = 1 := by
  have hj : jacobian (s • (1 : Tensor 3)) = s ^ 3 := by
    simp [jacobian]
  have hp : (s ^ (3 : ℕ)) ^ (-(1 / 3) : ℝ) = s⁻¹ := by
    rw [← Real.rpow_natCast s 3, ← Real.rpow_mul hs.le,
      show (↑(3 : ℕ) : ℝ) * (-(1 / 3)) = -1 by norm_num, Real.rpow_neg_one]
  rw [isochoricGradient, hj, hp, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

/-- The split neo-Hookean law gives a purely hydrostatic stress in uniform
dilation, with no contribution from its shear modulus. -/
theorem cauchy_splitNeoHookean_uniformDilation (bulk mu s : ℝ) (hs : 0 < s) :
    let F : Tensor 3 := s • (1 : Tensor 3)
    cauchyFromPiola F (firstPiolaStress (splitNeoHookean bulk mu) F) =
      (bulk * (s ^ 3 - 1)) • (1 : Tensor 3) := by
  intro F
  have hj : jacobian F = s ^ 3 := by simp [F, jacobian]
  have hp : 0 < jacobian F := by rw [hj]; exact pow_pos hs _
  have hdev : deviator (mu • (1 : Tensor 3)) = 0 := by
    have ht : (mu • (1 : Tensor 3)).trace / (3 : ℝ) = mu := by
      simp only [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
      ring
    change mu • (1 : Tensor 3) - ((mu • (1 : Tensor 3)).trace / (3 : ℝ)) • (1 : Tensor 3) = 0
    rw [ht, sub_self]
  rw [cauchy_splitNeoHookean bulk mu F hp, hj, show isochoricGradient F = 1 from
    isochoricGradient_uniformDilation s hs]
  simp only [leftCauchyGreen, Matrix.transpose_one, mul_one, hdev, smul_zero, add_zero]

end

end LeanSolid.ContinuumMechanics.Hyperelasticity
