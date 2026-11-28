module

public import LeanSolid.ContinuumMechanics.Theorems
public import LeanSolid.ContinuumMechanics.Invariants
public import LeanSolid.Math.Calculus.TensorPath
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section

open scoped ContDiff

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

variable {n : ℕ}

/-- Deformation-gradient rate at a fixed material point X. -/
def deformationGradientRate (χ : ℝ → Vector n → Vector n) (t : ℝ) (X : Vector n) : Tensor n :=
  tensorRate (fun s => deformationGradient (χ s) X) t

/-- Spatial velocity gradient reconstructed from the material rate of F.
Its kinematic interpretation requires a nonsingular F. -/
def velocityGradient (F Fdot : Tensor n) : Tensor n := Fdot * F⁻¹

/-- Rate of deformation (stretching), the symmetric part of the spatial velocity gradient. -/
def rateOfDeformation (L : Tensor n) : Tensor n := symPart L

/-- Spatial spin, the skew part of the spatial velocity gradient. -/
def spin (L : Tensor n) : Tensor n := skewPart L

theorem velocityGradient_mul (F H : Tensor n) (hJ : jacobian F ≠ 0) :
    velocityGradient F H * F = H :=
  Matrix.nonsing_inv_mul_cancel_right F H (isUnit_iff_ne_zero.mpr hJ)

theorem velocityGradient_eq_of_rate_eq_mul {F H L : Tensor n} (hJ : jacobian F ≠ 0)
    (h : H = L * F) : velocityGradient F H = L := by
  rw [velocityGradient, h]
  exact Matrix.mul_nonsing_inv_cancel_right F L (isUnit_iff_ne_zero.mpr hJ)

theorem rateOfDeformation_add_spin (L : Tensor n) : rateOfDeformation L + spin L = L :=
  symPart_add_skewPart L

theorem rateOfDeformation_transpose (L : Tensor n) :
    (rateOfDeformation L).transpose = rateOfDeformation L :=
  symPart_transpose L

theorem spin_transpose (L : Tensor n) : (spin L).transpose = -spin L := by
  simp only [spin, skewPart, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_transpose, smul_sub]
  abel

theorem hasTensorDerivAt_rightCauchyGreen {F : ℝ → Tensor n} {H : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt F H t) :
    HasTensorDerivAt (fun s => rightCauchyGreen (F s)) (H.transpose * F t + (F t).transpose * H) t :=
  h.transpose.mul h

theorem hasTensorDerivAt_leftCauchyGreen {F : ℝ → Tensor n} {H : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt F H t) :
    HasTensorDerivAt (fun s => leftCauchyGreen (F s)) (H * (F t).transpose + F t * H.transpose) t :=
  h.mul h.transpose

theorem hasTensorDerivAt_greenStrain {F : ℝ → Tensor n} {H : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt F H t) :
    HasTensorDerivAt (fun s => greenStrain (F s))
      ((1 / 2 : ℝ) • (H.transpose * F t + (F t).transpose * H)) t := by
  intro i j
  exact ((hasTensorDerivAt_rightCauchyGreen h i j).sub_const ((1 : Tensor n) i j)).const_mul _

/-- Pull back the spatial rate of deformation to obtain the material Green–Lagrange rate. -/
theorem hasTensorDerivAt_greenStrain_of_spatialRate {F : ℝ → Tensor n} {H : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt F H t) (hJ : jacobian (F t) ≠ 0) :
    HasTensorDerivAt (fun s => greenStrain (F s))
      ((F t).transpose * rateOfDeformation (velocityGradient (F t) H) * F t) t := by
  let L := velocityGradient (F t) H
  have hLF : L * F t = H := velocityGradient_mul _ _ hJ
  have he : (1 / 2 : ℝ) • (H.transpose * F t + (F t).transpose * H) =
      (F t).transpose * rateOfDeformation L * F t := by
    rw [← hLF]
    simp only [rateOfDeformation, symPart, Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, add_comm]
  rw [← he]
  exact hasTensorDerivAt_greenStrain h


/-- Spatial form of the left Cauchy–Green rate: Ḃ = LB + BLᵀ. -/
theorem hasTensorDerivAt_leftCauchyGreen_of_spatialRate {F : ℝ → Tensor n} {H : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt F H t) (hJ : jacobian (F t) ≠ 0) :
    let L := velocityGradient (F t) H
    let B := leftCauchyGreen (F t)
    HasTensorDerivAt (fun s => leftCauchyGreen (F s)) (L * B + B * L.transpose) t := by
  let L := velocityGradient (F t) H
  have hLF : L * F t = H := velocityGradient_mul _ _ hJ
  have he : H * (F t).transpose + F t * H.transpose =
      L * leftCauchyGreen (F t) + leftCauchyGreen (F t) * L.transpose := by
    rw [← hLF]
    simp only [leftCauchyGreen, Matrix.transpose_mul, Matrix.mul_assoc]
  change HasTensorDerivAt _ (L * leftCauchyGreen (F t) + leftCauchyGreen (F t) * L.transpose) t
  rw [← he]
  exact hasTensorDerivAt_leftCauchyGreen h

/-- The rate of local volume change is J times the trace of the spatial velocity gradient. -/
theorem hasDerivAt_jacobian_of_spatialRate {F : ℝ → Tensor 3} {H : Tensor 3} {t : ℝ}
    (h : HasTensorDerivAt F H t) (hJ : jacobian (F t) ≠ 0) :
    HasDerivAt (fun s => jacobian (F s))
      (jacobian (F t) * (velocityGradient (F t) H).trace) t := by
  have hd := hasDerivAt_invariant₃ h
  have ha : (F t).adjugate = jacobian (F t) • (F t)⁻¹ := by
    calc
      (F t).adjugate = (F t)⁻¹ * (F t * (F t).adjugate) :=
        (Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hJ)).symm
      _ = _ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]; rfl
  rw [contract_eq_trace, Matrix.transpose_transpose, ha, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul, Matrix.trace_mul_comm] at hd
  exact hd

/-- Eulerian and material velocities agree by composition with the placement.
The rate hypothesis records the commutation of the material and time derivatives. -/
theorem deformationGradientRate_eq_spatialGradient_mul
    (χ : ℝ → Vector n → Vector n) (v : Vector n → Vector n) (t : ℝ) (X : Vector n)
    (hχ : DifferentiableAt ℝ (χ t) X) (hv : DifferentiableAt ℝ v (χ t X))
    (hRate : HasTensorDerivAt (fun s => deformationGradient (χ s) X)
      (deformationGradient (v ∘ χ t) X) t) :
    deformationGradientRate χ t X =
      deformationGradient v (χ t X) * deformationGradient (χ t) X := by
  exact hRate.eq_tensorRate.trans (deformationGradient_comp hχ hv)


/-- Velocity of a material point, obtained by differentiating its placement in time. -/
def materialVelocity (χ : ℝ → Vector n → Vector n) (t : ℝ) (X : Vector n) : Vector n :=
  fun i => deriv (fun s => χ s X i) t

/-- Joint C² regularity lets the spatial and time derivatives of the placement commute. -/
theorem hasTensorDerivAt_deformationGradient_motion
    (χ : ℝ → Vector n → Vector n)
    (hχ : ∀ i, ContDiff ℝ 2 (fun z : ℝ × Vector n => χ z.1 z.2 i))
    (t : ℝ) (X : Vector n) :
    HasTensorDerivAt (fun s => deformationGradient (χ s) X)
      (deformationGradient (materialVelocity χ t) X) t := by
  intro i j
  let f : ℝ × Vector n → ℝ := fun z => χ z.1 z.2 i
  let et : ℝ × Vector n := (1, 0)
  let eX : ℝ × Vector n := (0, Pi.single j 1)
  have hf : ContDiff ℝ 2 f := hχ i
  have hf' := hf.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have ht (s : ℝ) (Y : Vector n) :
      HasDerivAt (fun r : ℝ => (r, Y)) et s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s Y)
  have hspace (g : ℝ × Vector n → ℝ) (hg : DifferentiableAt ℝ g (t, X)) :
      partialDeriv (fun Y => g (t, Y)) j X = fderiv ℝ g (t, X) eX :=
    congrArg (fun L : Vector n →L[ℝ] ℝ => L (Pi.single j 1))
      (hg.hasFDerivAt.comp X (hasFDerivAt_prodMk_right t X)).fderiv
  have hF : (fun s => deformationGradient (χ s) X i j) =
      fun s => (fderiv ℝ f (s, X)) eX := by
    funext s
    exact congrArg (fun L : Vector n →L[ℝ] ℝ => L (Pi.single j 1))
      ((hf' (s, X)).hasFDerivAt.comp X (hasFDerivAt_prodMk_right s X)).fderiv
  have hV : (fun Y => materialVelocity χ t Y i) = fun Y => (fderiv ℝ f (t, Y)) et := by
    funext Y
    exact ((hf' (t, Y)).hasFDerivAt.comp_hasDerivAt t (ht t Y)).deriv
  have hdX := hd.clm_apply (differentiable_const eX)
  have hdt := hd.clm_apply (differentiable_const et)
  have hs := (hf.contDiffAt (x := (t, X))).isSymmSndFDerivAt (by simp)
  have hcomm :
      fderiv ℝ (fun z => fderiv ℝ f z eX) (t, X) et =
        fderiv ℝ (fun z => fderiv ℝ f z et) (t, X) eX := by
    rw [fderiv_clm_apply (hd _) (differentiableAt_const _),
      fderiv_clm_apply (hd _) (differentiableAt_const _)]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
    exact hs _ _
  rw [hF]
  change HasDerivAt _ (partialDeriv (fun Y => materialVelocity χ t Y i) j X) t
  rw [hV, hspace _ (hdt _), ← hcomm]
  exact (hdX _).hasFDerivAt.comp_hasDerivAt t (ht t X)

/-- For a jointly C² motion, a differentiable spatial velocity field with the
correct material pullback satisfies Ḟ = (grad v) F. -/
theorem deformationGradientRate_motion
    (χ : ℝ → Vector n → Vector n)
    (hχ : ∀ i, ContDiff ℝ 2 (fun z : ℝ × Vector n => χ z.1 z.2 i))
    (v : Vector n → Vector n) (t : ℝ) (X : Vector n)
    (hv : DifferentiableAt ℝ v (χ t X))
    (hPullback : materialVelocity χ t = v ∘ χ t) :
    deformationGradientRate χ t X =
      deformationGradient v (χ t X) * deformationGradient (χ t) X := by
  have hPlacement : DifferentiableAt ℝ (χ t) X := differentiableAt_pi.mpr fun i =>
    (((hχ i).differentiable (by norm_num)) (t, X)).comp X
      (hasFDerivAt_prodMk_right t X).differentiableAt
  apply deformationGradientRate_eq_spatialGradient_mul χ v t X hPlacement hv
  rw [← hPullback]
  exact hasTensorDerivAt_deformationGradient_motion χ hχ t X

/-- Product rule for a time-dependent superposed spatial rotation. -/
theorem hasTensorDerivAt_rotatedGradient {Q F : ℝ → Tensor n} {Qdot Fdot : Tensor n} {t : ℝ}
    (hQ : HasTensorDerivAt Q Qdot t) (hF : HasTensorDerivAt F Fdot t) :
    HasTensorDerivAt (fun s => Q s * F s) (Qdot * F t + Q t * Fdot) t :=
  hQ.mul hF

theorem rotatingFrame_rate_skew {Q : ℝ → Tensor n} {Qdot : Tensor n} {t : ℝ}
    (hQ : HasTensorDerivAt Q Qdot t) (hOrth : ∀ s, Q s * (Q s).transpose = 1) :
    (Qdot * (Q t).transpose).transpose = -(Qdot * (Q t).transpose) := by
  have h := hQ.mul hQ.transpose
  have he : (fun s => Q s * (Q s).transpose) = fun _ => (1 : Tensor n) := funext hOrth
  rw [he] at h
  have hz := h.unique (hasTensorDerivAt_const (1 : Tensor n) t)
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  exact eq_neg_of_add_eq_zero_right hz

/-- The spatial velocity gradient gains the angular velocity of the observer. -/
theorem velocityGradient_rotated (Q Qdot F Fdot : Tensor n)
    (hQ : Q.transpose * Q = 1) (hJ : jacobian F ≠ 0) :
    velocityGradient (Q * F) (Qdot * F + Q * Fdot) =
      Qdot * Q.transpose + conjugate Q (velocityGradient F Fdot) := by
  have hdet := congrArg Matrix.det hQ
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hq : jacobian Q ≠ 0 := by
    intro hz
    change Q.det = 0 at hz
    simp [hz] at hdet
  apply velocityGradient_eq_of_rate_eq_mul (by rw [jacobian_mul]; exact mul_ne_zero hq hJ)
  unfold conjugate
  rw [Matrix.add_mul]
  have h1 : (Qdot * Q.transpose) * (Q * F) = Qdot * F := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q.transpose, hQ, one_mul]
  have h2 : (Q * velocityGradient F Fdot * Q.transpose) * (Q * F) = Q * Fdot := by
    calc
      _ = (Q * velocityGradient F Fdot) * ((Q.transpose * Q) * F) := by
        simp only [Matrix.mul_assoc]
      _ = Q * Fdot := by rw [hQ, one_mul, Matrix.mul_assoc, velocityGradient_mul F Fdot hJ]
  rw [h1, h2]

/-- Rate of deformation rotates by conjugation, with the observer spin cancelling out. -/
theorem rateOfDeformation_rotated (Q Qdot F Fdot : Tensor n)
    (hQ : Q.transpose * Q = 1) (hJ : jacobian F ≠ 0)
    (hSkew : (Qdot * Q.transpose).transpose = -(Qdot * Q.transpose)) :
    rateOfDeformation (velocityGradient (Q * F) (Qdot * F + Q * Fdot)) =
      conjugate Q (rateOfDeformation (velocityGradient F Fdot)) := by
  rw [velocityGradient_rotated Q Qdot F Fdot hQ hJ, rateOfDeformation, symPart_add,
    (symPart_eq_zero_iff _).mpr hSkew, zero_add]
  change symPart (conjugate Q (velocityGradient F Fdot)) =
    conjugate Q (symPart (velocityGradient F Fdot))
  unfold symPart
  rw [conjugate_transpose]
  simp only [conjugate, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul]

/-- Spin has the same additive observer term as the full velocity gradient. -/
theorem spin_rotated (Q Qdot F Fdot : Tensor n)
    (hQ : Q.transpose * Q = 1) (hJ : jacobian F ≠ 0)
    (hSkew : (Qdot * Q.transpose).transpose = -(Qdot * Q.transpose)) :
    spin (velocityGradient (Q * F) (Qdot * F + Q * Fdot)) =
      Qdot * Q.transpose + conjugate Q (spin (velocityGradient F Fdot)) := by
  let L := velocityGradient F Fdot
  have hc : conjugate Q L =
      conjugate Q (rateOfDeformation L) + conjugate Q (spin L) := by
    conv_lhs => rw [← rateOfDeformation_add_spin L]
    simp only [conjugate, Matrix.mul_add, Matrix.add_mul]
  have h := rateOfDeformation_add_spin (velocityGradient (Q * F) (Qdot * F + Q * Fdot))
  rw [rateOfDeformation_rotated Q Qdot F Fdot hQ hJ hSkew,
    velocityGradient_rotated Q Qdot F Fdot hQ hJ] at h
  rw [velocityGradient_rotated Q Qdot F Fdot hQ hJ]
  change conjugate Q (rateOfDeformation L) + spin (Qdot * Q.transpose + conjugate Q L) =
    Qdot * Q.transpose + conjugate Q L at h
  apply add_left_cancel (a := conjugate Q (rateOfDeformation L))
  rw [h, hc]
  abel


/-- The material strain-rate path is invariant under arbitrary time-dependent orthogonal left factors. -/
theorem greenStrain_rate_rotated (Q F : ℝ → Tensor n) (t : ℝ)
    (hQ : ∀ s, (Q s).transpose * Q s = 1) :
    tensorRate (fun s => greenStrain (Q s * F s)) t =
      tensorRate (fun s => greenStrain (F s)) t := by
  have h : (fun s => greenStrain (Q s * F s)) = fun s => greenStrain (F s) :=
    funext fun s => greenStrain_orthogonal_mul (Q s) (F s) (hQ s)
  rw [h]

end LeanSolid.ContinuumMechanics
