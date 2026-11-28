module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Theorems
import Mathlib.Tactic.Abel

@[expose] public section

open scoped Matrix.Norms.Elementwise

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

variable {n : ℕ}

/-- Material frame indifference of stored energy under proper spatial rotations. -/
def FrameIndifferent (energy : Tensor n → ℝ) : Prop :=
  ∀ Q F, Q.transpose * Q = 1 → jacobian Q = 1 → energy (Q * F) = energy F

/-- Jaumann rate of a spatial tensor with material derivative H and spatial spin W. -/
noncomputable def jaumannRate (A H W : Tensor n) : Tensor n := H - W * A + A * W

/-- Derivative of a spatial tensor along a path seen by a rotating observer. -/
theorem hasTensorDerivAt_conjugate {Q A : ℝ → Tensor n} {Qdot H : Tensor n} {t : ℝ}
    (hQ : HasTensorDerivAt Q Qdot t) (hA : HasTensorDerivAt A H t) :
    HasTensorDerivAt (fun s => conjugate (Q s) (A s))
      ((Qdot * A t + Q t * H) * (Q t).transpose + Q t * A t * Qdot.transpose) t :=
  (hQ.mul hA).mul hQ.transpose

theorem jaumannRate_conjugate (Q Qdot A H W : Tensor n)
    (hQ : Q.transpose * Q = 1)
    (hspin : (Qdot * Q.transpose).transpose = -(Qdot * Q.transpose)) :
    jaumannRate (conjugate Q A)
      ((Qdot * A + Q * H) * Q.transpose + Q * A * Qdot.transpose)
      (Qdot * Q.transpose + conjugate Q W) =
      conjugate Q (jaumannRate A H W) := by
  have hqt : Q * Qdot.transpose = -(Qdot * Q.transpose) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hspin
  have hd : Qdot.transpose = -(Q.transpose * Qdot * Q.transpose) := by
    calc
      Qdot.transpose = Q.transpose * (Q * Qdot.transpose) := by
        rw [← Matrix.mul_assoc, hQ, one_mul]
      _ = _ := by rw [hqt, Matrix.mul_neg, Matrix.mul_assoc]
  unfold jaumannRate conjugate
  rw [hd]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
    Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc Q.transpose Q, hQ, one_mul]
  abel

theorem frameIndifferent_rightCauchyGreen (energy : Tensor n → ℝ) :
    FrameIndifferent (fun F => energy (rightCauchyGreen F)) := by
  intro Q F hQ _
  exact congrArg energy (rightCauchyGreen_orthogonal_mul Q F hQ)

/-- The Jaumann rate along a material path transforms by conjugation. -/
theorem jaumannRate_rotatingFrame {Q A F : ℝ → Tensor n} {Qdot H Fdot : Tensor n} {t : ℝ}
    (hQ : HasTensorDerivAt Q Qdot t) (hA : HasTensorDerivAt A H t)
    (hF : HasTensorDerivAt F Fdot t)
    (hOrth : ∀ s, (Q s).transpose * Q s = 1) (hJ : jacobian (F t) ≠ 0) :
    jaumannRate (conjugate (Q t) (A t)) (tensorRate (fun s => conjugate (Q s) (A s)) t)
      (spin (velocityGradient (Q t * F t) (tensorRate (fun s => Q s * F s) t))) =
      conjugate (Q t) (jaumannRate (A t) H (spin (velocityGradient (F t) Fdot))) := by
  have hSkew := rotatingFrame_rate_skew hQ (fun s => mul_eq_one_comm.mp (hOrth s))
  rw [(hasTensorDerivAt_conjugate hQ hA).eq_tensorRate, (hQ.mul hF).eq_tensorRate,
    spin_rotated _ _ _ _ (hOrth t) hJ hSkew]
  exact jaumannRate_conjugate _ _ _ _ _ (hOrth t) hSkew

theorem frameIndifferent_greenStrain (energy : Tensor n → ℝ) :
    FrameIndifferent (fun F => energy (greenStrain F)) := by
  intro Q F hQ _
  exact congrArg energy (greenStrain_orthogonal_mul Q F hQ)

/-- Differentiable frame-indifferent energy gives equivariant first Piola stress. -/
theorem firstPiolaStress_objective {energy : Tensor n → ℝ} (hObj : FrameIndifferent energy)
    (Q F : Tensor n) (hQ : Q.transpose * Q = 1) (hdet : jacobian Q = 1)
    (hE : DifferentiableAt ℝ energy F) :
    Hyperelasticity.firstPiolaStress energy (Q * F) =
      Q * Hyperelasticity.firstPiolaStress energy F := by
  let G := Hyperelasticity.energyGradient energy F
  have hGrad := Hyperelasticity.hasEnergyGradient_of_differentiable hE
  have hInv : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQ
  have hc : Hyperelasticity.HasEnergyGradient energy (Q * F) (Q * G) := by
    intro c H h0 hH
    have hPath := (hasTensorDerivAt_const Q.transpose 0).mul hH
    simp only [zero_mul, zero_add] at hPath
    have hBase : Q.transpose * c 0 = F := by rw [h0, ← Matrix.mul_assoc, hQ, one_mul]
    have h := hGrad (fun t => Q.transpose * c t) (Q.transpose * H) hBase hPath
    have hf : (fun t => energy (Q.transpose * c t)) = fun t => energy (c t) := by
      funext t
      have hh := hObj Q (Q.transpose * c t) hQ hdet
      rw [← Matrix.mul_assoc, hInv, one_mul] at hh
      exact hh.symm
    rw [hf] at h
    have hw : contract G (Q.transpose * H) = contract (Q * G) H := by
      simp only [contract_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hw] at h
    exact h
  exact hc.eq_energyGradient

theorem cauchyStress_objective {energy : Tensor n → ℝ} (hObj : FrameIndifferent energy)
    (Q F : Tensor n) (hQ : Q.transpose * Q = 1) (hdet : jacobian Q = 1)
    (hE : DifferentiableAt ℝ energy F) :
    cauchyFromPiola (Q * F) (Hyperelasticity.firstPiolaStress energy (Q * F)) =
      conjugate Q (cauchyFromPiola F (Hyperelasticity.firstPiolaStress energy F)) := by
  rw [firstPiolaStress_objective hObj Q F hQ hdet hE]
  simp only [cauchyFromPiola, jacobian_mul, hdet, one_mul, Matrix.transpose_mul, conjugate,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end LeanSolid.ContinuumMechanics
