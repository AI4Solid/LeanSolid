module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Theorems
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

public section

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math Hyperelasticity

variable {n : ℕ}

/-- The three work-conjugate pairings give the same power per reference volume.
S is symmetric and P = FS, so the recovered Cauchy stress is symmetric. -/
theorem stressPower_eq (F S H : Tensor n) (hS : S.transpose = S) (hJ : jacobian F ≠ 0) :
    let P := F * S
    let σ := cauchyFromPiola F P
    contract P H = contract S ((1 / 2 : ℝ) • (H.transpose * F + F.transpose * H)) ∧
      contract P H =
        jacobian F * contract σ (rateOfDeformation (velocityGradient F H)) := by
  dsimp only
  let P := F * S
  let L := velocityGradient F H
  have hs : (P * F.transpose).transpose = P * F.transpose := momentBalanced_of_secondPiola F S hS
  refine ⟨(greenStrain_work F S H hS).symm, ?_⟩
  have hPair : contract P H = contract (P * F.transpose) L := by
    calc
      contract P H = contract P (L * F) := congrArg (contract P) (velocityGradient_mul F H hJ).symm
      _ = _ := by
        simp only [LeanSolid.Math.contract_eq_trace, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P.transpose, Matrix.trace_mul_comm (P.transpose * L)]
  calc
    contract P H = contract (P * F.transpose) L := hPair
    _ = contract (P * F.transpose) (rateOfDeformation L) := by
      rw [contract_comm _ (rateOfDeformation L), rateOfDeformation,
        contract_symPart_of_symmetric _ _ hs, contract_comm]
    _ = _ := by
      simp only [P, L, cauchyFromPiola, contract_smul_left, ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]

/-- Along a material path, the reference mass density has zero rate exactly
when the spatial density satisfies the local continuity equation. -/
theorem localMassBalance_iff {F : ℝ → Tensor 3} {H : Tensor 3} {t ρdot : ℝ}
    {ρ : ℝ → ℝ} (hF : HasTensorDerivAt F H t)
    (hρ : HasDerivAt ρ ρdot t) (hJ : jacobian (F t) ≠ 0) :
    HasDerivAt (fun s => ρ s * jacobian (F s)) 0 t ↔
      ρdot + ρ t * (velocityGradient (F t) H).trace = 0 := by
  have h := hρ.mul (hasDerivAt_jacobian_of_spatialRate hF hJ)
  have hf : ρdot * jacobian (F t) + ρ t * (jacobian (F t) * (velocityGradient (F t) H).trace) =
      (ρdot + ρ t * (velocityGradient (F t) H).trace) * jacobian (F t) := by ring
  rw [hf] at h
  constructor
  · intro hz
    exact (mul_eq_zero.mp (h.unique hz)).resolve_right hJ
  · intro hz
    have he : (fun s => ρ s * jacobian (F s)) = ρ * (fun s => jacobian (F s)) := rfl
    rw [he]
    rwa [hz, zero_mul] at h

end LeanSolid.ContinuumMechanics
