module

public import LeanSolid.Elastostatics.Radial.Theorems
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

open Filter
open scoped Topology

namespace LeanSolid.Elastostatics.SphericalInclusion

open Radial

/-- Uniform interior dilation for a spherical inclusion with the same moduli as its matrix. -/
noncomputable def amplitude (lam mu α : ℝ) : ℝ :=
  (3 * lam + 2 * mu) * α / (3 * lam + 6 * mu)

/-- Radial displacement and traction continuity for the branches A r and B/r². -/
def IsMatched (lam mu α R A B : ℝ) : Prop :=
  A * R = B / R ^ 2 ∧ (3 * lam + 2 * mu) * (A - α) = -4 * mu * B / R ^ 3

theorem matched_iff (lam mu α R A B : ℝ) (hR : R ≠ 0) (hmod : 3 * lam + 6 * mu ≠ 0) :
    IsMatched lam mu α R A B ↔ A = amplitude lam mu α ∧ B = A * R ^ 3 := by
  have h₂ : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
  constructor
  · rintro ⟨hd, ht⟩
    have hb : B = A * R ^ 3 := by
      have h := (eq_div_iff h₂).mp hd
      linear_combination -h
    rw [hb, show -4 * mu * (A * R ^ 3) / R ^ 3 = -4 * mu * A by
      field_simp] at ht
    exact ⟨(eq_div_iff hmod).mpr (by linear_combination ht), hb⟩
  · rintro ⟨ha, rfl⟩
    constructor
    · field_simp
    · rw [show -4 * mu * (A * R ^ 3) / R ^ 3 = -4 * mu * A by
        field_simp]
      have h := (eq_div_iff hmod).mp ha
      linear_combination h

/-- Interior total radial and hoop strains are constant and equal. -/
theorem interior_strain (A : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (fun s : ℝ => A * s) r = A ∧ (A * r) / r = A :=
  ⟨by simp, mul_div_cancel_right₀ _ hr⟩

theorem interior_stress (lam mu α A : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sphSigR lam mu (A - α) ((A - α) * r) r = (3 * lam + 2 * mu) * (A - α) ∧
      sphSigT lam mu (A - α) ((A - α) * r) r = (3 * lam + 2 * mu) * (A - α) := by
  have h := sphere_general lam mu (A - α) 0 hr
  simpa using h

theorem exterior_stress (lam mu B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sphSigR lam mu (-2 * B / r ^ 3) (B / r ^ 2) r = -4 * mu * B / r ^ 3 ∧
      sphSigT lam mu (-2 * B / r ^ 3) (B / r ^ 2) r = 2 * mu * B / r ^ 3 := by
  have h := sphere_general lam mu 0 B hr
  simpa [neg_div] using h

theorem exterior_farField (B : ℝ) :
    Tendsto (fun r : ℝ => B / r ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv, inv_pow] using (h.pow 2).const_mul B

end LeanSolid.Elastostatics.SphericalInclusion
