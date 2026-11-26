module

public import LeanSolid.Plane.Eshelby.Definitions
import LeanSolid.Elastostatics.Radial.Theorems
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

public section

open Filter LeanSolid.Elastostatics.Radial
open scoped Topology

namespace LeanSolid.Plane.Eshelby

/-- The two interface equations determine the two radial amplitudes. -/
theorem matched_iff (lam mu α R A B : ℝ) (hR : R ≠ 0) (hmod : lam + 2 * mu ≠ 0) :
    IsMatched lam mu α R A B ↔ A = amplitude lam mu α ∧ B = amplitude lam mu α * R ^ 2 := by
  constructor
  · rintro ⟨hd, ht⟩
    have hb : B = A * R ^ 2 := by
      field_simp [hR] at hd
      linear_combination -hd
    rw [hb] at ht
    have ht' : 2 * (lam + mu) * (A - α) = -2 * mu * A := by
      convert ht using 1
      field_simp [hR]
    have ha : A = amplitude lam mu α := by
      unfold amplitude
      apply (eq_div_iff hmod).mpr
      linear_combination ht' / 2
    exact ⟨ha, hb.trans (congrArg (fun x => x * R ^ 2) ha)⟩
  · rintro ⟨rfl, rfl⟩
    constructor
    · field_simp [hR]
    · have h : amplitude lam mu α * (lam + 2 * mu) = (lam + mu) * α :=
        (eq_div_iff hmod).mp rfl
      have hc : -2 * mu * (amplitude lam mu α * R ^ 2) / R ^ 2 =
          -2 * mu * amplitude lam mu α := by
        field_simp [hR]
      rw [hc]
      linear_combination 2 * h

/-- For u = Ar the two total in-plane normal strains are constant and equal. -/
theorem interior_strain (A : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (fun s : ℝ => A * s) r = A ∧ (A * r) / r = A := by
  constructor
  · simp
  · exact mul_div_cancel_right₀ A hr

/-- The eigenstrain shifts both interior in-plane normal stresses by the same amount.
The interior traction is constant, so radial equilibrium holds. -/
theorem interior_stress_equilibrium (lam mu α A : ℝ) {r : ℝ} (hr : r ≠ 0) :
    let S := fun _ : ℝ => 2 * (lam + mu) * (A - α)
    sigR lam mu (A - α) ((A - α) * r) r = S r ∧
    sigT lam mu (A - α) ((A - α) * r) r = S r ∧
    deriv S r + (S r - S r) / r = 0 := by
  dsimp
  refine ⟨?_, ?_, by simp⟩
  · unfold sigR
    field_simp [hr]
    ring
  · unfold sigT
    field_simp [hr]
    ring

/-- The exterior branch u = B/r satisfies radial equilibrium in the matrix. -/
theorem exterior_equilibrium (lam mu B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (fun s => sigR lam mu (genD 0 B s) (gen 0 B s) s) r +
      (sigR lam mu (genD 0 B r) (gen 0 B r) r -
        sigT lam mu (genD 0 B r) (gen 0 B r) r) / r = 0 := by
  rw [equilibrium_eq lam mu (hasDerivAt_gen 0 B hr) (hasDerivAt_genD 0 B hr) hr,
    general_solves 0 B hr, mul_zero]

/-- Displacement and both exterior in-plane normal stresses vanish at infinity. -/
theorem exterior_far_field (mu B : ℝ) :
    Tendsto (fun r : ℝ => B / r) atTop (𝓝 0) ∧
    Tendsto (fun r : ℝ => -2 * mu * B / r ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun r : ℝ => 2 * mu * B / r ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 := h.pow 2
  refine ⟨?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv] using h.const_mul B
  · simpa [div_eq_mul_inv, inv_pow] using h2.const_mul (-2 * mu * B)
  · simpa [div_eq_mul_inv, inv_pow] using h2.const_mul (2 * mu * B)

/-- Circular Eshelby inclusion under uniform in-plane dilatational eigenstrain.
The matched radial solution has constant total strain inside. -/
theorem circular_dilatation (lam mu α R : ℝ) (hR : 0 < R) (hmod : lam + 2 * mu ≠ 0) :
    ∃! AB : ℝ × ℝ, IsMatched lam mu α R AB.1 AB.2 := by
  let A := amplitude lam mu α
  refine ⟨(A, A * R ^ 2), (matched_iff lam mu α R _ _ hR.ne' hmod).mpr ⟨rfl, rfl⟩, ?_⟩
  intro AB hAB
  obtain ⟨hA, hB⟩ := (matched_iff lam mu α R _ _ hR.ne' hmod).mp hAB
  exact Prod.ext hA hB

/-- The matched amplitudes give continuity of displacement and of the constitutive
normal traction evaluated from the two radial branches. -/
theorem circular_interface (lam mu α R : ℝ) (hR : 0 < R) (hmod : lam + 2 * mu ≠ 0) :
    let A := amplitude lam mu α
    let B := A * R ^ 2
    A * R = gen 0 B R ∧
      sigR lam mu (A - α) ((A - α) * R) R =
        sigR lam mu (genD 0 B R) (gen 0 B R) R := by
  dsimp only
  let A := amplitude lam mu α
  let B := A * R ^ 2
  have hm : IsMatched lam mu α R A B :=
    (matched_iff lam mu α R A B hR.ne' hmod).mpr ⟨rfl, rfl⟩
  obtain ⟨hd, ht⟩ := hm
  refine ⟨by simpa [gen] using hd, ?_⟩
  rw [(interior_stress_equilibrium lam mu α A hR.ne').1,
    sigR_general lam mu 0 B hR.ne']
  simpa [neg_div] using ht

end LeanSolid.Plane.Eshelby
