module

public import LeanSolid.AntiPlane.Inclusion.Definitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

namespace LeanSolid.AntiPlane.Inclusion

/-- Displacement and traction matching determine the two coefficients. -/
theorem matched_iff (outer inner A B : ℝ) (h : outer + inner ≠ 0) :
    IsMatched outer inner A B ↔
      A = (outer - inner) / (outer + inner) ∧ B = 2 * outer / (outer + inner) := by
  constructor
  · rintro ⟨hB, ht⟩
    have hA : A = (outer - inner) / (outer + inner) := by
      apply (eq_div_iff h).2
      rw [← hB] at ht
      nlinarith only [ht]
    refine ⟨hA, ?_⟩
    apply (eq_div_iff h).2
    rw [← hB, hA]
    field_simp [h]
    ring
  · rintro ⟨rfl, rfl⟩
    constructor <;> field_simp [h] <;> ring

end LeanSolid.AntiPlane.Inclusion
