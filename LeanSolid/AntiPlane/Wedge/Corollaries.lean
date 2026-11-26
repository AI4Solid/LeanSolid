module

public import LeanSolid.AntiPlane.Wedge.Theorems
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

public section

namespace LeanSolid.AntiPlane.Wedge

/-- The leading positive separated exponent gives a Mode III crack stress exponent of −1/2.
This is a modal statement for a slit of opening angle `2π`. -/
theorem crack_first_mode :
    FreeMode Real.pi (1 / 2) ∧
      (∀ q > 0, FreeMode Real.pi q → -(1 / 2 : ℝ) ≤ q - 1) := by
  have h : Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  constructor
  · rw [← h]
    exact first_mode _ Real.pi_pos
  · intro q hq hm
    have hq' := first_mode_le _ q Real.pi_pos hq hm
    rw [h] at hq'
    linarith

end LeanSolid.AntiPlane.Wedge
