module

public import LeanSolid.Elastostatics.Definitions
import Mathlib.Tactic.Linarith

public section

namespace LeanSolid.Elastostatics

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {a : V →L[ℝ] V →L[ℝ] ℝ} {f : V →L[ℝ] ℝ}
variable {W : Submodule ℝ V} {u uh v : V}

/-- Adapted from the Galerkin development in lean-mechanics (Apache-2.0). -/
theorem galerkin_orthogonality (hu : IsWeakSolution a f u)
    (hh : IsGalerkinSolution a f W uh) (hv : v ∈ W) : a (u - uh) v = 0 := by
  rw [map_sub, sub_apply, hu v, hh.2 v hv, sub_self]

/-- Céa's estimate for an explicit candidate in the conforming subspace. -/
theorem cea {α M : ℝ} (hα : 0 < α) (hM₀ : 0 ≤ M)
    (hM : ∀ x y, |a x y| ≤ M * ‖x‖ * ‖y‖)
    (hcoer : ∀ x, α * ‖x‖ ^ 2 ≤ a x x)
    (hu : IsWeakSolution a f u) (hh : IsGalerkinSolution a f W uh) (hv : v ∈ W) :
    ‖u - uh‖ ≤ M / α * ‖u - v‖ := by
  have hz := galerkin_orthogonality hu hh (W.sub_mem hv hh.1)
  have he : a (u - uh) (u - uh) = a (u - uh) (u - v) := by
    calc
      a (u - uh) (u - uh) = a (u - uh) ((u - v) + (v - uh)) := by
        rw [sub_add_sub_cancel]
      _ = a (u - uh) (u - v) := by rw [map_add, hz, add_zero]
  have hb : α * ‖u - uh‖ ^ 2 ≤ M * ‖u - uh‖ * ‖u - v‖ := by
    refine (hcoer _).trans ?_
    rw [he]
    exact (le_abs_self _).trans (hM _ _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hα]
  rcases (norm_nonneg (u - uh)).eq_or_lt with hzero | hpos
  · rw [← hzero, zero_mul]
    exact mul_nonneg hM₀ (norm_nonneg _)
  · apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hb]

end LeanSolid.Elastostatics
