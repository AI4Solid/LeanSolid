module

public import LeanSolid.Elastostatics.Definitions
import Mathlib.Tactic.Linarith

public section

namespace LeanSolid.Elastostatics

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {a : V →L[ℝ] V →L[ℝ] ℝ} {f g : V →L[ℝ] ℝ} {u v : V}

theorem weakSolution_add (hu : IsWeakSolution a f u) (hv : IsWeakSolution a g v) :
    IsWeakSolution a (f + g) (u + v) := by
  intro w
  simp only [map_add, add_apply, hu w, hv w]

theorem weakSolution_smul (c : ℝ) (hu : IsWeakSolution a f u) :
    IsWeakSolution a (c • f) (c • u) := by
  intro w
  simp only [map_smul, smul_apply, hu w]

/-- Betti reciprocity on one admissible space with a symmetric bilinear form. -/
theorem betti (hs : ∀ x y, a x y = a y x)
    (hu : IsWeakSolution a f u) (hv : IsWeakSolution a g v) : f v = g u := by
  rw [← hu v, ← hv u, hs u v]

/-- In equilibrium, the load work equals twice the stored quadratic energy. -/
theorem clapeyron (hu : IsWeakSolution a f u) : f u = 2 * (a u u / 2) := by
  linarith [hu u]

theorem potentialEnergy_add (hs : ∀ x y, a x y = a y x)
    (hu : IsWeakSolution a f u) (w : V) :
    potentialEnergy a f (u + w) = potentialEnergy a f u + a w w / 2 := by
  simp only [potentialEnergy, map_add, add_apply]
  linarith [hs w u, hu w]

theorem potentialEnergy_min (hs : ∀ x y, a x y = a y x)
    (hp : ∀ w, 0 ≤ a w w) (hu : IsWeakSolution a f u) (w : V) :
    potentialEnergy a f u ≤ potentialEnergy a f w := by
  have h := potentialEnergy_add hs hu (w - u)
  rw [add_comm u, sub_add_cancel] at h
  linarith [hp (w - u)]

theorem eq_of_same_weakLoad_of_pos (hp : ∀ w ≠ 0, 0 < a w w)
    (hu : IsWeakSolution a f u) (hv : IsWeakSolution a f v) : u = v := by
  by_contra h
  have hz : a (u - v) = 0 := by
    ext w
    rw [map_sub, sub_apply, hu w, hv w, sub_self, zero_apply]
  simpa [hz] using hp (u - v) (sub_ne_zero.mpr h)

end LeanSolid.Elastostatics
