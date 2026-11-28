module

public import LeanSolid.Elastostatics.Eigenstrain
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace LeanSolid.Elastostatics

variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup E] [Module ℝ E]

/-- Complementary potential in the compliance variable s, the strain recovered
from its stress. The prescribed displacement lift contributes strain d. -/
noncomputable def complementaryPotential (a : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (d s : E) : ℝ :=
  a s s / 2 - a s d

/-- The complementary-potential difference equals the energy of the stress
variation in compliance coordinates when the two stresses have the same virtual work. -/
theorem complementaryPotential_difference
    (a : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ε : V →ₗ[ℝ] E) (symm : ∀ x y, a x y = a y x)
    (d s : E) (u : V)
    (h : ∀ v, a (s - (d + ε u)) (ε v) = 0) :
    complementaryPotential a d s - complementaryPotential a d (d + ε u) =
      a (s - (d + ε u)) (s - (d + ε u)) / 2 := by
  let s₀ := d + ε u
  let δ := s - s₀
  have hz : a δ (ε u) = 0 := h u
  have hw : a δ s₀ = a δ d := by
    change a δ (d + ε u) = a δ d
    rw [map_add, hz, add_zero]
  have he : s = s₀ + δ := by dsimp [δ]; abel
  change complementaryPotential a d s - complementaryPotential a d s₀ = a δ δ / 2
  conv_lhs => rw [he]
  unfold complementaryPotential
  simp only [map_add, LinearMap.add_apply, symm s₀ δ, hw]
  ring

/-- Positive elastic energy implies the minimum complementary potential principle
over stresses with the same virtual work. -/
theorem complementaryPotential_minimum
    (a : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ε : V →ₗ[ℝ] E) (symm : ∀ x y, a x y = a y x)
    (pos : ∀ x, 0 ≤ a x x) (d s : E) (u : V)
    (h : ∀ v, a (s - (d + ε u)) (ε v) = 0) :
    complementaryPotential a d (d + ε u) ≤ complementaryPotential a d s := by
  have hd := complementaryPotential_difference a ε symm d s u h
  linarith only [hd, pos (s - (d + ε u))]

end LeanSolid.Elastostatics
