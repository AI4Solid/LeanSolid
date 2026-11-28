module

public import LeanSolid.Elastostatics.Definitions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

namespace LeanSolid.Elastostatics.Eigenstrain

variable {V E : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup E] [Module ℝ E]

/-- Stored energy with a prescribed eigenstrain in the strain space. -/
noncomputable def storedEnergy (a : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ε : V →ₗ[ℝ] E)
    (e : E) (u : V) : ℝ := a (ε u - e) (ε u - e) / 2

/-- Weak equilibrium with elastic strain `ε u - e` tested against compatible strains. -/
def IsEquilibrated (a : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ε : V →ₗ[ℝ] E)
    (e : E) (load : V →ₗ[ℝ] ℝ) (u : V) : Prop :=
  ∀ v, a (ε u - e) (ε v) = load v

/-- Colonetti's orthogonality of internal stress and compatible applied strain.
The internal equilibrium is tested with the applied displacement. -/
theorem storedEnergy_add_of_selfEquilibrated
    (a : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ε : V →ₗ[ℝ] E)
    (hs : ∀ x y, a x y = a y x) (e : E) (u v : V)
    (hu : IsEquilibrated a ε e 0 u) :
    storedEnergy a ε e (u + v) = storedEnergy a ε e u + storedEnergy a ε 0 v := by
  have hz : a (ε u - e) (ε v) = 0 := hu v
  have hzr : a (ε v) (ε u - e) = 0 := (hs _ _).trans hz
  have hsplit : ε (u + v) - e = (ε u - e) + ε v := by
    rw [map_add]
    abel
  unfold storedEnergy
  rw [hsplit]
  simp only [map_add, LinearMap.add_apply, hz, hzr, sub_zero, zero_add, add_zero]
  ring

/-- Self-equilibrated inclusion energy in terms of the elastic strain paired with
the prescribed eigenstrain. -/
theorem storedEnergy_selfEquilibrated
    (a : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ε : V →ₗ[ℝ] E) (e : E) (u : V)
    (hu : IsEquilibrated a ε e 0 u) :
    storedEnergy a ε e u = -(a (ε u - e) e) / 2 := by
  have hz : a (ε u - e) (ε u) = 0 := hu u
  rw [storedEnergy, map_sub, hz, zero_sub]

/-- Work of the external load on the eigenstrain displacement, with the
positive sign for work and the opposite sign in total potential energy. -/
theorem appliedWork_selfEquilibrated
    (a : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (ε : V →ₗ[ℝ] E)
    (hs : ∀ x y, a x y = a y x) (e : E) (load : V →ₗ[ℝ] ℝ) (u v : V)
    (hu : IsEquilibrated a ε e 0 u) (hv : IsEquilibrated a ε 0 load v) :
    load u = a (ε v) e := by
  have hz : a (ε v) (ε u - e) = 0 := (hs _ _).trans (hu v)
  have hw := hv u
  rw [map_sub] at hz
  rw [sub_zero] at hw
  exact hw.symm.trans (sub_eq_zero.mp hz)

end LeanSolid.Elastostatics.Eigenstrain
