module

public import LeanSolid.LinearElasticity.Cartesian
import Mathlib.Tactic.Linarith

public section

namespace LeanSolid.Elastostatics

open LeanSolid.Math

variable {n : ℕ}

/-- A fixed face removes infinitesimal rigid motion. A point and one nonzero offset in
each tangential coordinate direction suffice. The offsets may be chosen inside a rectangular face. -/
theorem rigid_eq_zero_of_fixed_face (axis : Fin n) (x₀ a : Vector n)
    (W : Vector n →L[ℝ] Vector n)
    (hskew : ∀ i j : Fin n, W (Pi.single j 1) i + W (Pi.single i 1) j = 0)
    (h₀ : a + W x₀ = 0)
    (hface : ∀ j : Fin n, j ≠ axis → ∃ t : ℝ, t ≠ 0 ∧
      a + W (x₀ + t • (Pi.single j 1 : Vector n)) = 0) :
    ∀ x : Vector n, a + W x = 0 := by
  have htangent (j : Fin n) (hj : j ≠ axis) : W (Pi.single j 1) = 0 := by
    obtain ⟨t, ht, hv⟩ := hface j hj
    rw [map_add, map_smul, ← add_assoc, h₀, zero_add] at hv
    exact (smul_eq_zero.mp hv).resolve_left ht
  have hb (j : Fin n) : W (Pi.single j 1) = 0 := by
    by_cases hj : j = axis
    · subst j
      funext i
      have h := hskew i axis
      by_cases hi : i = axis
      · subst i
        change W (Pi.single axis 1) axis = 0
        linarith
      · rw [htangent i hi] at h
        simpa using h
    · exact htangent j hj
  have hz : W = 0 := by
    apply ContinuousLinearMap.coe_injective
    exact (Pi.basisFun ℝ (Fin n)).ext (fun j => by simpa [Pi.basisFun_apply] using hb j)
  intro x
  simpa [hz] using h₀

end LeanSolid.Elastostatics
