module

public import LeanSolid.ContinuumMechanics.Theorems
public import LeanSolid.ContinuumMechanics.Statics
public import LeanSolid.LinearElasticity.Definitions

public section

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

variable {n : ℕ}

/-- For a placement written as identity plus displacement, the infinitesimal strain
is the linear term in its Green–Lagrange strain. -/
theorem greenStrain_placement (u : Vector n → Vector n) (X : Vector n)
    (hu : DifferentiableAt ℝ u X) :
    greenStrain (deformationGradient (placement u) X) =
      LinearElasticity.strainField u X +
        (1 / 2 : ℝ) • ((deformationGradient u X).transpose * deformationGradient u X) := by
  rw [deformationGradient_placement u X hu, greenStrain_one_add]
  rfl

/-- An affine placement with uniform symmetric Cauchy stress solves the
unloaded bulk equilibrium equations. Boundary traction is supplied separately. -/
theorem affine_referenceEquilibrium {Ω : Set (Vector n)} (hΩ : IsOpen Ω)
    (L : Vector n →L[ℝ] Vector n) (c : Vector n) (σ : Tensor n)
    (hσ : σ.transpose = σ) (hJ : jacobian (LinearMap.toMatrix' L.toLinearMap) ≠ 0) :
    let F := deformationGradient (fun X => L X + c)
    IsReferenceEquilibriumOn Ω (fun X => firstPiola (F X) σ) (fun _ => 0) ∧
      ∀ X ∈ Ω, IsMomentBalanced (F X) (firstPiola (F X) σ) := by
  simp only [deformationGradient_affine]
  exact ⟨constant_referenceEquilibrium hΩ _,
    fun _ _ => (momentBalanced_firstPiola_iff _ σ hJ).mpr hσ⟩

end LeanSolid.ContinuumMechanics
