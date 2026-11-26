module

public import LeanSolid.LinearElasticity.Theorems

@[expose] public section

namespace LeanSolid.LinearElasticity

open LeanSolid.Math

/-- Stiffness as a linear map on Cartesian second-order tensors. -/
noncomputable def stiffness (n : ℕ) (lam mu : ℝ) : Tensor n →ₗ[ℝ] Tensor n where
  toFun := stress lam mu
  map_add' := stress_add lam mu
  map_smul' := stress_smul lam mu

theorem stiffness_apply (n : ℕ) (lam mu : ℝ) (A : Tensor n) :
    stiffness n lam mu A = stress lam mu A := rfl

end LeanSolid.LinearElasticity
