module

public import LeanSolid.Math.Calculus.Definitions
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

noncomputable section

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

variable {n : ℕ}

/-- Placement associated with a displacement field in reference coordinates. -/
def placement (u : Vector n → Vector n) (X : Vector n) : Vector n := X + u X

/-- Cartesian deformation gradient. Row `i` is spatial and column `j` is material:
`F i j = ∂χᵢ/∂Xⱼ`. Derivative identities require differentiability of `χ`. -/
def deformationGradient (χ : Vector n → Vector n) (X : Vector n) : Tensor n :=
  Matrix.of fun i j => partialDeriv (fun Y => χ Y i) j X

/-- Signed local volume ratio of a deformation gradient. -/
def jacobian (F : Tensor n) : ℝ := F.det

/-- Right Cauchy–Green tensor, expressed in reference coordinates. -/
def rightCauchyGreen (F : Tensor n) : Tensor n := F.transpose * F

/-- Left Cauchy–Green tensor, expressed in spatial coordinates. -/
def leftCauchyGreen (F : Tensor n) : Tensor n := F * F.transpose

/-- Green–Lagrange strain in reference coordinates. -/
def greenStrain (F : Tensor n) : Tensor n := (1 / 2 : ℝ) • (rightCauchyGreen F - 1)

end LeanSolid.ContinuumMechanics
