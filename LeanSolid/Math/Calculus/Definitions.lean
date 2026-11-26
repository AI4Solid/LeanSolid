module

public import LeanSolid.Math.Definitions
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

namespace LeanSolid.Math

variable {n : ℕ}

/-- Cartesian partial derivative in the indexed unit direction. -/
noncomputable def partialDeriv (f : Vector n → ℝ) (j : Fin n) (x : Vector n) : ℝ :=
  fderiv ℝ f x (Pi.single j 1)

/-- The Cartesian Laplacian of a scalar field. -/
noncomputable def laplacian (f : Vector n → ℝ) (x : Vector n) : ℝ :=
  ∑ j, partialDeriv (partialDeriv f j) j x

/-- Expanded Cartesian biharmonic operator, with the two pure derivatives paired. -/
noncomputable def biharmonic (f : Vector n → ℝ) (x : Vector n) : ℝ :=
  ∑ i, ∑ j, partialDeriv (partialDeriv (partialDeriv (partialDeriv f i) i) j) j x

/-- Tensor divergence with the second matrix index contracted against the derivative. -/
noncomputable def tensorDivergence (A : Vector n → Tensor n) (x : Vector n) : Vector n :=
  fun i => ∑ j, partialDeriv (fun y => A y i j) j x

end LeanSolid.Math
