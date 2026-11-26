module

public import Mathlib.Analysis.Normed.Operator.NormedSpace

@[expose] public section

namespace LeanSolid.Elastostatics

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Weak equilibrium. Boundary conditions enter through the admissible displacement space. -/
def IsWeakSolution (a : V →L[ℝ] V →L[ℝ] ℝ) (load : V →L[ℝ] ℝ) (u : V) : Prop :=
  ∀ v : V, a u v = load v

/-- Total potential energy on the homogeneous admissible displacement space. -/
noncomputable def potentialEnergy (a : V →L[ℝ] V →L[ℝ] ℝ)
    (load : V →L[ℝ] ℝ) (u : V) : ℝ :=
  a u u / 2 - load u

/-- Conforming Galerkin equilibrium with trials and tests in the same subspace. -/
def IsGalerkinSolution (a : V →L[ℝ] V →L[ℝ] ℝ) (load : V →L[ℝ] ℝ)
    (space : Submodule ℝ V) (u : V) : Prop :=
  u ∈ space ∧ ∀ v ∈ space, a u v = load v

end LeanSolid.Elastostatics
