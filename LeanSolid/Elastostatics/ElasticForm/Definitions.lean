module

public import LeanSolid.Elastostatics.Definitions
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

namespace LeanSolid.Elastostatics

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Strain and stiffness operators induce the internal virtual-work form.
The construction follows lean-mechanics, Elastostatics/Weak.lean (Apache-2.0). -/
noncomputable def elasticForm (strain : V →L[ℝ] H) (stiffness : H →L[ℝ] H) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ V H ℝ).flip strain).comp
    ((innerSL ℝ).comp (stiffness.comp strain))

end LeanSolid.Elastostatics
