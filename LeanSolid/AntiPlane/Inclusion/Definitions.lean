module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace LeanSolid.AntiPlane.Inclusion

/-- Interface matching for the first cosine mode of a circular inclusion.
The exterior radial factor is `r + A * radius^2 / r`, the interior factor is `B * r`. -/
def IsMatched (outer inner A B : ℝ) : Prop :=
  1 + A = B ∧ outer * (1 - A) = inner * B

end LeanSolid.AntiPlane.Inclusion
