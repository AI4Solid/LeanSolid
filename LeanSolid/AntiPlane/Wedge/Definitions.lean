module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace LeanSolid.AntiPlane.Wedge

/-- Angular part of a separated anti-plane displacement. -/
noncomputable def angular (q A B θ : ℝ) : ℝ :=
  A * Real.cos (q * θ) + B * Real.sin (q * θ)

/-- Angular derivative divided by the nonzero separation exponent. -/
noncomputable def tractionFactor (q A B θ : ℝ) : ℝ :=
  -A * Real.sin (q * θ) + B * Real.cos (q * θ)

/-- A nonzero angular mode with traction-free faces at angles ±α. -/
def FreeMode (α q : ℝ) : Prop :=
  ∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧
    tractionFactor q A B α = 0 ∧ tractionFactor q A B (-α) = 0

end LeanSolid.AntiPlane.Wedge
