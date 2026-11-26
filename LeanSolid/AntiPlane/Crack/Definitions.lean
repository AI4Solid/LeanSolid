module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace LeanSolid.AntiPlane.Crack

/-- Ahead-of-tip shear for the infinite-body center-crack candidate, using distance from the right tip. -/
noncomputable def aheadShear (remote halfLength r : ℝ) : ℝ :=
  remote * (halfLength + r) / Real.sqrt (r * (2 * halfLength + r))

/-- The Mode III stress-intensity coefficient from the course normalization. -/
noncomputable def stressIntensity (remote halfLength : ℝ) : ℝ :=
  remote * Real.sqrt (Real.pi * halfLength)

end LeanSolid.AntiPlane.Crack
