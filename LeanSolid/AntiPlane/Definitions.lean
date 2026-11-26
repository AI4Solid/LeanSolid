module

public import LeanSolid.LinearElasticity.Definitions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace LeanSolid.AntiPlane

open LeanSolid.Math

/-- Displacement gradient for `u = (0, 0, w)` with no variation in the third direction. -/
noncomputable def gradient (wx wy : ℝ) : Tensor 3 :=
  Matrix.of ![![0, 0, 0], ![0, 0, 0], ![wx, wy, 0]]

/-- The two shear stresses of an anti-plane displacement field. -/
noncomputable def shear (mu : ℝ) (w : Vector 2 → ℝ) (x : Vector 2) : Vector 2 :=
  fun i => mu * partialDeriv w i x

/-- Third component of the divergence of the anti-plane stress. -/
noncomputable def balanceResidual (mu : ℝ) (w : Vector 2 → ℝ) (x : Vector 2) : ℝ :=
  ∑ i, partialDeriv (fun y => shear mu w y i) i x

/-- A screw dislocation displacement on the lifted angular coordinate. -/
noncomputable def screwDisplacement (b θ : ℝ) : ℝ := b / (2 * Real.pi) * θ

/-- Circumferential shear from the angular displacement derivative. -/
noncomputable def polarShear (mu r : ℝ) (w : ℝ → ℝ) (θ : ℝ) : ℝ :=
  mu / r * deriv w θ

end LeanSolid.AntiPlane
