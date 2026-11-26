module

public import LeanSolid.Math.Calculus.Definitions

@[expose] public section

namespace LeanSolid.Plane.Airy

open LeanSolid.Math

noncomputable def normalStressX (φ : Vector 2 → ℝ) : Vector 2 → ℝ :=
  partialDeriv (partialDeriv φ 1) 1

noncomputable def normalStressY (φ : Vector 2 → ℝ) : Vector 2 → ℝ :=
  partialDeriv (partialDeriv φ 0) 0

noncomputable def shearStress (φ : Vector 2 → ℝ) : Vector 2 → ℝ :=
  fun x => -partialDeriv (partialDeriv φ 0) 1 x

/-- Two-dimensional Saint-Venant compatibility residual. -/
noncomputable def compatibility (exx eyy exy : Vector 2 → ℝ) (x : Vector 2) : ℝ :=
  partialDeriv (partialDeriv exx 1) 1 x + partialDeriv (partialDeriv eyy 0) 0 x -
    2 * partialDeriv (partialDeriv exy 0) 1 x

/-- Cartesian in-plane strains from the Airy stresses using compliance coefficients. -/
noncomputable def strainXX (a b : ℝ) (φ : Vector 2 → ℝ) : Vector 2 → ℝ :=
  fun x => a * normalStressX φ x - b * normalStressY φ x

noncomputable def strainYY (a b : ℝ) (φ : Vector 2 → ℝ) : Vector 2 → ℝ :=
  fun x => a * normalStressY φ x - b * normalStressX φ x

noncomputable def strainXY (a b : ℝ) (φ : Vector 2 → ℝ) : Vector 2 → ℝ :=
  fun x => (a + b) * shearStress φ x

end LeanSolid.Plane.Airy
