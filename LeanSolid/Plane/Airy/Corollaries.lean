/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Elastostatics/Airy.lean at 7e41dfe
   (Apache-2.0), specifically compat_planeStress and compat_planeStrain. -/
module

public import LeanSolid.Plane.Airy.Theorems
import Mathlib.Tactic.Ring

public section

open LeanSolid.Math

namespace LeanSolid.Plane.Airy

/-- For plane stress with Young's modulus `E` and Poisson ratio `ν`, the Airy
compatibility residual is `Δ²φ / E`. -/
theorem compatibility_planeStress {φ : Vector 2 → ℝ} (E ν : ℝ)
    (hφ : ContDiff ℝ 4 φ) (x : Vector 2) :
    compatibility (strainXX (1 / E) (ν / E) φ) (strainYY (1 / E) (ν / E) φ)
      (strainXY (1 / E) (ν / E) φ) x = biharmonic φ x / E := by
  rw [compatibility_eq_biharmonic _ _ hφ]
  ring

/-- For plane strain with Young's modulus `E` and Poisson ratio `ν`, the Airy
compatibility residual is `((1 - ν²) / E) Δ²φ`. -/
theorem compatibility_planeStrain {φ : Vector 2 → ℝ} (E ν : ℝ)
    (hφ : ContDiff ℝ 4 φ) (x : Vector 2) :
    compatibility
      (strainXX ((1 - ν ^ 2) / E) (ν * (1 + ν) / E) φ)
      (strainYY ((1 - ν ^ 2) / E) (ν * (1 + ν) / E) φ)
      (strainXY ((1 - ν ^ 2) / E) (ν * (1 + ν) / E) φ) x =
        (1 - ν ^ 2) / E * biharmonic φ x :=
  compatibility_eq_biharmonic _ _ hφ x

end LeanSolid.Plane.Airy
