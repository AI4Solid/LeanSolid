/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Fluids/Hydrostatics.lean
at 7e41dfe (Apache-2.0). -/
module

public import LeanSolid.ContinuumMechanics.NewtonianFluid
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FinCases

@[expose] public section

namespace LeanSolid.ContinuumMechanics.Hydrostatics

open LeanSolid.Math

def gravity (g : ℝ) : Vector 3 := ![0, 0, -g]

def pressure (p₀ ρ g : ℝ) (x : Vector 3) : ℝ := p₀ - ρ * g * x 2

theorem hasFDerivAt_pressure (p₀ ρ g : ℝ) (x : Vector 3) :
    HasFDerivAt (pressure p₀ ρ g)
      (-((ρ * g) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2)) x :=
  ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x).const_mul (ρ * g)).const_sub p₀

theorem partialDeriv_pressure (p₀ ρ g : ℝ) (x : Vector 3) (j : Fin 3) :
    partialDeriv (pressure p₀ ρ g) j x = ρ * gravity g j := by
  rw [partialDeriv, (hasFDerivAt_pressure p₀ ρ g x).fderiv]
  fin_cases j <;> simp [gravity]

/-- A resting fluid satisfies Cauchy momentum balance under the constant gravitational force. -/
theorem equilibrium (p₀ ρ g μ : ℝ) (x : Vector 3) (i : Fin 3) :
    tensorDivergence (fun y => NewtonianFluid.stress (pressure p₀ ρ g y) μ
      (rateOfDeformation (deformationGradient (fun _ => (0 : Vector 3)) y))) x i
      + ρ * gravity g i = 0 := by
  rw [NewtonianFluid.tensorDivergence_stress_incompressible
    (pressure p₀ ρ g) μ (fun _ => 0) (fun y => (hasFDerivAt_pressure p₀ ρ g y).differentiableAt)
    (by intro j; exact contDiff_const)
    (by intro y; simp [spatialDivergence, deformationGradient, Matrix.trace, partialDeriv]),
    partialDeriv_pressure]
  have hconst (j : Fin 3) :
      partialDeriv (fun _ : Vector 3 => (0 : ℝ)) j = fun _ => 0 := by
    funext y
    simp [partialDeriv]
  change μ * laplacian (fun _ : Vector 3 => (0 : ℝ)) x - _ + _ = 0
  simp [laplacian, hconst]

/-- Integration over the rectangular horizontal faces gives the upward pressure force. -/
theorem box_buoyancy (p₀ ρ g x₁ x₂ y₁ y₂ z₁ z₂ : ℝ) :
    (∫ a in x₁..x₂, ∫ b in y₁..y₂,
      (pressure p₀ ρ g ![a, b, z₁] - pressure p₀ ρ g ![a, b, z₂])) =
      ρ * g * ((x₂ - x₁) * (y₂ - y₁) * (z₂ - z₁)) := by
  have h (a b : ℝ) :
      pressure p₀ ρ g ![a, b, z₁] - pressure p₀ ρ g ![a, b, z₂] =
        ρ*g*(z₂-z₁) := by
    change (p₀-ρ*g*z₁)-(p₀-ρ*g*z₂) = _
    ring
  simp only [h]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

end LeanSolid.ContinuumMechanics.Hydrostatics
