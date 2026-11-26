/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Elastostatics/Korn.lean at 7e41dfe (Apache-2.0). -/
module

public import LeanSolid.Math.Calculus.Definitions
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section

noncomputable section

namespace LeanSolid.Elastostatics.Korn

open LeanSolid.Math
open MeasureTheory
open scoped ContDiff

variable {n : ℕ}

/-- The squared norm of the gradient, `|∇u|² = Σᵢⱼ (∂ⱼuᵢ)²`. -/
def gradSq (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, partialDeriv (u i) j x ^ 2

/-- The squared norm of the strain, `|ε|² = Σᵢⱼ ((∂ⱼuᵢ + ∂ᵢuⱼ)/2)²`. -/
def strainSq (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ((partialDeriv (u i) j x + partialDeriv (u j) i x) / 2) ^ 2

/-- The divergence `div u = Σᵢ ∂ᵢuᵢ`. -/
def div (u : Fin n → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, partialDeriv (u i) i x

end LeanSolid.Elastostatics.Korn
