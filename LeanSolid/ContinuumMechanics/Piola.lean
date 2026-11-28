module

public import LeanSolid.ContinuumMechanics.Area
import LeanSolid.Math.Calculus.Theorems
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

open scoped Matrix ContDiff

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

private theorem divergence_cross_gradients (f g : Vector 3 → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (X : Vector 3) :
    (∑ j, partialDeriv (fun Y =>
      ((fun i => partialDeriv f i Y) ⨯₃ (fun i => partialDeriv g i Y)) j) j X) = 0 := by
  let p := partialDeriv f
  let q := partialDeriv g
  have hp (i : Fin 3) : Differentiable ℝ (p i) :=
    (contDiff_partial hf (k := 1) (by norm_num) i).differentiable one_ne_zero
  have hq (i : Fin 3) : Differentiable ℝ (q i) :=
    (contDiff_partial hg (k := 1) (by norm_num) i).differentiable one_ne_zero
  have hprod (i j k l m : Fin 3) :
      partialDeriv (fun Y => p i Y * q j Y - p k Y * q l Y) m X =
      partialDeriv (p i) m X * q j X + p i X * partialDeriv (q j) m X -
        (partialDeriv (p k) m X * q l X + p k X * partialDeriv (q l) m X) := by
    have h₁ : Differentiable ℝ (fun Y => p i Y * q j Y) := (hp i).mul (hq j)
    have h₂ : Differentiable ℝ (fun Y => p k Y * q l Y) := (hp k).mul (hq l)
    rw [partial_sub h₁ h₂, partial_mul (hp i) (hq j), partial_mul (hp k) (hq l)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change partialDeriv (fun Y => p 1 Y * q 2 Y - p 2 Y * q 1 Y) 0 X +
    (partialDeriv (fun Y => p 2 Y * q 0 Y - p 0 Y * q 2 Y) 1 X +
      partialDeriv (fun Y => p 0 Y * q 1 Y - p 1 Y * q 0 Y) 2 X) = 0
  simp only [hprod, p, q]
  simp only [partial_partial_comm hf 1 0, partial_partial_comm hf 2 0,
    partial_partial_comm hf 2 1, partial_partial_comm hg 1 0,
    partial_partial_comm hg 2 0, partial_partial_comm hg 2 1]
  ring

/-- Differential Piola identity in three dimensions. The cofactor field of a C² placement
has zero reference divergence, without any invertibility assumption. -/
theorem tensorDivergence_cofactor_deformationGradient
    (χ : Vector 3 → Vector 3) (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i)) (X : Vector 3) :
    tensorDivergence (fun Y => (deformationGradient χ Y).adjugate.transpose) X = 0 := by
  let a : Fin 3 → Fin 3 := ![1, 2, 0]
  let b : Fin 3 → Fin 3 := ![2, 0, 1]
  have hrow (i j : Fin 3) :
      (fun Y => (deformationGradient χ Y).adjugate.transpose i j) =
      (fun Y => ((fun k => partialDeriv (fun Z => χ Z (a i)) k Y) ⨯₃
        (fun k => partialDeriv (fun Z => χ Z (b i)) k Y)) j) := by
    funext Y
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.transpose_apply, Matrix.adjugate_fin_three, deformationGradient, cross_apply, a, b] <;>
      ring
  funext i
  change (∑ j, partialDeriv (fun Y => (deformationGradient χ Y).adjugate.transpose i j) j X) = 0
  simp only [hrow]
  exact divergence_cross_gradients _ _ (hχ (a i)) (hχ (b i)) X

/-- The inverse-transpose form of the Piola identity for nonsingular placements. -/
theorem tensorDivergence_jacobian_smul_invTranspose
    (χ : Vector 3 → Vector 3) (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i))
    (hJ : ∀ X, jacobian (deformationGradient χ X) ≠ 0) (X : Vector 3) :
    tensorDivergence (fun Y =>
      jacobian (deformationGradient χ Y) • ((deformationGradient χ Y)⁻¹).transpose) X = 0 := by
  have he : (fun Y => (deformationGradient χ Y).adjugate.transpose) =
      (fun Y => jacobian (deformationGradient χ Y) • ((deformationGradient χ Y)⁻¹).transpose) :=
    funext fun Y => cofactor_eq_jacobian_smul_invTranspose _ (hJ Y)
  rw [← he]
  exact tensorDivergence_cofactor_deformationGradient χ hχ X

end LeanSolid.ContinuumMechanics
