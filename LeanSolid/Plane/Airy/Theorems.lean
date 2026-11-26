module

public import LeanSolid.Plane.Airy.Definitions
public import LeanSolid.Math.Calculus.Theorems
import Mathlib.Tactic.Ring

public section

open scoped ContDiff

namespace LeanSolid.Plane.Airy

open LeanSolid.Math

variable {φ : Vector 2 → ℝ}

theorem shearStress_eq (φ : Vector 2 → ℝ) :
    shearStress φ = fun x => -partialDeriv (partialDeriv φ 0) 1 x := rfl

theorem strainXX_eq (a b : ℝ) (φ : Vector 2 → ℝ) :
    strainXX a b φ = fun x => a * normalStressX φ x - b * normalStressY φ x := rfl

theorem strainYY_eq (a b : ℝ) (φ : Vector 2 → ℝ) :
    strainYY a b φ = fun x => a * normalStressY φ x - b * normalStressX φ x := rfl

theorem strainXY_eq (a b : ℝ) (φ : Vector 2 → ℝ) :
    strainXY a b φ = fun x => (a + b) * shearStress φ x := rfl

/-- Airy's first equilibrium equation. Adapted from lean-mechanics, Elastostatics/Airy.lean. -/
theorem equilibrium_x (hφ : ContDiff ℝ 3 φ) (x : Vector 2) :
    partialDeriv (normalStressX φ) 0 x + partialDeriv (shearStress φ) 1 x = 0 := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have h1 : ContDiff ℝ 2 (partialDeriv φ 1) := contDiff_partial hφ (by norm_num) 1
  simp only [normalStressX, shearStress_eq, partial_neg, partial_partial_comm h1 1 0,
    partial_partial_comm h2 1 0]
  ring

/-- Airy's second equilibrium equation. Adapted from lean-mechanics, Elastostatics/Airy.lean. -/
theorem equilibrium_y (hφ : ContDiff ℝ 3 φ) (x : Vector 2) :
    partialDeriv (shearStress φ) 0 x + partialDeriv (normalStressY φ) 1 x = 0 := by
  have h0 : ContDiff ℝ 2 (partialDeriv φ 0) := contDiff_partial hφ (by norm_num) 0
  simp only [normalStressY, shearStress_eq, partial_neg, partial_partial_comm h0 0 1]
  ring

/-- Compatibility residual of an Airy field, following lean-mechanics, Elastostatics/Airy.lean. -/
theorem compatibility_eq_biharmonic (a b : ℝ) (hφ : ContDiff ℝ 4 φ) (x : Vector 2) :
    compatibility (strainXX a b φ) (strainYY a b φ) (strainXY a b φ) x =
      a * biharmonic φ x := by
  have c2 : ∀ i j, ContDiff ℝ 2 (partialDeriv (partialDeriv φ i) j) := fun i j =>
    contDiff_partial (contDiff_partial hφ (k := 3) (by norm_num) i) (by norm_num) j
  have c3 : ∀ i j k, ContDiff ℝ 1 (partialDeriv (partialDeriv (partialDeriv φ i) j) k) :=
    fun i j k => contDiff_partial (c2 i j) (by norm_num) k
  have d2 : ∀ i j, Differentiable ℝ (partialDeriv (partialDeriv φ i) j) :=
    fun i j => (c2 i j).differentiable (by norm_num)
  have d3 : ∀ i j k, Differentiable ℝ (partialDeriv (partialDeriv (partialDeriv φ i) j) k) :=
    fun i j k => (c3 i j k).differentiable one_ne_zero
  have hh0 : ContDiff ℝ 2 (partialDeriv φ 0) := contDiff_partial hφ (by norm_num) 0
  have hh1 : ContDiff ℝ 2 (partialDeriv φ 1) := contDiff_partial hφ (by norm_num) 1
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have e1 :
      partialDeriv (partialDeriv (partialDeriv (partialDeriv φ 0) 1) 0) 1 =
      partialDeriv (partialDeriv (partialDeriv (partialDeriv φ 0) 0) 1) 1 := by
    rw [partial_partial_comm hh0 1 0]
  have e2 :
      partialDeriv (partialDeriv (partialDeriv (partialDeriv φ 1) 1) 0) 0 =
      partialDeriv (partialDeriv (partialDeriv (partialDeriv φ 0) 0) 1) 1 := by
    rw [partial_partial_comm hh1 1 0, partial_partial_comm h2 1 0,
      partial_partial_comm (c2 0 1) 1 0, partial_partial_comm hh0 1 0]
  simp only [compatibility, strainXX_eq, strainYY_eq, strainXY_eq, normalStressX,
    normalStressY, shearStress_eq]
  have := d2 0 0
  have := d2 1 1
  have := d2 0 1
  have := d3 1 1 1
  have := d3 0 0 1
  have := d3 0 0 0
  have := d3 1 1 0
  have := d3 0 1 0
  simp (disch := assumption) only [partial_linear_sub]
  simp (disch := fun_prop) only [partial_mul, partial_const, partial_neg,
    zero_mul, zero_add]
  simp only [biharmonic, Fin.sum_univ_two, e1, e2]
  ring

theorem compatible_iff_biharmonic {a : ℝ} (b : ℝ) (ha : a ≠ 0) (hφ : ContDiff ℝ 4 φ) :
    (∀ x, compatibility (strainXX a b φ) (strainYY a b φ) (strainXY a b φ) x = 0) ↔
      ∀ x, biharmonic φ x = 0 := by
  simp only [compatibility_eq_biharmonic a b hφ, mul_eq_zero, ha, false_or]

end LeanSolid.Plane.Airy
