module

public import LeanSolid.LinearElasticity.Theorems
public import LeanSolid.Math.Calculus.Theorems
public import LeanSolid.Plane.Airy.Definitions
import Mathlib.Tactic.Ring

public section

open scoped ContDiff

namespace LeanSolid.LinearElasticity

open LeanSolid.Math

variable {n : ℕ}

theorem strainField_apply (u : Vector n → Vector n) (x : Vector n) (i j : Fin n) :
    strainField u x i j =
      (1 / 2 : ℝ) * (partialDeriv (fun y => u y i) j x +
        partialDeriv (fun y => u y j) i x) := rfl

theorem strainField_symm (u : Vector n → Vector n) (x : Vector n) :
    (strainField u x).transpose = strainField u x :=
  strain_transpose (displacementGradient u x)

theorem strainField_of_skew_gradient (u : Vector n → Vector n) (x : Vector n)
    (h : (displacementGradient u x).transpose = -displacementGradient u x) :
    strainField u x = 0 :=
  (symPart_eq_zero_iff _).2 h

theorem stressField_symm (lam mu : ℝ) (u : Vector n → Vector n) (x : Vector n) :
    (stress lam mu (strainField u x)).transpose = stress lam mu (strainField u x) :=
  stress_transpose lam mu _ (strainField_symm u x)

/-- Any smooth planar displacement induces a compatible small strain. -/
theorem planeCompatibility_of_displacement (u : Vector 2 → Vector 2)
    (hu : ∀ i, ContDiff ℝ 3 (fun x => u x i)) (x : Vector 2) :
    Plane.Airy.compatibility (fun y => strainField u y 0 0)
      (fun y => strainField u y 1 1) (fun y => strainField u y 0 1) x = 0 := by
  let u₀ : Vector 2 → ℝ := fun y => u y 0
  let u₁ : Vector 2 → ℝ := fun y => u y 1
  have h₀ : ContDiff ℝ 3 u₀ := hu 0
  have h₁ : ContDiff ℝ 3 u₁ := hu 1
  have d₀ (j : Fin 2) : ContDiff ℝ 2 (partialDeriv u₀ j) :=
    contDiff_partial h₀ (by norm_num) j
  have d₁ (j : Fin 2) : ContDiff ℝ 2 (partialDeriv u₁ j) :=
    contDiff_partial h₁ (by norm_num) j
  have hxx : (fun y => strainField u y 0 0) = partialDeriv u₀ 0 := by
    funext y
    rw [strainField_apply]
    change (1 / 2 : ℝ) * (partialDeriv u₀ 0 y + partialDeriv u₀ 0 y) =
      partialDeriv u₀ 0 y
    ring
  have hyy : (fun y => strainField u y 1 1) = partialDeriv u₁ 1 := by
    funext y
    rw [strainField_apply]
    change (1 / 2 : ℝ) * (partialDeriv u₁ 1 y + partialDeriv u₁ 1 y) =
      partialDeriv u₁ 1 y
    ring
  have hxy : (fun y => strainField u y 0 1) =
      (fun y => (1 / 2 : ℝ) * (partialDeriv u₀ 1 y + partialDeriv u₁ 0 y)) := by
    funext y
    exact strainField_apply u y 0 1
  have he₀ := (d₀ 1).differentiable (by norm_num)
  have he₁ := (d₁ 0).differentiable (by norm_num)
  have hf₀ := (contDiff_partial (d₀ 1) (k := 1) (by norm_num) 0).differentiable one_ne_zero
  have hf₁ := (contDiff_partial (d₁ 0) (k := 1) (by norm_num) 0).differentiable one_ne_zero
  have he : Differentiable ℝ (fun y => partialDeriv u₀ 1 y + partialDeriv u₁ 0 y) :=
    he₀.add he₁
  have hf : Differentiable ℝ (fun y =>
      partialDeriv (partialDeriv u₀ 1) 0 y + partialDeriv (partialDeriv u₁ 0) 0 y) :=
    hf₀.add hf₁
  rw [hxx, hyy, hxy, Plane.Airy.compatibility, partial_const_mul _ he 0,
    partial_add he₀ he₁ 0, partial_const_mul _ hf 1, partial_add hf₀ hf₁ 1]
  rw [partial_partial_comm (h₀.of_le (by norm_num) : ContDiff ℝ 2 u₀) 0 1,
    partial_partial_comm (h₁.of_le (by norm_num) : ContDiff ℝ 2 u₁) 1 0,
    partial_partial_comm (d₁ 0) 1 0]
  ring

end LeanSolid.LinearElasticity
