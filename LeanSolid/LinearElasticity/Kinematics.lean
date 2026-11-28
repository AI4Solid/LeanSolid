module

public import LeanSolid.LinearElasticity.Theorems
public import LeanSolid.Math.Calculus.Theorems
public import LeanSolid.Plane.Airy.Definitions
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul

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


/-- Divergence of the constant-coefficient isotropic stress in Cartesian coordinates. -/
theorem tensorDivergence_stress_strainField (lam mu : ℝ) (u : Vector n → Vector n)
    (hu : ∀ i, ContDiff ℝ 2 (fun x => u x i)) (x : Vector n) (i : Fin n) :
    tensorDivergence (fun y => stress lam mu (strainField u y)) x i =
      mu * laplacian (fun y => u y i) x +
      (lam + mu) * partialDeriv (fun y => ∑ j, partialDeriv (fun z => u z j) j y) i x := by
  classical
  let D (k j : Fin n) := partialDeriv (fun y => u y k) j
  let divU (y : Vector n) := ∑ j, D j j y
  have hd (k j : Fin n) : Differentiable ℝ (D k j) :=
    (contDiff_partial (hu k) (k := 1) (by norm_num) j).differentiable one_ne_zero
  have hdiv : Differentiable ℝ divU := Differentiable.fun_sum (fun j _ => hd j j)
  have htrace (y : Vector n) : (strainField u y).trace = divU y := by
    unfold Matrix.trace divU
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.diag_apply, strainField_apply]
    change (1 / 2 : ℝ) * (D j j y + D j j y) = D j j y
    ring
  have hstress (j : Fin n) :
      (fun y => stress lam mu (strainField u y) i j) =
      (fun y => (if i = j then lam else 0) * divU y +
        mu * (D i j y + D j i y)) := by
    funext y
    simp only [stress, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, htrace,
      strainField_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp only [h, ite_true, ite_false] <;> ring
  have hpartial (j : Fin n) :
      partialDeriv (fun y => stress lam mu (strainField u y) i j) j x =
      (if i = j then lam else 0) * partialDeriv divU j x +
        mu * (partialDeriv (D i j) j x + partialDeriv (D j j) i x) := by
    have h₁ : Differentiable ℝ (fun y => (if i = j then lam else 0) * divU y) :=
      (differentiable_const _).mul hdiv
    have hD : Differentiable ℝ (fun y => D i j y + D j i y) := (hd i j).add (hd j i)
    have h₂ : Differentiable ℝ (fun y => mu * (D i j y + D j i y)) :=
      (differentiable_const _).mul hD
    rw [hstress, partial_add h₁ h₂,
      partial_const_mul _ hdiv, partial_const_mul _ hD,
      partial_add (hd i j) (hd j i), partial_partial_comm (hu j) i j]
  have hsum : partialDeriv divU i x = ∑ j, partialDeriv (D j j) i x := by
    simp [divU, partialDeriv, fderiv_fun_sum (fun j _ => hd j j x)]
  unfold tensorDivergence laplacian
  simp only [hpartial, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdiag : (∑ j, (if i = j then lam else 0) * partialDeriv divU j x) =
      lam * partialDeriv divU i x := by
    simp [ite_mul]
  change _ = _ + (lam + mu) * partialDeriv divU i x
  rw [hdiag, hsum]
  ring

end LeanSolid.LinearElasticity
