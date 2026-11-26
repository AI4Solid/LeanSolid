module

public import LeanSolid.Math.Calculus.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

open scoped ContDiff

namespace LeanSolid.Math

variable {n : ℕ} {f : Vector n → ℝ}

theorem contDiff_partial {k m : WithTop ℕ∞} (hf : ContDiff ℝ m f)
    (hk : k + 1 ≤ m) (j : Fin n) : ContDiff ℝ k (partialDeriv f j) :=
  (hf.fderiv_right hk).clm_apply contDiff_const

theorem partial_neg (f : Vector n → ℝ) (j : Fin n) :
    partialDeriv (fun x => -f x) j = fun x => -partialDeriv f j x := by
  funext x
  simp [partialDeriv]

theorem partial_const (c : ℝ) (j : Fin n) :
    partialDeriv (fun _ => c) j = fun _ => 0 := by
  funext x
  simp [partialDeriv]

theorem partial_add {g : Vector n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    partialDeriv (fun x => f x + g x) j =
      fun x => partialDeriv f j x + partialDeriv g j x := by
  funext x
  simp [partialDeriv, fderiv_fun_add (hf x) (hg x)]

theorem partial_sub {g : Vector n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    partialDeriv (fun x => f x - g x) j =
      fun x => partialDeriv f j x - partialDeriv g j x := by
  funext x
  simp [partialDeriv, fderiv_fun_sub (hf x) (hg x)]

theorem partial_mul {g : Vector n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    partialDeriv (fun x => f x * g x) j =
      fun x => partialDeriv f j x * g x + f x * partialDeriv g j x := by
  funext x
  simp [partialDeriv, fderiv_fun_mul (hf x) (hg x)]
  ring

theorem partial_const_mul (c : ℝ) (hf : Differentiable ℝ f) (j : Fin n) :
    partialDeriv (fun x => c * f x) j = fun x => c * partialDeriv f j x := by
  rw [partial_mul (differentiable_const c) hf, partial_const]
  simp

theorem partial_linear_sub {g : Vector n → ℝ} (a b : ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (j : Fin n) :
    partialDeriv (fun x => a * f x - b * g x) j =
      fun x => a * partialDeriv f j x - b * partialDeriv g j x := by
  rw [partial_sub (hf.const_mul a) (hg.const_mul b),
    partial_const_mul a hf, partial_const_mul b hg]

/-- Adapted from lean-mechanics, Elastostatics/Korn.lean (Apache-2.0). -/
theorem partial_partial_comm (hf : ContDiff ℝ 2 f) (i j : Fin n) :
    partialDeriv (partialDeriv f i) j = partialDeriv (partialDeriv f j) i := by
  funext x
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single j 1) =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) x (Pi.single i 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd
    (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hs _ _

end LeanSolid.Math
