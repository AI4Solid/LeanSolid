module

public import LeanSolid.Math.Definitions
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

namespace LeanSolid.Math

variable {n : ℕ}

/-- The time derivative of a Cartesian tensor path, specified entry by entry. -/
def HasTensorDerivAt (A : ℝ → Tensor n) (H : Tensor n) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => A s i j) (H i j) t

/-- Entrywise time derivative. Use `HasTensorDerivAt` to record differentiability. -/
noncomputable def tensorRate (A : ℝ → Tensor n) (t : ℝ) : Tensor n :=
  Matrix.of fun i j => deriv (fun s => A s i j) t

theorem HasTensorDerivAt.eq_tensorRate {A : ℝ → Tensor n} {H : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt A H t) : tensorRate A t = H := by
  ext i j
  exact (h i j).deriv

theorem HasTensorDerivAt.unique {A : ℝ → Tensor n} {H K : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt A H t) (hk : HasTensorDerivAt A K t) : H = K :=
  h.eq_tensorRate.symm.trans hk.eq_tensorRate

theorem HasTensorDerivAt.transpose {A : ℝ → Tensor n} {H : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt A H t) :
    HasTensorDerivAt (fun s => (A s).transpose) H.transpose t :=
  fun i j => h j i

theorem HasTensorDerivAt.mul {A B : ℝ → Tensor n} {H K : Tensor n} {t : ℝ}
    (h : HasTensorDerivAt A H t) (hk : HasTensorDerivAt B K t) :
    HasTensorDerivAt (fun s => A s * B s) (H * B t + A t * K) t := by
  intro i j
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (h i k).mul (hk k j)
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Pi.mul_apply] using hd

theorem hasTensorDerivAt_const (A : Tensor n) (t : ℝ) :
    HasTensorDerivAt (fun _ => A) 0 t :=
  fun i j => hasDerivAt_const t (A i j)

end LeanSolid.Math
