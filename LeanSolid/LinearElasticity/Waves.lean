module

public import LeanSolid.LinearElasticity.Definitions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring

@[expose] public section

namespace LeanSolid.LinearElasticity.Waves

open LeanSolid.Math
open scoped Matrix

noncomputable section

variable {n : ℕ}

/-- Isotropic acoustic tensor for a unit propagation direction. -/
def acoustic (lam mu : ℝ) (normal : Vector n) : Tensor n :=
  mu • (1 : Tensor n) + (lam + mu) • Matrix.vecMulVec normal normal

theorem acoustic_mulVec (lam mu : ℝ) (normal v : Vector n) :
    acoustic lam mu normal *ᵥ v =
      mu • v + ((lam + mu) * dotProduct normal v) • normal := by
  rw [acoustic, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem longitudinal_mode (lam mu : ℝ) (normal : Vector n) (h : dotProduct normal normal = 1) :
    acoustic lam mu normal *ᵥ normal = (lam + 2 * mu) • normal := by
  rw [acoustic_mulVec, h, mul_one, ← add_smul]
  congr 1
  ring

theorem transverse_mode (lam mu : ℝ) (normal v : Vector n) (h : dotProduct normal v = 0) :
    acoustic lam mu normal *ᵥ v = mu • v := by
  rw [acoustic_mulVec, h, mul_zero, zero_smul, add_zero]

theorem waveSpeed_sq (stiffness density : ℝ) (hρ : 0 < density) (hk : 0 ≤ stiffness) :
    density * (Real.sqrt (stiffness / density)) ^ 2 = stiffness := by
  rw [Real.sq_sqrt (div_nonneg hk hρ.le), mul_comm, div_mul_cancel₀ _ hρ.ne']

/-- A smooth traveling profile solves the one-dimensional wave equation.
The time argument is t and the spatial argument is x. -/
theorem travelingWave (g g' g'' : ℝ → ℝ)
    (hg : ∀ s, HasDerivAt g (g' s) s) (hgg : ∀ s, HasDerivAt g' (g'' s) s)
    (c t x : ℝ) :
    deriv (deriv (fun s => g (x - c * s))) t =
      c ^ 2 * deriv (deriv (fun y => g (y - c * t))) x := by
  have ht (s : ℝ) : HasDerivAt (fun r => x - c * r) (-c) s := by
    have h := (hasDerivAt_const s x).sub ((hasDerivAt_id s).const_mul c)
    change HasDerivAt (fun r => x - c * r) (0 - c * 1) s at h
    simpa only [mul_one, zero_sub] using h
  have hx (y : ℝ) : HasDerivAt (fun r => r - c * t) 1 y :=
    (hasDerivAt_id y).sub_const _
  have ht₁ : deriv (fun s => g (x - c * s)) = fun s => g' (x - c * s) * (-c) := by
    funext s
    exact ((hg _).comp s (ht s)).deriv
  have hx₁ : deriv (fun y => g (y - c * t)) = fun y => g' (y - c * t) := by
    funext y
    have h := ((hg _).comp y (hx y)).deriv
    change deriv (fun r => g (r - c * t)) y = g' (y - c * t) * 1 at h
    simpa only [mul_one] using h
  rw [ht₁, hx₁]
  have htt := (((hgg _).comp t (ht t)).mul_const (-c)).deriv
  have hxx := ((hgg _).comp x (hx x)).deriv
  change deriv (fun s => g' (x - c * s) * (-c)) t = _ at htt
  change deriv (fun y => g' (y - c * t)) x = _ at hxx
  rw [htt, hxx]
  ring

end

end LeanSolid.LinearElasticity.Waves
