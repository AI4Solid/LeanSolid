module

public import LeanSolid.Elastostatics.Sobolev.Existence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

open scoped InnerProductSpace

namespace LeanSolid.Elastostatics.Sobolev

variable {n : ℕ} {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]

/-- Virtual work of a traction paired with a supplied continuous face trace. -/
noncomputable def tractionLoad (V : Submodule ℝ (G n)) (trace : V →L[ℝ] B)
    (traction : B) : V →L[ℝ] ℝ :=
  (innerSL ℝ traction).comp trace

/-- Mixed weak equilibrium on the supplied space of zero-displacement variations.
Only the supplied trace contributes surface work. -/
def IsMixedWeakSolution (V : Submodule ℝ (G n)) (μ lam : ℝ) (trace : V →L[ℝ] B)
    (traction : B) (body : V →L[ℝ] ℝ) (U : V) : Prop :=
  ∀ W : V, lameForm strain div μ lam (U : G n) (W : G n) =
    body W + tractionLoad V trace traction W

/-- A continuous trace and a Korn estimate on the mixed variation space give a unique
mixed weak solution for nonnegative first Lamé parameter. -/
theorem existsUnique_mixed_of_korn (V : Submodule ℝ (G n)) [CompleteSpace V]
    {μ lam K : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam) (hK : 0 < K)
    (hkorn : ∀ W : V, ‖W‖ ≤ K * ‖strain (W : G n)‖)
    (trace : V →L[ℝ] B) (traction : B) (body : V →L[ℝ] ℝ) :
    ∃! U : V, IsMixedWeakSolution V μ lam trace traction body U := by
  let ε := (strain (n := n)).comp V.subtypeL
  let d := (div (n := n)).comp V.subtypeL
  have hcoer (W : V) : (2 * μ / K ^ 2) * ‖W‖ ^ 2 ≤ lameForm ε d μ lam W W := by
    rw [lameForm_self]
    change 2 * μ / K ^ 2 * ‖W‖ ^ 2 ≤
      2 * μ * ‖strain (W : G n)‖ ^ 2 + lam * ‖div (W : G n)‖ ^ 2
    have hs := pow_le_pow_left₀ (norm_nonneg W) (hkorn W) 2
    rw [mul_pow] at hs
    have hbound := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * μ / K ^ 2 by positivity)
    have hcancel : (2 * μ / K ^ 2) * (K ^ 2 * ‖strain (W : G n)‖ ^ 2) =
        2 * μ * ‖strain (W : G n)‖ ^ 2 := by
      rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hK.ne')]
    rw [hcancel] at hbound
    exact hbound.trans (le_add_of_nonneg_right (mul_nonneg hlam (sq_nonneg _)))
  have h := existsUnique_lame (by positivity : 0 < 2 * μ / K ^ 2) hcoer
    (body + tractionLoad V trace traction)
  simpa only [IsMixedWeakSolution, lameForm_apply, ε, d, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, add_apply] using h

end LeanSolid.Elastostatics.Sobolev
