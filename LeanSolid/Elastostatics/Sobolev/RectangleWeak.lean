module

public import LeanSolid.Elastostatics.Sobolev.RectangleTrace
public import LeanSolid.Elastostatics.Sobolev.Existence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

@[expose] public section

open scoped InnerProductSpace

namespace LeanSolid.Elastostatics.Rectangle

variable {a b L : ℝ}

abbrev Gradient (a b L : ℝ) := WithLp 2 (Vec (Interior a b L) × Vec (Interior a b L))
abbrev Strain (a b L : ℝ) := Vec (Vec (Interior a b L))

/-- The two derivative columns of a rectangular displacement–gradient pair. -/
noncomputable def gradient : Graph a b L →L[ℝ] Gradient a b L := WithLp.sndL 2 ℝ _ _

/-- Component `i` of derivative column `j`, with column zero tangential and column one normal. -/
noncomputable def derivativeEntry (i j : Fin 2) : Graph a b L →L[ℝ] Interior a b L :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 2 => Interior a b L) i).comp
    ((if j = 0 then WithLp.fstL 2 ℝ (Vec (Interior a b L)) (Vec (Interior a b L))
      else WithLp.sndL 2 ℝ (Vec (Interior a b L)) (Vec (Interior a b L))).comp gradient)

/-- Symmetric part of the rectangle gradient using its Cartesian derivative columns. -/
noncomputable def rectangleStrain : Graph a b L →L[ℝ] Strain a b L :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => Vec (Interior a b L))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => Interior a b L)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun j => (1 / 2 : ℝ) • (derivativeEntry i j + derivativeEntry j i)))

/-- Sum of the diagonal entries of the rectangle gradient. -/
noncomputable def rectangleDiv : Graph a b L →L[ℝ] Interior a b L :=
  derivativeEntry 0 0 + derivativeEntry 1 1

theorem rectangleStrain_apply (U : Graph a b L) (i j : Fin 2) :
    rectangleStrain U i j =
      (1 / 2 : ℝ) • (derivativeEntry i j U + derivativeEntry j i U) := by
  simp [rectangleStrain]

theorem rectangleDiv_apply (U : Graph a b L) :
    rectangleDiv U = derivativeEntry 0 0 U + derivativeEntry 1 1 U := rfl

/-- Bottom Poincaré reduces the full trial norm estimate to control of the gradient. -/
theorem trial_norm_sq_le_gradient (hL : 0 < L) (u : Trials a b) :
    ‖trialGraph a b L u‖ ^ 2 ≤ (1 + 4 * L ^ 2) * ‖gradient (trialGraph a b L u)‖ ^ 2 := by
  let U := trialGraph a b L u
  have hp := trial_normal_poincare hL u
  have hn : ‖U.snd.snd‖ ^ 2 ≤ ‖U.snd‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left hn (show 0 ≤ 4 * L ^ 2 by positivity)
  change ‖U‖ ^ 2 ≤ (1 + 4 * L ^ 2) * ‖U.snd‖ ^ 2
  rw [WithLp.prod_norm_sq_eq_of_L2]
  linarith only [hp.trans h]

/-- A uniform Korn estimate on smooth trials passes to the completed graph space
with the same constant. -/
theorem rectangle_korn_of_trials {K : ℝ}
    (h : ∀ u : Trials a b, ‖trialGraph a b L u‖ ≤ K * ‖rectangleStrain (trialGraph a b L u)‖)
    (U : bottomFixedSpace a b L) : ‖U‖ ≤ K * ‖rectangleStrain (U : Graph a b L)‖ := by
  have hclosed : IsClosed {W : Graph a b L | ‖W‖ ≤ K * ‖rectangleStrain W‖} :=
    isClosed_le continuous_norm (continuous_const.mul rectangleStrain.continuous.norm)
  have hsubset : Set.range (trialGraph a b L) ⊆
      {W : Graph a b L | ‖W‖ ≤ K * ‖rectangleStrain W‖} := by
    rintro _ ⟨u, rfl⟩
    exact h u
  have hmem : (U : Graph a b L) ∈ closure (Set.range (trialGraph a b L)) := by
    rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
    exact U.property
  exact closure_minimal hsubset hclosed hmem

/-- The rectangular Lamé bilinear form restricted to the bottom-fixed variation space. -/
noncomputable def rectangleLameForm (μ lam : ℝ) :
    bottomFixedSpace a b L →L[ℝ] bottomFixedSpace a b L →L[ℝ] ℝ :=
  Sobolev.lameForm (V := bottomFixedSpace a b L)
    ((rectangleStrain (a := a) (b := b) (L := L)).comp (bottomFixedSpace a b L).subtypeL)
    ((rectangleDiv (a := a) (b := b) (L := L)).comp (bottomFixedSpace a b L).subtypeL) μ lam

/-- Weak equilibrium with prescribed top traction, zero bottom displacement, and no lateral
traction term. A continuous body load can also be supplied. -/
def IsRectangleWeakSolution (hL : 0 < L) (μ lam : ℝ) (t : Vec (Edge a b))
    (body : bottomFixedSpace a b L →L[ℝ] ℝ) (U : bottomFixedSpace a b L) : Prop :=
  ∀ V : bottomFixedSpace a b L,
    rectangleLameForm μ lam U V = body V + topTractionLoad hL t V

set_option maxHeartbeats 800000 in
/-- A quantitative Korn estimate on the concrete bottom-fixed graph implies existence and
uniqueness for the rectangular top-traction problem. -/
theorem existsUnique_rectangle_of_korn (hL : 0 < L) {μ lam K : ℝ}
    (hμ : 0 < μ) (hlam : 0 ≤ lam) (hK : 0 < K)
    (hkorn : ∀ U : bottomFixedSpace a b L, ‖U‖ ≤ K * ‖rectangleStrain (U : Graph a b L)‖)
    (t : Vec (Edge a b)) (body : bottomFixedSpace a b L →L[ℝ] ℝ) :
    ∃! U, IsRectangleWeakSolution hL μ lam t body U := by
  let : CompleteSpace (bottomFixedSpace a b L) :=
    (Submodule.isClosed_topologicalClosure (LinearMap.range (trialGraph a b L))).completeSpace_coe
  have hcoer (U : bottomFixedSpace a b L) :
      2 * μ / K ^ 2 * ‖U‖ ^ 2 ≤ rectangleLameForm μ lam U U := by
    rw [rectangleLameForm, Sobolev.lameForm_self]
    change 2 * μ / K ^ 2 * ‖U‖ ^ 2 ≤
      2 * μ * ‖rectangleStrain (U : Graph a b L)‖ ^ 2 +
        lam * ‖rectangleDiv (U : Graph a b L)‖ ^ 2
    have hs := pow_le_pow_left₀ (norm_nonneg U) (hkorn U) 2
    rw [mul_pow] at hs
    have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * μ / K ^ 2 by positivity)
    rw [← mul_assoc (2 * μ / K ^ 2), div_mul_cancel₀ _ (pow_ne_zero _ hK.ne')] at h
    exact h.trans (le_add_of_nonneg_right (mul_nonneg hlam (sq_nonneg _)))
  have h := Sobolev.existsUnique_lame (by positivity : 0 < 2 * μ / K ^ 2) hcoer
    (body + topTractionLoad hL t)
  simpa only [IsRectangleWeakSolution, rectangleLameForm, add_apply] using h

/-- To close the mixed problem it suffices to prove the estimate on smooth bottom-fixed
displacements, before passing to the graph closure. -/
theorem existsUnique_rectangle_of_trial_korn (hL : 0 < L) {μ lam K : ℝ}
    (hμ : 0 < μ) (hlam : 0 ≤ lam) (hK : 0 < K)
    (hkorn : ∀ u : Trials a b,
      ‖trialGraph a b L u‖ ≤ K * ‖rectangleStrain (trialGraph a b L u)‖)
    (t : Vec (Edge a b)) (body : bottomFixedSpace a b L →L[ℝ] ℝ) :
    ∃! U, IsRectangleWeakSolution hL μ lam t body U :=
  existsUnique_rectangle_of_korn hL hμ hlam hK (rectangle_korn_of_trials hkorn) t body

end LeanSolid.Elastostatics.Rectangle
