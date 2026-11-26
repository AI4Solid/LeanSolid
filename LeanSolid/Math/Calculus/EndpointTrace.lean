module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section

namespace LeanSolid.Math

/-- The endpoint estimate on a normal line of length `L`. This bounds smooth endpoint
evaluation by the bulk displacement and derivative integrals. -/
theorem endpoint_trace_bound {L : ℝ} (hL : 0 < L) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) :
    L * u L ^ 2 ≤ ∫ x in (0 : ℝ)..L, (1 + L) * u x ^ 2 + L * deriv u x ^ 2 := by
  have hdu := hu.differentiable one_ne_zero
  have hcu := hu.continuous
  have hcdu := hu.continuous_deriv_one
  have hd (x : ℝ) : HasDerivAt (fun y => y * u y ^ 2)
      (u x ^ 2 + 2 * x * u x * deriv u x) x := by
    convert (hasDerivAt_id' x).mul (((hdu x).hasDerivAt).pow 2) using 1
    change u x ^ 2 + 2 * x * u x * deriv u x =
      1 * u x ^ 2 + x * ((2 : ℝ) * u x ^ 1 * deriv u x)
    ring
  have hcont : Continuous (fun x => u x ^ 2 + 2 * x * u x * deriv u x) := by
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hcont.intervalIntegrable 0 L)
  simp only [zero_mul, sub_zero] at hftc
  rw [← hftc]
  have htarget : Continuous (fun x => (1 + L) * u x ^ 2 + L * deriv u x ^ 2) := by
    fun_prop
  refine intervalIntegral.integral_mono_on hL.le (hcont.intervalIntegrable 0 L)
    (htarget.intervalIntegrable 0 L) fun x hx => ?_
  have ha := mul_nonneg hx.1 (sq_nonneg (u x - deriv u x))
  have hb := mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg (sq_nonneg (u x))
    (sq_nonneg (deriv u x)))
  nlinarith only [ha, hb]

/-- Zero displacement at the bottom of a normal slice gives an explicit Poincaré bound. -/
theorem bottom_fixed_slice_poincare {L : ℝ} (hL : 0 < L) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (h₀ : u 0 = 0) :
    (∫ x in (0 : ℝ)..L, u x ^ 2) ≤
      4 * L ^ 2 * ∫ x in (0 : ℝ)..L, deriv u x ^ 2 := by
  have hdu := hu.differentiable one_ne_zero
  have hcu := hu.continuous
  have hcdu := hu.continuous_deriv_one
  have hd (x : ℝ) : HasDerivAt (fun y => (L - y) * u y ^ 2)
      (-u x ^ 2 + 2 * (L - x) * u x * deriv u x) x := by
    have hlin : HasDerivAt (fun y => L - y) (-1) x := by
      rw [show (fun y : ℝ => L - y) = (fun _ : ℝ => L) - (fun y : ℝ => y) by rfl]
      simpa only [zero_sub] using (hasDerivAt_const x L).sub (hasDerivAt_id' x)
    convert hlin.mul (((hdu x).hasDerivAt).pow 2) using 1
    change -u x ^ 2 + 2 * (L - x) * u x * deriv u x =
      -1 * u x ^ 2 + (L - x) * ((2 : ℝ) * u x ^ 1 * deriv u x)
    ring
  let F := fun x => -u x ^ 2 + 2 * (L - x) * u x * deriv u x
  let G := fun x => -(1 / 2 : ℝ) * u x ^ 2 + (2 * L ^ 2) * deriv u x ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hzero : ∫ x in (0 : ℝ)..L, F x = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hF.intervalIntegrable 0 L)]
    simp [h₀]
  have hle : (∫ x in (0 : ℝ)..L, F x) ≤ ∫ x in (0 : ℝ)..L, G x := by
    refine intervalIntegral.integral_mono_on hL.le (hF.intervalIntegrable 0 L)
      (hG.intervalIntegrable 0 L) fun x hx => ?_
    dsimp [F, G]
    have hs := sq_nonneg (u x - 2 * (L - x) * deriv u x)
    have hbound : (L - x) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ (sub_nonneg.mpr hx.2) (sub_le_self L hx.1) 2
    have hm := mul_le_mul_of_nonneg_right hbound (sq_nonneg (deriv u x))
    nlinarith only [hs, hm]
  rw [hzero] at hle
  dsimp [G] at hle
  have h1 : Continuous (fun x => -(1 / 2 : ℝ) * u x ^ 2) := by fun_prop
  have h2 : Continuous (fun x => (2 * L ^ 2) * deriv u x ^ 2) := by fun_prop
  rw [intervalIntegral.integral_add (h1.intervalIntegrable 0 L)
    (h2.intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hle
  linarith only [hle]

end LeanSolid.Math
