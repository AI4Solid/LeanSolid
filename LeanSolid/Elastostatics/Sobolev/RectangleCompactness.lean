module

public import LeanSolid.Elastostatics.Sobolev.RectangleKorn
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import LeanSolid.Math.Calculus.Wirtinger
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

open Filter Set MeasureTheory
open scoped Topology

namespace LeanSolid.Elastostatics.Rectangle

/-- Approximation by the average on a normal interval, with error controlled by the
first derivative. This is the mean-zero Wirtinger estimate applied to the residual. -/
theorem slice_average_approximation {L : ℝ} (hL : 0 < L) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) :
    (Real.pi / L) ^ 2 *
        (∫ y in (0 : ℝ)..L, (u y - (∫ x in (0 : ℝ)..L, u x) / L) ^ 2) ≤
      ∫ y in (0 : ℝ)..L, deriv u y ^ 2 := by
  let mean := (∫ x in (0 : ℝ)..L, u x) / L
  let v := fun y => u y - mean
  have hv : ContDiff ℝ 1 v := hu.sub contDiff_const
  have hmean : (∫ y in (0 : ℝ)..L, v y) = 0 := by
    change (∫ y in (0 : ℝ)..L, u y - mean) = 0
    rw [intervalIntegral.integral_sub (hu.continuous.intervalIntegrable 0 L)
      (continuous_const.intervalIntegrable 0 L), intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, mean]
    rw [mul_comm L, div_mul_cancel₀ _ hL.ne', sub_self]
  have hder : deriv v = deriv u := by
    funext y
    have hd := (hu.differentiable one_ne_zero y).hasDerivAt.sub_const mean
    exact hd.deriv
  have h := LeanSolid.Math.Wirtinger.wirtinger_mean_zero hL hv hmean
  rwa [hder] at h

/-- The averaging estimate on an arbitrary cell interval. -/
theorem interval_average_approximation {s t : ℝ} (hst : s < t) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) :
    (Real.pi / (t - s)) ^ 2 *
        (∫ y in s..t, (u y - (∫ x in s..t, u x) / (t - s)) ^ 2) ≤
      ∫ y in s..t, deriv u y ^ 2 := by
  let w := fun x => u (x + s)
  have hw : ContDiff ℝ 1 w := hu.comp (contDiff_id.add contDiff_const)
  have hd (x : ℝ) : deriv w x = deriv u (x + s) := by
    have hshift : HasDerivAt (fun y : ℝ => y + s) 1 x := (hasDerivAt_id' x).add_const s
    have h := ((hu.differentiable one_ne_zero (x + s)).hasDerivAt.comp x hshift).deriv
    change deriv (u ∘ fun y : ℝ => y + s) x = _
    simpa only [mul_one] using h
  have hmove (f : ℝ → ℝ) :
      (∫ x in (0 : ℝ)..t - s, f (x + s)) = ∫ x in s..t, f x := by
    rw [intervalIntegral.integral_comp_add_right, zero_add, sub_add_cancel]
  have h := slice_average_approximation (sub_pos.mpr hst) hw
  simp only [hd, w] at h
  rw [hmove u, hmove (fun y => (u y - (∫ x in s..t, u x) / (t - s)) ^ 2),
    hmove (fun y => deriv u y ^ 2)] at h
  exact h

/-- The squared average on an interval is bounded by the average of the square. -/
theorem interval_average_sq_le {s t : ℝ} (hst : s < t) {u : ℝ → ℝ}
    (hu : Continuous u) :
    (t - s) * ((∫ x in s..t, u x) / (t - s)) ^ 2 ≤ ∫ x in s..t, u x ^ 2 := by
  let m := (∫ x in s..t, u x) / (t - s)
  have hm : m * (t - s) = ∫ x in s..t, u x :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hst.ne')
  have h0 := intervalIntegral.integral_nonneg_of_forall (μ := MeasureTheory.volume)
    (f := fun x => (u x - m) ^ 2)
    hst.le fun x => sq_nonneg (u x - m)
  have hrewrite : (fun x => (u x - m) ^ 2) =
      fun x => (u x ^ 2 - (2 * m) * u x) + m ^ 2 := by
    funext x
    ring
  have hsq : Continuous (fun x => u x ^ 2) := hu.pow 2
  have hlin : Continuous (fun x => (2 * m) * u x) := continuous_const.mul hu
  have hdiff : Continuous (fun x => u x ^ 2 - (2 * m) * u x) := hsq.sub hlin
  rw [hrewrite, intervalIntegral.integral_add (hdiff.intervalIntegrable s t)
    (continuous_const.intervalIntegrable s t),
    intervalIntegral.integral_sub (hsq.intervalIntegrable s t) (hlin.intervalIntegrable s t),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
    ← hm] at h0
  change (t - s) * m ^ 2 ≤ _
  nlinarith only [h0]

/-- A two-dimensional cell residual splits into the horizontal slice residual and the
horizontal average of the vertical slice residual. The latter is bounded by Jensen. -/
theorem cell_residual_pointwise_bound {s t r q : ℝ} (hst : s < t)
    {u : ℝ → ℝ → ℝ} (y x : ℝ)
    (hrow : Continuous (fun z => u z y))
    (hcolMean : Continuous (fun z => (∫ w in r..q, u z w) / (q - r))) :
    (u x y - (∫ z in s..t, (∫ w in r..q, u z w) / (q - r)) / (t - s)) ^ 2 ≤
      2 * (u x y - (∫ z in s..t, u z y) / (t - s)) ^ 2 +
      (2 / (t - s)) * ∫ z in s..t, (u z y - (∫ w in r..q, u z w) / (q - r)) ^ 2 := by
  let col := fun z => (∫ w in r..q, u z w) / (q - r)
  let v := fun z => u z y - col z
  let d := t - s
  have hd : 0 < d := sub_pos.mpr hst
  have hsplit : (∫ z in s..t, v z) / d =
      (∫ z in s..t, u z y) / d - (∫ z in s..t, col z) / d := by
    unfold v
    rw [intervalIntegral.integral_sub (hrow.intervalIntegrable s t)
      (hcolMean.intervalIntegrable s t), sub_div]
  have hj := interval_average_sq_le hst (hrow.sub hcolMean)
  change d * ((∫ z in s..t, v z) / d) ^ 2 ≤ ∫ z in s..t, v z ^ 2 at hj
  have hj' : ((∫ z in s..t, v z) / d) ^ 2 ≤ (∫ z in s..t, v z ^ 2) / d :=
    (le_div_iff₀ hd).2 (by simpa only [mul_comm d] using hj)
  rw [hsplit] at hj'
  change (u x y - (∫ z in s..t, col z) / d) ^ 2 ≤
    2 * (u x y - (∫ z in s..t, u z y) / d) ^ 2 +
      (2 / d) * ∫ z in s..t, v z ^ 2
  rw [div_mul_eq_mul_div, mul_div_assoc]
  nlinarith only [hj', sq_nonneg
    ((u x y - (∫ z in s..t, u z y) / d) -
      ((∫ z in s..t, u z y) / d - (∫ z in s..t, col z) / d))]

private theorem interval_average_scaled {s t : ℝ} (hst : s < t) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) :
    (∫ y in s..t, (u y - (∫ x in s..t, u x) / (t - s)) ^ 2) ≤
      ((t - s) / Real.pi) ^ 2 * ∫ y in s..t, deriv u y ^ 2 := by
  have h := interval_average_approximation hst hu
  have hd : 0 < t - s := sub_pos.mpr hst
  apply le_of_mul_le_mul_left _ (show 0 < (Real.pi / (t - s)) ^ 2 by positivity)
  rw [← mul_assoc, show (Real.pi / (t - s)) ^ 2 * ((t - s) / Real.pi) ^ 2 = 1 by
    field_simp [hd.ne', Real.pi_ne_zero], one_mul]
  exact h

/-- The integrated Poincaré estimate for subtracting the mean on a rectangular cell.
The two derivative terms scale with the squares of their respective side lengths. -/
theorem rectangular_cell_average_error {s t r q : ℝ} (hx : s < t) (hy : r < q)
    {u : ℝ → ℝ → ℝ}
    (hu : Continuous (Function.uncurry u))
    (hsx : ∀ y, ContDiff ℝ 1 (fun x => u x y))
    (hsy : ∀ x, ContDiff ℝ 1 (u x))
    (hdx : Continuous (fun p : ℝ × ℝ => deriv (fun x => u x p.2) p.1))
    (hdy : Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2)) :
    let μ := (volume.restrict (Ioc s t)).prod (volume.restrict (Ioc r q))
    let m := (∫ p, u p.1 p.2 ∂μ) / ((t - s) * (q - r))
    (∫ p, (u p.1 p.2 - m) ^ 2 ∂μ) ≤
      2 * ((t - s) / Real.pi) ^ 2 * (∫ p, deriv (fun x => u x p.2) p.1 ^ 2 ∂μ) +
      2 * ((q - r) / Real.pi) ^ 2 * (∫ p, deriv (u p.1) p.2 ^ 2 ∂μ) := by
  let X := volume.restrict (Ioc s t)
  let Y := volume.restrict (Ioc r q)
  let μ := X.prod Y
  let col := fun x => (∫ y in r..q, u x y) / (q - r)
  let row := fun y => (∫ x in s..t, u x y) / (t - s)
  let m := (∫ x in s..t, col x) / (t - s)
  let Rx := fun p : ℝ × ℝ => (u p.1 p.2 - row p.2) ^ 2
  let Ry := fun p : ℝ × ℝ => (u p.1 p.2 - col p.1) ^ 2
  let Dx := fun p : ℝ × ℝ => deriv (fun x => u x p.2) p.1 ^ 2
  let Dy := fun p : ℝ × ℝ => deriv (u p.1) p.2 ^ 2
  let err := fun p : ℝ × ℝ => (u p.1 p.2 - m) ^ 2
  have hcol : Continuous col :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hu r q).div_const _
  have hswap : Continuous (Function.uncurry (fun y x => u x y)) := hu.comp continuous_swap
  have hrow : Continuous row :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hswap s t).div_const _
  have hRx : Continuous Rx := (hu.sub (hrow.comp continuous_snd)).pow 2
  have hRy : Continuous Ry := (hu.sub (hcol.comp continuous_fst)).pow 2
  have hInt (f : ℝ × ℝ → ℝ) (hf : Continuous f) : Integrable f μ := by
    dsimp [μ, X, Y]
    rw [Measure.prod_restrict]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hmean : m = (∫ p, u p.1 p.2 ∂μ) / ((t - s) * (q - r)) := by
    change (∫ x in s..t, (∫ y in r..q, u x y) / (q - r)) / (t - s) = _
    rw [intervalIntegral.integral_div, integral_prod (fun p => u p.1 p.2) (hInt _ hu)]
    simp only [X, Y, ← intervalIntegral.integral_of_le hx.le,
      ← intervalIntegral.integral_of_le hy.le]
    rw [div_div, mul_comm (q - r)]
  have hlocal : (∫ p, err p ∂μ) ≤ 2 * (∫ p, Rx p ∂μ) + 2 * (∫ p, Ry p ∂μ) := by
    let J := fun y => ∫ x in s..t, Ry (x, y)
    have hcJ : Continuous (Function.uncurry (fun y x => Ry (x, y))) :=
      hRy.comp continuous_swap
    have hJ : Continuous J :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcJ s t
    let B := fun p : ℝ × ℝ => (2 / (t - s)) * J p.2
    have hB : Continuous B := continuous_const.mul (hJ.comp continuous_snd)
    have hRx2 : Continuous (fun p => 2 * Rx p) := continuous_const.mul hRx
    have hmono := integral_mono (hInt err ((hu.sub continuous_const).pow 2))
      (hInt (fun p => 2 * Rx p + B p) (hRx2.add hB))
      (fun p => cell_residual_pointwise_bound hx p.2 p.1
        (hsx p.2).continuous hcol)
    rw [integral_add (hInt _ hRx2) (hInt _ hB), integral_const_mul] at hmono
    have hBI : (∫ p, B p ∂μ) = 2 * ∫ p, Ry p ∂μ := by
      rw [integral_prod_symm _ (hInt _ hB), integral_prod_symm _ (hInt _ hRy)]
      have hb (y : ℝ) : (∫ x, B (x, y) ∂X) = 2 * ∫ x, Ry (x, y) ∂X := by
        change (∫ _ : ℝ, (2 / (t - s)) * J y ∂X) = _
        rw [integral_const]
        have hmass : X.real univ = t - s := by
          simp [X, measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hx.le)]
        rw [hmass, smul_eq_mul]
        change (t - s) * ((2 / (t - s)) * J y) = _
        have hJ' : J y = ∫ x, Ry (x, y) ∂X := intervalIntegral.integral_of_le hx.le
        rw [← hJ']
        field_simp [sub_ne_zero.mpr hx.ne']
      simp_rw [hb, integral_const_mul]
    rwa [hBI] at hmono
  have hxI : (∫ p, Rx p ∂μ) ≤ ((t - s) / Real.pi) ^ 2 * ∫ p, Dx p ∂μ := by
    have hDi : Integrable Dx μ := hInt Dx (hdx.pow 2)
    rw [integral_prod_symm _ (hInt _ hRx), integral_prod_symm _ hDi,
      ← integral_const_mul]
    refine integral_mono (hInt _ hRx).integral_prod_right
      (hDi.integral_prod_right.const_mul _) fun y => ?_
    change (∫ x, Rx (x, y) ∂X) ≤ ((t - s) / Real.pi) ^ 2 * ∫ x, Dx (x, y) ∂X
    simp only [X, ← intervalIntegral.integral_of_le hx.le]
    exact interval_average_scaled hx (hsx y)
  have hyI : (∫ p, Ry p ∂μ) ≤ ((q - r) / Real.pi) ^ 2 * ∫ p, Dy p ∂μ := by
    have hDi : Integrable Dy μ := hInt Dy (hdy.pow 2)
    rw [integral_prod _ (hInt _ hRy), integral_prod _ hDi,
      ← integral_const_mul]
    refine integral_mono (hInt _ hRy).integral_prod_left
      (hDi.integral_prod_left.const_mul _) fun x => ?_
    change (∫ y, Ry (x, y) ∂Y) ≤ ((q - r) / Real.pi) ^ 2 * ∫ y, Dy (x, y) ∂Y
    simp only [Y, ← intervalIntegral.integral_of_le hy.le]
    exact interval_average_scaled hy (hsy x)
  change (∫ p, (u p.1 p.2 - (∫ p, u p.1 p.2 ∂μ) / ((t - s) * (q - r))) ^ 2 ∂μ) ≤ _
  rw [← hmean]
  change (∫ p, err p ∂μ) ≤
    2 * ((t - s) / Real.pi) ^ 2 * (∫ p, Dx p ∂μ) +
      2 * ((q - r) / Real.pi) ^ 2 * (∫ p, Dy p ∂μ)
  linarith only [hlocal, hxI, hyI]

variable {a b L : ℝ}

/-- Operator-norm convergence of explicit finite-dimensional approximations implies
compactness of the concrete rectangular displacement projection. -/
theorem rectangleDisplacement_compact_of_finite_rank_approx
    (D : ℕ → Type) [∀ k, NormedAddCommGroup (D k)] [∀ k, NormedSpace ℝ (D k)]
    [∀ k, FiniteDimensional ℝ (D k)]
    (project : ∀ k, bottomFixedSpace a b L →L[ℝ] D k)
    (reconstruct : ∀ k, D k →L[ℝ] Vec (Interior a b L))
    (happrox : Tendsto (fun k => (reconstruct k).comp (project k)) atTop
      (𝓝 (rectangleDisplacement (a := a) (b := b) (L := L)))) :
    IsCompact (closure (rectangleDisplacement ''
      {U : bottomFixedSpace a b L | ‖U‖ = 1})) := by
  have hcompact : IsCompactOperator (rectangleDisplacement (a := a) (b := b) (L := L)) := by
    apply isCompactOperator_of_tendsto happrox
    exact Eventually.of_forall fun k =>
      (isCompactOperator_of_locallyCompactSpace_rng (reconstruct k)).comp_clm (project k)
  refine (hcompact.isCompact_closure_image_closedBall 1).of_isClosed_subset isClosed_closure ?_
  apply closure_mono
  apply image_mono
  intro U hU
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hU.le

end LeanSolid.Elastostatics.Rectangle
