module

public import LeanSolid.LinearElasticity.Waves
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

open MeasureTheory Set Filter

namespace LeanSolid.LinearElasticity.Waves

/-- Scalar piecewise-constant field with a single moving front. -/
noncomputable def frontState (left right ξ : ℝ) (x : ℝ) : ℝ :=
  if x ≤ ξ then left else right

theorem integral_frontState (a b ξ left right : ℝ) (ha : a ≤ ξ) (hb : ξ ≤ b) :
    (∫ x in Icc a b, frontState left right ξ x) = (ξ - a) * left + (b - ξ) * right := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let : IsFiniteMeasure μ := ⟨by
    rw [show μ univ = volume (Icc a b) from Measure.restrict_apply_univ _]
    exact isCompact_Icc.measure_lt_top⟩
  have hL : Iic ξ ∩ Icc a b = Icc a ξ := by
    ext x
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hb⟩⟩
  have hR : (Iic ξ)ᶜ ∩ Icc a b = Ioc ξ b := by
    rw [compl_Iic]
    ext x
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ha.trans h.1.le, h.2⟩⟩
  change (∫ x, (Iic ξ).piecewise (fun _ => left) (fun _ => right) x ∂μ) = _
  rw [integral_piecewise measurableSet_Iic (integrable_const left).integrableOn
    (integrable_const right).integrableOn]
  simp only [μ, Measure.restrict_restrict measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic.compl, hL, hR, integral_const,
    measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ha), ENNReal.toReal_ofReal (sub_nonneg.mpr hb), smul_eq_mul]

/-- A moving discontinuity inside a fixed interval changes the integral at
the front speed times the left-minus-right jump. -/
theorem hasDerivAt_integral_frontState (a b left right : ℝ) {ξ : ℝ → ℝ} {t s : ℝ}
    (hξ : HasDerivAt ξ s t) (hInside : ξ t ∈ Ioo a b) :
    HasDerivAt (fun τ => ∫ x in Icc a b, frontState left right (ξ τ) x)
      (s * (left - right)) t := by
  have hl : HasDerivAt (fun τ => ξ τ - a) s t := HasDerivAt.sub_const a hξ
  have hr : HasDerivAt (fun τ => b - ξ τ) (-s) t := HasDerivAt.const_sub b hξ
  have h := (hl.mul_const left).add (hr.mul_const right)
  change HasDerivAt (fun τ => (ξ τ - a) * left + (b - ξ τ) * right)
    (s * left + (-s) * right) t at h
  have hd : s * left + (-s) * right = s * (left - right) := by ring
  rw [hd] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [hξ.continuousAt.eventually (Ioo_mem_nhds hInside.1 hInside.2)] with τ hτ
  exact integral_frontState a b (ξ τ) left right hτ.1.le hτ.2.le

/-- The kinematic and momentum flux balances for a rod front give their
Rankine–Hugoniot conditions. Strain and stress are tensile-positive. -/
theorem rod_jump_of_integral_balances (a b ρ εL εR vL vR σL σR : ℝ)
    {ξ : ℝ → ℝ} {t s : ℝ} (hξ : HasDerivAt ξ s t) (hi : ξ t ∈ Ioo a b)
    (hStrain : HasDerivAt (fun τ => ∫ x in Icc a b, frontState εL εR (ξ τ) x) (vR - vL) t)
    (hMomentum : HasDerivAt (fun τ => ∫ x in Icc a b, frontState (ρ * vL) (ρ * vR) (ξ τ) x)
      (σR - σL) t) :
    s * (εL - εR) = -(vL - vR) ∧ ρ * s * (vL - vR) = -(σL - σR) := by
  have he := (hasDerivAt_integral_frontState a b εL εR hξ hi).unique hStrain
  have hv := (hasDerivAt_integral_frontState a b (ρ * vL) (ρ * vR) hξ hi).unique hMomentum
  constructor
  · linear_combination he
  · linear_combination hv

/-- A nontrivial jump in a Hookean rod has the same speed squared as the
smooth longitudinal wave. -/
theorem rod_jump_speed_sq (ρ E s strainJump velocityJump : ℝ) (hJump : strainJump ≠ 0)
    (hStrain : s * strainJump = -velocityJump)
    (hMomentum : ρ * s * velocityJump = -(E * strainJump)) :
    ρ * s ^ 2 = E := by
  apply mul_right_cancel₀ hJump
  linear_combination (ρ * s) * hStrain - hMomentum

/-- A right-running wave into an initially unstressed, stationary region
has compressive strain behind the front for positive piston speed. -/
theorem rod_piston_compression (s piston strain : ℝ) (hs : 0 < s) (hp : 0 < piston)
    (hJump : s * strain = -piston) :
    strain = -piston / s ∧ strain < 0 := by
  have h : strain = -piston / s := by
    apply (eq_div_iff hs.ne').mpr
    rw [mul_comm, hJump]
  exact ⟨h, h ▸ div_neg_of_neg_of_pos (neg_neg_of_pos hp) hs⟩

/-- A positive-speed piston driving an unstressed Hookean rod produces
a right-running front with longitudinal wave speed and compressive stress. -/
theorem rod_piston_front (ρ E s piston strain σ : ℝ)
    (hρ : 0 < ρ) (hs : 0 < s) (hp : 0 < piston)
    (hStrain : s * strain = -piston) (hMomentum : ρ * s * piston = -σ)
    (hHooke : σ = E * strain) :
    s = Real.sqrt (E / ρ) ∧ strain = -piston / s ∧ σ = -(ρ * s) * piston ∧ σ < 0 := by
  have hJump : strain ≠ 0 := by
    intro h
    rw [h, mul_zero] at hStrain
    exact hp.ne' (neg_eq_zero.mp hStrain.symm)
  have hsq := rod_jump_speed_sq ρ E s strain piston hJump hStrain (by rwa [← hHooke])
  have hs' : s ^ 2 = E / ρ := (eq_div_iff hρ.ne').mpr (by rwa [mul_comm])
  have hStress : σ = -(ρ * s) * piston := by linear_combination hMomentum
  refine ⟨?_, (rod_piston_compression s piston strain hs hp hStrain).1, hStress, ?_⟩
  · rw [← hs', Real.sqrt_sq hs.le]
  · rw [hStress, neg_mul]
    exact neg_neg_of_pos (mul_pos (mul_pos hρ hs) hp)

end LeanSolid.LinearElasticity.Waves
