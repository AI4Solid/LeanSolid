module

public import LeanSolid.AntiPlane.Wedge.Definitions
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

public section

namespace LeanSolid.AntiPlane.Wedge

theorem angular_deriv (q A B θ : ℝ) :
    deriv (angular q A B) θ = q * tractionFactor q A B θ := by
  have hq := (hasDerivAt_id θ).const_mul q
  have hc := ((Real.hasDerivAt_cos (q * θ)).comp θ hq).const_mul A
  have hs := ((Real.hasDerivAt_sin (q * θ)).comp θ hq).const_mul B
  have h := (hc.add hs).deriv
  change deriv (angular q A B) θ =
    A * (-Real.sin (q * θ) * (q * 1)) + B * (Real.cos (q * θ) * (q * 1)) at h
  rw [h, tractionFactor]
  ring

theorem freeMode_iff_sin_double (α q : ℝ) :
    FreeMode α q ↔ Real.sin (2 * (q * α)) = 0 := by
  rw [Real.sin_two_mul]
  constructor
  · rintro ⟨A, B, hAB, hp, hm⟩
    simp only [tractionFactor, mul_neg, Real.sin_neg, Real.cos_neg] at hp hm
    have hAs : A * Real.sin (q * α) = 0 := by linarith
    have hBc : B * Real.cos (q * α) = 0 := by linarith
    rcases hAB with hA | hB
    · rw [(mul_eq_zero.mp hAs).resolve_left hA]
      simp
    · rw [(mul_eq_zero.mp hBc).resolve_left hB]
      simp
  · intro h
    have hsc : Real.sin (q * α) * Real.cos (q * α) = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · simp [h]
      · simp [h]
    rcases mul_eq_zero.mp hsc with hsin | hcos
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [tractionFactor, hsin],
        by simp [tractionFactor, hsin]⟩
    · exact ⟨0, 1, Or.inr one_ne_zero, by simp [tractionFactor, hcos],
        by simp [tractionFactor, hcos]⟩

theorem first_mode (α : ℝ) (hα : 0 < α) :
    FreeMode α (Real.pi / (2 * α)) := by
  rw [freeMode_iff_sin_double]
  rw [show 2 * (Real.pi / (2 * α) * α) = Real.pi by field_simp [hα.ne']]
  exact Real.sin_pi

theorem first_mode_le (α q : ℝ) (hα : 0 < α) (hq : 0 < q) (hm : FreeMode α q) :
    Real.pi / (2 * α) ≤ q := by
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp ((freeMode_iff_sin_double α q).mp hm)
  have hkp : (0 : ℝ) < (k : ℝ) * Real.pi := by rw [hk]; positivity
  have hk0 : (0 : ℤ) < k := by
    exact_mod_cast (pos_of_mul_pos_left hkp Real.pi_pos.le)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hk1 Real.pi_pos.le]

end LeanSolid.AntiPlane.Wedge
