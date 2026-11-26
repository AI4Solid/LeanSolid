module

public import LeanSolid.AntiPlane.Crack.Definitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace LeanSolid.AntiPlane.Crack

open Filter
open scoped Topology

/-- The candidate's ahead-of-tip stress approaches the Mode III intensity after scaling.
The full complex field and the crack-face/remote boundary conditions are separate claims. -/
theorem scaled_aheadShear_tendsto (remote : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r => Real.sqrt (2 * Real.pi * r) * aheadShear remote a r)
      (𝓝[Set.Ioi 0] 0) (𝓝 (stressIntensity remote a)) := by
  have hd : 0 < Real.sqrt (2 * a) := Real.sqrt_pos.2 (by positivity)
  have cnum : ContinuousAt (fun r : ℝ => remote * (a + r) * Real.sqrt (2 * Real.pi)) 0 :=
    continuousAt_const.mul (continuousAt_const.add continuousAt_id) |>.mul continuousAt_const
  have cden : ContinuousAt (fun r : ℝ => Real.sqrt (2 * a + r)) 0 :=
    (continuousAt_const.add continuousAt_id).sqrt
  have ht := (cnum.div cden (by simpa using hd.ne')).continuousWithinAt (s := Set.Ioi (0 : ℝ))
  have hval :
      remote * (a + 0) * Real.sqrt (2 * Real.pi) / Real.sqrt (2 * a + 0) =
        stressIntensity remote a := by
    rw [add_zero, add_zero, stressIntensity, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) Real.pi,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) a, Real.sqrt_mul Real.pi_pos.le a]
    have hs0 := (Real.sqrt_pos.2 ha).ne'
    have h2 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    apply (div_eq_iff (mul_ne_zero h2 hs0)).2
    calc
      remote * a * (Real.sqrt 2 * Real.sqrt Real.pi) =
          remote * (Real.sqrt a ^ 2) * (Real.sqrt 2 * Real.sqrt Real.pi) := by
            rw [Real.sq_sqrt ha.le]
      _ = _ := by ring
  change Tendsto (fun r : ℝ => remote * (a + r) * Real.sqrt (2 * Real.pi) /
    Real.sqrt (2 * a + r)) (𝓝[Set.Ioi 0] 0)
    (𝓝 (remote * (a + 0) * Real.sqrt (2 * Real.pi) / Real.sqrt (2 * a + 0))) at ht
  rw [hval] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := hr
  rw [aheadShear, Real.sqrt_mul hr'.le, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  have hn := (Real.sqrt_pos.2 hr').ne'
  have hs := (Real.sqrt_pos.2 (by positivity : 0 < 2 * a + r)).ne'
  field_simp [hn, hs]

end LeanSolid.AntiPlane.Crack
