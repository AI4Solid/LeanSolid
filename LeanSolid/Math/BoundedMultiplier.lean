module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LeanSolid.Math

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Multiplication by a bounded real coefficient on scalar L². -/
noncomputable def l2Multiplier (c : Lp ℝ ∞ ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  ({ toFun := fun u => c • u
     map_add' := fun u v => Lp.add_smul c u v
     map_smul' := fun r u => (Lp.smul_comm r c u).symm } :
     Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν).mkContinuous ‖c‖ (Lp.norm_smul_le c)

theorem l2Multiplier_apply (c : Lp ℝ ∞ ν) (u : Lp ℝ 2 ν) :
    l2Multiplier c u = c • u := by unfold l2Multiplier; rfl

/-- The weighted L² pairing is the integral of the pointwise weighted product. -/
theorem l2Multiplier_inner (c : Lp ℝ ∞ ν) (u v : Lp ℝ 2 ν) :
    ⟪l2Multiplier c u, v⟫_ℝ = ∫ x, c x * u x * v x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul c u (r := 2)] with x hx
  change (c • u : Lp ℝ 2 ν) x = _ at hx
  change ⟪(c • u : Lp ℝ 2 ν) x, v x⟫_ℝ = _
  rw [hx]
  simp [mul_comm]

end LeanSolid.Math
