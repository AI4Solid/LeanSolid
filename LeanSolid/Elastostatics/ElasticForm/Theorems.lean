module

public import LeanSolid.Elastostatics.ElasticForm.Definitions
public import LeanSolid.Elastostatics.Theorems
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open scoped InnerProductSpace

namespace LeanSolid.Elastostatics

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (strain : V →L[ℝ] H) (stiffness : H →L[ℝ] H)

theorem elasticForm_apply (u v : V) :
    elasticForm strain stiffness u v = ⟪stiffness (strain u), strain v⟫_ℝ := by
  simp [elasticForm, ContinuousLinearMap.compL_apply, innerSL_apply_apply]

theorem elasticForm_comm
    (hs : ∀ e f, ⟪stiffness e, f⟫_ℝ = ⟪e, stiffness f⟫_ℝ) (u v : V) :
    elasticForm strain stiffness u v = elasticForm strain stiffness v u := by
  rw [elasticForm_apply, elasticForm_apply, hs, real_inner_comm]

/-- Pointwise operator positivity and a Korn estimate imply coercivity of virtual work.
The Hilbert-space argument follows lean-mechanics, Elastostatics/Weak.lean (Apache-2.0). -/
theorem elasticForm_isCoercive (c K : ℝ) (hc : 0 < c) (hK : 0 < K)
    (hpos : ∀ e, c * ‖e‖ ^ 2 ≤ ⟪stiffness e, e⟫_ℝ)
    (hkorn : ∀ v, ‖v‖ ≤ K * ‖strain v‖) :
    IsCoercive (elasticForm strain stiffness) := by
  refine ⟨c / K ^ 2, by positivity, fun v => ?_⟩
  rw [elasticForm_apply]
  refine le_trans ?_ (hpos (strain v))
  rw [show c / K ^ 2 * ‖v‖ * ‖v‖ = (c * ‖v‖ ^ 2) / K ^ 2 by ring,
    div_le_iff₀ (by positivity)]
  have h := pow_le_pow_left₀ (norm_nonneg v) (hkorn v) 2
  nlinarith [mul_le_mul_of_nonneg_left h hc.le]

theorem existsUnique_of_korn [CompleteSpace V] (c K : ℝ) (hc : 0 < c) (hK : 0 < K)
    (hpos : ∀ e, c * ‖e‖ ^ 2 ≤ ⟪stiffness e, e⟫_ℝ)
    (hkorn : ∀ v, ‖v‖ ≤ K * ‖strain v‖) (load : V →L[ℝ] ℝ) :
    ∃! u : V, IsWeakSolution (elasticForm strain stiffness) load u :=
  existsUnique_weakSolution _ load (elasticForm_isCoercive strain stiffness c K hc hK hpos hkorn)

end LeanSolid.Elastostatics
