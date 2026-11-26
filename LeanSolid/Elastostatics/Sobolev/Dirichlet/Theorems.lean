module

public import LeanSolid.Elastostatics.Sobolev.Dirichlet.Definitions
import Mathlib.Tactic.Abel

public section

namespace LeanSolid.Elastostatics.Sobolev

variable {n : ℕ} {Ω : Set (Fin n → ℝ)} {μ lam : ℝ}

/-- A given lift shifts the load on the homogeneous space by the work of the lift. -/
theorem existsUnique_dirichlet [NeZero n] (hμ : 0 < μ) (hlam : 0 ≤ lam + μ)
    (hΩ : Bornology.IsBounded Ω) (load : H10 Ω →L[ℝ] ℝ) (lift : G n) :
    ∃! U : G n, IsDirichletWeakSolution Ω μ lam load lift U := by
  let a : G n →L[ℝ] G n →L[ℝ] ℝ := lameForm strain div μ lam
  let load' := load - (a lift).comp (H10 Ω).subtypeL
  have hshift (w : G n) (V : H10 Ω) :
      a (lift + w) (V : G n) = load V ↔
      a w (V : G n) = load' V := by
    change a (lift + w) (V : G n) = load V ↔
      a w (V : G n) = load V - a lift (V : G n)
    rw [map_add, add_apply, eq_sub_iff_add_eq, add_comm (a lift (V : G n))]
  obtain ⟨w, hw, huniq⟩ := existsUnique_weak hμ hlam hΩ load'
  refine ⟨lift + (w : G n), ⟨?_, ?_⟩, ?_⟩
  · change lift + (w : G n) - lift ∈ H10 Ω
    rw [add_sub_cancel_left]
    exact w.property
  · intro V
    apply (hshift w V).mpr
    simpa only [a, lameForm_apply] using hw V
  · intro U hU
    let z : H10 Ω := ⟨U - lift, hU.1⟩
    have hz : lift + (z : G n) = U := by
      change lift + (U - lift) = U
      abel
    have heq : z = w := by
      apply huniq
      intro V
      rw [← lameForm_apply]
      apply (hshift z V).mp
      rw [hz]
      exact hU.2 V
    rw [← hz, heq]

/-- Lifts differing by a zero-boundary field describe the same affine class. -/
theorem hasDirichletData_iff_of_sub_mem {g h U : G n} (hgh : g - h ∈ H10 Ω) :
    HasDirichletData Ω g U ↔ HasDirichletData Ω h U := by
  unfold HasDirichletData
  constructor
  · intro hg
    convert (H10 Ω).add_mem hg hgh using 1
    abel
  · intro hh
    convert (H10 Ω).sub_mem hh hgh using 1
    abel

/-- Changing to an equivalent lift preserves the weak solution predicate. -/
theorem isDirichletWeakSolution_iff_of_sub_mem {g h U : G n}
    {load : H10 Ω →L[ℝ] ℝ} (hgh : g - h ∈ H10 Ω) :
    IsDirichletWeakSolution Ω μ lam load g U ↔
      IsDirichletWeakSolution Ω μ lam load h U :=
  and_congr_left' (hasDirichletData_iff_of_sub_mem hgh)

/-- The unique physical displacement–gradient pair is independent of the lift. -/
theorem dirichlet_solution_eq_of_sub_mem [NeZero n] (hμ : 0 < μ) (hlam : 0 ≤ lam + μ)
    (hΩ : Bornology.IsBounded Ω) {load : H10 Ω →L[ℝ] ℝ} {g h U W : G n}
    (hgh : g - h ∈ H10 Ω) (hU : IsDirichletWeakSolution Ω μ lam load g U)
    (hW : IsDirichletWeakSolution Ω μ lam load h W) : U = W := by
  obtain ⟨_, _, hunique⟩ := existsUnique_dirichlet hμ hlam hΩ load h
  exact (hunique U ((isDirichletWeakSolution_iff_of_sub_mem hgh).mp hU)).trans
    (hunique W hW).symm

end LeanSolid.Elastostatics.Sobolev
