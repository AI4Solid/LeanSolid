module

public import LeanSolid.Elastostatics.Definitions
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual

public section

open scoped InnerProductSpace

namespace LeanSolid.Elastostatics

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Lax–Milgram on the chosen admissible space, with coercivity as an explicit input. -/
theorem existsUnique_weakSolution (a : V →L[ℝ] V →L[ℝ] ℝ)
    (load : V →L[ℝ] ℝ) (ha : IsCoercive a) :
    ∃! u : V, IsWeakSolution a load u := by
  let g := (InnerProductSpace.toDual ℝ V).symm load
  have hg (v : V) : ⟪g, v⟫_ℝ = load v := InnerProductSpace.toDual_symm_apply
  refine ⟨ha.continuousLinearEquivOfBilin.symm g, ?_, ?_⟩
  · intro v
    rw [← ha.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply, hg]
  · intro u hu
    have he := ha.unique_continuousLinearEquivOfBilin (v := u) (f := g)
      (fun v => by rw [hg, hu v])
    rw [he, ContinuousLinearEquiv.symm_apply_apply]

end LeanSolid.Elastostatics
