module

public import LeanSolid.Elastostatics.Sobolev.Existence

@[expose] public section

namespace LeanSolid.Elastostatics.Sobolev

variable {n : ℕ}

/-- The affine Dirichlet class represented by a displacement–gradient lift. -/
def HasDirichletData (Ω : Set (Fin n → ℝ)) (lift U : G n) : Prop :=
  U - lift ∈ H10 Ω

/-- Weak equilibrium in the given affine class, tested against zero-boundary variations. -/
def IsDirichletWeakSolution (Ω : Set (Fin n → ℝ)) (μ lam : ℝ)
    (load : H10 Ω →L[ℝ] ℝ) (lift U : G n) : Prop :=
  HasDirichletData Ω lift U ∧
    ∀ V : H10 Ω, lameForm strain div μ lam U (V : G n) = load V

end LeanSolid.Elastostatics.Sobolev
