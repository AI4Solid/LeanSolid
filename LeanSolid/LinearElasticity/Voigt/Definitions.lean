module

public import LeanSolid.Math.Definitions

@[expose] public section

namespace LeanSolid.LinearElasticity.Voigt

open LeanSolid.Math

/-- Voigt stress order: 11, 22, 33, 23, 13, 12. -/
noncomputable def stressVector (A : Tensor 3) : Vector 6 :=
  ![A 0 0, A 1 1, A 2 2, A 1 2, A 0 2, A 0 1]

/-- The same order with engineering shear strains. -/
noncomputable def strainVector (A : Tensor 3) : Vector 6 :=
  ![A 0 0, A 1 1, A 2 2, 2 * A 1 2, 2 * A 0 2, 2 * A 0 1]

end LeanSolid.LinearElasticity.Voigt
