module

public import LeanSolid.LinearElasticity.Voigt.Definitions
import Mathlib.Tactic.Ring

public section

namespace LeanSolid.LinearElasticity.Voigt

open LeanSolid.Math

/-- The Voigt stress and engineering-strain conventions preserve work pairing. -/
theorem preserves_contract (A B : Tensor 3) (hA : A.transpose = A) (hB : B.transpose = B) :
    (∑ i, stressVector A i * strainVector B i) = contract A B := by
  have a10 : A 1 0 = A 0 1 := congrArg (fun T : Tensor 3 => T 0 1) hA
  have a20 : A 2 0 = A 0 2 := congrArg (fun T : Tensor 3 => T 0 2) hA
  have a21 : A 2 1 = A 1 2 := congrArg (fun T : Tensor 3 => T 1 2) hA
  have b10 : B 1 0 = B 0 1 := congrArg (fun T : Tensor 3 => T 0 1) hB
  have b20 : B 2 0 = B 0 2 := congrArg (fun T : Tensor 3 => T 0 2) hB
  have b21 : B 2 1 = B 1 2 := congrArg (fun T : Tensor 3 => T 1 2) hB
  simp [stressVector, strainVector, contract, Fin.sum_univ_succ, a10, a20, a21, b10, b20, b21]
  ring

end LeanSolid.LinearElasticity.Voigt
