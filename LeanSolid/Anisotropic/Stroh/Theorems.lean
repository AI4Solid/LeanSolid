module

public import LeanSolid.Anisotropic.Stroh.Definitions

public section

namespace LeanSolid.Anisotropic.Stroh

open scoped Matrix

open LeanSolid.Math

/-- A positive acoustic quadratic form excludes a nonzero real kernel vector.
The positivity input is the rank-one consequence to be obtained from the material law. -/
theorem no_real_mode (Q R T : Tensor 3)
    (hpositive : ∀ (p : ℝ) (a : Vector 3), a ≠ 0 →
      0 < a ⬝ᵥ Matrix.mulVec (pencil Q R T p) a) (p : ℝ) (a : Vector 3)
    (ha : Matrix.mulVec (pencil Q R T p) a = 0) : a = 0 := by
  by_contra h
  have hp := hpositive p a h
  rw [ha, dotProduct_zero] at hp
  exact (lt_irrefl 0) hp

end LeanSolid.Anisotropic.Stroh
