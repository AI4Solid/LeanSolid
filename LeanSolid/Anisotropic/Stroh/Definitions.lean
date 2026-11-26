module

public import LeanSolid.Math.Definitions

@[expose] public section

namespace LeanSolid.Anisotropic.Stroh

open LeanSolid.Math

/-- Stroh quadratic pencil in the real spectral parameter. -/
noncomputable def pencil (Q R T : Tensor 3) (p : ℝ) : Tensor 3 :=
  Q + p • (R + R.transpose) + p ^ 2 • T

end LeanSolid.Anisotropic.Stroh
