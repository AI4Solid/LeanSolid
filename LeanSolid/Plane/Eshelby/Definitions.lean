module

public import LeanSolid.Elastostatics.Radial.Definitions

@[expose] public section

noncomputable section

namespace LeanSolid.Plane.Eshelby

/-- Interior strain amplitude for equal Lamé moduli and in-plane eigenstrain αI. -/
def amplitude (lam mu α : ℝ) : ℝ := (lam + mu) * α / (lam + 2 * mu)

/-- The radial displacement and normal traction matching equations at radius R. -/
def IsMatched (lam mu α R A B : ℝ) : Prop :=
  A * R = B / R ∧
    2 * (lam + mu) * (A - α) = -2 * mu * B / R ^ 2

end LeanSolid.Plane.Eshelby
