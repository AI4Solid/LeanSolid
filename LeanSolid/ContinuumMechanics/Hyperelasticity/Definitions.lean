module

public import LeanSolid.ContinuumMechanics.Invariants
public import LeanSolid.ContinuumMechanics.Statics
public import LeanSolid.Math.Calculus.TensorPath
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis

@[expose] public section

noncomputable section

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

open LeanSolid.Math

variable {n : ℕ}

/-- Entrywise derivative of a tensor-valued path at zero. -/
def HasTensorDerivative (c : ℝ → Tensor n) (H : Tensor n) : Prop :=
  HasTensorDerivAt c H 0

/-- The energy derivative along every differentiable path is represented by Frobenius pairing. -/
def HasEnergyGradient (W : Tensor n → ℝ) (A G : Tensor n) : Prop :=
  ∀ (c : ℝ → Tensor n) (H : Tensor n), c 0 = A →
    HasTensorDerivative c H → HasDerivAt (fun t => W (c t)) (contract G H) 0

/-- Matrix of energy partial derivatives in the elementary matrix directions.
Its interpretation as a gradient uses a differentiability hypothesis. -/
def energyGradient (W : Tensor n → ℝ) (A : Tensor n) : Tensor n :=
  Matrix.of fun i j => deriv (fun t : ℝ => W (A + t • Matrix.single i j 1)) 0

/-- First Piola stress derived from an energy per reference volume written as a function of F. -/
def firstPiolaStress (W : Tensor n → ℝ) (F : Tensor n) : Tensor n := energyGradient W F

/-- Second Piola stress when the energy is expressed in Green–Lagrange strain E. -/
def secondPiolaStress (W : Tensor n → ℝ) (E : Tensor n) : Tensor n := energyGradient W E

/-- Second Piola stress when the energy is expressed in the right Cauchy–Green tensor C. -/
def secondPiolaFromC (W : Tensor n → ℝ) (C : Tensor n) : Tensor n := (2 : ℝ) • energyGradient W C

/-- Stored energy expressed in the principal invariants of a tensor. -/
def invariantEnergy (W : Vector 3 → ℝ) (A : Tensor 3) : ℝ := W (principalInvariants A)

/-- Frobenius gradient of an invariant energy with supplied partial derivatives dW/dIₖ. -/
def invariantGradient (A : Tensor 3) (dW : Vector 3) : Tensor 3 :=
  dW 0 • (1 : Tensor 3) + dW 1 • (A.trace • (1 : Tensor 3) - A.transpose) +
    dW 2 • A.adjugate.transpose

/-- Second Piola stress for an energy written in the three invariants of C. -/
def invariantSecondPiola (C : Tensor 3) (dW : Vector 3) : Tensor 3 :=
  (2 : ℝ) • invariantGradient C dW

end LeanSolid.ContinuumMechanics.Hyperelasticity
