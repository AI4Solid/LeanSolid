module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace LeanSolid.Math

/-- Vectors in Cartesian coordinates. -/
abbrev Vector (n : ℕ) := Fin n → ℝ

/-- Second-order tensors in a fixed orthonormal Cartesian basis. -/
abbrev Tensor (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Symmetric part of a second-order tensor. -/
noncomputable def symPart {n : ℕ} (A : Tensor n) : Tensor n :=
  (1 / 2 : ℝ) • (A + A.transpose)

/-- Frobenius contraction in the chosen orthonormal basis. -/
noncomputable def contract {n : ℕ} (A B : Tensor n) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Skew part of a Cartesian tensor. -/
noncomputable def skewPart {n : ℕ} (A : Tensor n) : Tensor n :=
  (1 / 2 : ℝ) • (A - A.transpose)

/-- Spherical part of a tensor. In dimension zero the matrix is empty. -/
noncomputable def spherical {n : ℕ} (A : Tensor n) : Tensor n :=
  (A.trace / (n : ℝ)) • (1 : Tensor n)

/-- The remainder after subtracting the spherical part. -/
noncomputable def deviator {n : ℕ} (A : Tensor n) : Tensor n := A - spherical A

/-- Represent a tensor after an orthogonal change of Cartesian coordinates. -/
noncomputable def conjugate {n : ℕ} (Q A : Tensor n) : Tensor n := Q * A * Q.transpose

end LeanSolid.Math
