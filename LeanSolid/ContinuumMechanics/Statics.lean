module

public import LeanSolid.ContinuumMechanics.Definitions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import LeanSolid.Math.Calculus.Theorems
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math
open Filter Set
open MeasureTheory
open scoped Matrix

variable {n : ℕ}

/-- First Piola–Kirchhoff stress. Cauchy stress `σ` is evaluated at the image
of the reference point. For nonsingular `F` this is `J σ F⁻ᵀ`. -/
def firstPiola (F σ : Tensor n) : Tensor n := σ * F.adjugate.transpose

/-- Second Piola–Kirchhoff stress recovered from first Piola stress.
Its physical interpretation requires a nonsingular `F`. -/
def secondPiola (F P : Tensor n) : Tensor n := F⁻¹ * P

/-- Cauchy stress recovered from first Piola stress where `J ≠ 0`. -/
def cauchyFromPiola (F P : Tensor n) : Tensor n := (jacobian F)⁻¹ • (P * F.transpose)

/-- Force per unit reference area for a supplied reference unit normal. -/
def nominalTraction (P : Tensor n) (N : Vector n) : Vector n := Matrix.mulVec P N

/-- Strong force balance in the open reference configuration.
`b` is force per unit reference volume, and divergence contracts the material index of `P`. -/
def IsReferenceEquilibriumOn (Ω : Set (Vector n)) (P : Vector n → Tensor n)
    (b : Vector n → Vector n) : Prop :=
  IsOpen Ω ∧ (∀ i j, DifferentiableOn ℝ (fun X => P X i j) Ω) ∧
    ∀ X ∈ Ω, tensorDivergence P X + b X = 0

/-- Pointwise angular momentum balance in the absence of body couples. -/
def IsMomentBalanced (F P : Tensor n) : Prop := (P * F.transpose).transpose = P * F.transpose

theorem firstPiola_mul_transpose (F σ : Tensor n) :
    firstPiola F σ * F.transpose = jacobian F • σ := by
  rw [firstPiola, Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_adjugate,
    Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, mul_one]
  rfl

theorem cauchyFromPiola_firstPiola (F σ : Tensor n) (hJ : jacobian F ≠ 0) :
    cauchyFromPiola F (firstPiola F σ) = σ := by
  rw [cauchyFromPiola, firstPiola_mul_transpose, smul_smul, inv_mul_cancel₀ hJ, one_smul]

/-- The pointwise pullback identity for tractions, with the cofactor-transformed
normal carrying the change of area. -/
theorem nominalTraction_firstPiola (F σ : Tensor n) (N : Vector n) :
    nominalTraction (firstPiola F σ) N = Matrix.mulVec σ (Matrix.mulVec F.adjugate.transpose N) := by
  simp only [nominalTraction, firstPiola, Matrix.mulVec_mulVec]

theorem momentBalanced_firstPiola_iff (F σ : Tensor n) (hJ : jacobian F ≠ 0) :
    IsMomentBalanced F (firstPiola F σ) ↔ σ.transpose = σ := by
  rw [IsMomentBalanced, firstPiola_mul_transpose, Matrix.transpose_smul]
  constructor
  · intro h
    have h' := congrArg (fun A : Tensor n => (jacobian F)⁻¹ • A) h
    simpa only [smul_smul, inv_mul_cancel₀ hJ, one_smul] using h'
  · intro h
    rw [h]

theorem secondPiola_mul (F P : Tensor n) (hJ : jacobian F ≠ 0) :
    F * secondPiola F P = P := by
  exact Matrix.mul_nonsing_inv_cancel_left F P (isUnit_iff_ne_zero.mpr hJ)

theorem constant_referenceEquilibrium {Ω : Set (Vector n)} (hΩ : IsOpen Ω) (P : Tensor n) :
    IsReferenceEquilibriumOn Ω (fun _ => P) (fun _ => 0) := by
  refine ⟨hΩ, fun i j => differentiableOn_const (P i j), fun X _ => ?_⟩
  funext i
  simp [tensorDivergence, partial_const]

/-- The stress reconstructed from the tractions on positive coordinate faces. -/
def stressOfTraction (traction : Vector 3 → Vector 3) : Tensor 3 :=
  Matrix.of fun i j => traction (Pi.single j 1) i

/-- Cauchy's pointwise tetrahedron argument. The weighted face balance uses
signed projected areas. A vanishing normalized residual accounts for the terms
from the finite tetrahedra that disappear in the limit. -/
theorem traction_eq_stressOfTraction_mulVec
    (traction : Vector 3 → Vector 3) (normal : Vector 3)
    (residual : ℝ → Vector 3)
    (hResidual : Filter.Tendsto residual (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hBalance : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0),
      traction normal = ∑ j, normal j • traction (Pi.single j 1) + residual ε) :
    traction normal = stressOfTraction traction *ᵥ normal := by
  have hlim : Filter.Tendsto
      (fun ε => (∑ j, normal j • traction (Pi.single j 1)) + residual ε)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (∑ j, normal j • traction (Pi.single j 1))) := by
    simpa only [add_zero] using tendsto_const_nhds.add hResidual
  have hconst : Filter.Tendsto (fun _ : ℝ => traction normal) (nhdsWithin 0 (Ioi 0))
      (nhds (∑ j, normal j • traction (Pi.single j 1))) :=
    hlim.congr' (hBalance.mono fun _ he => he.symm)
  have he := tendsto_nhds_unique (tendsto_const_nhds (x := traction normal)) hconst
  rw [he]
  funext i
  simp only [Matrix.mulVec, dotProduct, stressOfTraction, Matrix.of_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- A bounded volume force divided by the oblique face area vanishes as
the tetrahedron shrinks. The measures may be volume restricted to the scaled
tetrahedra. The volume and area scaling laws are supplied as hypotheses. -/
theorem tendsto_areaNormalized_volumeForce
    (μ : ℝ → Measure (Vector 3)) [∀ ε, IsFiniteMeasure (μ ε)]
    (force : Vector 3 → Vector 3) (V A M : ℝ) (hA : 0 < A)
    (hVolume : ∀ ε > 0, (μ ε).real univ = V * ε ^ 3)
    (hBound : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ∀ᵐ x ∂μ ε, ‖force x‖ ≤ M) :
    Tendsto (fun ε => (A * ε ^ 2)⁻¹ • ∫ x, force x ∂μ ε)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hLinear : Tendsto (fun ε : ℝ => (M * V / A) * ε)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [id_eq, mul_zero] using
      tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto id (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
  apply squeeze_zero_norm' _ hLinear
  filter_upwards [self_mem_nhdsWithin, hBound] with ε hε hbound
  have hε' : 0 < ε := hε
  have hpos : 0 < A * ε ^ 2 := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  calc
    _ ≤ (A * ε ^ 2)⁻¹ * (M * (μ ε).real univ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hbound)
        (inv_nonneg.mpr hpos.le)
    _ = _ := by
      rw [hVolume ε hε']
      field_simp [hA.ne', hε'.ne']

end LeanSolid.ContinuumMechanics
