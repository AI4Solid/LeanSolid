/- Adapted from raphos-com/lean-mechanics at 7e41dfe (Apache-2.0),
   ContinuumMechanics/Kinematics/SaintVenant.lean and SaintVenantStar.lean.
   Uses Mathlib's adjoint directly on real Hilbert-space operators. -/
module

public import LeanSolid.Math.Calculus.PoincareStar
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

@[expose] public section

open scoped InnerProductSpace
open ContinuousLinearMap

noncomputable section

namespace LeanSolid.LinearElasticity.Compatibility

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Operator (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  E →L[ℝ] E

/-- The real adjoint as a continuous linear map on operators. -/
def transposeL : Operator E →L[ℝ] Operator E :=
  (ContinuousLinearMap.adjoint : Operator E ≃ₗᵢ[ℝ] Operator E).toLinearIsometry.toContinuousLinearMap

theorem transposeL_apply (A : Operator E) : transposeL A = A.adjoint := rfl

/-- `A ↦ A - Aᵀ`. -/
def skewL : Operator E →L[ℝ] Operator E := ContinuousLinearMap.id ℝ (Operator E) - transposeL

theorem skewL_apply (A : Operator E) : skewL A = A - A.adjoint := by
  simp [skewL, transposeL_apply]

variable [FiniteDimensional ℝ E]

/-- `T ↦ (c ↦ (a ↦ T(a)c) - (a ↦ T(a)c)ᵀ)`: the rotation-gradient form of a strain gradient. -/
def Φ : (E →L[ℝ] Operator E) →L[ℝ] (E →L[ℝ] Operator E) :=
  (ContinuousLinearMap.compL ℝ E (Operator E) (Operator E) skewL).comp
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).toContinuousLinearMap

theorem inner_Φ (T : E →L[ℝ] Operator E) (c a b : E) :
    ⟪Φ T c a, b⟫_ℝ = ⟪T a c, b⟫_ℝ - ⟪a, T b c⟫_ℝ := by
  simp [Φ, skewL_apply, inner_sub_left, ContinuousLinearMap.adjoint_inner_left]

theorem transpose_Φ (T : E →L[ℝ] Operator E) (c : E) : (Φ T c).adjoint = -Φ T c := by
  have h : Φ T c = skewL (T.flip c) := rfl
  rw [h, skewL_apply, ← transposeL_apply, map_sub, transposeL_apply, transposeL_apply,
    ContinuousLinearMap.adjoint_adjoint, neg_sub]

omit [FiniteDimensional ℝ E] in
/-- The derivative of a symmetric-tensor-valued map is symmetric. -/
theorem transpose_fderiv {f : E → Operator E} (hf : Differentiable ℝ f) (hs : ∀ y, (f y).adjoint = f y)
    (x d : E) : (fderiv ℝ f x d).adjoint = fderiv ℝ f x d := by
  have he : (⇑transposeL ∘ f) = f := funext fun y => by
    rw [Function.comp_apply, transposeL_apply, hs]
  have h := (transposeL.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
  rw [he] at h
  conv_rhs => rw [h, ContinuousLinearMap.comp_apply, transposeL_apply]

/-- **Saint-Venant compatibility** (sufficiency, star-shaped domains): on an open set `Ω`
star-shaped about some point `c`, a symmetric `C²` strain field satisfying the compatibility
conditions is the strain `sym ∇u` of a displacement. [Gurtin1981], §14. -/
theorem saintVenant_sufficient_of_starConvex {Ω : Set E} {c : E} (hΩ : StarConvex ℝ c Ω)
    (hΩo : IsOpen Ω) {ε : E → Operator E}
    (hε : ContDiff ℝ 2 ε) (hs : ∀ x, (ε x).adjoint = ε x)
    (hc : ∀ x ∈ Ω, ∀ a b c d : E,
      ⟪fderiv ℝ (fderiv ℝ ε) x c d a, b⟫_ℝ + ⟪fderiv ℝ (fderiv ℝ ε) x a b c, d⟫_ℝ -
        ⟪fderiv ℝ (fderiv ℝ ε) x a c b, d⟫_ℝ - ⟪fderiv ℝ (fderiv ℝ ε) x b d a, c⟫_ℝ = 0) :
    ∃ u : E → E, ∀ x ∈ Ω, DifferentiableAt ℝ u x ∧ (1 / 2 : ℝ) • (fderiv ℝ u x + (fderiv ℝ u x).adjoint) = ε x := by
  have hε1 : Differentiable ℝ ε := hε.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ ε) :=
    (hε.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set H := fderiv ℝ (fderiv ℝ ε) with hH
  -- symmetries of `D²ε`
  have hHs : ∀ x p q, H x p q = H x q p := fun x p q =>
    (hε.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) p q
  have hH' : ∀ x p q, fderiv ℝ (fun y => fderiv ℝ ε y q) x p = H x p q := fun x p q => by
    have h := ((hD x).hasFDerivAt.clm_apply (hasFDerivAt_const q x))
    rw [h.fderiv, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  have hHT : ∀ x p q r s, ⟪H x p q r, s⟫_ℝ = ⟪H x p q s, r⟫_ℝ := fun x p q r s => by
    have h := transpose_fderiv (f := fun y => fderiv ℝ ε y q)
      (hD.clm_apply (differentiable_const q)) (fun y => transpose_fderiv hε1 hs y q) x p
    rw [hH'] at h
    rw [← ContinuousLinearMap.adjoint_inner_right, h, real_inner_comm]
  have hDT : ∀ x p r s, ⟪fderiv ℝ ε x p r, s⟫_ℝ = ⟪fderiv ℝ ε x p s, r⟫_ℝ := fun x p r s => by
    rw [← ContinuousLinearMap.adjoint_inner_right, transpose_fderiv hε1 hs, real_inner_comm]
  -- step 1: the rotation gradient `ω = Φ(Dε)` is closed, `ω = DW`
  set ω : E → E →L[ℝ] Operator E := fun x => Φ (fderiv ℝ ε x) with hω
  have hωd : ∀ x, HasFDerivAt ω (Φ.comp (H x)) x := fun x => by
    have h := HasFDerivAt.comp (𝕜 := ℝ) (E := E) (F := E →L[ℝ] Operator E) (G := E →L[ℝ] Operator E) x
      Φ.hasFDerivAt (hD x).hasFDerivAt
    exact h
  obtain ⟨W, hW⟩ := hΩ.exists_forall_hasFDerivAt_of_fderiv_symmetric hΩo
    (fun x _ => (hωd x).differentiableAt.differentiableWithinAt) fun x hx p q => by
      rw [(hωd x).fderiv]
      ext a
      refine ext_inner_right ℝ fun b => ?_
      simp only [ContinuousLinearMap.comp_apply]
      rw [inner_Φ, inner_Φ]
      have h := hc x hx q b a p
      have e1 : ⟪H x a p q, b⟫_ℝ = ⟪H x p a q, b⟫_ℝ := by rw [hHs x a p]
      have e2 : ⟪H x q b a, p⟫_ℝ = ⟪a, H x q b p⟫_ℝ := by rw [hHT, real_inner_comm]
      have e3 : ⟪H x q a b, p⟫_ℝ = ⟪H x q a p, b⟫_ℝ := hHT x q a b p
      have e4 : ⟪H x b p q, a⟫_ℝ = ⟪a, H x p b q⟫_ℝ := by rw [hHs x b p, real_inner_comm]
      linarith
  -- `W` can be taken skew
  set S : Operator E →L[ℝ] Operator E := (1 / 2 : ℝ) • skewL
  have hW' : ∀ x ∈ Ω, HasFDerivAt (fun y => S (W y)) (ω x) x := fun x hx => by
    have h := HasFDerivAt.comp (𝕜 := ℝ) (E := E) (F := Operator E) (G := Operator E) x S.hasFDerivAt
      (hW x hx)
    have e : S.comp (ω x) = ω x := by
      ext c : 1
      change (1 / 2 : ℝ) • skewL (ω x c) = ω x c
      rw [skewL_apply, hω, transpose_Φ, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
      norm_num
    rw [e] at h
    exact h
  -- step 2: `ε + W` is closed, `ε + W = ∇u`
  have hβ : ∀ x ∈ Ω, HasFDerivAt (fun y => ε y + S (W y)) (fderiv ℝ ε x + ω x) x :=
    fun x hx => (hε1 x).hasFDerivAt.add (hW' x hx)
  obtain ⟨u, hu⟩ := hΩ.exists_forall_hasFDerivAt_of_fderiv_symmetric hΩo
    (fun x hx => (hβ x hx).differentiableAt.differentiableWithinAt) fun x hx p q => by
      rw [(hβ x hx).fderiv]
      refine ext_inner_right ℝ fun b => ?_
      simp only [add_apply, inner_add_left]
      rw [inner_Φ, inner_Φ, real_inner_comm _ q, real_inner_comm _ p, hDT x b p q]
      ring
  refine ⟨u, fun x hx => ⟨(hu x hx).differentiableAt, ?_⟩⟩
  have hskew : (S (W x)).adjoint = -(S (W x)) := by
    change ((1 / 2 : ℝ) • skewL (W x)).adjoint = -((1 / 2 : ℝ) • skewL (W x))
    rw [← transposeL_apply, map_smul, skewL_apply, map_sub, transposeL_apply,
      transposeL_apply, ContinuousLinearMap.adjoint_adjoint, ← smul_neg, neg_sub]
  rw [(hu x hx).fderiv, ContinuousLinearMap.adjoint.map_add, hs x, hskew]
  module

end LeanSolid.LinearElasticity.Compatibility
