module

public import LeanSolid.LinearElasticity.Cartesian
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Ring

@[expose] public section

open scoped InnerProductSpace ContDiff Matrix.Norms.Elementwise
open LeanSolid.Math

namespace LeanSolid.LinearElasticity

variable {n : ℕ}

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private noncomputable def e (n : ℕ) := cartesianCoordinates n

private noncomputable def b (i : Fin n) : E n := EuclideanSpace.single i 1

/-- Saint-Venant compatibility in Cartesian coordinates, with the outer derivative index
written first in each pair. -/
def IsCartesianCompatibleOn (A : Vector n → Tensor n) (Ω : Set (Vector n)) : Prop :=
  ∀ x ∈ Ω, ∀ i j k l : Fin n,
    partialDeriv (partialDeriv (fun y => A y j i) l) k x +
    partialDeriv (partialDeriv (fun y => A y l k) j) i x -
    partialDeriv (partialDeriv (fun y => A y l j) k) i x -
    partialDeriv (partialDeriv (fun y => A y k i) l) j x = 0

private noncomputable def asOperator (n : ℕ) :
    Tensor n →L[ℝ] (E n →L[ℝ] E n) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (Matrix.toEuclideanLin : Tensor n ≃ₗ[ℝ] (E n →ₗ[ℝ] E n)).toLinearMap).toContinuousLinearMap

private theorem asOperator_entry (A : Tensor n) (i j : Fin n) :
    ⟪asOperator n A (b j), b i⟫_ℝ = A i j := by
  simp [asOperator, b, EuclideanSpace.inner_single_right, Matrix.toLpLin_apply]

private theorem pullback_partial {f : Vector n → ℝ} (hf : Differentiable ℝ f)
    (x : E n) (i : Fin n) :
    fderiv ℝ (fun y => f (e n y)) x (b i) = partialDeriv f i (e n x) := by
  have hd := (hf (e n x)).hasFDerivAt.comp x (e n).toContinuousLinearMap.hasFDerivAt
  change HasFDerivAt (fun y => f (e n y)) _ x at hd
  rw [hd.fderiv]
  change fderiv ℝ f (e n x) (e n (b i)) = _
  have h : e n (b i) = Pi.single i 1 := by
    funext j
    simp [e, b, cartesianCoordinates, PiLp.single_apply, Pi.single_apply]
  rw [h]
  rfl

private theorem operator_second_entry {A : Vector n → Tensor n} (hA : ContDiff ℝ 2 A)
    (x : E n) (i j k l : Fin n) :
    let F := fun y => asOperator n (A (e n y))
    ⟪fderiv ℝ (fderiv ℝ F) x (b k) (b l) (b j), b i⟫_ℝ =
      partialDeriv (partialDeriv (fun y => A y i j) l) k (e n x) := by
  let F := fun y => asOperator n (A (e n y))
  let p : (E n →L[ℝ] E n) →L[ℝ] ℝ :=
    (innerSL ℝ (b i)).comp (ContinuousLinearMap.apply ℝ (E n) (b j))
  have hp (M : E n →L[ℝ] E n) : p M = ⟪M (b j), b i⟫_ℝ := by
    change ⟪b i, M (b j)⟫_ℝ = _
    exact real_inner_comm _ _
  let f := fun y => A y i j
  have hf : ContDiff ℝ 2 f := by
    have hπ : ContDiff ℝ 2 (fun y i j => A y i j) := hA
    exact contDiff_pi.mp (contDiff_pi.mp hπ i) j
  have hF : ContDiff ℝ 2 F :=
    (asOperator n).contDiff.comp (hA.comp (e n).toContinuousLinearMap.contDiff)
  have hD := (hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hentry : (fun y => p (F y)) = fun y => f (e n y) := by
    funext y
    exact (hp _).trans (asOperator_entry _ _ _)
  have hfirst : (fun y => p (fderiv ℝ F y (b l))) =
      fun y => partialDeriv f l (e n y) := by
    funext y
    have h := (p.hasFDerivAt.comp y ((hF.differentiable (by norm_num) y).hasFDerivAt)).fderiv
    change fderiv ℝ (fun z => p (F z)) y = _ at h
    rw [hentry] at h
    rw [← pullback_partial (hf.differentiable (by norm_num)) y l, h]
    rfl
  have hder := ((ContinuousLinearMap.apply ℝ (E n →L[ℝ] E n) (b l)).hasFDerivAt.comp
    x (hD x).hasFDerivAt)
  have h := (p.hasFDerivAt.comp x hder).fderiv
  change fderiv ℝ (fun y => p (fderiv ℝ F y (b l))) x = _ at h
  have hh := congrArg (fun L : E n →L[ℝ] ℝ => L (b k)) h
  change fderiv ℝ (fun y => p (fderiv ℝ F y (b l))) x (b k) =
    p (fderiv ℝ (fderiv ℝ F) x (b k) (b l)) at hh
  change ⟪fderiv ℝ (fderiv ℝ F) x (b k) (b l) (b j), b i⟫_ℝ = _
  rw [← hp, ← hh, hfirst]
  exact pullback_partial ((contDiff_partial hf (k := 1) (by norm_num) l).differentiable
    one_ne_zero) x k


private noncomputable def residual
    (H : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] E n) (a c d z : E n) : ℝ :=
  ⟪H d z a, c⟫_ℝ + ⟪H a c d, z⟫_ℝ - ⟪H a d c, z⟫_ℝ - ⟪H c z a, d⟫_ℝ

private theorem residual_eq_zero_of_basis
    (H : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] E n)
    (hb : ∀ i j k l : Fin n, residual H (b i) (b j) (b k) (b l) = 0) :
    ∀ a c d z, residual H a c d z = 0 := by
  have h1 (a : E n) (c : Fin n) (d : Fin n) (z : Fin n) :
      residual H a (b c) (b d) (b z) = 0 := by
    let L : E n →ₗ[ℝ] ℝ :=
      { toFun := fun t => residual H t (b c) (b d) (b z)
        map_add' := by intros; simp [residual, inner_add_left]; ring
        map_smul' := by intros; simp [residual, inner_smul_left]; ring }
    have hL : L = 0 := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro i
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      exact hb i c d z
    exact congrArg (fun M : E n →ₗ[ℝ] ℝ => M a) hL
  have h2 (a : E n) (c : E n) (d : Fin n) (z : Fin n) :
      residual H a c (b d) (b z) = 0 := by
    let L : E n →ₗ[ℝ] ℝ :=
      { toFun := fun t => residual H a t (b d) (b z)
        map_add' := by intros; simp [residual, inner_add_left, inner_add_right]; ring
        map_smul' := by intros; simp [residual, inner_smul_left, inner_smul_right]; ring }
    have hL : L = 0 := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro i
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      exact h1 a i d z
    exact congrArg (fun M : E n →ₗ[ℝ] ℝ => M c) hL
  have h3 (a : E n) (c : E n) (d : E n) (z : Fin n) :
      residual H a c d (b z) = 0 := by
    let L : E n →ₗ[ℝ] ℝ :=
      { toFun := fun t => residual H a c t (b z)
        map_add' := by intros; simp [residual, inner_add_left, inner_add_right]; ring
        map_smul' := by intros; simp [residual, inner_smul_left, inner_smul_right]; ring }
    have hL : L = 0 := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro i
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      exact h2 a c i z
    exact congrArg (fun M : E n →ₗ[ℝ] ℝ => M d) hL
  have h4 (a : E n) (c : E n) (d : E n) (z : E n) :
      residual H a c d z = 0 := by
    let L : E n →ₗ[ℝ] ℝ :=
      { toFun := fun t => residual H a c d t
        map_add' := by intros; simp [residual, inner_add_left, inner_add_right]; ring
        map_smul' := by intros; simp [residual, inner_smul_left, inner_smul_right]; ring }
    have hL : L = 0 := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro i
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      exact h3 a c d i
    exact congrArg (fun M : E n →ₗ[ℝ] ℝ => M z) hL
  exact h4

private theorem compatible_iff_operator {A : Vector n → Tensor n} {Ω : Set (Vector n)}
    (hA : ContDiff ℝ 2 A) :
    IsCartesianCompatibleOn A Ω ↔
      ∀ x : E n, e n x ∈ Ω → ∀ a c d z,
        residual (fderiv ℝ (fderiv ℝ (fun y => asOperator n (A (e n y)))) x) a c d z = 0 := by
  have hb (x : E n) (i j k l : Fin n) :
      residual (fderiv ℝ (fderiv ℝ (fun y => asOperator n (A (e n y)))) x)
          (b i) (b j) (b k) (b l) =
        partialDeriv (partialDeriv (fun y => A y j i) l) k (e n x) +
        partialDeriv (partialDeriv (fun y => A y l k) j) i (e n x) -
        partialDeriv (partialDeriv (fun y => A y l j) k) i (e n x) -
        partialDeriv (partialDeriv (fun y => A y k i) l) j (e n x) := by
    unfold residual
    rw [operator_second_entry hA x j i k l, operator_second_entry hA x l k i j,
      operator_second_entry hA x l j i k, operator_second_entry hA x k i j l]
  constructor
  · intro hc x hx
    apply residual_eq_zero_of_basis
    intro i j k l
    rw [hb]
    exact hc _ hx i j k l
  · intro hc y hy i j k l
    let x := (e n).symm y
    have hx : e n x = y := (e n).apply_symm_apply y
    have hm : e n x ∈ Ω := hx.symm ▸ hy
    have h := hc x hm (b i) (b j) (b k) (b l)
    rwa [hb, hx] at h

/-- A symmetric Cartesian strain satisfying Saint-Venant compatibility on a star-shaped open
domain is the small strain of a differentiable Cartesian displacement there. -/
theorem exists_displacement_of_cartesian_compatibility
    {Ω : Set (Vector n)} {o : Vector n} (hΩ : StarConvex ℝ o Ω) (ho : IsOpen Ω)
    {A : Vector n → Tensor n} (hA : ContDiff ℝ 2 A) (hs : ∀ y, (A y).transpose = A y)
    (hc : IsCartesianCompatibleOn A Ω) :
    ∃ u : Vector n → Vector n, ∀ y ∈ Ω, DifferentiableAt ℝ u y ∧ strainField u y = A y := by
  let F := fun x => asOperator n (A (e n x))
  have hF : ContDiff ℝ 2 F :=
    (asOperator n).contDiff.comp (hA.comp (e n).toContinuousLinearMap.contDiff)
  have hSym (x : E n) : (F x).adjoint = F x := by
    apply ContinuousLinearMap.coe_injective
    rw [← ContinuousLinearMap.adjoint_toLinearMap]
    change (A (e n x)).toEuclideanLin.adjoint = (A (e n x)).toEuclideanLin
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial, hs]
  obtain ⟨u, hu⟩ := exists_cartesian_displacement_of_compatible_operator hΩ ho hF hSym
    ((compatible_iff_operator hA).mp hc)
  refine ⟨u, fun y hy => ⟨(hu y hy).1, ?_⟩⟩
  ext i j
  rw [(hu y hy).2]
  change ⟪b i, asOperator n (A (e n ((e n).symm y))) (b j)⟫_ℝ = A y i j
  rw [(e n).apply_symm_apply]
  exact (real_inner_comm _ _).trans (asOperator_entry _ _ _)


end LeanSolid.LinearElasticity
