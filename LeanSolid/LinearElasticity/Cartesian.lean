module

public import LeanSolid.LinearElasticity.Kinematics
public import LeanSolid.LinearElasticity.Rigid
public import LeanSolid.LinearElasticity.Compatibility
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

open scoped InnerProductSpace ContDiff

namespace LeanSolid.LinearElasticity

open LeanSolid.Math

variable {n : ℕ}

/-- The same real coordinates with the Euclidean and Cartesian function norms. -/
noncomputable def cartesianCoordinates (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] Vector n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

/-- Express a Euclidean displacement field in Cartesian coordinates. -/
noncomputable def cartesianField (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    Vector n → Vector n :=
  fun y => cartesianCoordinates n (v ((cartesianCoordinates n).symm y))

private theorem coordinate_single (j : Fin n) :
    cartesianCoordinates n (EuclideanSpace.single j (1 : ℝ)) = Pi.single j 1 := by
  funext k
  simp [cartesianCoordinates, PiLp.single_apply, Pi.single_apply]

private theorem partial_cartesianField
    {v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hv : DifferentiableAt ℝ v x) (i j : Fin n) :
    partialDeriv (fun y => cartesianField v y i) j (cartesianCoordinates n x) =
      (fderiv ℝ v x (EuclideanSpace.single j 1)) i := by
  let e := cartesianCoordinates n
  let coord : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : Vector n →L[ℝ] ℝ).comp e.toContinuousLinearMap
  have h := (coord.hasFDerivAt.comp x hv.hasFDerivAt).comp (e x)
    e.symm.toContinuousLinearMap.hasFDerivAt
  have hd : HasFDerivAt (fun y => cartesianField v y i)
      ((coord.comp (fderiv ℝ v x)).comp e.symm.toContinuousLinearMap) (e x) := h
  rw [partialDeriv, hd.fderiv]
  change (fderiv ℝ v x (e.symm (Pi.single j 1))) i = _
  rw [← coordinate_single j]
  exact congrArg (fun z => (fderiv ℝ v x z) i) (e.symm_apply_apply _)

/-- The Cartesian small strain is the matrix of the symmetric Euclidean derivative. -/
theorem strainField_cartesian_eq
    {v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hv : DifferentiableAt ℝ v x) (i j : Fin n) :
    strainField (cartesianField v) (cartesianCoordinates n x) i j =
      ⟪EuclideanSpace.single i (1 : ℝ),
        ((1 / 2 : ℝ) • (fderiv ℝ v x + (fderiv ℝ v x).adjoint))
          (EuclideanSpace.single j 1)⟫_ℝ := by
  rw [strainField_apply, partial_cartesianField hv, partial_cartesianField hv]
  simp only [smul_apply, inner_smul_right, add_apply,
    inner_add_right, ContinuousLinearMap.adjoint_inner_right]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]

/-- Zero Cartesian strain implies infinitesimal rigid motion on a connected open domain.
The linear part is expressed using the original Cartesian coordinates. -/
theorem eq_rigid_of_strainField_eq_zero {Ω : Set (Vector n)} (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) {u : Vector n → Vector n} (hu : ContDiffOn ℝ 2 u Ω)
    (hε : ∀ x ∈ Ω, strainField u x = 0) :
    ∃ (a : Vector n) (W : Vector n →L[ℝ] Vector n),
      (∀ i j : Fin n, W (Pi.single j 1) i + W (Pi.single i 1) j = 0) ∧
      ∀ x ∈ Ω, u x = a + W x := by
  let e := cartesianCoordinates n
  let Ω' := e ⁻¹' Ω
  let v := e.symm ∘ u ∘ e
  have hfield : cartesianField v = u := by
    funext y
    change e (e.symm (u (e (e.symm y)))) = u y
    rw [e.apply_symm_apply, e.apply_symm_apply]
  have ho' : IsOpen Ω' := hΩ.preimage e.continuous
  have hc' : IsPreconnected Ω' := by
    rw [show Ω' = e.symm '' Ω by
      ext x
      constructor
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        change e (e.symm y) ∈ Ω
        rwa [e.apply_symm_apply]]
    exact hc.image _ e.symm.continuous.continuousOn
  have hv : ContDiffOn ℝ 2 v Ω' :=
    e.symm.comp_contDiffOn_iff.mpr (e.contDiffOn_comp_iff.mpr hu)
  have hs : ∀ x ∈ Ω', ∀ b c : EuclideanSpace ℝ (Fin n),
      ⟪fderiv ℝ v x b, c⟫_ℝ + ⟪fderiv ℝ v x c, b⟫_ℝ = 0 := by
    intro x hx
    let D := fderiv ℝ v x
    let S := (1 / 2 : ℝ) • (D + D.adjoint)
    have hd := (hv.contDiffAt (ho'.mem_nhds hx)).differentiableAt (by norm_num)
    have hS : S = 0 := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
      intro j
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      ext i
      have hj := strainField_cartesian_eq hd i j
      rw [hfield, hε (e x) hx] at hj
      simpa [S, D, EuclideanSpace.inner_single_left] using hj.symm
    intro b c
    have hh := congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
      ⟪b, A c⟫_ℝ) hS
    simp only [S, smul_apply, inner_smul_right, add_apply,
      inner_add_right, ContinuousLinearMap.adjoint_inner_right, zero_apply,
      inner_zero_right] at hh
    rw [show ⟪b, D c⟫_ℝ = ⟪D c, b⟫_ℝ from real_inner_comm _ _] at hh
    simpa only [D, add_comm] using (mul_eq_zero.mp hh).resolve_left (by norm_num)
  obtain ⟨a, W, hW, hrigid⟩ := eq_rigid_of_skew_fderiv ho' hc' hv hs
  refine ⟨e a, (e.toContinuousLinearMap.comp W).comp e.symm.toContinuousLinearMap, ?_, ?_⟩
  · intro i j
    change (W (e.symm (Pi.single j 1))) i + (W (e.symm (Pi.single i 1))) j = 0
    rw [← coordinate_single j, ← coordinate_single i, e.symm_apply_apply, e.symm_apply_apply]
    simpa [EuclideanSpace.inner_single_right] using hW (EuclideanSpace.single j 1)
      (EuclideanSpace.single i 1)
  · intro x hx
    have hx' : e.symm x ∈ Ω' := by simpa [Ω'] using hx
    have h := congrArg e (hrigid (e.symm x) hx')
    simpa [v, Function.comp_def] using h

/-- Recover a Cartesian displacement on a star-shaped open domain from a compatible
self-adjoint Euclidean strain field. The input compatibility is in operator form. -/
theorem exists_cartesian_displacement_of_compatible_operator
    {Ω : Set (Vector n)} {o : Vector n} (hΩ : StarConvex ℝ o Ω) (ho : IsOpen Ω)
    {ε : EuclideanSpace ℝ (Fin n) → Compatibility.Operator (EuclideanSpace ℝ (Fin n))}
    (hε : ContDiff ℝ 2 ε) (hs : ∀ x, (ε x).adjoint = ε x)
    (hc : ∀ x, cartesianCoordinates n x ∈ Ω →
      ∀ a b c d : EuclideanSpace ℝ (Fin n),
      ⟪fderiv ℝ (fderiv ℝ ε) x c d a, b⟫_ℝ + ⟪fderiv ℝ (fderiv ℝ ε) x a b c, d⟫_ℝ -
        ⟪fderiv ℝ (fderiv ℝ ε) x a c b, d⟫_ℝ -
        ⟪fderiv ℝ (fderiv ℝ ε) x b d a, c⟫_ℝ = 0) :
    ∃ u : Vector n → Vector n, ∀ y ∈ Ω, DifferentiableAt ℝ u y ∧
      ∀ i j : Fin n, strainField u y i j =
        ⟪EuclideanSpace.single i (1 : ℝ),
          ε ((cartesianCoordinates n).symm y) (EuclideanSpace.single j 1)⟫_ℝ := by
  let e := cartesianCoordinates n
  have hstar : StarConvex ℝ (e.symm o) (e ⁻¹' Ω) :=
    StarConvex.linear_preimage e.toLinearEquiv.toLinearMap (by simpa using hΩ)
  obtain ⟨v, hv⟩ := Compatibility.saintVenant_sufficient_of_starConvex hstar
    (ho.preimage e.continuous) hε hs hc
  refine ⟨cartesianField v, fun y hy => ?_⟩
  have hx : e.symm y ∈ e ⁻¹' Ω := by
    change e (e.symm y) ∈ Ω
    rwa [e.apply_symm_apply]
  obtain ⟨hd, he⟩ := hv (e.symm y) hx
  constructor
  · exact (e.toContinuousLinearMap.differentiableAt.comp y
      (hd.comp y e.symm.toContinuousLinearMap.differentiableAt))
  · intro i j
    have h := strainField_cartesian_eq hd i j
    rw [he] at h
    change strainField (cartesianField v) (e (e.symm y)) i j = _ at h
    rwa [e.apply_symm_apply] at h

end LeanSolid.LinearElasticity
