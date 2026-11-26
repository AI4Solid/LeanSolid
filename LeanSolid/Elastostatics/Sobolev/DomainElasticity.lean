module

public import LeanSolid.Elastostatics.Sobolev.DomainGraph
public import LeanSolid.Elastostatics.Sobolev.VariableLamé

public section

open MeasureTheory

namespace LeanSolid.Elastostatics.Sobolev.Domain

variable {Ω : Set (Fin 3 → ℝ)} (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
variable {lam mu : (Fin 3 → ℝ) → ℝ}
  (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω))

/-- The physical Lamé form on the completed domain graph. Zero extension is used
only as an L² representative to reuse the verified body form. -/
noncomputable def lameForm : H1 hΩ →L[ℝ] H1 hΩ →L[ℝ] ℝ :=
  let e := (extendJet ho.measurableSet).comp (H1 hΩ).subtypeL
  (bodyLameForm ho hΩ hl hm).bilinearComp e e

theorem lameForm_apply (u v : H1 hΩ) :
    lameForm ho hΩ hl hm u v =
      bodyLameForm ho hΩ hl hm (extendJet ho.measurableSet u.val)
        (extendJet ho.measurableSet v.val) := by
  simp [lameForm, ContinuousLinearMap.bilinearComp_apply]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency false in
/-- The domain energy controls the zero-trace graph norm by isometric transport. -/
theorem lameForm_coercive
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) :
    IsCoercive ((lameForm ho hΩ hl hm).bilinearComp
      (zeroTraceInH1 hΩ).subtypeL (zeroTraceInH1 hΩ).subtypeL) := by
  obtain ⟨C, hC, hc⟩ := bodyLameForm_coercive ho hΩ hl hm hp
  refine ⟨C, hC, fun v => ?_⟩
  obtain ⟨w, rfl⟩ := (testSpaceEquiv hΩ).surjective v
  have h := hc w
  simp only [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply] at h ⊢
  rw [lameForm_apply, testSpaceEquiv_apply_val, extend_restrict_H10,
    LinearIsometryEquiv.norm_map]
  exact h

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency false in
/-- Every Dirichlet lift in the physical domain graph has a unique solution. -/
theorem existsUnique_solution
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) (g : H1 hΩ) :
    ∃! u, BoundaryResponse.Solves (zeroTraceInH1 hΩ) (lameForm ho hΩ hl hm) g u :=
  BoundaryResponse.existsUnique_solution (zeroTraceInH1 hΩ) _
    (lameForm_coercive ho hΩ hl hm hp) g

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency false in
/-- Displacement-to-traction work on the variational quotient of the physical H¹ graph. -/
noncomputable def dn
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) :
    BoundaryResponse.Trace (V := H1 hΩ) (zeroTraceInH1 hΩ) →
      BoundaryResponse.Trace (V := H1 hΩ) (zeroTraceInH1 hΩ) → ℝ :=
  BoundaryResponse.dnOfExists (V := H1 hΩ) (zeroTraceInH1 hΩ) (lameForm ho hΩ hl hm)
    (existsUnique_solution ho hΩ hl hm hp)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluate the physical domain DN on canonical trace representatives. -/
theorem dn_on_trace
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x)
    {f u : H1 hΩ}
    (hu : BoundaryResponse.Solves (zeroTraceInH1 hΩ) (lameForm ho hΩ hl hm) f u)
    (g : H1 hΩ) :
    dn ho hΩ hl hm hp
      (Quot.mk (fun p q : H1 hΩ => p - q ∈ zeroTraceInH1 hΩ) f)
      (Quot.mk (fun p q : H1 hΩ => p - q ∈ zeroTraceInH1 hΩ) g) =
      lameForm ho hΩ hl hm u g := by
  unfold dn
  exact BoundaryResponse.dnOfExists_apply (V := H1 hΩ) (N := zeroTraceInH1 hΩ)
    (a := lameForm ho hΩ hl hm) (existsUnique_solution ho hΩ hl hm hp) hu g

/-- The divergence is the trace of the three-dimensional domain gradient. -/
@[expose] noncomputable def jetDiv (u : Jet Ω) : Scalar Ω := ∑ i, u.snd i i

/-- Cartesian components of the symmetric domain gradient. -/
@[expose] noncomputable def jetStrain (u : Jet Ω) (i j : Fin 3) : Scalar Ω :=
  (1 / 2 : ℝ) • (u.snd i j + u.snd j i)

private theorem extend_div_ae (u : Jet Ω) :
    ⇑(Sobolev.div (extendJet ho.measurableSet u)) =ᵐ[volume.restrict Ω] ⇑(jetDiv u) := by
  have h : restrictScalar Ω (Sobolev.div (extendJet ho.measurableSet u)) = jetDiv u := by
    rw [Sobolev.div_apply, map_sum]
    unfold jetDiv
    apply Finset.sum_congr rfl
    intro i _
    rw [(extendJet_components ho.measurableSet u i i).2, restrict_extendScalar]
  have he := restrictScalar_ae Ω (Sobolev.div (extendJet ho.measurableSet u))
  rw [h] at he
  exact he.symm

private theorem extend_strain_ae (u : Jet Ω) (i j : Fin 3) :
    ⇑(Sobolev.strain (extendJet ho.measurableSet u) i j) =ᵐ[volume.restrict Ω]
      ⇑(jetStrain u i j) := by
  have h : restrictScalar Ω (Sobolev.strain (extendJet ho.measurableSet u) i j) =
      jetStrain u i j := by
    rw [Sobolev.strain_apply, map_smul, map_add, (extendJet_components ho.measurableSet u i j).2,
      (extendJet_components ho.measurableSet u j i).2, restrict_extendScalar, restrict_extendScalar]
    rfl
  have he := restrictScalar_ae Ω (Sobolev.strain (extendJet ho.measurableSet u) i j)
  rw [h] at he
  exact he.symm

/-- The domain form evaluates directly on the restricted strain and divergence classes. -/
theorem lameForm_integral (u v : H1 hΩ) :
    lameForm ho hΩ hl hm u v =
      (∫ x in Ω, lam x * jetDiv u.val x * jetDiv v.val x) +
        2 * ∑ i, ∑ j, ∫ x in Ω, mu x * jetStrain u.val i j x * jetStrain v.val i j x := by
  rw [lameForm_apply, bodyLameForm_apply]
  have hdiv :
      (∫ x in Ω, lam x * Sobolev.div (extendJet ho.measurableSet u.val) x *
        Sobolev.div (extendJet ho.measurableSet v.val) x) =
      ∫ x in Ω, lam x * jetDiv u.val x * jetDiv v.val x := by
    apply integral_congr_ae
    filter_upwards [extend_div_ae ho u.val, extend_div_ae ho v.val] with x hu hv
    rw [hu, hv]
  rw [hdiv]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [extend_strain_ae ho u.val i j, extend_strain_ae ho v.val i j] with x hu hv
  rw [hu, hv]

end LeanSolid.Elastostatics.Sobolev.Domain
