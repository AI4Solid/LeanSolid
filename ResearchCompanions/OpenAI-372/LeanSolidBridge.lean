import LeanSolid.Elastostatics.Sobolev.EuclideanEnergy
import OAI.MathematicalPhysics.Elasticity.Variational

/-!
The paper's variational definitions are from upstream revision
3344da59991ed94f9ba711217b29c1d760badfa6. This adapter identifies the actual
boundary data and proves equality of the two solution operators via uniqueness.
-/

noncomputable section

namespace LeanSolid.Elastostatics.Sobolev.Domain

open Set
open OAI.Elasticity (X Admissible)

variable {Ω : Set X} {lam mu : X → ℝ}

private theorem upstreamEnergy_eq (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω))
    (u v : EuclideanH1 Ω) :
    OAI.Elasticity.energy Ω lam mu u v = euclideanEnergy lam mu u.val v.val :=
  (euclideanEnergy_eq_singleIntegral ho hb hl hm u.val v.val).symm

set_option maxHeartbeats 1600000 in
theorem upstreamDN_eq (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (ha : Admissible Ω lam mu) :
    OAI.Elasticity.DN Ω lam mu =
      euclideanDN hb (coordinates_image_isBounded hb) (coordinates_image_isOpen ho)
        (coordinates_pullback_continuousOn (ha.1.choose_spec.2.2.continuousOn.mono
          ha.1.choose_spec.2.1))
        (coordinates_pullback_continuousOn (ha.2.1.choose_spec.2.2.continuousOn.mono
          ha.2.1.choose_spec.2.1))
        (fun _ hx => ha.2.2 _ (coordinates_symm_mem_closure hx)) := by
  have hl : ContinuousOn lam (closure Ω) :=
    ha.1.choose_spec.2.2.continuousOn.mono ha.1.choose_spec.2.1
  have hm : ContinuousOn mu (closure Ω) :=
    ha.2.1.choose_spec.2.2.continuousOn.mono ha.2.1.choose_spec.2.1
  funext f g
  let u := OAI.Elasticity.dirichletSolution Ω lam mu f
  obtain ⟨htrace, hweak⟩ := OAI.Elasticity.dirichletSolution_spec ha ho hb f
  have hu : euclideanSolves lam mu f.out u := by
    constructor
    · exact (OAI.Elasticity.trace_eq_iff u f.out).mp (htrace.trans (Quot.out_eq f).symm)
    · intro v hv
      rw [← upstreamEnergy_eq ho hb hl hm u v]
      exact hweak v hv
  let hex := existsUnique_euclideanSolution hb (coordinates_image_isBounded hb)
    (coordinates_image_isOpen ho) (coordinates_pullback_continuousOn hl)
    (coordinates_pullback_continuousOn hm)
    (fun _ hx => ha.2.2 _ (coordinates_symm_mem_closure hx)) f.out
  have hsol : u = hex.exists.choose :=
    hex.unique hu hex.exists.choose_spec
  change OAI.Elasticity.energy Ω lam mu u g.out =
    euclideanEnergy lam mu hex.exists.choose.val g.out.val
  rw [upstreamEnergy_eq ho hb hl hm u g.out, hsol]

/-- Full-data uniqueness for the Cartesian formulation on the paper's domains. -/
def CartesianUniqueness : Prop :=
    ∀ {Ω : Set X} (hD : OAI.Elasticity.Domain Ω)
    {l₁ m₁ l₂ m₂ : X → ℝ}
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂),
    let hb := coordinates_image_isBounded hD.2.2.1
    let ho := coordinates_image_isOpen hD.1
    let hl₁ := coordinates_pullback_continuousOn
      (ha₁.1.choose_spec.2.2.continuousOn.mono ha₁.1.choose_spec.2.1)
    let hm₁ := coordinates_pullback_continuousOn
      (ha₁.2.1.choose_spec.2.2.continuousOn.mono ha₁.2.1.choose_spec.2.1)
    let hl₂ := coordinates_pullback_continuousOn
      (ha₂.1.choose_spec.2.2.continuousOn.mono ha₂.1.choose_spec.2.1)
    let hm₂ := coordinates_pullback_continuousOn
      (ha₂.2.1.choose_spec.2.2.continuousOn.mono ha₂.2.1.choose_spec.2.1)
    let hp₁ := fun (y : Fin 3 → ℝ) (hx : y ∈ closure (coordinates '' Ω)) =>
      ha₁.2.2 _ (coordinates_symm_mem_closure hx)
    let hp₂ := fun (y : Fin 3 → ℝ) (hx : y ∈ closure (coordinates '' Ω)) =>
      ha₂.2.2 _ (coordinates_symm_mem_closure hx)
    dn ho hb hl₁ hm₁ hp₁ = dn ho hb hl₂ hm₂ hp₂ →
      (∀ y ∈ coordinates '' Ω, l₁ (coordinates.symm y) = l₂ (coordinates.symm y)) ∧
      (∀ y ∈ coordinates '' Ω, m₁ (coordinates.symm y) = m₂ (coordinates.symm y))

set_option maxHeartbeats 1600000 in
/-- Transfer the upstream MainClaim to the Cartesian domain formulation. -/
theorem coefficients_equal_of_upstream_mainClaim (main : OAI.Elasticity.MainClaim) :
    CartesianUniqueness := by
  intro Ω hD l₁ m₁ l₂ m₂ ha₁ ha₂
  dsimp only
  intro hdn
  refine coefficients_equal_of_euclidean_uniqueness hD.2.2.1 _ _ _ _ _ _ _ _ ?_ hdn
  intro he
  apply main Ω hD l₁ m₁ l₂ m₂ ha₁ ha₂
  rw [upstreamDN_eq hD.1 hD.2.2.1 ha₁, upstreamDN_eq hD.1 hD.2.2.1 ha₂]
  exact he

end LeanSolid.Elastostatics.Sobolev.Domain
