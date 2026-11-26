module

public import LeanSolid.Elastostatics.Sobolev.DomainElasticity
public import LeanSolid.Elastostatics.Sobolev.EuclideanCoordinates
import Mathlib.Tactic.Ring

/-!
Transport of the elastic energy in OpenAI (2026), §2. The Euclidean expressions
follow the companion Basic.lean, div, strain and energy at revision
3344da59991ed94f9ba711217b29c1d760badfa6.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LeanSolid.Elastostatics.Sobolev.Domain

variable {Ω : Set (EuclideanSpace ℝ (Fin 3))}
local notation "body" => coordinates '' Ω

/-- Divergence in the upstream column layout. -/
noncomputable def euclideanDiv (u : EuclideanJet Ω) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, (u.2 i x) i

/-- Strain in the upstream column layout. -/
noncomputable def euclideanStrain (u : EuclideanJet Ω) (i j : Fin 3)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ((u.2 j x) i + (u.2 i x) j) / 2

theorem jetDiv_coordinates_ae (u : EuclideanJet Ω) :
    ⇑(jetDiv (jetCoordinates Ω u)) =ᵐ[volume.restrict body]
      fun x => euclideanDiv u (coordinates.symm x) := by
  unfold jetDiv euclideanDiv
  have h (i : Fin 3) :
      ⇑((jetCoordinates Ω u).snd i i) =ᵐ[volume.restrict body] fun x =>
        (u.2 i (coordinates.symm x)) i := by
    rw [(jetCoordinates_components Ω u i i).2]
    exact vectorCoordinates_ae Ω _ i
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => (jetCoordinates Ω u).snd i i),
    Filter.eventually_all.mpr h] with x hx hy
  rw [hx]
  exact Finset.sum_congr rfl fun i _ => hy i

theorem jetStrain_coordinates_ae (u : EuclideanJet Ω) (i j : Fin 3) :
    ⇑(jetStrain (jetCoordinates Ω u) i j) =ᵐ[volume.restrict body]
      fun x => euclideanStrain u i j (coordinates.symm x) := by
  unfold jetStrain euclideanStrain
  rw [(jetCoordinates_components Ω u i j).2, (jetCoordinates_components Ω u j i).2]
  let a := vectorCoordinates Ω (u.2 j) i
  let b := vectorCoordinates Ω (u.2 i) j
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (a + b), Lp.coeFn_add a b,
    vectorCoordinates_ae Ω (u.2 j) i, vectorCoordinates_ae Ω (u.2 i) j] with x h₁ h₂ h₃ h₄
  change ((1 / 2 : ℝ) • (a + b)) x = _
  simp only [h₁, Pi.smul_apply, h₂, Pi.add_apply, smul_eq_mul, a, b, h₃, h₄]
  ring

/-- The Euclidean virtual-work integral from the paper, written as a sum of the
volumetric integral and the componentwise strain integrals. -/
noncomputable def euclideanEnergy (lam mu : EuclideanSpace ℝ (Fin 3) → ℝ)
    (u v : EuclideanJet Ω) : ℝ :=
  (∫ x in Ω, lam x * euclideanDiv u x * euclideanDiv v x) +
    2 * ∑ i, ∑ j, ∫ x in Ω, mu x * euclideanStrain u i j x * euclideanStrain v i j x

/-- The two coordinate models assign identical energy to the same physical pair. -/
theorem lameForm_eq_euclideanEnergy (hE : Bornology.IsBounded Ω)
    (hΩ : Bornology.IsBounded body) (ho : IsOpen body)
    {lam mu : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hl : ContinuousOn (lam ∘ coordinates.symm) (closure body))
    (hm : ContinuousOn (mu ∘ coordinates.symm) (closure body))
    (u v : EuclideanH1 Ω) :
    lameForm ho hΩ hl hm (h1Coordinates Ω hE hΩ u) (h1Coordinates Ω hE hΩ v) =
      euclideanEnergy lam mu u.val v.val := by
  let e := MeasurableEquiv.toLp 2 (Fin 3 → ℝ)
  have he : MeasurePreserving e (volume.restrict body) (volume.restrict Ω) :=
    coordinates_symm_measurePreservingOn Ω
  rw [lameForm_integral, h1Coordinates_apply_val, h1Coordinates_apply_val]
  unfold euclideanEnergy
  have hd : (∫ x in body, (lam ∘ coordinates.symm) x *
      jetDiv (jetCoordinates Ω u.val) x * jetDiv (jetCoordinates Ω v.val) x) =
      ∫ x in Ω, lam x * euclideanDiv u.val x * euclideanDiv v.val x := by
    refine Eq.trans (integral_congr_ae ?_) (he.integral_comp e.measurableEmbedding _)
    filter_upwards [jetDiv_coordinates_ae u.val, jetDiv_coordinates_ae v.val] with x hx hy
    rw [hx, hy]
    simp only [Function.comp_apply, coordinates_symm_apply, e, MeasurableEquiv.coe_toLp]
  rw [hd]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  refine Eq.trans (integral_congr_ae ?_) (he.integral_comp e.measurableEmbedding _)
  filter_upwards [jetStrain_coordinates_ae u.val i j, jetStrain_coordinates_ae v.val i j]
    with x hx hy
  rw [hx, hy]
  simp only [Function.comp_apply, coordinates_symm_apply, e, MeasurableEquiv.coe_toLp]

/-- Weak equilibrium in the Euclidean convention of the paper. -/
def euclideanSolves (lam mu : EuclideanSpace ℝ (Fin 3) → ℝ)
    (g u : EuclideanH1 Ω) : Prop :=
  euclideanSameTrace Ω u g ∧
    ∀ v : EuclideanH1 Ω, v.val ∈ closure (euclideanTestJets Ω) →
      euclideanEnergy lam mu u.val v.val = 0

set_option maxHeartbeats 1000000 in
/-- The Euclidean and Cartesian weak Dirichlet problems have exactly the same solutions. -/
theorem euclideanSolves_iff (hE : Bornology.IsBounded Ω)
    (hΩ : Bornology.IsBounded body) (ho : IsOpen body)
    {lam mu : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hl : ContinuousOn (lam ∘ coordinates.symm) (closure body))
    (hm : ContinuousOn (mu ∘ coordinates.symm) (closure body))
    (g u : EuclideanH1 Ω) :
    euclideanSolves lam mu g u ↔
      BoundaryResponse.Solves (zeroTraceInH1 hΩ) (lameForm ho hΩ hl hm)
        (h1Coordinates Ω hE hΩ g) (h1Coordinates Ω hE hΩ u) := by
  let e := h1Coordinates Ω hE hΩ
  change (_ ∧ _) ↔ (e u - e g ∈ zeroTraceInH1 hΩ ∧
    ∀ w : zeroTraceInH1 hΩ, lameForm ho hΩ hl hm (e u) w.val = 0)
  refine and_congr (sameTrace_iff_coordinates Ω hE hΩ u g) ?_
  constructor
  · intro h w
    obtain ⟨v, hv⟩ := e.surjective w.val
    have hv' : v.val ∈ closure (euclideanTestJets Ω) :=
      (zeroTrace_iff_coordinates Ω hE hΩ v).mpr (hv.symm ▸ w.property)
    rw [← hv]
    exact (lameForm_eq_euclideanEnergy hE hΩ ho hl hm u v).trans (h v hv')
  · intro h v hv
    have hz := (zeroTrace_iff_coordinates Ω hE hΩ v).mp hv
    exact (lameForm_eq_euclideanEnergy hE hΩ ho hl hm u v).symm.trans (h ⟨e v, hz⟩)

/-- Well-posedness in the Euclidean formulation follows from the Cartesian one. -/
theorem existsUnique_euclideanSolution (hE : Bornology.IsBounded Ω)
    (hΩ : Bornology.IsBounded body) (ho : IsOpen body)
    {lam mu : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hl : ContinuousOn (lam ∘ coordinates.symm) (closure body))
    (hm : ContinuousOn (mu ∘ coordinates.symm) (closure body))
    (hp : ∀ x ∈ closure body, 0 < mu (coordinates.symm x) ∧
      0 < 3 * lam (coordinates.symm x) + 2 * mu (coordinates.symm x)) (g : EuclideanH1 Ω) :
    ∃! u, euclideanSolves lam mu g u := by
  let e := h1Coordinates Ω hE hΩ
  obtain ⟨w, hw, hu⟩ := existsUnique_solution ho hΩ hl hm hp (e g)
  have hsol (v : EuclideanH1 Ω) := euclideanSolves_iff hE hΩ ho hl hm g v
  refine ⟨e.symm w, (hsol _).mpr ?_, fun v hv => e.injective ?_⟩
  · simpa only [e, Equiv.apply_symm_apply] using hw
  · rw [Equiv.apply_symm_apply]
    exact hu (e v) ((hsol v).mp hv)

private theorem vector_entry_memLp (f : EuclideanL2 Ω) (i : Fin 3) :
    MemLp (fun x => f x i) 2 (volume.restrict Ω) := by
  exact (memLp_congr_ae (LeanSolid.Math.splitVectorL2_ae f i)).mp (Lp.memLp _)

private theorem div_memLp (u : EuclideanJet Ω) :
    MemLp (euclideanDiv u) 2 (volume.restrict Ω) := by
  unfold euclideanDiv
  exact memLp_finsetSum Finset.univ fun i _ => vector_entry_memLp (u.2 i) i

private theorem strain_memLp (u : EuclideanJet Ω) (i j : Fin 3) :
    MemLp (euclideanStrain u i j) 2 (volume.restrict Ω) := by
  have h := ((vector_entry_memLp (u.2 j) i).add (vector_entry_memLp (u.2 i) j)).const_smul
    (1 / 2 : ℝ)
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).mp h
  change (1 / 2 : ℝ) * ((u.2 j x) i + (u.2 i x) j) = euclideanStrain u i j x
  unfold euclideanStrain
  ring

private theorem coefficient_memLp_top (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    {a : EuclideanSpace ℝ (Fin 3) → ℝ} (ha : ContinuousOn a (closure Ω)) :
    MemLp a ∞ (volume.restrict Ω) := by
  obtain ⟨C, hC⟩ := hΩ.isCompact_closure.bddAbove_image ha.norm
  refine memLp_top_of_bound ((ha.mono subset_closure).aestronglyMeasurable ho.measurableSet) C ?_
  filter_upwards [self_mem_ae_restrict ho.measurableSet] with x hx
  exact hC ⟨x, subset_closure hx, rfl⟩

private theorem weighted_integrable
    {a f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (ha : MemLp a ∞ (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) :
    Integrable (fun x => a x * f x * g x) (volume.restrict Ω) := by
  have h : MemLp (a * f) 2 (volume.restrict Ω) := ha.mul hf
  exact memLp_one_iff_integrable.mp (h.mul hg)

/-- The separated work integrals equal the single integral used in the
companion Basic.lean energy definition. -/
theorem euclideanEnergy_eq_singleIntegral (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    {lam mu : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω))
    (u v : EuclideanJet Ω) :
    euclideanEnergy lam mu u v =
      ∫ x in Ω, lam x * euclideanDiv u x * euclideanDiv v x +
        2 * mu x * ∑ i, ∑ j, euclideanStrain u i j x * euclideanStrain v i j x := by
  have hL := weighted_integrable (coefficient_memLp_top ho hΩ hl) (div_memLp u) (div_memLp v)
  have hs (i j : Fin 3) : Integrable (fun x => mu x * euclideanStrain u i j x *
      euclideanStrain v i j x) (volume.restrict Ω) :=
    weighted_integrable (coefficient_memLp_top ho hΩ hm) (strain_memLp u i j) (strain_memLp v i j)
  have hi (i : Fin 3) : Integrable (fun x => ∑ j, mu x * euclideanStrain u i j x *
      euclideanStrain v i j x) (volume.restrict Ω) :=
    integrable_finsetSum _ fun j _ => hs i j
  have hS : Integrable (fun x => 2 * ∑ i, ∑ j, mu x * euclideanStrain u i j x *
      euclideanStrain v i j x) (volume.restrict Ω) :=
    (integrable_finsetSum _ fun i _ => hi i).const_mul 2
  have hEq (x : EuclideanSpace ℝ (Fin 3)) :
      2 * mu x * (∑ i, ∑ j, euclideanStrain u i j x * euclideanStrain v i j x) =
      2 * (∑ i, ∑ j, mu x * euclideanStrain u i j x * euclideanStrain v i j x) := by
    rw [mul_assoc]
    congr 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hEq]
  unfold euclideanEnergy
  rw [integral_add hL hS, integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_finsetSum _ (fun j _ => hs _ j)]

set_option maxHeartbeats 1600000 in
/-- The Euclidean DN pairing selects the unique weak solution for the prescribed
boundary class and evaluates its work on a lift of the test class. -/
noncomputable def euclideanDN (hE : Bornology.IsBounded Ω)
    (hΩ : Bornology.IsBounded body) (ho : IsOpen body)
    {lam mu : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hl : ContinuousOn (lam ∘ coordinates.symm) (closure body))
    (hm : ContinuousOn (mu ∘ coordinates.symm) (closure body))
    (hp : ∀ x ∈ closure body, 0 < mu (coordinates.symm x) ∧
      0 < 3 * lam (coordinates.symm x) + 2 * mu (coordinates.symm x))
    (f g : EuclideanTrace Ω) : ℝ :=
  let u := (existsUnique_euclideanSolution hE hΩ ho hl hm hp f.out).exists.choose
  euclideanEnergy lam mu u.val g.out.val

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 300000 in
set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency false in
/-- The Euclidean DN and the LeanSolid domain DN give the same numbers on
corresponding trace classes, for all boundary data. -/
theorem euclideanDN_eq_domainDN (hE : Bornology.IsBounded Ω)
    (hΩ : Bornology.IsBounded body) (ho : IsOpen body)
    {lam mu : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hl : ContinuousOn (lam ∘ coordinates.symm) (closure body))
    (hm : ContinuousOn (mu ∘ coordinates.symm) (closure body))
    (hp : ∀ x ∈ closure body, 0 < mu (coordinates.symm x) ∧
      0 < 3 * lam (coordinates.symm x) + 2 * mu (coordinates.symm x))
    (f g : EuclideanTrace Ω) :
    euclideanDN hE hΩ ho hl hm hp f g =
      dn ho hΩ hl hm hp
        (Quot.mk (fun p q : H1 hΩ => p - q ∈ zeroTraceInH1 hΩ) (h1Coordinates Ω hE hΩ f.out))
        (Quot.mk (fun p q : H1 hΩ => p - q ∈ zeroTraceInH1 hΩ) (h1Coordinates Ω hE hΩ g.out)) :=
  let u := (existsUnique_euclideanSolution hE hΩ ho hl hm hp f.out).exists.choose
  have hu : euclideanSolves lam mu f.out u :=
    (existsUnique_euclideanSolution hE hΩ ho hl hm hp f.out).exists.choose_spec
  have hsol := (euclideanSolves_iff hE hΩ ho hl hm f.out u).mp hu
  (lameForm_eq_euclideanEnergy hE hΩ ho hl hm u g.out).symm.trans
    (dn_on_trace ho hΩ hl hm hp hsol (h1Coordinates Ω hE hΩ g.out)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical trace map with the quotient type used by the physical DN API. -/
noncomputable def dnTraceCoordinates (hE : Bornology.IsBounded Ω)
    (hΩ : Bornology.IsBounded body) :
    EuclideanTrace Ω → BoundaryResponse.Trace (V := H1 hΩ) (zeroTraceInH1 hΩ) :=
  Quot.map (h1Coordinates Ω hE hΩ) fun u v h =>
    (sameTrace_iff_coordinates Ω hE hΩ u v).mp h

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem dnTraceCoordinates_surjective (hE : Bornology.IsBounded Ω)
    (hΩ : Bornology.IsBounded body) : Function.Surjective (dnTraceCoordinates hE hΩ) := by
  intro q
  obtain ⟨u, hu⟩ := (h1Coordinates Ω hE hΩ).surjective q.out
  refine ⟨Quot.mk (euclideanSameTrace Ω) u, ?_⟩
  change Quot.mk (fun p r : H1 hΩ => p - r ∈ zeroTraceInH1 hΩ)
    (h1Coordinates Ω hE hΩ u) = q
  rw [hu]
  exact Quot.out_eq q

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Equality on the Euclidean trace quotient is equivalent to equality of the
corresponding LeanSolid DN maps, for two coefficient pairs. -/
theorem dn_eq_iff_euclideanDN_eq (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded body)
    (ho : IsOpen body) {l₁ m₁ l₂ m₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hl₁ : ContinuousOn (l₁ ∘ coordinates.symm) (closure body))
    (hm₁ : ContinuousOn (m₁ ∘ coordinates.symm) (closure body))
    (hl₂ : ContinuousOn (l₂ ∘ coordinates.symm) (closure body))
    (hm₂ : ContinuousOn (m₂ ∘ coordinates.symm) (closure body))
    (hp₁ : ∀ x ∈ closure body, 0 < m₁ (coordinates.symm x) ∧
      0 < 3 * l₁ (coordinates.symm x) + 2 * m₁ (coordinates.symm x))
    (hp₂ : ∀ x ∈ closure body, 0 < m₂ (coordinates.symm x) ∧
      0 < 3 * l₂ (coordinates.symm x) + 2 * m₂ (coordinates.symm x)) :
    dn ho hΩ hl₁ hm₁ hp₁ = dn ho hΩ hl₂ hm₂ hp₂ ↔
      euclideanDN hE hΩ ho hl₁ hm₁ hp₁ = euclideanDN hE hΩ ho hl₂ hm₂ hp₂ := by
  have happly (hl : ContinuousOn (l₁ ∘ coordinates.symm) (closure body))
      (hm : ContinuousOn (m₁ ∘ coordinates.symm) (closure body)) (f g : EuclideanTrace Ω) :
      euclideanDN hE hΩ ho hl hm hp₁ f g =
        dn ho hΩ hl hm hp₁ (dnTraceCoordinates hE hΩ f) (dnTraceCoordinates hE hΩ g) := by
    have hf := congrArg (dnTraceCoordinates hE hΩ) (Quot.out_eq f)
    have hg := congrArg (dnTraceCoordinates hE hΩ) (Quot.out_eq g)
    rw [← hf, ← hg]
    exact LeanSolid.Elastostatics.Sobolev.Domain.euclideanDN_eq_domainDN hE hΩ ho hl hm hp₁ f g
  have hright (f g : EuclideanTrace Ω) :
      euclideanDN hE hΩ ho hl₂ hm₂ hp₂ f g =
        dn ho hΩ hl₂ hm₂ hp₂ (dnTraceCoordinates hE hΩ f) (dnTraceCoordinates hE hΩ g) := by
    have hf := congrArg (dnTraceCoordinates hE hΩ) (Quot.out_eq f)
    have hg := congrArg (dnTraceCoordinates hE hΩ) (Quot.out_eq g)
    rw [← hf, ← hg]
    exact LeanSolid.Elastostatics.Sobolev.Domain.euclideanDN_eq_domainDN hE hΩ ho hl₂ hm₂ hp₂ f g
  constructor
  · intro h
    funext f g
    rw [happly hl₁ hm₁, hright, h]
  · intro h
    funext f g
    obtain ⟨a, rfl⟩ := dnTraceCoordinates_surjective hE hΩ f
    obtain ⟨b, rfl⟩ := dnTraceCoordinates_surjective hE hΩ g
    rw [← happly hl₁ hm₁, ← hright, h]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- A uniqueness implication for the Euclidean DN map transfers to the Cartesian
Lamé coefficients through the verified conjugacy. -/
theorem coefficients_equal_of_euclidean_uniqueness
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded body) (ho : IsOpen body)
    {l₁ m₁ l₂ m₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hl₁ : ContinuousOn (l₁ ∘ coordinates.symm) (closure body))
    (hm₁ : ContinuousOn (m₁ ∘ coordinates.symm) (closure body))
    (hl₂ : ContinuousOn (l₂ ∘ coordinates.symm) (closure body))
    (hm₂ : ContinuousOn (m₂ ∘ coordinates.symm) (closure body))
    (hp₁ : ∀ x ∈ closure body, 0 < m₁ (coordinates.symm x) ∧
      0 < 3 * l₁ (coordinates.symm x) + 2 * m₁ (coordinates.symm x))
    (hp₂ : ∀ x ∈ closure body, 0 < m₂ (coordinates.symm x) ∧
      0 < 3 * l₂ (coordinates.symm x) + 2 * m₂ (coordinates.symm x))
    (huniq : euclideanDN hE hΩ ho hl₁ hm₁ hp₁ = euclideanDN hE hΩ ho hl₂ hm₂ hp₂ →
      (∀ x ∈ Ω, l₁ x = l₂ x) ∧ (∀ x ∈ Ω, m₁ x = m₂ x))
    (hdn : dn ho hΩ hl₁ hm₁ hp₁ = dn ho hΩ hl₂ hm₂ hp₂) :
    (∀ y ∈ body, l₁ (coordinates.symm y) = l₂ (coordinates.symm y)) ∧
      (∀ y ∈ body, m₁ (coordinates.symm y) = m₂ (coordinates.symm y)) := by
  obtain ⟨hl, hm⟩ := huniq ((dn_eq_iff_euclideanDN_eq hE hΩ ho hl₁ hm₁ hl₂ hm₂ hp₁ hp₂).mp hdn)
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hl x hx
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hm x hx

end LeanSolid.Elastostatics.Sobolev.Domain
