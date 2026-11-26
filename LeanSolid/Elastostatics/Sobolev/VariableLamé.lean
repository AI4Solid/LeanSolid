module

public import LeanSolid.Elastostatics.Sobolev.Existence
public import LeanSolid.Elastostatics.BoundaryResponse
public import LeanSolid.Math.BoundedMultiplier
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Classical

namespace LeanSolid.Elastostatics.Sobolev

variable {n : ℕ}

/-- A bounded Lamé coefficient represented as an almost-everywhere equivalence class. -/
noncomputable abbrev Coefficient (n : ℕ) := Lp ℝ ∞ (volume : Measure (Fin n → ℝ))

/-- The weighted product of two copies of a scalar differential component. -/
noncomputable def weightedComponent (c : Coefficient n) (d : G n →L[ℝ] L2 n) :
    G n →L[ℝ] G n →L[ℝ] ℝ :=
  (innerSL ℝ (E := L2 n)).bilinearComp ((LeanSolid.Math.l2Multiplier c).comp d) d

theorem weightedComponent_apply (c : Coefficient n) (d : G n →L[ℝ] L2 n) (u v : G n) :
    weightedComponent c d u v = ∫ x, c x * d u x * d v x := by
  rw [weightedComponent, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
  exact LeanSolid.Math.l2Multiplier_inner c (d u) (d v)

/-- The scalar strain component used in the variable-coefficient form. -/
noncomputable def strainComponent (i j : Fin n) : G n →L[ℝ] L2 n :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => L2 n) j).comp
    ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => Vec n) i).comp strain)

theorem strainComponent_apply (i j : Fin n) (u : G n) :
    strainComponent i j u = strain u i j := by unfold strainComponent; rfl

/-- The Lamé form with two spatially varying essentially bounded coefficients. -/
noncomputable def variableLameForm (lam mu : Coefficient n) : G n →L[ℝ] G n →L[ℝ] ℝ :=
  weightedComponent lam div + 2 • ∑ i, ∑ j, weightedComponent mu (strainComponent i j)

set_option synthInstance.maxHeartbeats 100000 in
theorem variableLameForm_apply (lam mu : Coefficient n) (u v : G n) :
    variableLameForm lam mu u v = (∫ x, lam x * div u x * div v x) +
      2 * ∑ i, ∑ j, ∫ x, mu x * strain u i j x * strain v i j x := by
  simp only [variableLameForm, two_nsmul, add_apply, sum_apply,
    weightedComponent_apply, strainComponent_apply]
  ring

/-- Spatial variation preserves Betti symmetry of the bilinear form. -/
theorem variableLameForm_comm (lam mu : Coefficient n) (u v : G n) :
    variableLameForm lam mu u v = variableLameForm lam mu v u := by
  simp only [variableLameForm_apply, mul_assoc, mul_comm (div u _), mul_comm (strain u _ _ _)]

/-- A uniform strain-energy bound gives coercivity on the zero-trace space of any bounded
domain, using the existing Korn and Poincaré inequalities. -/
theorem variableLameForm_coercive [NeZero n] {Ω : Set (Fin n → ℝ)}
    (hΩ : Bornology.IsBounded Ω) {lam mu : Coefficient n} {c : ℝ} (hc : 0 < c)
    (hbound : ∀ U : H10 Ω, c * ‖strain (U : G n)‖ ^ 2 ≤ variableLameForm lam mu U U) :
    IsCoercive ((variableLameForm lam mu).bilinearComp (H10 Ω).subtypeL (H10 Ω).subtypeL) := by
  obtain ⟨R, hR⟩ := exists_slab hΩ
  let C := 2 * (1 + 4 * R ^ 2)
  have hC : 0 < C := by unfold C; positivity
  refine ⟨c / C, div_pos hc hC, fun U => ?_⟩
  have hp := poincare 0 hR U.property
  have hk := korn_first U.property
  have hn : ‖(U : G n)‖ ^ 2 ≤ C * ‖strain (U : G n)‖ ^ 2 := by
    rw [norm_sq_eq]
    calc
      _ ≤ (1 + 4 * R ^ 2) * ‖grad (U : G n)‖ ^ 2 := by linarith
      _ ≤ (1 + 4 * R ^ 2) * (2 * ‖strain (U : G n)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by unfold C; ring
  change c / C * ‖(U : G n)‖ * ‖(U : G n)‖ ≤ variableLameForm lam mu U U
  rw [show c / C * ‖(U : G n)‖ * ‖(U : G n)‖ = (c / C) * ‖(U : G n)‖ ^ 2 by ring]
  exact (mul_le_mul_of_nonneg_left hn (div_pos hc hC).le).trans
    (by simpa [← mul_assoc, div_mul_cancel₀ c hC.ne'] using hbound U)

/-- First variable-coefficient Dirichlet interface, on a prescribed ambient lift. -/
theorem existsUnique_variableDirichlet [NeZero n] {Ω : Set (Fin n → ℝ)}
    (hΩ : Bornology.IsBounded Ω) {lam mu : Coefficient n} {c : ℝ} (hc : 0 < c)
    (hbound : ∀ U : H10 Ω, c * ‖strain (U : G n)‖ ^ 2 ≤ variableLameForm lam mu U U)
    (g : G n) : ∃! u, BoundaryResponse.Solves (H10 Ω) (variableLameForm lam mu) g u := by
  let : CompleteSpace (H10 Ω) :=
    (Submodule.isClosed_topologicalClosure (LinearMap.range (graph Ω))).completeSpace_coe
  exact BoundaryResponse.existsUnique_solution (H10 Ω) _ (variableLameForm_coercive hΩ hc hbound) g

/-- Equal boundary responses imply the two weighted Lamé work integrals agree on
solutions of their respective coefficient systems. -/
theorem variableLame_work_eq_of_dn_eq (N : Submodule ℝ (G n)) [CompleteSpace N]
    {lam₁ mu₁ lam₂ mu₂ : Coefficient n}
    (hc₁ : IsCoercive ((variableLameForm lam₁ mu₁).bilinearComp N.subtypeL N.subtypeL))
    (hc₂ : IsCoercive ((variableLameForm lam₂ mu₂).bilinearComp N.subtypeL N.subtypeL))
    (hDN : BoundaryResponse.dn N (variableLameForm lam₁ mu₁) hc₁ =
      BoundaryResponse.dn N (variableLameForm lam₂ mu₂) hc₂)
    {f g u v : G n}
    (hu : BoundaryResponse.Solves N (variableLameForm lam₁ mu₁) f u)
    (hv : BoundaryResponse.Solves N (variableLameForm lam₂ mu₂) g v) :
    (∫ x, lam₁ x * div u x * div v x) +
      2 * (∑ i, ∑ j, ∫ x, mu₁ x * strain u i j x * strain v i j x) =
    (∫ x, lam₂ x * div u x * div v x) +
      2 * (∑ i, ∑ j, ∫ x, mu₂ x * strain u i j x * strain v i j x) := by
  rw [← variableLameForm_apply, ← variableLameForm_apply]
  exact BoundaryResponse.alessandrini_of_dn_eq hc₁ hc₂
    (variableLameForm_comm lam₂ mu₂) hDN hu hv

/-- A common positive margin for the shear and bulk conditions on a compact set.
See OpenAI (2026), companion Variational.lean, Admissible.uniform_positive. -/
theorem uniform_lame_margin {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {lam mu : X → ℝ} (hl : ContinuousOn lam K) (hm : ContinuousOn mu K)
    (hp : ∀ x ∈ K, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ mu x ∧ c ≤ 3 * lam x + 2 * mu x := by
  have h := hm.inf ((hl.const_mul 3).add (hm.const_mul 2))
  obtain ⟨c, hc, hle⟩ := hK.exists_forall_le' h
    (fun x hx => lt_min (hp x hx).1 (hp x hx).2)
  exact ⟨c, hc, fun x hx => le_min_iff.mp (hle x hx)⟩

/-- The three-dimensional energy density controls the Frobenius strain energy
throughout the positive bulk/shear regime, including negative lambda.
Compare OpenAI (2026), companion Variational.lean, elasticity_density_lower. -/
theorem lame_density_lower (lam mu c : ℝ) (hc : 0 ≤ c) (hm : c ≤ mu)
    (hk : c ≤ 3 * lam + 2 * mu) (A : Fin 3 → Fin 3 → ℝ) :
    c * (∑ i, ∑ j, A i j ^ 2) ≤
      lam * (∑ i, A i i) ^ 2 + 2 * mu * (∑ i, ∑ j, A i j ^ 2) := by
  have hA : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))
  by_cases hl : 0 ≤ lam
  · nlinarith only [mul_nonneg hl (sq_nonneg (∑ i, A i i)),
      mul_le_mul_of_nonneg_right hm hA, mul_nonneg (hc.trans hm) hA]
  · have hd : (∑ i, A i i) ^ 2 ≤ 3 * ∑ i, A i i ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => A i i)
    have ht : (∑ i, A i i) ^ 2 ≤ 3 * ∑ i, ∑ j, A i j ^ 2 :=
      hd.trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)) (by norm_num))
    nlinarith only [mul_le_mul_of_nonpos_left ht (le_of_not_ge hl),
      mul_le_mul_of_nonneg_right hk hA]

private theorem integrable_weighted (c : Coefficient n) (u v : L2 n) :
    Integrable (fun x => c x * u x * v x) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (LeanSolid.Math.l2Multiplier c u) v).congr ?_
  filter_upwards [Lp.coeFn_lpSMul c u (r := 2)] with x hx
  change (c • u : L2 n) x = _ at hx
  rw [LeanSolid.Math.l2Multiplier_apply]
  rw [hx]
  simp [mul_comm]

private theorem integral_scalar_sq (f : L2 n) : (∫ x, f x ^ 2) = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [pow_two]

/-- Integrating the pointwise margin yields the lower bound required by the variable
coefficient Dirichlet theorem. The margin here is on the ambient coefficient extension. -/
theorem variableLameForm_lower_of_ae_margin {lam mu : Coefficient 3} {c : ℝ} (hc : 0 ≤ c)
    (hpos : ∀ᵐ x, c ≤ mu x ∧ c ≤ 3 * lam x + 2 * mu x) (U : G 3) :
    c * ‖strain U‖ ^ 2 ≤ variableLameForm lam mu U U := by
  let E (i j : Fin 3) := strain U i j
  have hDiag (i : Fin 3) : E i i = grad U i i := by
    dsimp [E]
    rw [strain_apply, ← two_smul ℝ, smul_smul]
    norm_num
  have ht : div U = ∑ i, E i i := by simp only [div_apply, hDiag]
  have htrace : ∀ᵐ x, div U x = ∑ i, E i i x := by
    rw [ht]
    exact Lp.coeFn_fun_finsetSum _ _
  have hI (i j : Fin 3) : Integrable (fun x => E i j x ^ 2) := by
    convert L2.integrable_inner (𝕜 := ℝ) (E i j) (E i j) using 1
    funext x
    simp [pow_two]
  have hM (i j : Fin 3) : Integrable (fun x => mu x * E i j x * E i j x) :=
    integrable_weighted mu _ _
  have hL : Integrable (fun x => lam x * div U x * div U x) :=
    integrable_weighted lam _ _
  have h0 : Integrable (fun x => ∑ i, ∑ j, E i j x ^ 2) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j
  have h1 : Integrable (fun x => ∑ i, ∑ j, mu x * E i j x * E i j x) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hM i j
  have h := integral_mono_ae (h0.const_mul c) (hL.add (h1.const_mul 2)) (by
    filter_upwards [hpos, htrace] with x hx ht'
    change c * (∑ i, ∑ j, E i j x ^ 2) ≤
      lam x * div U x * div U x + 2 * ∑ i, ∑ j, mu x * E i j x * E i j x
    rw [ht']
    have hl := lame_density_lower (lam x) (mu x) c hc hx.1 hx.2 (fun i j => E i j x)
    have hm : (∑ i, ∑ j, mu x * E i j x * E i j x) = mu x * ∑ i, ∑ j, E i j x ^ 2 := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hm]
    convert hl using 1; ring)
  have h2 : Integrable (fun x => 2 * ∑ i, ∑ j, mu x * E i j x * E i j x) :=
    h1.const_mul 2
  change (∫ x, c * (∑ i, ∑ j, E i j x ^ 2)) ≤
    (∫ x, lam x * div U x * div U x + 2 * ∑ i, ∑ j, mu x * E i j x * E i j x) at h
  rw [integral_const_mul, integral_add hL h2, integral_const_mul,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hM i j)] at h
  simp_rw [integral_finsetSum _ (fun j _ => hI _ j),
    integral_finsetSum _ (fun j _ => hM _ j), integral_scalar_sq] at h
  simpa only [variableLameForm_apply, norm_mat_sq, E] using h

/-- Three-dimensional variable-coefficient Dirichlet well-posedness under an almost-everywhere
uniform Lamé margin, with a supplied lift. -/
theorem existsUnique_variableDirichlet_of_ae_margin {Ω : Set (Fin 3 → ℝ)}
    (hΩ : Bornology.IsBounded Ω) {lam mu : Coefficient 3} {c : ℝ} (hc : 0 < c)
    (hpos : ∀ᵐ x, c ≤ mu x ∧ c ≤ 3 * lam x + 2 * mu x) (g : G 3) :
    ∃! u, BoundaryResponse.Solves (H10 Ω) (variableLameForm lam mu) g u :=
  existsUnique_variableDirichlet hΩ hc (fun U => variableLameForm_lower_of_ae_margin hc.le hpos U) g

private theorem memLp_piecewise_const {Ω : Set (Fin 3 → ℝ)}
    (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω)
    {f : (Fin 3 → ℝ) → ℝ} (hf : ContinuousOn f (closure Ω)) (d : ℝ) :
    MemLp (Ω.piecewise f (fun _ => d)) ∞ volume := by
  have hmeas := (hf.mono subset_closure).aestronglyMeasurable (μ := volume) ho.measurableSet
  obtain ⟨B, hB⟩ := hΩ.isCompact_closure.bddAbove_image hf.norm
  refine memLp_top_of_bound (hmeas.piecewise ho.measurableSet.nullMeasurableSet
    aestronglyMeasurable_const) (max B ‖d‖) ?_
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ Ω
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      exact (hB ⟨x, subset_closure hx, rfl⟩).trans (le_max_left _ _)
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact le_max_right _ _

/-- Admissible coefficients on a bounded open body admit bounded ambient extensions
with a uniform margin and the original values almost everywhere in the body. -/
theorem exists_admissible_coefficients {Ω : Set (Fin 3 → ℝ)}
    (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω) {lam mu : (Fin 3 → ℝ) → ℝ}
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω))
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) :
    ∃ (l m : Coefficient 3) (c : ℝ), 0 < c ∧
      (⇑l =ᵐ[volume.restrict Ω] lam) ∧ (⇑m =ᵐ[volume.restrict Ω] mu) ∧
      (∀ᵐ x, c ≤ m x ∧ c ≤ 3 * l x + 2 * m x) := by
  classical
  obtain ⟨c, hc, hb⟩ := uniform_lame_margin hΩ.isCompact_closure hl hm hp
  let L := Ω.piecewise lam (fun _ => 0)
  let M := Ω.piecewise mu (fun _ => c)
  have hL : MemLp L ∞ volume := memLp_piecewise_const ho hΩ hl 0
  have hM : MemLp M ∞ volume := memLp_piecewise_const ho hΩ hm c
  refine ⟨hL.toLp L, hM.toLp M, c, hc, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hL.coeFn_toLp,
      self_mem_ae_restrict ho.measurableSet] with x hx hs
    exact hx.trans (Set.piecewise_eq_of_mem _ _ _ hs)
  · filter_upwards [ae_restrict_of_ae hM.coeFn_toLp,
      self_mem_ae_restrict ho.measurableSet] with x hx hs
    exact hx.trans (Set.piecewise_eq_of_mem _ _ _ hs)
  · filter_upwards [hL.coeFn_toLp, hM.coeFn_toLp] with x hx hy
    rw [hx, hy]
    by_cases hs : x ∈ Ω
    · simpa [L, M, Set.piecewise_eq_of_mem _ _ _ hs] using hb x (subset_closure hs)
    · simp [L, M, Set.piecewise_eq_of_notMem _ _ _ hs, show c ≤ 2 * c by linarith]

/-- The domain positivity conditions of the smooth elasticity inverse problem give a
well-posed forward problem on every prescribed lift, via bounded ambient coefficients. -/
theorem existsUnique_variableDirichlet_of_admissible {Ω : Set (Fin 3 → ℝ)}
    (ho : IsOpen Ω) (hΩ : Bornology.IsBounded Ω) {lam mu : (Fin 3 → ℝ) → ℝ}
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω))
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) :
    ∃ l m : Coefficient 3,
      (⇑l =ᵐ[volume.restrict Ω] lam) ∧ (⇑m =ᵐ[volume.restrict Ω] mu) ∧
      ∀ g : G 3, ∃! u, BoundaryResponse.Solves (H10 Ω) (variableLameForm l m) g u := by
  obtain ⟨l, m, c, hc, hL, hM, hpos⟩ := exists_admissible_coefficients ho hΩ hl hm hp
  exact ⟨l, m, hL, hM, fun g => existsUnique_variableDirichlet_of_ae_margin hΩ hc hpos g⟩

private noncomputable def restrictL2 (s : Set (Fin n → ℝ)) :
    L2 n →L[ℝ] Lp ℝ 2 (volume.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using Measure.restrict_le_self)

private theorem restrictL2_ae (s : Set (Fin n → ℝ)) (w : L2 n) :
    ⇑(restrictL2 s w) =ᵐ[volume.restrict s] ⇑w := by
  unfold restrictL2
  exact Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

/-- Zero-trace gradients, viewed as ambient L² functions, vanish outside the body. -/
theorem grad_ae_zero_compl {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    {U : G n} (hU : U ∈ H10 Ω) (i j : Fin n) :
    ∀ᵐ x ∂volume.restrict Ωᶜ, grad U i j x = 0 := by
  let d : G n →L[ℝ] L2 n :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => L2 n) j).comp
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => Vec n) i).comp grad)
  let A := (restrictL2 Ωᶜ).comp d
  have hclosed : IsClosed {W : G n | A W = 0} := isClosed_eq A.continuous continuous_const
  have hsub : Set.range (graph Ω) ⊆ {W : G n | A W = 0} := by
    rintro _ ⟨w, rfl⟩
    change restrictL2 Ωᶜ (toL2 (LeanSolid.Math.partialDeriv (w.val i) j)) = 0
    apply Lp.ext
    have he := (memLp_pd_of_mem w.property i j).coeFn_toLp
    filter_upwards [restrictL2_ae Ωᶜ (toL2 (LeanSolid.Math.partialDeriv (w.val i) j)),
      ae_restrict_of_ae he, Lp.coeFn_zero ℝ 2 (volume.restrict Ωᶜ),
      self_mem_ae_restrict hΩ.compl] with x hR hE hZ hx
    have hs : x ∉ tsupport (LeanSolid.Math.partialDeriv (w.val i) j) := fun h =>
      hx ((w.property i).2.2 ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)) h))
    rw [hR]
    rw [toL2_of_memLp (memLp_pd_of_mem w.property i j), hE, hZ]
    exact image_eq_zero_of_notMem_tsupport hs
  have hmem : U ∈ closure (Set.range (graph Ω)) := by
    rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
    exact hU
  have hz : A U = 0 := closure_minimal hsub hclosed hmem
  change restrictL2 Ωᶜ (grad U i j) = 0 at hz
  have he := restrictL2_ae Ωᶜ (grad U i j)
  rw [hz] at he
  filter_upwards [he, Lp.coeFn_zero ℝ 2 (volume.restrict Ωᶜ)] with x hx h0
  exact hx.symm.trans h0

theorem strain_ae_zero_compl {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    {U : G n} (hU : U ∈ H10 Ω) (i j : Fin n) :
    ∀ᵐ x ∂volume.restrict Ωᶜ, strain U i j x = 0 := by
  rw [strain_apply]
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (1 / 2 : ℝ) (grad U i j + grad U j i)),
    ae_restrict_of_ae (Lp.coeFn_add (grad U i j) (grad U j i)),
    grad_ae_zero_compl hΩ hU i j, grad_ae_zero_compl hΩ hU j i] with x h₁ h₂ h₃ h₄
  simp only [h₁, Pi.smul_apply, Pi.add_apply, h₂, h₃, h₄, add_zero, smul_zero]

theorem div_ae_zero_compl {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    {U : G n} (hU : U ∈ H10 Ω) :
    ∀ᵐ x ∂volume.restrict Ωᶜ, div U x = 0 := by
  rw [div_apply]
  have hall : ∀ᵐ x ∂volume.restrict Ωᶜ, ∀ i : Fin n, grad U i i x = 0 :=
    Filter.eventually_all.mpr fun i => grad_ae_zero_compl hΩ hU i i
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_fun_finsetSum Finset.univ (fun i => grad U i i)),
    hall] with x he hz
  rw [he]
  simp only [hz, Finset.sum_const_zero]

/-- Virtual work against a zero-trace test field is independent of coefficient values
outside the physical domain. -/
theorem variableLameForm_eq_of_domain_coefficients {Ω : Set (Fin n → ℝ)}
    (hΩ : MeasurableSet Ω) {l₁ m₁ l₂ m₂ : Coefficient n}
    (hl : ⇑l₁ =ᵐ[volume.restrict Ω] ⇑l₂) (hm : ⇑m₁ =ᵐ[volume.restrict Ω] ⇑m₂)
    (U : G n) (W : H10 Ω) :
    variableLameForm l₁ m₁ U W = variableLameForm l₂ m₂ U W := by
  have he (c₁ c₂ : Coefficient n) (h : ⇑c₁ =ᵐ[volume.restrict Ω] ⇑c₂)
      (f g : L2 n) (hg : ∀ᵐ x ∂volume.restrict Ωᶜ, g x = 0) :
      (∫ x, c₁ x * f x * g x) = ∫ x, c₂ x * f x * g x := by
    apply integral_congr_ae
    change ∀ᵐ x, c₁ x * f x * g x = c₂ x * f x * g x
    have H : ∀ᵐ x ∂volume.restrict (Ω ∪ Ωᶜ), c₁ x * f x * g x = c₂ x * f x * g x :=
      (ae_restrict_union_iff _ _ _).mpr
        ⟨h.mono fun x hx => by rw [hx], hg.mono fun x hx => by simp [hx]⟩
    simpa only [Set.union_compl_self, Measure.restrict_univ] using H
  rw [variableLameForm_apply, variableLameForm_apply,
    he l₁ l₂ hl _ _ (div_ae_zero_compl hΩ W.property)]
  congr 2
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    he m₁ m₂ hm _ _ (strain_ae_zero_compl hΩ W.property i j)

/-- The original coefficients on the body determine the weak equation for every
ambient representative of the displacement. -/
theorem variableDirichlet_iff_of_domain_coefficients {Ω : Set (Fin n → ℝ)}
    (hΩ : MeasurableSet Ω) {l₁ m₁ l₂ m₂ : Coefficient n}
    (hl : ⇑l₁ =ᵐ[volume.restrict Ω] ⇑l₂) (hm : ⇑m₁ =ᵐ[volume.restrict Ω] ⇑m₂)
    (g U : G n) :
    BoundaryResponse.Solves (H10 Ω) (variableLameForm l₁ m₁) g U ↔
      BoundaryResponse.Solves (H10 Ω) (variableLameForm l₂ m₂) g U := by
  unfold BoundaryResponse.Solves
  refine and_congr_right fun _ => forall_congr' fun W => ?_
  rw [variableLameForm_eq_of_domain_coefficients hΩ hl hm U W]

/-- The physical energy integrates only over the body. Coefficients are represented
by zero extension for this pairing, including when both lifts have nonzero trace. -/
noncomputable def bodyLameForm {Ω : Set (Fin 3 → ℝ)} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {lam mu : (Fin 3 → ℝ) → ℝ}
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω)) :
    G 3 →L[ℝ] G 3 →L[ℝ] ℝ :=
  variableLameForm
    ((memLp_piecewise_const ho hΩ hl 0).toLp (Ω.piecewise lam (fun _ => 0)))
    ((memLp_piecewise_const ho hΩ hm 0).toLp (Ω.piecewise mu (fun _ => 0)))

theorem bodyLameForm_apply {Ω : Set (Fin 3 → ℝ)} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {lam mu : (Fin 3 → ℝ) → ℝ}
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω)) (u v : G 3) :
    bodyLameForm ho hΩ hl hm u v =
      (∫ x in Ω, lam x * div u x * div v x) +
        2 * ∑ i, ∑ j, ∫ x in Ω, mu x * strain u i j x * strain v i j x := by
  have h (f : (Fin 3 → ℝ) → ℝ) (hf : ContinuousOn f (closure Ω)) (a b : L2 3) :
      (∫ x, ((memLp_piecewise_const ho hΩ hf 0).toLp _) x * a x * b x) =
        ∫ x in Ω, f x * a x * b x := by
    rw [← integral_indicator ho.measurableSet]
    apply integral_congr_ae
    filter_upwards [(memLp_piecewise_const ho hΩ hf 0).coeFn_toLp] with x hx
    rw [hx]
    by_cases hs : x ∈ Ω
    · rw [Set.piecewise_eq_of_mem _ _ _ hs, Set.indicator_of_mem hs]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hs, Set.indicator_of_notMem hs, zero_mul, zero_mul]
  simp only [bodyLameForm, variableLameForm_apply]
  rw [h lam hl (div u) (div v)]
  congr 2
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    h mu hm (strain u i j) (strain v i j)

/-- Coercivity of the three-dimensional body energy, under the pointwise admissibility
assumptions used in the smooth elasticity inverse problem. -/
theorem bodyLameForm_coercive {Ω : Set (Fin 3 → ℝ)} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {lam mu : (Fin 3 → ℝ) → ℝ}
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω))
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) :
    IsCoercive ((bodyLameForm ho hΩ hl hm).bilinearComp (H10 Ω).subtypeL (H10 Ω).subtypeL) := by
  obtain ⟨l, m, c, hc, hl', hm', hpos⟩ := exists_admissible_coefficients ho hΩ hl hm hp
  have hlocal (f : (Fin 3 → ℝ) → ℝ) (hf : ContinuousOn f (closure Ω)) :
      ⇑((memLp_piecewise_const ho hΩ hf 0).toLp _) =ᵐ[volume.restrict Ω] f := by
    filter_upwards [ae_restrict_of_ae (memLp_piecewise_const ho hΩ hf 0).coeFn_toLp,
      self_mem_ae_restrict ho.measurableSet] with x hx hs
    exact hx.trans (Set.piecewise_eq_of_mem _ _ _ hs)
  have he (U : H10 Ω) :
      bodyLameForm ho hΩ hl hm U U = variableLameForm l m U U := by
    unfold bodyLameForm
    exact variableLameForm_eq_of_domain_coefficients ho.measurableSet
      ((hlocal lam hl).trans hl'.symm) ((hlocal mu hm).trans hm'.symm) U U
  obtain ⟨K, hK, hb⟩ := variableLameForm_coercive hΩ hc
    (fun U => variableLameForm_lower_of_ae_margin hc.le hpos (U : G 3))
  refine ⟨K, hK, fun U => ?_⟩
  simp only [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply] at hb ⊢
  rw [he U]
  exact hb U

/-- The physical variable-coefficient Dirichlet problem on a prescribed ambient lift. -/
theorem existsUnique_bodyDirichlet {Ω : Set (Fin 3 → ℝ)} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {lam mu : (Fin 3 → ℝ) → ℝ}
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω))
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) (g : G 3) :
    ∃! u, BoundaryResponse.Solves (H10 Ω) (bodyLameForm ho hΩ hl hm) g u := by
  let : CompleteSpace (H10 Ω) := (isClosed_H10 Ω).completeSpace_coe
  exact BoundaryResponse.existsUnique_solution (H10 Ω) _ (bodyLameForm_coercive ho hΩ hl hm hp) g

/-- The DN pairing of the body energy on the current ambient lift quotient. -/
noncomputable def bodyDN {Ω : Set (Fin 3 → ℝ)} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {lam mu : (Fin 3 → ℝ) → ℝ}
    (hl : ContinuousOn lam (closure Ω)) (hm : ContinuousOn mu (closure Ω))
    (hp : ∀ x ∈ closure Ω, 0 < mu x ∧ 0 < 3 * lam x + 2 * mu x) :
    BoundaryResponse.Trace (H10 Ω) → BoundaryResponse.Trace (H10 Ω) → ℝ :=
  BoundaryResponse.dn (H10 Ω) (bodyLameForm ho hΩ hl hm)
    (bodyLameForm_coercive ho hΩ hl hm hp)

/-- Equal DN pairings give equal physical two-material work integrals on the body. -/
theorem body_work_eq_of_dn_eq {Ω : Set (Fin 3 → ℝ)} (ho : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) {l₁ m₁ l₂ m₂ : (Fin 3 → ℝ) → ℝ}
    (hl₁ : ContinuousOn l₁ (closure Ω)) (hm₁ : ContinuousOn m₁ (closure Ω))
    (hl₂ : ContinuousOn l₂ (closure Ω)) (hm₂ : ContinuousOn m₂ (closure Ω))
    (hp₁ : ∀ x ∈ closure Ω, 0 < m₁ x ∧ 0 < 3 * l₁ x + 2 * m₁ x)
    (hp₂ : ∀ x ∈ closure Ω, 0 < m₂ x ∧ 0 < 3 * l₂ x + 2 * m₂ x)
    (hDN : bodyDN ho hΩ hl₁ hm₁ hp₁ = bodyDN ho hΩ hl₂ hm₂ hp₂)
    {f g u v : G 3}
    (hu : BoundaryResponse.Solves (H10 Ω) (bodyLameForm ho hΩ hl₁ hm₁) f u)
    (hv : BoundaryResponse.Solves (H10 Ω) (bodyLameForm ho hΩ hl₂ hm₂) g v) :
    (∫ x in Ω, l₁ x * div u x * div v x) +
      2 * (∑ i, ∑ j, ∫ x in Ω, m₁ x * strain u i j x * strain v i j x) =
    (∫ x in Ω, l₂ x * div u x * div v x) +
      2 * (∑ i, ∑ j, ∫ x in Ω, m₂ x * strain u i j x * strain v i j x) := by
  rw [← bodyLameForm_apply ho hΩ hl₁ hm₁, ← bodyLameForm_apply ho hΩ hl₂ hm₂]
  unfold bodyDN at hDN
  exact BoundaryResponse.alessandrini_of_dn_eq
    (bodyLameForm_coercive ho hΩ hl₁ hm₁ hp₁) (bodyLameForm_coercive ho hΩ hl₂ hm₂ hp₂)
    (fun p q => by unfold bodyLameForm; exact variableLameForm_comm _ _ p q) hDN hu hv

end LeanSolid.Elastostatics.Sobolev
