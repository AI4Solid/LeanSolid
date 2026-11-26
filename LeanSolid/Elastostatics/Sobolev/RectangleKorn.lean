module

public import LeanSolid.Elastostatics.Sobolev.RectangleWeak
public import LeanSolid.Math.CompactEstimate
import LeanSolid.Elastostatics.Korn.RectangleExtension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

@[expose] public section

open MeasureTheory Set
open scoped InnerProductSpace ContDiff

namespace LeanSolid.Elastostatics.Rectangle

variable {a b L : ℝ}

/-- The bulk displacement projection on the completed rectangular graph. -/
noncomputable def rectangleDisplacement : bottomFixedSpace a b L →L[ℝ] Vec (Interior a b L) :=
  (WithLp.fstL 2 ℝ (Vec (Interior a b L)) (Gradient a b L)).comp
    (bottomFixedSpace a b L).subtypeL

/-- The strain kernel on the completed bottom-fixed rectangle is trivial. -/
theorem rectangle_strain_kernel (hab : a ≤ b) (hL : 0 < L)
    (U : bottomFixedSpace a b L) (hε : rectangleStrain (U : Graph a b L) = 0) : U = 0 := by
  let W := (U : Graph a b L)
  have hs (i j : Fin 2) : derivativeEntry i j W + derivativeEntry j i W = 0 := by
    have h := congrArg (fun A : Strain a b L => A i j) hε
    change rectangleStrain W i j = 0 at h
    rw [rectangleStrain_apply] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hx : W.snd.fst 0 = 0 := by
    have h := hs 0 0
    change W.snd.fst 0 + W.snd.fst 0 = 0 at h
    rw [← two_smul ℝ] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hy : W.snd.snd 1 = 0 := by
    have h := hs 1 1
    change W.snd.snd 1 + W.snd.snd 1 = 0 at h
    rw [← two_smul ℝ] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hdisp (i : Fin 2) (hi : W.snd.snd i = 0) : W.fst i = 0 := by
    have h := component_normal_poincare hL U i
    change ‖W.fst i‖ ^ 2 ≤ (4 * L ^ 2) * ‖W.snd.snd i‖ ^ 2 at h
    rw [hi, norm_zero, zero_pow (by decide), mul_zero] at h
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm h (sq_nonneg _)))
  have hu1 : W.fst 1 = 0 := hdisp 1 hy
  have hyx : W.snd.fst 1 = 0 := by
    apply eq_zero_of_interior_pairings
    intro ψ hψ
    have h := weak_tangential_derivative hab U 1 ψ hψ
    change ⟪W.snd.fst 1, valueMap a b L ψ⟫_ℝ +
      ⟪W.fst 1, derivativeMap a b L (1, 0) ψ⟫_ℝ = 0 at h
    simpa [hu1] using h
  have hxy : W.snd.snd 0 = 0 := by
    have h := hs 0 1
    change W.snd.snd 0 + W.snd.fst 1 = 0 at h
    simpa [hyx] using h
  have hu0 : W.fst 0 = 0 := hdisp 0 hxy
  apply Subtype.ext
  change W = 0
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply PiLp.ext
    intro i
    fin_cases i
    · exact hu0
    · exact hu1
  · apply WithLp.ofLp_injective
    apply Prod.ext
    · apply PiLp.ext
      intro i
      fin_cases i
      · exact hx
      · exact hyx
    · apply PiLp.ext
      intro i
      fin_cases i
      · exact hxy
      · exact hy

/-- A second Korn bound on smooth trials passes to the closed rectangle graph. -/
theorem rectangle_second_korn_of_trials {C : ℝ}
    (h : ∀ u : Trials a b,
      ‖trialGraph a b L u‖ ≤ C *
        (‖rectangleStrain (trialGraph a b L u)‖ + ‖(trialGraph a b L u).fst‖))
    (U : bottomFixedSpace a b L) :
    ‖U‖ ≤ C * (‖rectangleStrain (U : Graph a b L)‖ + ‖rectangleDisplacement U‖) := by
  let P : Graph a b L →L[ℝ] Vec (Interior a b L) :=
    WithLp.fstL 2 ℝ (Vec (Interior a b L)) (Gradient a b L)
  let Q := {W : Graph a b L | ‖W‖ ≤ C * (‖rectangleStrain W‖ + ‖P W‖)}
  have hQ : IsClosed Q :=
    isClosed_le continuous_norm (continuous_const.mul (rectangleStrain.continuous.norm.add
      P.continuous.norm))
  have hsub : Set.range (trialGraph a b L) ⊆ Q := by
    rintro _ ⟨u, rfl⟩
    exact h u
  have hmem : (U : Graph a b L) ∈ closure (Set.range (trialGraph a b L)) := by
    rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
    exact U.property
  exact closure_minimal hsub hQ hmem

private theorem component_norm_sq {f : Interior a b L} {g : ℝ × ℝ → ℝ}
    (h : ⇑f =ᵐ[bulkMeasure a b L] g) :
    ‖f‖ ^ 2 = ∫ p, g p ^ 2 ∂bulkMeasure a b L := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h] with p hp
  rw [hp, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem bulk_integrable {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Integrable f (bulkMeasure a b L) := by
  rw [bulkMeasure, Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Subset.rfl Ioc_subset_Icc_self)

set_option maxHeartbeats 1200000 in
/-- The second Korn estimate for the completed bottom-fixed rectangle graph. -/
theorem rectangle_second_korn (hab : a < b) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : bottomFixedSpace a b L,
      ‖U‖ ≤ C * (‖rectangleStrain (U : Graph a b L)‖ + ‖rectangleDisplacement U‖) := by
  obtain ⟨K, hK, hk⟩ := Korn.rectangle_second_korn_integral hab hL
  refine ⟨1 + K, by positivity, rectangle_second_korn_of_trials ?_⟩
  intro u
  let W := trialGraph a b L u
  let f (i : Fin 2) := (u i).val
  let d (i j : Fin 2) (p : ℝ × ℝ) :=
    fderiv ℝ (f i) p (if j = 0 then (1, 0) else (0, 1))
  let e (i j : Fin 2) (p : ℝ × ℝ) := (1 / 2 : ℝ) * (d i j p + d j i p)
  have hf (i : Fin 2) : ContDiff ℝ 1 (f i) := (u i).property.1
  have hd (i j : Fin 2) : Continuous (d i j) :=
    ((hf i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have he (i j : Fin 2) : Continuous (e i j) :=
    continuous_const.mul ((hd i j).add (hd j i))
  have hval (i : Fin 2) : ⇑(W.fst i) =ᵐ[bulkMeasure a b L] f i := by
    change ⇑((trialGraph a b L u).fst i) =ᵐ[bulkMeasure a b L] f i
    rw [(trialGraph_components a b L u i).1]
    exact valueMap_ae (u i)
  have hgrad (i j : Fin 2) : ⇑(derivativeEntry i j W) =ᵐ[bulkMeasure a b L] d i j := by
    fin_cases j
    · change ⇑((trialGraph a b L u).snd.fst i) =ᵐ[bulkMeasure a b L] _
      rw [(trialGraph_components a b L u i).2.1]
      exact derivativeMap_ae (u i) (1, 0)
    · change ⇑((trialGraph a b L u).snd.snd i) =ᵐ[bulkMeasure a b L] _
      rw [(trialGraph_components a b L u i).2.2]
      exact derivativeMap_ae (u i) (0, 1)
  have hstrain (i j : Fin 2) : ⇑(rectangleStrain W i j) =ᵐ[bulkMeasure a b L] e i j := by
    rw [rectangleStrain_apply]
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (derivativeEntry i j W + derivativeEntry j i W),
      Lp.coeFn_add (derivativeEntry i j W) (derivativeEntry j i W), hgrad i j, hgrad j i]
      with p h₁ h₂ h₃ h₄
    simpa only [e, Pi.smul_apply, Pi.add_apply, smul_eq_mul, h₂, h₃, h₄] using h₁
  have hFi (i : Fin 2) : Integrable (fun p => f i p ^ 2) (bulkMeasure a b L) :=
    bulk_integrable ((hf i).continuous.pow 2)
  have hD : ‖W.fst‖ ^ 2 =
      ∫ p, f 0 p ^ 2 + f 1 p ^ 2 ∂bulkMeasure a b L := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, component_norm_sq (hval 0),
      component_norm_sq (hval 1), integral_add (hFi 0) (hFi 1)]
  have hE : ‖rectangleStrain W‖ ^ 2 =
      ∫ p, Korn.strainComponentSq (Korn.strainComponents (f 0) (f 1) p) ∂bulkMeasure a b L := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Fin.sum_univ_two,
      component_norm_sq (hstrain 0 0), component_norm_sq (hstrain 0 1),
      component_norm_sq (hstrain 1 0), component_norm_sq (hstrain 1 1)]
    have hi (i j : Fin 2) : Integrable (fun p => e i j p ^ 2) (bulkMeasure a b L) :=
      bulk_integrable ((he i j).pow 2)
    have hj (i : Fin 2) : Integrable (fun p => e i 0 p ^ 2 + e i 1 p ^ 2)
        (bulkMeasure a b L) := (hi i 0).add (hi i 1)
    rw [← integral_add (hi 0 0) (hi 0 1), ← integral_add (hi 1 0) (hi 1 1),
      ← integral_add (hj 0) (hj 1)]
    apply integral_congr_ae
    filter_upwards with p
    simp [e, d, Korn.strainComponentSq, Korn.strainComponents]
    ring
  have hG : ‖W.snd‖ ^ 2 =
      ∫ p, Korn.planeGradSq (f 0) (f 1) p ∂bulkMeasure a b L := by
    rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      Fin.sum_univ_two, Fin.sum_univ_two]
    change ‖derivativeEntry 0 0 W‖ ^ 2 + ‖derivativeEntry 1 0 W‖ ^ 2 +
      (‖derivativeEntry 0 1 W‖ ^ 2 + ‖derivativeEntry 1 1 W‖ ^ 2) = _
    rw [component_norm_sq (hgrad 0 0), component_norm_sq (hgrad 1 0),
      component_norm_sq (hgrad 0 1), component_norm_sq (hgrad 1 1)]
    have hi (i j : Fin 2) : Integrable (fun p => d i j p ^ 2) (bulkMeasure a b L) :=
      bulk_integrable ((hd i j).pow 2)
    have hj (j : Fin 2) : Integrable (fun p => d 0 j p ^ 2 + d 1 j p ^ 2)
        (bulkMeasure a b L) := (hi 0 j).add (hi 1 j)
    rw [← integral_add (hi 0 0) (hi 1 0), ← integral_add (hi 0 1) (hi 1 1),
      ← integral_add (hj 0) (hj 1)]
    apply integral_congr_ae
    filter_upwards with p
    simp [d, Korn.planeGradSq]
    ring
  have hk' := hk (hf 0) (hf 1)
  rw [restrict_Ioo_eq_restrict_Icc, restrict_Ioo_eq_restrict_Ioc] at hk'
  change (∫ p, Korn.planeGradSq (f 0) (f 1) p ∂bulkMeasure a b L) ≤
    K * ∫ p, Korn.strainComponentSq (Korn.strainComponents (f 0) (f 1) p) +
      (f 0 p ^ 2 + f 1 p ^ 2) ∂bulkMeasure a b L at hk'
  have hEc : Continuous (fun p => Korn.strainComponentSq (Korn.strainComponents (f 0) (f 1) p)) := by
    have h₀ := (hf 0).continuous_fderiv one_ne_zero
    have h₁ := (hf 1).continuous_fderiv one_ne_zero
    unfold Korn.strainComponentSq Korn.strainComponents
    dsimp
    fun_prop
  have hDi : Integrable (fun p => f 0 p ^ 2 + f 1 p ^ 2) (bulkMeasure a b L) :=
    (hFi 0).add (hFi 1)
  rw [integral_add (bulk_integrable hEc) hDi,
    ← hD, ← hE, ← hG] at hk'
  change ‖W‖ ≤ (1 + K) * (‖rectangleStrain W‖ + ‖W.fst‖)
  apply le_of_sq_le_sq _ (by positivity)
  rw [WithLp.prod_norm_sq_eq_of_L2]
  have hB : ‖rectangleStrain W‖ ^ 2 + ‖W.fst‖ ^ 2 ≤
      (‖rectangleStrain W‖ + ‖W.fst‖) ^ 2 := by
    nlinarith [mul_nonneg (norm_nonneg (rectangleStrain W)) (norm_nonneg W.fst)]
  have hA : (1 + K) * (‖rectangleStrain W‖ + ‖W.fst‖) ^ 2 ≤
      ((1 + K) * (‖rectangleStrain W‖ + ‖W.fst‖)) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg K]) (sq_nonneg _)
  exact (by nlinarith only [hk', mul_le_mul_of_nonneg_left hB hK.le, hB, sq_nonneg ‖rectangleStrain W‖] :
    ‖W.fst‖ ^ 2 + ‖W.snd‖ ^ 2 ≤ (1 + K) * (‖rectangleStrain W‖ + ‖W.fst‖) ^ 2).trans hA

/-- Second Korn, compactness of the displacement projection, and a trivial strain kernel
imply the needed first Korn estimate on the completed graph. -/
theorem rectangle_korn_of_compact_displacement {C : ℝ} (hC : 0 < C)
    (hsecond : ∀ U : bottomFixedSpace a b L, ‖U‖ ≤ C *
      (‖rectangleStrain (U : Graph a b L)‖ + ‖rectangleDisplacement U‖))
    (hcompact : IsCompact (closure (rectangleDisplacement ''
      {U : bottomFixedSpace a b L | ‖U‖ = 1})))
    (hkernel : ∀ U : bottomFixedSpace a b L,
      rectangleStrain (U : Graph a b L) = 0 → U = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ U : bottomFixedSpace a b L,
      ‖U‖ ≤ K * ‖rectangleStrain (U : Graph a b L)‖ := by
  let : CompleteSpace (bottomFixedSpace a b L) :=
    (Submodule.isClosed_topologicalClosure (LinearMap.range (trialGraph a b L))).completeSpace_coe
  exact LeanSolid.Math.exists_norm_le_of_compact_remainder
    ((rectangleStrain (a := a) (b := b) (L := L)).comp (bottomFixedSpace a b L).subtypeL)
    rectangleDisplacement hC hsecond hcompact hkernel

/-- On the bottom-fixed rectangle, second Korn and compactness suffice for the mixed weak
solution because the strain kernel has already been proved trivial. -/
theorem existsUnique_rectangle_of_second_korn (hab : a ≤ b) (hL : 0 < L) {μ lam C : ℝ}
    (hμ : 0 < μ) (hlam : 0 ≤ lam) (hC : 0 < C)
    (hsecond : ∀ U : bottomFixedSpace a b L, ‖U‖ ≤ C *
      (‖rectangleStrain (U : Graph a b L)‖ + ‖rectangleDisplacement U‖))
    (hcompact : IsCompact (closure (rectangleDisplacement ''
      {U : bottomFixedSpace a b L | ‖U‖ = 1})))
    (t : Vec (Edge a b)) (body : bottomFixedSpace a b L →L[ℝ] ℝ) :
    ∃! U, IsRectangleWeakSolution hL μ lam t body U := by
  obtain ⟨K, hK, hkorn⟩ := rectangle_korn_of_compact_displacement hC hsecond hcompact
    (rectangle_strain_kernel hab hL)
  exact existsUnique_rectangle_of_korn hL hμ hlam hK hkorn t body

end LeanSolid.Elastostatics.Rectangle
