module

public import LeanSolid.Elastostatics.Sobolev.H10
public import LeanSolid.Elastostatics.BoundaryResponse
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
Domain graph and variational trace conventions. Compare OpenAI (2026),
Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, §2,
companion Basic.lean (SmoothJets, TestJets, H1, SameTrace), revision
3344da59991ed94f9ba711217b29c1d760badfa6.
-/

@[expose] public section

open MeasureTheory Set LeanSolid.Math
open scoped ContDiff InnerProductSpace

noncomputable section

namespace LeanSolid.Elastostatics.Sobolev.Domain

variable {n : ℕ}

abbrev Scalar (Ω : Set (Fin n → ℝ)) := Lp ℝ 2 (volume.restrict Ω)
abbrev VectorL2 (Ω : Set (Fin n → ℝ)) := PiLp 2 fun _ : Fin n => Scalar Ω
abbrev MatrixL2 (Ω : Set (Fin n → ℝ)) := PiLp 2 fun _ : Fin n => VectorL2 Ω

/-- A displacement and gradient pair with all components measured only on the body. -/
abbrev Jet (Ω : Set (Fin n → ℝ)) := WithLp 2 (VectorL2 Ω × MatrixL2 Ω)

/-- Smooth Cartesian displacement fields without a support restriction. -/
def smoothFields (n : ℕ) : Submodule ℝ (Fin n → (Fin n → ℝ) → ℝ) where
  carrier := {w | ∀ i, ContDiff ℝ ∞ (w i)}
  add_mem' hf hg i := (hf i).add (hg i)
  zero_mem' _ := contDiff_const
  smul_mem' a _ h i := (h i).const_smul a

theorem smooth_of_test {Ω : Set (Fin n → ℝ)} (w : testFields Ω) :
    w.val ∈ smoothFields n := fun i => (w.property i).1

/-- Forget compact support while retaining smoothness and the original displacement. -/
def testInclusion (Ω : Set (Fin n → ℝ)) : testFields Ω →ₗ[ℝ] smoothFields n where
  toFun w := ⟨w.val, smooth_of_test w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem memLp_on_bounded {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) : MemLp f 2 (volume.restrict Ω) := by
  rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
  exact ((hf.pow 2).continuousOn.integrableOn_compact hΩ.isCompact_closure).mono_set subset_closure

theorem smoothComponent {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω)
    (w : smoothFields n) (i : Fin n) : MemLp (w.val i) 2 (volume.restrict Ω) :=
  memLp_on_bounded hΩ (w.property i).continuous

theorem smoothDerivative {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω)
    (w : smoothFields n) (i j : Fin n) :
    MemLp (partialDeriv (w.val i) j) 2 (volume.restrict Ω) :=
  memLp_on_bounded hΩ (Korn.continuous_pd ((w.property i).of_le (by simp)) j)

/-- The pure domain graph of a smooth displacement, before completion. -/
def smoothGraph {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω) :
    smoothFields n →ₗ[ℝ] Jet Ω where
  toFun w := WithLp.toLp 2
    (WithLp.toLp 2 fun i => (smoothComponent hΩ w i).toLp (w.val i),
      WithLp.toLp 2 fun i => WithLp.toLp 2 fun j =>
        (smoothDerivative hΩ w i j).toLp (partialDeriv (w.val i) j))
  map_add' w v := by
    have hd (u : smoothFields n) (i : Fin n) : Differentiable ℝ (u.val i) :=
      (u.property i).differentiable (by simp)
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply PiLp.ext
      intro i
      exact MemLp.toLp_add (smoothComponent hΩ w i) (smoothComponent hΩ v i)
    · apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      change (smoothDerivative hΩ (w + v) i j).toLp (partialDeriv (w.val i + v.val i) j) = _
      refine (MemLp.toLp_congr _ ((smoothDerivative hΩ w i j).add
        (smoothDerivative hΩ v i j)) (Filter.EventuallyEq.of_eq
          (LeanSolid.Math.partial_add (hd w i) (hd v i) j))).trans ?_
      exact MemLp.toLp_add (smoothDerivative hΩ w i j) (smoothDerivative hΩ v i j)
  map_smul' a w := by
    have hd (i : Fin n) : Differentiable ℝ (w.val i) :=
      (w.property i).differentiable (by simp)
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply PiLp.ext
      intro i
      exact MemLp.toLp_const_smul a (smoothComponent hΩ w i)
    · apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      change (smoothDerivative hΩ (a • w) i j).toLp (partialDeriv (a • w.val i) j) = _
      refine (MemLp.toLp_congr _ ((smoothDerivative hΩ w i j).const_smul a)
        (Filter.EventuallyEq.of_eq (pd_smul a (hd i) j))).trans ?_
      exact MemLp.toLp_const_smul a (smoothDerivative hΩ w i j)

variable {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω)

/-- H¹ model as the closure of smooth displacement–gradient pairs in the body. -/
def H1 : Submodule ℝ (Jet Ω) :=
  (LinearMap.range (smoothGraph hΩ)).topologicalClosure

/-- Zero-trace model as the closure of the compactly supported smooth pairs. -/
def zeroTrace : Submodule ℝ (Jet Ω) :=
  (LinearMap.range ((smoothGraph hΩ).comp (testInclusion Ω))).topologicalClosure

theorem zeroTrace_le : zeroTrace hΩ ≤ H1 hΩ := by
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨w, rfl⟩
  exact ⟨testInclusion Ω w, rfl⟩

/-- Zero trace as a closed subspace of the completed domain graph. -/
def zeroTraceInH1 : Submodule ℝ (H1 hΩ) :=
  (zeroTrace hΩ).comap (H1 hΩ).subtype

instance : CompleteSpace (H1 hΩ) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

instance : CompleteSpace (zeroTraceInH1 hΩ) :=
  ((Submodule.isClosed_topologicalClosure _).preimage
    (H1 hΩ).subtypeL.continuous).completeSpace_coe

instance normedSpaceH1 : NormedSpace ℝ (H1 hΩ) :=
  Submodule.normedSpace (𝕜 := ℝ) (H1 hΩ)

instance normedSpaceZeroTraceInH1 : NormedSpace ℝ (zeroTraceInH1 hΩ) :=
  Submodule.normedSpace (𝕜 := ℝ) (zeroTraceInH1 hΩ)

/-- Variational trace space of the physical domain graph. -/
abbrev Trace := Quot (fun u v : H1 hΩ => u - v ∈ zeroTraceInH1 hΩ)

/-- Restriction from the whole-space scalar L² class to the body. -/
def restrictScalar (Ω : Set (Fin n → ℝ)) : L2 n →L[ℝ] Scalar Ω :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using Measure.restrict_le_self)

theorem restrictScalar_ae (Ω : Set (Fin n → ℝ)) (f : L2 n) :
    ⇑(restrictScalar Ω f) =ᵐ[volume.restrict Ω] ⇑f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

private def restrictVector (Ω : Set (Fin n → ℝ)) : Vec n →L[ℝ] VectorL2 Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => Scalar Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (restrictScalar Ω).comp
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => L2 n) i))

private def restrictMatrix (Ω : Set (Fin n → ℝ)) : Mat n →L[ℝ] MatrixL2 Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => VectorL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (restrictVector Ω).comp
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => Vec n) i))

/-- Componentwise restriction of ambient displacement–gradient pairs. -/
@[no_expose] def restrictJet (Ω : Set (Fin n → ℝ)) : G n →L[ℝ] Jet Ω :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (VectorL2 Ω) (MatrixL2 Ω)).symm.toContinuousLinearMap.comp
    (((restrictVector Ω).comp disp).prod ((restrictMatrix Ω).comp grad))

theorem restrictJet_components (Ω : Set (Fin n → ℝ)) (U : G n) (i j : Fin n) :
    (restrictJet Ω U).fst i = restrictScalar Ω (disp U i) ∧
    (restrictJet Ω U).snd i j = restrictScalar Ω (grad U i j) := by
  simp [restrictJet, restrictVector, restrictMatrix]

private theorem restrict_toLp {Ω : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp f 2 (volume.restrict Ω)) :
    restrictScalar Ω (toL2 f) = hg.toLp f := by
  rw [toL2_of_memLp hf]
  apply Lp.ext
  have h : ⇑(hf.toLp f) =ᵐ[volume.restrict Ω] f := ae_restrict_of_ae hf.coeFn_toLp
  exact (restrictScalar_ae Ω (hf.toLp f)).trans (h.trans hg.coeFn_toLp.symm)

/-- The ambient compactly supported graph restricts to the domain test graph. -/
theorem restrict_testGraph {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω)
    (w : testFields Ω) :
    restrictJet Ω (graph Ω w) = smoothGraph hΩ (testInclusion Ω w) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply PiLp.ext
    intro i
    change (restrictJet Ω (graph Ω w)).fst i = _
    rw [(restrictJet_components Ω (graph Ω w) i i).1]
    exact restrict_toLp (memLp_of_mem w.property i) (smoothComponent hΩ (testInclusion Ω w) i)
  · apply PiLp.ext
    intro i
    apply PiLp.ext
    intro j
    change (restrictJet Ω (graph Ω w)).snd i j = _
    rw [(restrictJet_components Ω (graph Ω w) i j).2]
    exact restrict_toLp (memLp_pd_of_mem w.property i j)
      (smoothDerivative hΩ (testInclusion Ω w) i j)

/-- The image of the existing ambient H¹₀ is dense in the domain zero-trace space. -/
theorem closure_restrict_H10 {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω) :
    ((H10 Ω).map (restrictJet Ω).toLinearMap).topologicalClosure = zeroTrace hΩ := by
  have hmap : (LinearMap.range (graph Ω)).map (restrictJet Ω).toLinearMap =
      LinearMap.range ((smoothGraph hΩ).comp (testInclusion Ω)) := by
    ext U
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (restrict_testGraph hΩ w).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨graph Ω w, ⟨w, rfl⟩, restrict_testGraph hΩ w⟩
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · unfold H10
      simpa only [hmap, zeroTrace] using
        (LinearMap.range (graph Ω)).topologicalClosure_map (restrictJet Ω)
    · exact Submodule.isClosed_topologicalClosure _
  · unfold zeroTrace
    rw [← hmap]
    exact Submodule.topologicalClosure_mono
      (Submodule.map_mono (Submodule.le_topologicalClosure _))

private theorem norm_domain_toLp_sq {Ω : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x in Ω, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

private theorem norm_sq_restrict_of_support {Ω : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp f 2 (volume.restrict Ω)) (hs : tsupport f ⊆ Ω) :
    ‖restrictScalar Ω (toL2 f)‖ ^ 2 = ‖toL2 f‖ ^ 2 := by
  rw [restrict_toLp hf hg, norm_domain_toLp_sq hg, norm_toL2_sq hf]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_pow (by decide)]

private theorem restrict_test_normSq {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω)
    (w : testFields Ω) :
    ‖restrictJet Ω (graph Ω w)‖ ^ 2 = ‖graph Ω w‖ ^ 2 := by
  simp only [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  have hD (i : Fin n) :
      ‖(restrictJet Ω (graph Ω w)).fst i‖ ^ 2 = ‖disp (graph Ω w) i‖ ^ 2 := by
    rw [(restrictJet_components Ω (graph Ω w) i i).1]
    exact norm_sq_restrict_of_support (memLp_of_mem w.property i)
      (smoothComponent hΩ (testInclusion Ω w) i) (w.property i).2.2
  have hG (i j : Fin n) :
      ‖(restrictJet Ω (graph Ω w)).snd i j‖ ^ 2 = ‖grad (graph Ω w) i j‖ ^ 2 := by
    rw [(restrictJet_components Ω (graph Ω w) i j).2]
    exact norm_sq_restrict_of_support (memLp_pd_of_mem w.property i j)
      (smoothDerivative hΩ (testInclusion Ω w) i j)
      ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans (w.property i).2.2)
  simp only [hD, hG]
  rfl

/-- Restricting a zero-trace displacement–gradient pair preserves its full graph norm. -/
theorem restrict_H10_norm {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω) (U : H10 Ω) :
    ‖restrictJet Ω U‖ = ‖U‖ := by
  let C := {W : G n | ‖restrictJet Ω W‖ ^ 2 = ‖W‖ ^ 2}
  have hclosed : IsClosed C := isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : Set.range (graph Ω) ⊆ C := by
    rintro _ ⟨w, rfl⟩
    exact restrict_test_normSq hΩ w
  have hmem : (U : G n) ∈ closure (Set.range (graph Ω)) := by
    rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
    exact U.property
  have h : ‖restrictJet Ω (U : G n)‖ ^ 2 = ‖(U : G n)‖ ^ 2 :=
    closure_minimal hsub hclosed hmem
  exact le_antisymm (le_of_sq_le_sq h.le (norm_nonneg _))
    (le_of_sq_le_sq h.ge (norm_nonneg _))

/-- The domain zero-trace space is exactly the image of the existing ambient H¹₀. -/
theorem restrict_H10_eq_zeroTrace {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω) :
    (H10 Ω).map (restrictJet Ω).toLinearMap = zeroTrace hΩ := by
  let r := (restrictJet Ω).comp (H10 Ω).subtypeL
  have hr : Isometry r := AddMonoidHomClass.isometry_of_norm r (restrict_H10_norm hΩ)
  have he : Set.range r = ((H10 Ω).map (restrictJet Ω).toLinearMap : Set (Jet Ω)) := by
    ext U
    constructor
    · rintro ⟨W, rfl⟩
      exact ⟨W, W.property, rfl⟩
    · rintro ⟨W, hW, rfl⟩
      exact ⟨⟨W, hW⟩, rfl⟩
  have hc : IsClosed ((H10 Ω).map (restrictJet Ω).toLinearMap : Set (Jet Ω)) :=
    he ▸ hr.isClosedEmbedding.isClosed_range
  rw [← closure_restrict_H10 hΩ]
  exact le_antisymm (Submodule.le_topologicalClosure _)
    (Submodule.topologicalClosure_minimal _ le_rfl hc)

/-- The exact isometric identification of whole-space zero extensions with the
zero-trace subspace of the body's graph. -/
@[no_expose] def zeroTraceEquiv {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω) :
    H10 Ω ≃ₗᵢ[ℝ] zeroTrace hΩ := by
  have hm (u : H10 Ω) : restrictJet Ω u ∈ zeroTrace hΩ := by
    rw [← restrict_H10_eq_zeroTrace hΩ]
    exact ⟨u, u.property, rfl⟩
  let r : H10 Ω →ₗᵢ[ℝ] zeroTrace hΩ :=
    { toLinearMap := ((restrictJet Ω).toLinearMap.comp (H10 Ω).subtype).codRestrict
        (zeroTrace hΩ) hm
      norm_map' := restrict_H10_norm hΩ }
  apply LinearIsometryEquiv.ofSurjective r
  intro v
  have hv : v.val ∈ (H10 Ω).map (restrictJet Ω).toLinearMap :=
    Eq.mp (congrArg (fun N : Submodule ℝ (Jet Ω) => v.val ∈ N)
      (restrict_H10_eq_zeroTrace hΩ).symm) v.property
  obtain ⟨u, hu, he⟩ := hv
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

/-- Equality of variational traces means that the difference belongs to the
domain closure of compactly supported smooth displacement–gradient pairs. -/
def traceOf (u : H1 hΩ) : Trace hΩ := Quot.mk _ u

theorem traceOf_eq_iff (u v : H1 hΩ) :
    traceOf hΩ u = traceOf hΩ v ↔ u - v ∈ zeroTraceInH1 hΩ := by
  let N := zeroTraceInH1 hΩ
  let R : Setoid (H1 hΩ) :=
    ⟨fun a b => a - b ∈ N, fun a => by rw [sub_self]; exact N.zero_mem,
      fun {a b} h => by simpa only [neg_sub] using N.neg_mem h,
      fun {a b c} hab hbc => by simpa only [sub_add_sub_cancel] using N.add_mem hab hbc⟩
  exact ⟨fun h => Quotient.exact (s := R) h, fun h => Quotient.sound (s := R) h⟩

/-- The canonical inclusion of the domain zero-trace graph into H¹ is an isometry. -/
@[no_expose] def zeroTraceInH1Equiv : zeroTrace hΩ ≃ₗᵢ[ℝ] zeroTraceInH1 hΩ := by
  let e : zeroTrace hΩ →ₗᵢ[ℝ] zeroTraceInH1 hΩ :=
    { toFun := fun u => ⟨⟨u.val, zeroTrace_le hΩ u.property⟩, u.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := fun _ => rfl }
  apply LinearIsometryEquiv.ofSurjective e
  intro u
  exact ⟨⟨u.val.val, u.property⟩, rfl⟩

/-- The existing ambient zero-trace space can be used as the test space in the
domain H¹ formulation via an exact linear isometry. -/
@[no_expose] def testSpaceEquiv : H10 Ω ≃ₗᵢ[ℝ] zeroTraceInH1 hΩ :=
  (zeroTraceEquiv hΩ).trans (zeroTraceInH1Equiv hΩ)

/-- Extension by zero is a linear isometry from the domain L² space into ambient L². -/
@[no_expose] def extendScalar {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) :
    Scalar Ω →ₗᵢ[ℝ] L2 n := by
  classical
  let h (f : Scalar Ω) : MemLp (Ω.indicator (⇑f)) 2 volume :=
    (memLp_indicator_iff_restrict hΩ.nullMeasurableSet).mpr (Lp.memLp f)
  let E (f : Scalar Ω) : L2 n := (h f).toLp _
  have hE (f : Scalar Ω) : ⇑(E f) =ᵐ[volume] Ω.indicator (⇑f) :=
    (h f).coeFn_toLp
  refine { toFun := E, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }
  · intro f g
    apply Lp.ext
    have hf := ae_imp_of_ae_restrict (Lp.coeFn_add f g)
    filter_upwards [hE (f + g), hE f, hE g, Lp.coeFn_add (E f) (E g), hf]
      with x hfg hf' hg' ha hsum
    rw [hfg, ha]
    change Ω.indicator (⇑(f + g)) x = E f x + E g x
    rw [hf', hg']
    by_cases hx : x ∈ Ω
    · simp only [Set.indicator_of_mem hx]
      exact hsum hx
    · simp [Set.indicator_of_notMem hx]
  · intro a f
    apply Lp.ext
    have hf := ae_imp_of_ae_restrict (Lp.coeFn_smul a f)
    filter_upwards [hE (a • f), hE f, Lp.coeFn_smul a (E f), hf]
      with x haf hf' hs hprod
    change E (a • f) x = (a • E f : L2 n) x
    rw [haf, hs]
    change Ω.indicator (⇑(a • f)) x = a • E f x
    rw [hf']
    by_cases hx : x ∈ Ω
    · simp only [Set.indicator_of_mem hx]
      exact hprod hx
    · simp [Set.indicator_of_notMem hx]
  · intro f
    change ‖E f‖ = ‖f‖
    simp only [Lp.norm_def, eLpNorm_congr_ae (hE f),
      eLpNorm_indicator_eq_eLpNorm_restrict hΩ.nullMeasurableSet]

theorem extendScalar_ae {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (f : Scalar Ω) :
    ⇑(extendScalar hΩ f) =ᵐ[volume] Ω.indicator (⇑f) := by
  classical
  unfold extendScalar
  exact ((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).mpr (Lp.memLp f)).coeFn_toLp

/-- Restricting a zero extension returns the original body field as an L² class. -/
theorem restrict_extendScalar {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (f : Scalar Ω) :
    restrictScalar Ω (extendScalar hΩ f) = f := by
  classical
  apply Lp.ext
  have he := extendScalar_ae hΩ f
  filter_upwards [restrictScalar_ae Ω (extendScalar hΩ f), ae_restrict_of_ae he,
    self_mem_ae_restrict hΩ] with x hr hE hx
  exact hr.trans (hE.trans (Set.indicator_of_mem hx _))

private def extendVector {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) :
    VectorL2 Ω →L[ℝ] Vec n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => L2 n)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (extendScalar hΩ).toContinuousLinearMap.comp
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => Scalar Ω) i))

private def extendMatrix {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) :
    MatrixL2 Ω →L[ℝ] Mat n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => Vec n)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (extendVector hΩ).comp
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => VectorL2 Ω) i))

/-- Componentwise zero extension of pairs. This is an ambient representative of a
domain jet, including when the jet has nonzero variational trace. -/
@[no_expose] def extendJet {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) :
    Jet Ω →L[ℝ] G n :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Vec n) (Mat n)).symm.toContinuousLinearMap.comp
    (((extendVector hΩ).comp (WithLp.fstL 2 ℝ _ _)).prod
      ((extendMatrix hΩ).comp (WithLp.sndL 2 ℝ _ _)))

theorem extendJet_components {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    (U : Jet Ω) (i j : Fin n) :
    disp (extendJet hΩ U) i = extendScalar hΩ (U.fst i) ∧
    grad (extendJet hΩ U) i j = extendScalar hΩ (U.snd i j) := by
  simp [disp, grad, extendJet, extendVector, extendMatrix]

/-- Every domain pair is obtained by restriction of its ambient representative. -/
theorem restrict_extendJet {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (U : Jet Ω) :
    restrictJet Ω (extendJet hΩ U) = U := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply PiLp.ext
    intro i
    change (restrictJet Ω (extendJet hΩ U)).fst i = U.fst i
    rw [(restrictJet_components Ω _ i i).1, (extendJet_components hΩ U i i).1,
      restrict_extendScalar]
  · apply PiLp.ext
    intro i
    apply PiLp.ext
    intro j
    change (restrictJet Ω (extendJet hΩ U)).snd i j = U.snd i j
    rw [(restrictJet_components Ω _ i j).2, (extendJet_components hΩ U i j).2,
      restrict_extendScalar]

private theorem extend_restrict_toL2 {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 volume) (hs : tsupport f ⊆ Ω) :
    extendScalar hΩ (restrictScalar Ω (toL2 f)) = toL2 f := by
  classical
  rw [restrict_toLp hf (hf.restrict Ω), toL2_of_memLp hf]
  apply Lp.ext
  have h := ae_imp_of_ae_restrict (hf.restrict Ω).coeFn_toLp
  filter_upwards [extendScalar_ae hΩ ((hf.restrict Ω).toLp f), hf.coeFn_toLp, h]
    with x he hf' hr
  rw [he, hf']
  by_cases hx : x ∈ Ω
  · rw [Set.indicator_of_mem hx]
    exact hr hx
  · rw [Set.indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport (fun hs' => hx (hs hs'))).symm

/-- A zero-trace ambient jet is recovered by restricting and extending its components. -/
theorem extend_restrict_H10 {Ω : Set (Fin n → ℝ)} (hΩ : MeasurableSet Ω) (U : H10 Ω) :
    extendJet hΩ (restrictJet Ω (U : G n)) = (U : G n) := by
  let C := {W : G n | extendJet hΩ (restrictJet Ω W) = W}
  have hclosed : IsClosed C := isClosed_eq
    ((extendJet hΩ).continuous.comp (restrictJet Ω).continuous) continuous_id
  have hsub : Set.range (graph Ω) ⊆ C := by
    rintro _ ⟨w, rfl⟩
    change extendJet hΩ (restrictJet Ω (graph Ω w)) = graph Ω w
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply PiLp.ext
      intro i
      change disp (extendJet hΩ (restrictJet Ω (graph Ω w))) i = disp (graph Ω w) i
      rw [(extendJet_components hΩ _ i i).1, (restrictJet_components Ω _ i i).1]
      exact extend_restrict_toL2 hΩ (memLp_of_mem w.property i) (w.property i).2.2
    · apply PiLp.ext
      intro i
      apply PiLp.ext
      intro j
      change grad (extendJet hΩ (restrictJet Ω (graph Ω w))) i j = grad (graph Ω w) i j
      rw [(extendJet_components hΩ _ i j).2, (restrictJet_components Ω _ i j).2]
      exact extend_restrict_toL2 hΩ (memLp_pd_of_mem w.property i j)
        ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans (w.property i).2.2)
  have hmem : (U : G n) ∈ closure (Set.range (graph Ω)) := by
    rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe]
    exact U.property
  exact closure_minimal hsub hclosed hmem

theorem testSpaceEquiv_apply_val {Ω : Set (Fin n → ℝ)} (hΩ : Bornology.IsBounded Ω)
    (u : H10 Ω) : (testSpaceEquiv hΩ u).val.val = restrictJet Ω (u : G n) := by
  unfold testSpaceEquiv zeroTraceInH1Equiv zeroTraceEquiv
  rfl

end LeanSolid.Elastostatics.Sobolev.Domain
