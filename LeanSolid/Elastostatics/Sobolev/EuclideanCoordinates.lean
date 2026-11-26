module

public import LeanSolid.Elastostatics.Sobolev.DomainGraph
public import LeanSolid.Math.VectorL2
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Coordinate conventions for the EuclideanSpace formulation of OpenAI (2026),
Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, §1–2.
Compare companion Basic.lean, coordVector and coordDeriv, at revision
3344da59991ed94f9ba711217b29c1d760badfa6.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace LeanSolid.Elastostatics.Sobolev.Domain

variable {n : ℕ}

/-- Euclidean points and their Cartesian coordinates with the product norm. -/
def coordinates : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

theorem coordinates_apply (x : EuclideanSpace ℝ (Fin n)) :
    coordinates x = WithLp.ofLp x := by unfold coordinates; rfl

theorem coordinates_symm_apply (x : Fin n → ℝ) :
    coordinates.symm x = WithLp.toLp 2 x := by unfold coordinates; rfl

theorem coordinates_measurePreserving :
    MeasurePreserving (coordinates (n := n)) :=
  PiLp.volume_preserving_ofLp (Fin n)

/-- The Cartesian change of coordinates preserves the restricted body measures. -/
theorem coordinates_measurePreservingOn (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    MeasurePreserving coordinates (volume.restrict Ω) (volume.restrict (coordinates '' Ω)) :=
  coordinates_measurePreserving.restrict_image_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding Ω

theorem coordinates_symm_measurePreservingOn (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℝ))
      (volume.restrict (coordinates '' Ω)) (volume.restrict Ω) :=
  MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
    (coordinates_measurePreservingOn Ω)

theorem coordinates_image_isBounded {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : Bornology.IsBounded Ω) : Bornology.IsBounded (coordinates '' Ω) :=
  coordinates.toContinuousLinearMap.lipschitzWith.isBounded_image hΩ

theorem coordinates_image_isOpen {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) :
    IsOpen (coordinates '' Ω) :=
  coordinates.toHomeomorph.isOpen_image.mpr hΩ

theorem coordinates_symm_mem_closure {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {x : Fin n → ℝ} (hx : x ∈ closure (coordinates '' Ω)) :
    coordinates.symm x ∈ closure Ω := by
  have he : Set.image coordinates (closure Ω) = closure (coordinates '' Ω) :=
    coordinates.toHomeomorph.image_closure Ω
  rw [← he] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [← hxy, ContinuousLinearEquiv.symm_apply_apply]
  exact hy

theorem coordinates_pullback_continuousOn {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n) → ℝ} (ha : ContinuousOn a (closure Ω)) :
    ContinuousOn (a ∘ coordinates.symm) (closure (coordinates '' Ω)) :=
  ha.comp coordinates.symm.continuous.continuousOn (fun _ hx => coordinates_symm_mem_closure hx)

/-- The Cartesian component functions of a Euclidean displacement field. -/
def componentField (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  (u (coordinates.symm x)) i

theorem componentField_contDiff {u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {k : WithTop ℕ∞} (hu : ContDiff ℝ k u) (i : Fin n) :
    ContDiff ℝ k (componentField u i) :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).contDiff.comp
    (hu.comp (coordinates.symm.contDiff))

/-- The scalar derivative in row i, column j is the i-th entry of the Euclidean
directional derivative in direction j. -/
theorem partialDeriv_componentField
    {u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (x : EuclideanSpace ℝ (Fin n)) (hu : DifferentiableAt ℝ u x) (i j : Fin n) :
    LeanSolid.Math.partialDeriv (componentField u i) j (coordinates x) =
      (fderiv ℝ u x (EuclideanSpace.single j 1)) i := by
  let p := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i
  have h := p.hasFDerivAt.comp (coordinates x)
    (hu.hasFDerivAt.comp (coordinates x) coordinates.symm.hasFDerivAt)
  change fderiv ℝ (p ∘ u ∘ coordinates.symm) (coordinates x) (Pi.single j 1) = _
  rw [h.fderiv]
  simp [p, coordinates_symm_apply, EuclideanSpace.single]

/-- Vector-valued fields on the Euclidean version of the body. -/
noncomputable abbrev EuclideanL2 (Ω : Set (EuclideanSpace ℝ (Fin n))) :=
  Lp (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict Ω)

/-- The upstream layout uses one vector field per derivative column. -/
noncomputable abbrev EuclideanJet (Ω : Set (EuclideanSpace ℝ (Fin n))) :=
  EuclideanL2 Ω × (Fin n → EuclideanL2 Ω)

private def transposeRows (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (Fin n → Fin n → E) ≃L[ℝ] (Fin n → Fin n → E) where
  toFun a i j := a j i
  invFun a i j := a j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (continuous_apply j)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).comp (continuous_apply j)

/-- The vector-valued Euclidean L² class is equivalent to the Cartesian component classes. -/
noncomputable def vectorCoordinates (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanL2 Ω ≃L[ℝ] VectorL2 (coordinates '' Ω) :=
  (LeanSolid.Math.reindexL2 (MeasurableEquiv.toLp 2 (Fin n → ℝ))
    (MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
      (coordinates_measurePreservingOn Ω))).toContinuousLinearEquiv.trans
      LeanSolid.Math.vectorL2Coordinates

/-- Change both the base coordinates and the gradient storage convention.
The map is a continuous linear equivalence on the underlying L² pairs. -/
noncomputable def jetCoordinates (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanJet Ω ≃L[ℝ] Jet (coordinates '' Ω) := by
  let S := Scalar (coordinates '' Ω)
  let V := VectorL2 (coordinates '' Ω)
  let C : (Fin n → EuclideanL2 Ω) ≃L[ℝ] (Fin n → V) :=
    ContinuousLinearEquiv.piCongrRight fun _ => vectorCoordinates Ω
  let cols : (Fin n → EuclideanL2 Ω) ≃L[ℝ] MatrixL2 (coordinates '' Ω) :=
    C.trans ((ContinuousLinearEquiv.piCongrRight
      (fun _ : Fin n => PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => S))).trans
        ((transposeRows (n := n) S).trans
          ((ContinuousLinearEquiv.piCongrRight
            (fun _ : Fin n => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => S)).symm)).trans
              (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => V)).symm)))
  exact ((vectorCoordinates Ω).prodCongr cols).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ V (MatrixL2 (coordinates '' Ω))).symm

theorem jetCoordinates_components (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (U : EuclideanJet Ω) (i j : Fin n) :
    (jetCoordinates Ω U).fst i = vectorCoordinates Ω U.1 i ∧
    (jetCoordinates Ω U).snd i j = vectorCoordinates Ω (U.2 j) i := by
  unfold jetCoordinates transposeRows
  exact ⟨rfl, rfl⟩

theorem vectorCoordinates_ae (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanL2 Ω) (i : Fin n) :
    ⇑(vectorCoordinates Ω f i) =ᵐ[volume.restrict (coordinates '' Ω)]
      fun x => f (coordinates.symm x) i := by
  let e := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have he := MeasurePreserving.symm e.symm (coordinates_measurePreservingOn Ω)
  let g := LeanSolid.Math.reindexL2 e he f
  have h₁ := LeanSolid.Math.splitVectorL2_ae g i
  have h₂ := LeanSolid.Math.reindexL2_ae e he f
  have hh : ⇑(vectorCoordinates Ω f i) =ᵐ[volume.restrict (coordinates '' Ω)]
      fun x => g x i := by
    rw [vectorCoordinates, ContinuousLinearEquiv.trans_apply, LeanSolid.Math.vectorL2Coordinates_apply]
    exact h₁
  filter_upwards [hh, h₂] with x hx hy
  exact hx.trans (congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hy)

/-- Smooth Euclidean fields form precisely the componentwise jets in the Cartesian
chart, with the vector derivative stored by column in the Euclidean input. -/
theorem jetCoordinates_smooth (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : Bornology.IsBounded (coordinates '' Ω))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hu : ContDiff ℝ ∞ u)
    (hf : MemLp u 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) 2 (volume.restrict Ω)) :
    jetCoordinates Ω (hf.toLp u, fun j => (hd j).toLp
      (fun x => fderiv ℝ u x (EuclideanSpace.single j 1))) =
    smoothGraph hΩ ⟨componentField u, componentField_contDiff hu⟩ := by
  let w : smoothFields n := ⟨componentField u, componentField_contDiff hu⟩
  let F : EuclideanJet Ω := (hf.toLp u, fun j => (hd j).toLp _)
  let e := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have he := (MeasurePreserving.symm e.symm (coordinates_measurePreservingOn Ω)).quasiMeasurePreserving
  change jetCoordinates Ω F = smoothGraph hΩ w
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply PiLp.ext
    intro i
    change (jetCoordinates Ω F).fst i = (smoothComponent hΩ w i).toLp (w.val i)
    rw [(jetCoordinates_components Ω F i i).1]
    apply Lp.ext
    have h := he.ae hf.coeFn_toLp
    filter_upwards [vectorCoordinates_ae Ω F.1 i, h, (smoothComponent hΩ w i).coeFn_toLp] with x hx hy hz
    exact hx.trans ((congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hy).trans hz.symm)
  · apply PiLp.ext
    intro i
    apply PiLp.ext
    intro j
    change (jetCoordinates Ω F).snd i j =
      (smoothDerivative hΩ w i j).toLp (LeanSolid.Math.partialDeriv (w.val i) j)
    rw [(jetCoordinates_components Ω F i j).2]
    apply Lp.ext
    have h := he.ae (hd j).coeFn_toLp
    filter_upwards [vectorCoordinates_ae Ω (F.2 j) i, h,
      (smoothDerivative hΩ w i j).coeFn_toLp] with x hx hy hz
    have hj := partialDeriv_componentField (coordinates.symm x)
      (hu.differentiable (by simp) _) i j
    rw [ContinuousLinearEquiv.apply_symm_apply] at hj
    exact hx.trans ((congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hy).trans
      (hj.symm.trans hz.symm))

/-- The Euclidean smooth generators, with the same membership conditions as
the companion paper's SmoothJets. -/
def euclideanSmoothJets (Ω : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanJet Ω) :=
  {U | ∃ (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hf : MemLp u 2 (volume.restrict Ω))
      (hd : ∀ j, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) 2 (volume.restrict Ω)),
    ContDiff ℝ ∞ u ∧ U.1 = hf.toLp u ∧
      U.2 = fun j => (hd j).toLp (fun x => fderiv ℝ u x (EuclideanSpace.single j 1))}

private theorem memLp_euclidean_of_bounded {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : Bornology.IsBounded Ω) {u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : Continuous u) : MemLp u 2 (volume.restrict Ω) := by
  rw [memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable]
  exact ((hu.norm.pow 2).continuousOn.integrableOn_compact hΩ.isCompact_closure).mono_set subset_closure

/-- The coordinate equivalence carries the full set of Euclidean smooth generators
onto the LeanSolid smooth graph. -/
theorem image_euclideanSmoothJets (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω)) :
    jetCoordinates Ω '' euclideanSmoothJets Ω = Set.range (smoothGraph hΩ) := by
  ext U
  constructor
  · rintro ⟨J, ⟨u, hf, hd, hu, h₁, h₂⟩, rfl⟩
    refine ⟨⟨componentField u, componentField_contDiff hu⟩, ?_⟩
    have hJ : J = (hf.toLp u, fun j => (hd j).toLp _) := Prod.ext h₁ h₂
    rw [hJ]
    exact (jetCoordinates_smooth Ω hΩ u hu hf hd).symm
  · rintro ⟨w, rfl⟩
    let u (x : EuclideanSpace ℝ (Fin n)) := coordinates.symm (fun i => w.val i (coordinates x))
    have hu : ContDiff ℝ ∞ u := coordinates.symm.contDiff.comp
      (contDiff_pi.mpr fun i => (w.property i).comp coordinates.contDiff)
    have hf := memLp_euclidean_of_bounded hE hu.continuous
    have hd (j : Fin n) : MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j 1))
        2 (volume.restrict Ω) :=
      memLp_euclidean_of_bounded hE
        ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
    refine ⟨(hf.toLp u, fun j => (hd j).toLp _), ⟨u, hf, hd, hu, rfl, rfl⟩, ?_⟩
    rw [jetCoordinates_smooth Ω hΩ u hu hf hd]
    congr 1

/-- The closure of the Euclidean smooth graph maps exactly onto LeanSolid's H¹ graph. -/
theorem image_euclideanH1 (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω)) :
    jetCoordinates Ω '' closure (euclideanSmoothJets Ω) = (H1 hΩ : Set _) := by
  refine ((jetCoordinates Ω).toHomeomorph.image_closure (euclideanSmoothJets Ω)).trans ?_
  change closure (Set.image (jetCoordinates Ω) (euclideanSmoothJets Ω)) = _
  rw [image_euclideanSmoothJets Ω hE hΩ, ← LinearMap.coe_range]
  exact (Submodule.topologicalClosure_coe _).symm

/-- Compactly supported Euclidean generators, in the companion paper's TestJets layout. -/
def euclideanTestJets (Ω : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanJet Ω) :=
  {U | ∃ (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hf : MemLp u 2 (volume.restrict Ω))
      (hd : ∀ j, MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) 2 (volume.restrict Ω)),
    ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ω ∧
    U.1 = hf.toLp u ∧ U.2 = fun j => (hd j).toLp
      (fun x => fderiv ℝ u x (EuclideanSpace.single j 1))}

private theorem component_support
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    tsupport (componentField u i) ⊆ coordinates.symm ⁻¹' tsupport u := by
  apply closure_minimal _ (isClosed_closure.preimage coordinates.symm.continuous)
  intro x hx
  apply subset_tsupport
  rw [Function.mem_support] at hx ⊢
  exact fun h => hx (by simp [componentField, h])

private theorem assembled_support {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (w : testFields (coordinates '' Ω)) :
    let u := fun x : EuclideanSpace ℝ (Fin n) =>
      coordinates.symm (fun i => w.val i (coordinates x))
    HasCompactSupport u ∧ tsupport u ⊆ Ω := by
  let K := ⋃ i : Fin n, tsupport (w.val i)
  have hK : IsCompact K := isCompact_iUnion fun i => (w.property i).2.1
  have hc : IsCompact (coordinates ⁻¹' K) := coordinates.toHomeomorph.isCompact_preimage.mpr hK
  let u := fun x : EuclideanSpace ℝ (Fin n) =>
    coordinates.symm (fun i => w.val i (coordinates x))
  have hs : tsupport u ⊆ coordinates ⁻¹' K := by
    apply closure_minimal _ hc.isClosed
    intro x hx
    by_contra h
    apply hx
    have hz (i : Fin n) : w.val i (coordinates x) = 0 :=
      image_eq_zero_of_notMem_tsupport fun hi => h (mem_iUnion.mpr ⟨i, hi⟩)
    have hzero : (fun i => w.val i (coordinates x)) = 0 := funext hz
    simp [u, hzero]
  refine ⟨hc.of_isClosed_subset isClosed_closure hs, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨y, hy, he⟩ := (w.property i).2.2 hi
  exact (coordinates.injective he) ▸ hy

/-- The coordinate equivalence maps the compactly supported Euclidean graph onto
the compactly supported Cartesian graph. -/
theorem image_euclideanTestJets (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω)) :
    jetCoordinates Ω '' euclideanTestJets Ω =
      Set.range ((smoothGraph hΩ).comp (testInclusion (coordinates '' Ω))) := by
  ext U
  constructor
  · rintro ⟨J, ⟨u, hf, hd, hu, hc, hs, h₁, h₂⟩, rfl⟩
    let w : testFields (coordinates '' Ω) := ⟨componentField u, fun i => by
      have hₖ : IsCompact (coordinates.symm ⁻¹' tsupport u) :=
        coordinates.symm.toHomeomorph.isCompact_preimage.mpr hc
      refine ⟨componentField_contDiff hu i,
        hₖ.of_isClosed_subset isClosed_closure (component_support u i), fun x hx => ?_⟩
      exact ⟨coordinates.symm x, hs (component_support u i hx), coordinates.apply_symm_apply x⟩⟩
    refine ⟨w, ?_⟩
    have hJ : J = (hf.toLp u, fun j => (hd j).toLp _) := Prod.ext h₁ h₂
    rw [hJ]
    exact (jetCoordinates_smooth Ω hΩ u hu hf hd).symm
  · rintro ⟨w, rfl⟩
    let u (x : EuclideanSpace ℝ (Fin n)) := coordinates.symm (fun i => w.val i (coordinates x))
    have hu : ContDiff ℝ ∞ u := coordinates.symm.contDiff.comp
      (contDiff_pi.mpr fun i => (w.property i).1.comp coordinates.contDiff)
    have hf := memLp_euclidean_of_bounded hE hu.continuous
    have hd (j : Fin n) : MemLp (fun x => fderiv ℝ u x (EuclideanSpace.single j 1))
        2 (volume.restrict Ω) :=
      memLp_euclidean_of_bounded hE ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
    obtain ⟨hc, hs⟩ := assembled_support w
    refine ⟨(hf.toLp u, fun j => (hd j).toLp _), ⟨u, hf, hd, hu, hc, hs, rfl, rfl⟩, ?_⟩
    rw [jetCoordinates_smooth Ω hΩ u hu hf hd]
    change smoothGraph hΩ ⟨componentField u, componentField_contDiff hu⟩ =
      smoothGraph hΩ (testInclusion (coordinates '' Ω) w)
    congr 1

/-- Closure of the Euclidean compactly supported generators gives exactly the
Cartesian zero-trace space after the coordinate change. -/
theorem image_euclideanZeroTrace (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω)) :
    jetCoordinates Ω '' closure (euclideanTestJets Ω) = (zeroTrace hΩ : Set _) := by
  refine ((jetCoordinates Ω).toHomeomorph.image_closure (euclideanTestJets Ω)).trans ?_
  change closure (Set.image (jetCoordinates Ω) (euclideanTestJets Ω)) = _
  rw [image_euclideanTestJets Ω hE hΩ, ← LinearMap.coe_range]
  exact (Submodule.topologicalClosure_coe _).symm

/-- The upstream-style completed Euclidean displacement–gradient graph. -/
abbrev EuclideanH1 (Ω : Set (EuclideanSpace ℝ (Fin n))) :=
  {U : EuclideanJet Ω // U ∈ closure (euclideanSmoothJets Ω)}

/-- The upstream-style quotient relation uses the closure of compactly supported jets. -/
def euclideanSameTrace (Ω : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanH1 Ω) : Prop :=
  u.val - v.val ∈ closure (euclideanTestJets Ω)

abbrev EuclideanTrace (Ω : Set (EuclideanSpace ℝ (Fin n))) := Quot (euclideanSameTrace Ω)

/-- The coordinate map restricts to a bijection of the two completed H¹ graphs. -/
noncomputable def h1Coordinates (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω)) :
    EuclideanH1 Ω ≃ H1 hΩ where
  toFun u := ⟨jetCoordinates Ω u.val, by
    change jetCoordinates Ω u.val ∈ (H1 hΩ : Set _)
    rw [← image_euclideanH1 Ω hE hΩ]
    exact ⟨u.val, u.property, rfl⟩⟩
  invFun u := ⟨(jetCoordinates Ω).symm u.val, by
    have h : u.val ∈ Set.image (jetCoordinates Ω) (closure (euclideanSmoothJets Ω)) := by
      rw [image_euclideanH1 Ω hE hΩ]
      exact u.property
    obtain ⟨v, hv, he⟩ := h
    rw [← he, ContinuousLinearEquiv.symm_apply_apply]
    exact hv⟩
  left_inv _ := Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _)

theorem h1Coordinates_apply_val (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω))
    (u : EuclideanH1 Ω) : (h1Coordinates Ω hE hΩ u).val = jetCoordinates Ω u.val := by
  unfold h1Coordinates
  rfl

/-- Two Euclidean jets have the same trace exactly when their Cartesian images do. -/
theorem sameTrace_iff_coordinates (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω))
    (u v : EuclideanH1 Ω) :
    euclideanSameTrace Ω u v ↔
      h1Coordinates Ω hE hΩ u - h1Coordinates Ω hE hΩ v ∈ zeroTraceInH1 hΩ := by
  unfold euclideanSameTrace zeroTraceInH1
  change (u.val - v.val ∈ closure (euclideanTestJets Ω)) ↔
    ((h1Coordinates Ω hE hΩ u).val - (h1Coordinates Ω hE hΩ v).val ∈ zeroTrace hΩ)
  rw [h1Coordinates_apply_val, h1Coordinates_apply_val, ← map_sub]
  change _ ↔ jetCoordinates Ω (u.val - v.val) ∈ (zeroTrace hΩ : Set _)
  rw [← image_euclideanZeroTrace Ω hE hΩ]
  constructor
  · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨p, hp, he⟩
    exact (jetCoordinates Ω).injective he ▸ hp

/-- The precise bijection of the Euclidean and Cartesian variational boundary data. -/
noncomputable def euclideanTraceCoordinates (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω)) :
    EuclideanTrace Ω ≃ Trace hΩ where
  toFun := Quot.map (h1Coordinates Ω hE hΩ) fun u v h =>
    (sameTrace_iff_coordinates Ω hE hΩ u v).mp h
  invFun := Quot.map (h1Coordinates Ω hE hΩ).symm fun u v h => by
    apply (sameTrace_iff_coordinates Ω hE hΩ _ _).mpr
    simpa only [Equiv.apply_symm_apply] using h
  left_inv q := by
    induction q using Quot.inductionOn with
    | _ u =>
      change Quot.mk _ ((h1Coordinates Ω hE hΩ).symm (h1Coordinates Ω hE hΩ u)) = Quot.mk _ u
      rw [Equiv.symm_apply_apply]
  right_inv q := by
    induction q using Quot.inductionOn with
    | _ u =>
      change Quot.mk _ (h1Coordinates Ω hE hΩ ((h1Coordinates Ω hE hΩ).symm u)) = Quot.mk _ u
      rw [Equiv.apply_symm_apply]

/-- Euclidean zero trace agrees with membership in the Cartesian test space. -/
theorem zeroTrace_iff_coordinates (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω))
    (u : EuclideanH1 Ω) :
    u.val ∈ closure (euclideanTestJets Ω) ↔
      h1Coordinates Ω hE hΩ u ∈ zeroTraceInH1 hΩ := by
  change _ ↔ (h1Coordinates Ω hE hΩ u).val ∈ (zeroTrace hΩ : Set _)
  rw [h1Coordinates_apply_val, ← image_euclideanZeroTrace Ω hE hΩ]
  constructor
  · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨p, hp, he⟩
    exact (jetCoordinates Ω).injective he ▸ hp

theorem euclideanTraceCoordinates_mk (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hE : Bornology.IsBounded Ω) (hΩ : Bornology.IsBounded (coordinates '' Ω))
    (u : EuclideanH1 Ω) :
    euclideanTraceCoordinates Ω hE hΩ (Quot.mk _ u) =
      traceOf hΩ (h1Coordinates Ω hE hΩ u) := by
  unfold euclideanTraceCoordinates traceOf
  rfl

end LeanSolid.Elastostatics.Sobolev.Domain
