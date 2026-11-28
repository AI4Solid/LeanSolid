module

public import LeanSolid.ContinuumMechanics.PiolaFlux
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith

@[expose] public section

open LeanSolid.Math MeasureTheory Set Filter
open scoped ContDiff Matrix

namespace LeanSolid.ContinuumMechanics

/-- A finite partition may have shared interfaces of volume zero. -/
theorem integral_finite_iUnion_ae {ι : Type*} [Fintype ι]
    (region : ι → Set (Vector 3)) (f : Vector 3 → ℝ)
    (hMeas : ∀ i, MeasurableSet (region i))
    (hDisjoint : Pairwise (fun i j => AEDisjoint volume (region i) (region j)))
    (hInt : IntegrableOn f (⋃ i, region i)) :
    (∫ x in ⋃ i, region i, f x) = ∑ i, ∫ x in region i, f x := by
  rw [integral_iUnion_ae (fun i => (hMeas i).nullMeasurableSet) hDisjoint hInt, tsum_fintype]

/-- Each internal face has an oppositely oriented mate. Summing all face
fluxes leaves just the exterior contribution. -/
theorem sum_faceFlux_eq_exterior {κ : Type*} [Fintype κ] [DecidableEq κ]
    (exterior interior : Finset κ) (q : κ → ℝ)
    (hCover : exterior ∪ interior = Finset.univ)
    (hDisjoint : Disjoint exterior interior) (mate : κ → κ)
    (hMem : ∀ j ∈ interior, mate j ∈ interior) (hInvolutive : Function.Involutive mate)
    (hOpposite : ∀ j, j ∈ interior → q (mate j) = -q j) :
    (∑ j, q j) = ∑ j ∈ exterior, q j := by
  have hCancel : ∑ j ∈ interior, q j = 0 := by
    apply Finset.sum_involution (fun j _ => mate j)
    · intro j hj
      rw [hOpposite j hj, add_neg_cancel]
    · intro j hj hq he
      have hh := hOpposite j hj
      rw [he] at hh
      exact hq (by linarith)
    · exact hMem
    · intro j _
      exact hInvolutive j
  rw [← hCover, Finset.sum_union hDisjoint, hCancel, add_zero]

/-- Summing the divergence theorem on a finite volume partition by deformed
boxes gives the sum of all patch boundary fluxes. -/
theorem integral_spatialDivergence_deformedBoxUnion {ι : Type*} [Fintype ι]
    (a b : ι → Vector 3) (placement : ι → Vector 3 → Vector 3)
    (v : Vector 3 → Vector 3) (hv : Differentiable ℝ v)
    (hab : ∀ i, a i ≤ b i)
    (hSmooth : ∀ i j, ContDiff ℝ 2 (fun X => placement i X j))
    (hInj : ∀ i, InjOn (placement i) (Icc (a i) (b i)))
    (hJ : ∀ i X, X ∈ Icc (a i) (b i) → 0 < jacobian (deformationGradient (placement i) X)) :
    let region (i : ι) := placement i '' Icc (a i) (b i)
    Pairwise (fun i j => AEDisjoint volume (region i) (region j)) →
    IntegrableOn (spatialDivergence v) (⋃ i, region i) →
    (∀ i, IntegrableOn (spatialDivergence (piolaFlux (placement i) v)) (Icc (a i) (b i))) →
    (∫ x in ⋃ i, region i, spatialDivergence v x) =
      ∑ i, boxBoundaryFlux (a i) (b i) (piolaFlux (placement i) v) := by
  intro region hDisjoint hInt hPullback
  have hMeas (i : ι) : MeasurableSet (region i) := by
    have hc : Continuous (placement i) := continuous_pi fun j => (hSmooth i j).continuous
    exact (isCompact_Icc.image hc).isClosed.measurableSet
  rw [integral_finite_iUnion_ae region _ hMeas hDisjoint hInt]
  exact Finset.sum_congr rfl fun i _ =>
    integral_spatialDivergence_image_box (hab i) _ v (hSmooth i) hv (hInj i) (hJ i) (hPullback i)

/-- Patchwise Reynolds derivatives assemble on the full moving region.
The per-patch boundary contributions combine into the exterior flux. -/
theorem hasDerivAt_reynolds_finitePartition {ι : Type*} [Fintype ι]
    (region : ℝ → ι → Set (Vector 3)) (φ : ℝ → Vector 3 → ℝ)
    (t : ℝ) (gTime : Vector 3 → ℝ) (patchFlux : ι → ℝ) (exteriorFlux : ℝ)
    (hPartition : ∀ᶠ s in nhds t, (∀ i, MeasurableSet (region s i)) ∧
      Pairwise (fun i j => AEDisjoint volume (region s i) (region s j)) ∧
      IntegrableOn (φ s) (⋃ i, region s i))
    (hMeas : ∀ i, MeasurableSet (region t i))
    (hDisjoint : Pairwise (fun i j => AEDisjoint volume (region t i) (region t j)))
    (hTime : IntegrableOn gTime (⋃ i, region t i))
    (hRate : ∀ i, HasDerivAt (fun s => ∫ x in region s i, φ s x)
      ((∫ x in region t i, gTime x) + patchFlux i) t)
    (hExterior : ∑ i, patchFlux i = exteriorFlux) :
    HasDerivAt (fun s => ∫ x in ⋃ i, region s i, φ s x)
      ((∫ x in ⋃ i, region t i, gTime x) + exteriorFlux) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hRate i)
  rw [Finset.sum_add_distrib, hExterior,
    ← integral_finite_iUnion_ae (region t) gTime hMeas hDisjoint hTime] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hPartition] with s hs
  exact integral_finite_iUnion_ae (region s) (φ s) hs.1 hs.2.1 hs.2.2

/-- The signed integral of one upper or lower reference face. -/
noncomputable def boxFaceFlux (a b : Vector 3) (w : Vector 3 → Vector 3)
    (i : Fin 3) (upper : Bool) : ℝ :=
  if upper then
    ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), w (i.insertNth (b i) y) i
  else
    -(∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), w (i.insertNth (a i) y) i)

theorem boxBoundaryFlux_eq_sum_boxFaceFlux (a b : Vector 3) (w : Vector 3 → Vector 3) :
    boxBoundaryFlux a b w = ∑ p : Fin 3 × Bool, boxFaceFlux a b w p.1 p.2 := by
  rw [Fintype.sum_prod_type]
  unfold boxBoundaryFlux
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [boxFaceFlux, sub_eq_add_neg, add_comm]

/-- Shared upper and lower faces cancel when they have a common parameter
domain and the two coordinate flux integrands agree there. -/
theorem boxFaceFlux_upper_eq_neg_lower
    (a b c d : Vector 3) (w z : Vector 3 → Vector 3) (i : Fin 3)
    (hDomain : Icc (a ∘ i.succAbove) (b ∘ i.succAbove) =
      Icc (c ∘ i.succAbove) (d ∘ i.succAbove))
    (hFlux : ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      w (i.insertNth (b i) y) i = z (i.insertNth (c i) y) i) :
    boxFaceFlux a b w i true = -boxFaceFlux c d z i false := by
  simp only [boxFaceFlux, Bool.false_eq_true, ite_false, ite_true, neg_neg]
  rw [← hDomain]
  exact setIntegral_congr_fun measurableSet_Icc hFlux

/-- For adjacent reference boxes placed by the same map, the Piola fluxes on
their common face cancel even when the placed face is curved. -/
theorem piolaFaceFlux_cancel_adjacent
    (a b c d : Vector 3) (χ v : Vector 3 → Vector 3) (i : Fin 3)
    (hLower : a ∘ i.succAbove = c ∘ i.succAbove)
    (hUpper : b ∘ i.succAbove = d ∘ i.succAbove) (hFace : b i = c i) :
    boxFaceFlux a b (piolaFlux χ v) i true +
      boxFaceFlux c d (piolaFlux χ v) i false = 0 := by
  rw [boxFaceFlux_upper_eq_neg_lower a b c d _ _ i (by rw [hLower, hUpper])
    (fun y _ => by rw [hFace]), neg_add_cancel]

/-- Two reference boxes with touching or separated normal intervals overlap
only in a set of volume zero. -/
theorem aeDisjoint_boxes_of_le {a b c d : Vector 3} (i : Fin 3) (hi : b i ≤ c i) :
    AEDisjoint volume (Icc a b) (Icc c d) := by
  apply measure_mono_null (t := {x : Vector 3 | x i = b i})
  · intro x hx
    exact le_antisymm (hx.1.2 i) (hi.trans (hx.2.1 i))
  · exact Measure.pi_hyperplane (fun _ => (volume : Measure ℝ)) i (b i)

/-- A common differentiable placement that is injective on both patches
preserves zero-volume overlap. -/
theorem aeDisjoint_image_of_differentiable {S T : Set (Vector 3)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : AEDisjoint volume S T)
    (χ : Vector 3 → Vector 3) (hχ : Differentiable ℝ χ) (hInj : InjOn χ (S ∪ T)) :
    AEDisjoint volume (χ '' S) (χ '' T) := by
  have he : χ '' S ∩ χ '' T = χ '' (S ∩ T) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hyx⟩, ⟨z, hz, hzx⟩⟩
      have hz' := hInj (Or.inl hy) (Or.inr hz) (hyx.trans hzx.symm)
      exact ⟨y, ⟨hy, hz' ▸ hz⟩, hyx⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  change volume (χ '' S ∩ χ '' T) = 0
  rw [he, ← lintegral_abs_det_fderiv_eq_addHaar_image volume (hS.inter hT)
    (fun x _ => (hχ x).hasFDerivAt.hasFDerivWithinAt)
    (hInj.mono (fun x hx => Or.inl hx.1)),
    Measure.restrict_eq_zero.mpr hST.eq, lintegral_zero_measure]

/-- The finite sum of box fluxes can be evaluated on the exterior face
indices alone when each internal face has an opposite contribution. -/
theorem sum_boxBoundaryFlux_eq_exterior {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → Vector 3) (w : ι → Vector 3 → Vector 3)
    (exterior interior : Finset (ι × (Fin 3 × Bool)))
    (mate : ι × (Fin 3 × Bool) → ι × (Fin 3 × Bool))
    (hCover : exterior ∪ interior = Finset.univ) (hDisjoint : Disjoint exterior interior)
    (hMem : ∀ p ∈ interior, mate p ∈ interior) (hInv : Function.Involutive mate) :
    let q (p : ι × (Fin 3 × Bool)) := boxFaceFlux (a p.1) (b p.1) (w p.1) p.2.1 p.2.2
    (∀ p ∈ interior, q (mate p) = -q p) →
    (∑ i, boxBoundaryFlux (a i) (b i) (w i)) = ∑ p ∈ exterior, q p := by
  intro q hOpp
  simp_rw [boxBoundaryFlux_eq_sum_boxFaceFlux]
  exact (Fintype.sum_prod_type q).symm.trans
    (sum_faceFlux_eq_exterior exterior interior q hCover hDisjoint mate hMem hInv hOpp)

private theorem imageBoxPartition {ι : Type*} (a b : ι → Vector 3)
    (χ : Vector 3 → Vector 3) (hχ : Differentiable ℝ χ)
    (hInj : InjOn χ (⋃ i, Icc (a i) (b i)))
    (hReference : Pairwise (fun i j => AEDisjoint volume (Icc (a i) (b i)) (Icc (a j) (b j)))) :
    (∀ i, MeasurableSet (χ '' Icc (a i) (b i))) ∧
      Pairwise (fun i j => AEDisjoint volume (χ '' Icc (a i) (b i)) (χ '' Icc (a j) (b j))) := by
  refine ⟨fun i => (isCompact_Icc.image hχ.continuous).isClosed.measurableSet, ?_⟩
  intro i j hij
  apply aeDisjoint_image_of_differentiable measurableSet_Icc measurableSet_Icc
    (hReference hij) χ hχ
  apply hInj.mono
  intro X hX
  rcases hX with hi | hj
  · exact mem_iUnion_of_mem i hi
  · exact mem_iUnion_of_mem j hj

/-- Divergence theorem for a common placement of a finite reference-box
partition with matched internal face fluxes. -/
theorem integral_spatialDivergence_eq_exterior_deformedBoxUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → Vector 3)
    (χ v : Vector 3 → Vector 3) (hv : Differentiable ℝ v) (hab : ∀ i, a i ≤ b i)
    (hSmooth : ∀ j, ContDiff ℝ 2 (fun X => χ X j))
    (hInj : InjOn χ (⋃ i, Icc (a i) (b i)))
    (hJ : ∀ X ∈ ⋃ i, Icc (a i) (b i), 0 < jacobian (deformationGradient χ X))
    (hReference : Pairwise (fun i j => AEDisjoint volume (Icc (a i) (b i)) (Icc (a j) (b j))))
    (hInt : IntegrableOn (spatialDivergence v) (⋃ i, χ '' Icc (a i) (b i)))
    (hPullback : ∀ i, IntegrableOn (spatialDivergence (piolaFlux χ v)) (Icc (a i) (b i)))
    (exterior interior : Finset (ι × (Fin 3 × Bool)))
    (mate : ι × (Fin 3 × Bool) → ι × (Fin 3 × Bool))
    (hCover : exterior ∪ interior = Finset.univ) (hDisjoint : Disjoint exterior interior)
    (hMem : ∀ p ∈ interior, mate p ∈ interior) (hInv : Function.Involutive mate) :
    let q (p : ι × (Fin 3 × Bool)) := boxFaceFlux (a p.1) (b p.1) (piolaFlux χ v) p.2.1 p.2.2
    (∀ p ∈ interior, q (mate p) = -q p) →
    (∫ x in ⋃ i, χ '' Icc (a i) (b i), spatialDivergence v x) = ∑ p ∈ exterior, q p := by
  intro q hOpp
  have hc : Differentiable ℝ χ :=
    differentiable_pi.mpr fun j => (hSmooth j).differentiable (by norm_num)
  have hPartition := (imageBoxPartition a b χ hc hInj hReference).2
  have hDivergence := integral_spatialDivergence_deformedBoxUnion a b (fun _ => χ) v hv hab
    (fun _ => hSmooth) (fun i => hInj.mono fun _ hX => mem_iUnion_of_mem i hX)
    (fun i X hX => hJ X (mem_iUnion_of_mem i hX)) hPartition hInt hPullback
  exact hDivergence.trans
    (sum_boxBoundaryFlux_eq_exterior a b (fun _ => piolaFlux χ v)
      exterior interior mate hCover hDisjoint hMem hInv hOpp)

/-- For a moving placement of a finite box partition, the fixed-time Piola
fluxes on matched internal faces disappear from the assembled Reynolds rate. -/
theorem hasDerivAt_reynolds_deformedBoxUnion
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → Vector 3)
    (χ : ℝ → Vector 3 → Vector 3) (φ : ℝ → Vector 3 → ℝ) (t : ℝ)
    (gTime : Vector 3 → ℝ) (v : Vector 3 → Vector 3)
    (hReference : Pairwise (fun i j => AEDisjoint volume (Icc (a i) (b i)) (Icc (a j) (b j))))
    (hPlacement : ∀ᶠ s in nhds t, Differentiable ℝ (χ s) ∧
      InjOn (χ s) (⋃ i, Icc (a i) (b i)))
    (hInt : ∀ᶠ s in nhds t, IntegrableOn (φ s) (⋃ i, χ s '' Icc (a i) (b i)))
    (hTime : IntegrableOn gTime (⋃ i, χ t '' Icc (a i) (b i)))
    (hRate : ∀ i, HasDerivAt (fun s => ∫ x in χ s '' Icc (a i) (b i), φ s x)
      ((∫ x in χ t '' Icc (a i) (b i), gTime x) +
        boxBoundaryFlux (a i) (b i) (piolaFlux (χ t) (advectiveFlux (φ t) v))) t)
    (exterior interior : Finset (ι × (Fin 3 × Bool)))
    (mate : ι × (Fin 3 × Bool) → ι × (Fin 3 × Bool))
    (hCover : exterior ∪ interior = Finset.univ) (hDisjoint : Disjoint exterior interior)
    (hMem : ∀ p ∈ interior, mate p ∈ interior) (hInv : Function.Involutive mate) :
    let q (p : ι × (Fin 3 × Bool)) :=
      boxFaceFlux (a p.1) (b p.1) (piolaFlux (χ t) (advectiveFlux (φ t) v)) p.2.1 p.2.2
    (∀ p ∈ interior, q (mate p) = -q p) →
    HasDerivAt (fun s => ∫ x in ⋃ i, χ s '' Icc (a i) (b i), φ s x)
      ((∫ x in ⋃ i, χ t '' Icc (a i) (b i), gTime x) + ∑ p ∈ exterior, q p) t := by
  intro q hOpp
  have hPartition (s : ℝ) (hs : Differentiable ℝ (χ s) ∧
      InjOn (χ s) (⋃ i, Icc (a i) (b i))) :=
    imageBoxPartition a b (χ s) hs.1 hs.2 hReference
  have ht := hPartition t hPlacement.self_of_nhds
  refine hasDerivAt_reynolds_finitePartition (fun s i => χ s '' Icc (a i) (b i))
    φ t gTime _ _ ?_ ht.1 ht.2 hTime hRate ?_
  · filter_upwards [hPlacement, hInt] with s hs hi
    exact ⟨(hPartition s hs).1, (hPartition s hs).2, hi⟩
  · exact sum_boxBoundaryFlux_eq_exterior a b (fun _ => piolaFlux (χ t) (advectiveFlux (φ t) v))
      exterior interior mate hCover hDisjoint hMem hInv hOpp

end LeanSolid.ContinuumMechanics
