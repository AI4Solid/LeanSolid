module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

open MeasureTheory

namespace LeanSolid.Math

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {n : ℕ}

abbrev ScalarVectorL2 (ν : Measure X) (n : ℕ) := PiLp 2 fun _ : Fin n => Lp ℝ 2 ν

private def coord (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i

private noncomputable def axis (i : Fin n) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i 1)

/-- Take the coordinate L² classes of a vector-valued L² field. -/
noncomputable def splitVectorL2 :
    Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] ScalarVectorL2 ν n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => Lp ℝ 2 ν)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (coord i).compLpL 2 ν)

theorem splitVectorL2_ae (f : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) (i : Fin n) :
    ⇑(splitVectorL2 f i) =ᵐ[ν] fun x => f x i := by
  change ⇑((coord i).compLpL 2 ν f) =ᵐ[ν] _
  exact (coord i).coeFn_compLpL f

/-- Assemble a vector-valued L² field from its finitely many scalar coordinates. -/
noncomputable def bundleVectorL2 :
    ScalarVectorL2 ν n →L[ℝ] Lp (EuclideanSpace ℝ (Fin n)) 2 ν :=
  ∑ i, ((axis i).compLpL 2 ν).comp
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => Lp ℝ 2 ν) i)

theorem bundleVectorL2_ae (f : ScalarVectorL2 ν n) (i : Fin n) :
    (fun x => bundleVectorL2 f x i) =ᵐ[ν] ⇑(f i) := by
  have h (j : Fin n) :
      ⇑((axis j).compLpL 2 ν (f j)) =ᵐ[ν] fun x => axis j (f j x) :=
    (axis j).coeFn_compLpL (f j)
  have hall := Filter.eventually_all.mpr h
  have hsum : bundleVectorL2 f = ∑ j, (axis j).compLpL 2 ν (f j) := by
    simp [bundleVectorL2]
  rw [hsum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => (axis j).compLpL 2 ν (f j)),
    hall] with x hx ha
  change ((∑ j, (axis j).compLpL 2 ν (f j)) x) i = f i x
  rw [hx]
  change coord i (∑ j, ((axis j).compLpL 2 ν (f j)) x) = _
  rw [map_sum]
  simp_rw [ha]
  rw [Finset.sum_eq_single i]
  · simp [coord, axis, EuclideanSpace.single]
  · intro j _ hji
    simp [coord, axis, EuclideanSpace.single, Ne.symm hji]
  · simp

theorem split_bundleVectorL2 (f : ScalarVectorL2 ν n) :
    splitVectorL2 (bundleVectorL2 f) = f := by
  apply PiLp.ext
  intro i
  exact Lp.ext ((splitVectorL2_ae (bundleVectorL2 f) i).trans (bundleVectorL2_ae f i))

theorem bundle_splitVectorL2 (f : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    bundleVectorL2 (splitVectorL2 f) = f := by
  apply Lp.ext
  have h (i : Fin n) :
      (fun x => bundleVectorL2 (splitVectorL2 f) x i) =ᵐ[ν] fun x => f x i :=
    (bundleVectorL2_ae (splitVectorL2 f) i).trans (splitVectorL2_ae f i)
  filter_upwards [Filter.eventually_all.mpr h] with x hx
  exact PiLp.ext hx

/-- Under one measure, the two vector L² representations are continuously linearly equivalent. -/
noncomputable def vectorL2Coordinates :
    Lp (EuclideanSpace ℝ (Fin n)) 2 ν ≃L[ℝ] ScalarVectorL2 ν n where
  toFun := splitVectorL2
  invFun := bundleVectorL2
  left_inv := bundle_splitVectorL2
  right_inv := split_bundleVectorL2
  map_add' := map_add splitVectorL2
  map_smul' := map_smul splitVectorL2
  continuous_toFun := splitVectorL2.continuous
  continuous_invFun := bundleVectorL2.continuous

theorem vectorL2Coordinates_apply (f : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    vectorL2Coordinates f = splitVectorL2 f := by unfold vectorL2Coordinates; rfl

/-- Pullback along a measure-preserving coordinate bijection is an isometric equivalence
of vector-valued L² spaces. -/
noncomputable def reindexL2 {Y E : Type*} [MeasurableSpace Y] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {η : Measure Y} (e : X ≃ᵐ Y)
    (he : MeasurePreserving e ν η) : Lp E 2 η ≃ₗᵢ[ℝ] Lp E 2 ν := by
  let pull := Lp.compMeasurePreservingₗᵢ ℝ e he (p := 2) (E := E)
  apply LinearIsometryEquiv.ofSurjective pull
  intro f
  refine ⟨Lp.compMeasurePreserving e.symm he.symm f, ?_⟩
  change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm he.symm f) = f
  apply Lp.ext
  have h₁ := Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving e.symm he.symm f) he
  have h₂ := he.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f he.symm)
  filter_upwards [h₁, h₂] with x hx hy
  exact hx.trans (hy.trans (congrArg (fun y => f y) (e.symm_apply_apply x)))

theorem reindexL2_ae {Y E : Type*} [MeasurableSpace Y] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {η : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e ν η)
    (f : Lp E 2 η) : ⇑(reindexL2 e he f) =ᵐ[ν] ⇑f ∘ e := by
  unfold reindexL2
  exact Lp.coeFn_compMeasurePreserving f he

end LeanSolid.Math
