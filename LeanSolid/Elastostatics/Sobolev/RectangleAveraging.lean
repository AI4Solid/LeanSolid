module

public import LeanSolid.Elastostatics.Sobolev.RectangleCompactness
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

@[expose] public section

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology ENNReal

namespace LeanSolid.Elastostatics.Rectangle

variable {a b L : ℝ}

/-- A half-open cell in a uniform rectangular grid. The grid has `k` intervals in each direction. -/
noncomputable def gridCell (a b L : ℝ) (k : ℕ) (j : Fin k × Fin k) : Set (ℝ × ℝ) :=
  Ioc (a + (b - a) * (j.1 : ℝ) / k) (a + (b - a) * ((j.1 : ℝ) + 1) / k) ×ˢ
  Ioc (L * (j.2 : ℝ) / k) (L * ((j.2 : ℝ) + 1) / k)

theorem measurableSet_gridCell (a b L : ℝ) (k : ℕ) (j : Fin k × Fin k) :
    MeasurableSet (gridCell a b L k j) := measurableSet_Ioc.prod measurableSet_Ioc

private theorem gridIntervals_disjoint {k : ℕ} {i j : Fin k} (hij : i < j)
    (x w : ℝ) (hw : 0 ≤ w) :
    Disjoint (Ioc (x + w * (i : ℝ) / k) (x + w * ((i : ℝ) + 1) / k))
      (Ioc (x + w * (j : ℝ) / k) (x + w * ((j : ℝ) + 1) / k)) := by
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (show i.val < j.val from hij)
  have h := add_le_add_left
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hij' hw)
      (Nat.cast_nonneg k : 0 ≤ (k : ℝ))) x
  have h' : x + w * ((i : ℝ) + 1) / k ≤ x + w * (j : ℝ) / k := by
    simpa only [add_comm] using h
  exact Set.disjoint_left.mpr fun _ hi hj => (not_lt_of_ge (hi.2.trans h')) hj.1

/-- Distinct cells do not overlap, including along their half-open edges. -/
theorem gridCell_pairwiseDisjoint (hab : a ≤ b) (hL : 0 ≤ L) (k : ℕ) :
    Pairwise (fun i j : Fin k × Fin k => Disjoint (gridCell a b L k i) (gridCell a b L k j)) := by
  intro i j hij
  by_cases hx : i.1 = j.1
  · have hy : i.2 ≠ j.2 := fun h => hij (Prod.ext hx h)
    have hd := (lt_or_gt_of_ne hy).elim
      (fun h => gridIntervals_disjoint h 0 L hL)
      (fun h => (gridIntervals_disjoint h 0 L hL).symm)
    exact Set.disjoint_left.mpr fun p hi hj => Set.disjoint_left.mp hd
      (by simpa only [zero_add] using hi.2) (by simpa only [zero_add] using hj.2)
  · have hd := (lt_or_gt_of_ne hx).elim
      (fun h => gridIntervals_disjoint h a (b - a) (sub_nonneg.mpr hab))
      (fun h => (gridIntervals_disjoint h a (b - a) (sub_nonneg.mpr hab)).symm)
    exact Set.disjoint_left.mpr fun _ hi hj => Set.disjoint_left.mp hd hi.1 hj.1

private theorem iUnion_adjacent (g : ℕ → ℝ) (hg : Monotone g) (n : ℕ) :
    (⋃ j : Fin n, Ioc (g j.val) (g (j.val + 1))) = Ioc (g 0) (g n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit :
        (⋃ j : Fin (n + 1), Ioc (g j.val) (g (j.val + 1))) =
          (⋃ j : Fin n, Ioc (g j.val) (g (j.val + 1))) ∪ Ioc (g n) (g (n + 1)) := by
      ext x
      simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨j, hj⟩
        induction j using Fin.lastCases with
        | last => exact Or.inr hj
        | cast j => exact Or.inl ⟨j, hj⟩
      · rintro (⟨j, hj⟩ | hj)
        · exact ⟨j.castSucc, hj⟩
        · exact ⟨Fin.last n, hj⟩
    rw [hsplit, ih, Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le n)) (hg (Nat.le_succ n))]

private theorem grid_axis_cover (x w : ℝ) (hw : 0 ≤ w) {k : ℕ} (hk : 0 < k) :
    (⋃ j : Fin k, Ioc (x + w * (j : ℝ) / k) (x + w * ((j : ℝ) + 1) / k)) =
      Ioc x (x + w) := by
  let g := fun i : ℕ => x + w * (i : ℝ) / k
  have hg : Monotone g := by
    intro i j hij
    exact add_le_add_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hw) (Nat.cast_nonneg k)) x
  have h := iUnion_adjacent g hg k
  simpa [g, Nat.cast_add, Nat.cast_ne_zero.mpr hk.ne', mul_div_cancel_right₀] using h

/-- The half-open grid covers the rectangle with its left and bottom edges omitted. -/
theorem gridCell_iUnion (hab : a ≤ b) (hL : 0 ≤ L) {k : ℕ} (hk : 0 < k) :
    (⋃ j : Fin k × Fin k, gridCell a b L k j) = Ioc a b ×ˢ Ioc 0 L := by
  have hx := grid_axis_cover a (b - a) (sub_nonneg.mpr hab) hk
  rw [add_sub_cancel] at hx
  have hy := grid_axis_cover 0 L hL hk
  simp only [zero_add] at hy
  rw [← hx, ← hy]
  ext p
  simp only [mem_iUnion, mem_prod, gridCell]
  constructor
  · rintro ⟨j, h₁, h₂⟩
    exact ⟨⟨j.1, h₁⟩, ⟨j.2, h₂⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨(i, j), hi, hj⟩

/-- The grid covers the bulk rectangle almost everywhere. -/
theorem ae_mem_gridCells (hab : a ≤ b) (hL : 0 ≤ L) {k : ℕ} (hk : 0 < k) :
    ∀ᵐ p ∂bulkMeasure a b L, p ∈ ⋃ j : Fin k × Fin k, gridCell a b L k j := by
  rw [gridCell_iUnion hab hL hk, bulkMeasure, Measure.prod_restrict]
  have hm : ((volume : Measure ℝ).prod volume).restrict (Icc a b ×ˢ Ioc 0 L) =
      ((volume : Measure ℝ).prod volume).restrict (Ioc a b ×ˢ Ioc 0 L) :=
    Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioc_ae_eq_Icc.symm
      (Filter.Eventually.of_forall fun _ => Iff.rfl))
  rw [hm]
  exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)

/-- A bulk integral splits into the finite sum of its integrals on the grid cells. -/
theorem integral_eq_sum_gridCells (hab : a ≤ b) (hL : 0 ≤ L) {k : ℕ} (hk : 0 < k)
    {f : ℝ × ℝ → ℝ} (hf : Integrable f (bulkMeasure a b L)) :
    (∫ p, f p ∂bulkMeasure a b L) =
      ∑ j : Fin k × Fin k, ∫ p in gridCell a b L k j, f p ∂bulkMeasure a b L := by
  have h := integral_iUnion_fintype (measurableSet_gridCell a b L k)
    (gridCell_pairwiseDisjoint hab hL k) (fun j => hf.integrableOn (s := gridCell a b L k j))
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem_gridCells hab hL hk)] at h

/-- A uniform cellwise error estimate sums to the same bulk estimate. -/
theorem integral_error_le_of_gridCells (hab : a ≤ b) (hL : 0 ≤ L) {k : ℕ} (hk : 0 < k)
    {error energy : ℝ × ℝ → ℝ} {C : ℝ}
    (he : Integrable error (bulkMeasure a b L)) (hd : Integrable energy (bulkMeasure a b L))
    (hcell : ∀ j : Fin k × Fin k,
      (∫ p in gridCell a b L k j, error p ∂bulkMeasure a b L) ≤
        C * ∫ p in gridCell a b L k j, energy p ∂bulkMeasure a b L) :
    (∫ p, error p ∂bulkMeasure a b L) ≤ C * ∫ p, energy p ∂bulkMeasure a b L := by
  rw [integral_eq_sum_gridCells hab hL hk he, integral_eq_sum_gridCells hab hL hk hd,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hcell j

/-- Restricting the bulk measure to a cell gives the product of its two interval measures. -/
theorem bulkMeasure_restrict_gridCell (hab : a ≤ b) (hL : 0 ≤ L) {k : ℕ} (hk : 0 < k)
    (j : Fin k × Fin k) :
    (bulkMeasure a b L).restrict (gridCell a b L k j) =
      (volume.restrict (Ioc (a + (b - a) * (j.1 : ℝ) / k)
        (a + (b - a) * ((j.1 : ℝ) + 1) / k))).prod
      (volume.restrict (Ioc (L * (j.2 : ℝ) / k) (L * ((j.2 : ℝ) + 1) / k))) := by
  have hs : gridCell a b L k j ⊆ Icc a b ×ˢ Ioc 0 L := by
    have hc : gridCell a b L k j ⊆ Ioc a b ×ˢ Ioc 0 L := by
      rw [← gridCell_iUnion hab hL hk]
      exact subset_iUnion _ j
    exact hc.trans (prod_mono Ioc_subset_Icc_self Subset.rfl)
  rw [bulkMeasure, Measure.prod_restrict, Measure.restrict_restrict
    (measurableSet_gridCell a b L k j), inter_eq_left.mpr hs]
  exact (Measure.prod_restrict _ _).symm

/-- A grid cell has the same horizontal and vertical widths as the other cells on its grid. -/
theorem gridCell_widths (k : ℕ) (j : Fin k × Fin k) :
    (a + (b - a) * ((j.1 : ℝ) + 1) / k) - (a + (b - a) * (j.1 : ℝ) / k) =
        (b - a) / k ∧
      L * ((j.2 : ℝ) + 1) / k - L * (j.2 : ℝ) / k = L / k := by
  constructor <;> ring

/-- On each uniform grid cell, the mean-subtraction error has the same bound in terms of
the grid widths and the squared directional derivatives. -/
theorem gridCell_average_error (hab : a < b) (hL : 0 < L) {k : ℕ} (hk : 0 < k)
    (j : Fin k × Fin k) {u : ℝ → ℝ → ℝ}
    (hu : Continuous (Function.uncurry u))
    (hsx : ∀ y, ContDiff ℝ 1 (fun x => u x y))
    (hsy : ∀ x, ContDiff ℝ 1 (u x))
    (hdx : Continuous (fun p : ℝ × ℝ => deriv (fun x => u x p.2) p.1))
    (hdy : Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2)) :
    let Q := gridCell a b L k j
    let m := (∫ p in Q, u p.1 p.2 ∂bulkMeasure a b L) / (bulkMeasure a b L Q).toReal
    (∫ p in Q, (u p.1 p.2 - m) ^ 2 ∂bulkMeasure a b L) ≤
      2 * (((b - a) / k) / Real.pi) ^ 2 *
        (∫ p in Q, deriv (fun x => u x p.2) p.1 ^ 2 ∂bulkMeasure a b L) +
      2 * ((L / k) / Real.pi) ^ 2 *
        (∫ p in Q, deriv (u p.1) p.2 ^ 2 ∂bulkMeasure a b L) := by
  let s := a + (b - a) * (j.1 : ℝ) / k
  let t := a + (b - a) * ((j.1 : ℝ) + 1) / k
  let r := L * (j.2 : ℝ) / k
  let q := L * ((j.2 : ℝ) + 1) / k
  obtain ⟨hw, hh⟩ := gridCell_widths (a := a) (b := b) (L := L) k j
  change t - s = _ at hw
  change q - r = _ at hh
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hx : s < t := sub_pos.mp (hw ▸ div_pos (sub_pos.mpr hab) hk')
  have hy : r < q := sub_pos.mp (hh ▸ div_pos hL hk')
  let μ := (volume.restrict (Ioc s t)).prod (volume.restrict (Ioc r q))
  have hm : (bulkMeasure a b L (gridCell a b L k j)).toReal = (t - s) * (q - r) := by
    rw [← Measure.restrict_apply_univ, bulkMeasure_restrict_gridCell hab.le hL.le hk,
      ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, Measure.restrict_apply_univ,
      ENNReal.toReal_mul, Real.volume_Ioc, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hx.le), ENNReal.toReal_ofReal (sub_nonneg.mpr hy.le)]
  dsimp only
  rw [hm]
  simp only [bulkMeasure_restrict_gridCell hab.le hL.le hk j]
  have h := rectangular_cell_average_error hx hy hu hsx hsy hdx hdy
  change (∫ p, (u p.1 p.2 - (∫ p, u p.1 p.2 ∂μ) / ((t - s) * (q - r))) ^ 2 ∂μ) ≤ _ at h
  rw [← hw, ← hh]
  exact h

theorem bulk_cell_ne_top (s : Set (ℝ × ℝ)) : bulkMeasure a b L s ≠ ∞ := by
  let : IsFiniteMeasure (bulkMeasure a b L) := by rw [bulkMeasure]; infer_instance
  exact (measure_lt_top _ _).ne

/-- The L² indicator of a measurable cell. -/
noncomputable def cellIndicator (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) : Interior a b L :=
  indicatorConstLp 2 hs (bulk_cell_ne_top s) (1 : ℝ)

/-- Scalar mean on a cell, using the bulk measure restricted to the rectangle. -/
noncomputable def cellAverage (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    Interior a b L →L[ℝ] ℝ :=
  (bulkMeasure a b L s).toReal⁻¹ • innerSL ℝ (cellIndicator s hs)

theorem cellAverage_apply (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) (f : Interior a b L) :
    cellAverage s hs f = (∫ p in s, f p ∂bulkMeasure a b L) / (bulkMeasure a b L s).toReal := by
  rw [cellAverage, smul_apply, innerSL_apply_apply, cellIndicator,
    L2.inner_indicatorConstLp_one hs (bulk_cell_ne_top s) f, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Continuous reconstruction of a scalar from the cell coefficients. -/
noncomputable def reconstructGridComponent (k : ℕ) :
    ((Fin k × Fin k) → ℝ) →L[ℝ] Interior a b L :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight
    (cellIndicator (gridCell a b L k j) (measurableSet_gridCell a b L k j))

theorem reconstructGridComponent_apply (k : ℕ) (c : (Fin k × Fin k) → ℝ) :
    reconstructGridComponent (a := a) (b := b) (L := L) k c =
    ∑ j, c j • cellIndicator (a := a) (b := b) (L := L)
      (gridCell a b L k j) (measurableSet_gridCell a b L k j) := by
  simp [reconstructGridComponent, ContinuousLinearMap.smulRight_apply]

/-- The reconstructed scalar equals the sum of cell-supported constants almost everywhere. -/
theorem reconstructGridComponent_ae (k : ℕ) (c : (Fin k × Fin k) → ℝ) :
    ⇑(reconstructGridComponent (a := a) (b := b) (L := L) k c) =ᵐ[bulkMeasure a b L]
      fun p => ∑ j, (gridCell a b L k j).indicator (fun _ => c j) p := by
  rw [reconstructGridComponent_apply]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  rw [show (fun p => ∑ j, (gridCell a b L k j).indicator (fun _ => c j) p) =
      ∑ j, (gridCell a b L k j).indicator (fun _ => c j) by
    funext p
    rw [Finset.sum_apply]]
  apply eventuallyEq_sum
  intro j _
  refine (Lp.coeFn_smul _ _).trans ?_
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := bulkMeasure a b L)
    (hs := measurableSet_gridCell a b L k j) (hμs := bulk_cell_ne_top _) (c := (1 : ℝ))]
    with p hp
  change c j * (cellIndicator (gridCell a b L k j) (measurableSet_gridCell a b L k j) : Interior a b L) p =
    (gridCell a b L k j).indicator (fun _ => c j) p
  rw [show (cellIndicator (gridCell a b L k j) (measurableSet_gridCell a b L k j) :
      Interior a b L) p = _ from hp]
  by_cases h : p ∈ gridCell a b L k j <;> simp [h]

/-- On a grid cell, the reconstruction has exactly the supplied coefficient almost everywhere. -/
theorem reconstructGridComponent_ae_on_cell (hab : a ≤ b) (hL : 0 ≤ L)
    (k : ℕ) (c : (Fin k × Fin k) → ℝ) (i : Fin k × Fin k) :
    ∀ᵐ p ∂bulkMeasure a b L, p ∈ gridCell a b L k i →
      reconstructGridComponent (a := a) (b := b) (L := L) k c p = c i := by
  filter_upwards [reconstructGridComponent_ae (a := a) (b := b) (L := L) k c] with p hp hi
  rw [hp, Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hj
    have hn : p ∉ gridCell a b L k j := fun hjp =>
      Set.disjoint_left.mp (gridCell_pairwiseDisjoint hab hL k hj) hjp hi
    simp [hn]
  · simp

/-- Uniform integrated error for a scalar L² grid reconstruction of a smooth field. -/
theorem gridComponent_error (hab : a < b) (hL : 0 < L) {k : ℕ} (hk : 0 < k)
    {u : ℝ → ℝ → ℝ}
    (hu : Continuous (Function.uncurry u))
    (hsx : ∀ y, ContDiff ℝ 1 (fun x => u x y))
    (hsy : ∀ x, ContDiff ℝ 1 (u x))
    (hdx : Continuous (fun p : ℝ × ℝ => deriv (fun x => u x p.2) p.1))
    (hdy : Continuous (fun p : ℝ × ℝ => deriv (u p.1) p.2))
    (f : Interior a b L) (hf : ⇑f =ᵐ[bulkMeasure a b L] Function.uncurry u) :
    let c := fun j => cellAverage (gridCell a b L k j) (measurableSet_gridCell a b L k j) f
    ‖f - reconstructGridComponent k c‖ ^ 2 ≤
      2 * (((b - a) / k) / Real.pi) ^ 2 *
        (∫ p, deriv (fun x => u x p.2) p.1 ^ 2 ∂bulkMeasure a b L) +
      2 * ((L / k) / Real.pi) ^ 2 *
        (∫ p, deriv (u p.1) p.2 ^ 2 ∂bulkMeasure a b L) := by
  let c := fun j => cellAverage (gridCell a b L k j) (measurableSet_gridCell a b L k j) f
  let g : Interior a b L := reconstructGridComponent k c
  let E := fun p : ℝ × ℝ => ((f - g : Interior a b L) p) ^ 2
  let D₁ := fun p : ℝ × ℝ => deriv (fun x => u x p.2) p.1 ^ 2
  let D₂ := fun p : ℝ × ℝ => deriv (u p.1) p.2 ^ 2
  have hnorm : ‖f - g‖ ^ 2 = ∫ p, E p ∂bulkMeasure a b L := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with p
    rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hi (d : ℝ × ℝ → ℝ) (hd : Continuous d) : Integrable d (bulkMeasure a b L) := by
    rw [bulkMeasure, Measure.prod_restrict]
    exact (hd.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Subset.rfl Ioc_subset_Icc_self)
  have he : Integrable E (bulkMeasure a b L) := (Lp.memLp (f - g)).integrable_sq
  have h₁ : Integrable D₁ (bulkMeasure a b L) := hi D₁ (hdx.pow 2)
  have h₂ : Integrable D₂ (bulkMeasure a b L) := hi D₂ (hdy.pow 2)
  change ‖f - g‖ ^ 2 ≤ _
  rw [hnorm, integral_eq_sum_gridCells hab.le hL.le hk he,
    integral_eq_sum_gridCells hab.le hL.le hk h₁, integral_eq_sum_gridCells hab.le hL.le hk h₂]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hcg : c j = (∫ p in gridCell a b L k j, u p.1 p.2 ∂bulkMeasure a b L) /
      (bulkMeasure a b L (gridCell a b L k j)).toReal := by
    dsimp only [c]
    rw [cellAverage_apply]
    congr 1
    exact integral_congr_ae (ae_restrict_of_ae hf)
  have hE : (∫ p in gridCell a b L k j, E p ∂bulkMeasure a b L) =
      ∫ p in gridCell a b L k j, (u p.1 p.2 - c j) ^ 2 ∂bulkMeasure a b L := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub f g), ae_restrict_of_ae hf,
      ae_restrict_of_ae (reconstructGridComponent_ae_on_cell hab.le hL.le k c j),
      ae_restrict_mem (measurableSet_gridCell a b L k j)] with p hfg hf' hg' hp
    change ((f - g : Interior a b L) p) ^ 2 = _
    rw [hfg, Pi.sub_apply, hf', hg' hp]
    rfl
  rw [hE, hcg]
  exact gridCell_average_error hab hL hk j hu hsx hsy hdx hdy

/-- Average both displacement components over each cell. The coefficients are finite-dimensional. -/
noncomputable def projectGrid (k : ℕ) : bottomFixedSpace a b L →L[ℝ] (Fin 2 → (Fin k × Fin k) → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.pi fun j =>
      (cellAverage (gridCell a b L k j) (measurableSet_gridCell a b L k j)).comp
        ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 2 => Interior a b L) i).comp rectangleDisplacement)

theorem projectGrid_apply (k : ℕ) (U : bottomFixedSpace a b L) (i : Fin 2)
    (j : Fin k × Fin k) :
    projectGrid k U i j =
      (∫ p in gridCell a b L k j, rectangleDisplacement U i p ∂bulkMeasure a b L) /
        (bulkMeasure a b L (gridCell a b L k j)).toReal :=
  cellAverage_apply _ _ _

/-- Rebuild a piecewise constant vector from the grid coefficients. -/
noncomputable def reconstructGrid (k : ℕ) :
    (Fin 2 → (Fin k × Fin k) → ℝ) →L[ℝ] Vec (Interior a b L) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => Interior a b L)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (reconstructGridComponent k).comp (ContinuousLinearMap.proj i))

private theorem l2_norm_sq_of_ae {f : Interior a b L} {g : ℝ × ℝ → ℝ}
    (h : ⇑f =ᵐ[bulkMeasure a b L] g) :
    ‖f‖ ^ 2 = ∫ p, g p ^ 2 ∂bulkMeasure a b L := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h] with p hp
  rw [hp, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The two-component grid approximation error is uniformly controlled by the graph norm
on smooth bottom-fixed trial fields. -/
theorem gridErrorSq_on_trials (hab : a < b) (hL : 0 < L) {k : ℕ} (hk : 0 < k)
    (u : Trials a b) :
    let U : bottomFixedSpace a b L := ⟨trialGraph a b L u,
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)⟩
    ‖rectangleDisplacement U - reconstructGrid k (projectGrid k U)‖ ^ 2 ≤
      (2 * (((b - a) / k) / Real.pi) ^ 2 + 2 * ((L / k) / Real.pi) ^ 2) * ‖U‖ ^ 2 := by
  intro U
  let W := trialGraph a b L u
  let cx := 2 * (((b - a) / k) / Real.pi) ^ 2
  let cy := 2 * ((L / k) / Real.pi) ^ 2
  have hi (i : Fin 2) :
      ‖((rectangleDisplacement U - reconstructGrid k (projectGrid k U)) :
        Vec (Interior a b L)) i‖ ^ 2 ≤
        cx * ‖W.snd.fst i‖ ^ 2 + cy * ‖W.snd.snd i‖ ^ 2 := by
    let f := u i
    let v := fun x y : ℝ => f.val (x, y)
    have hsx (y : ℝ) : ContDiff ℝ 1 (fun x => v x y) :=
      f.property.1.comp (contDiff_id.prodMk contDiff_const)
    have hsy (x : ℝ) : ContDiff ℝ 1 (v x) :=
      f.property.1.comp (contDiff_const.prodMk contDiff_id)
    have hx (p : ℝ × ℝ) : deriv (fun x => v x p.2) p.1 = fderiv ℝ f.val p (1, 0) := by
      have hline : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
        (hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2)
      exact ((f.property.1.differentiable one_ne_zero p).hasFDerivAt.comp_hasDerivAt
        p.1 hline).deriv
    have hy (p : ℝ × ℝ) : deriv (v p.1) p.2 = fderiv ℝ f.val p (0, 1) := by
      have hline : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
        (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
      exact ((f.property.1.differentiable one_ne_zero p).hasFDerivAt.comp_hasDerivAt
        p.2 hline).deriv
    have hc (d : ℝ × ℝ) : Continuous (fun p => fderiv ℝ f.val p d) :=
      (f.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    obtain ⟨hval, hdx, hdy⟩ := trialGraph_components a b L u i
    have hf : ⇑(rectangleDisplacement U i) =ᵐ[bulkMeasure a b L] Function.uncurry v := by
      change ⇑(W.fst i) =ᵐ[bulkMeasure a b L] _
      rw [hval]
      exact valueMap_ae f
    have h := gridComponent_error hab hL hk (u := v) f.property.1.continuous hsx hsy
      (by simp_rw [hx]; exact hc _) (by simp_rw [hy]; exact hc _) (rectangleDisplacement U i) hf
    have hX : ‖W.snd.fst i‖ ^ 2 =
        ∫ p, deriv (fun x => v x p.2) p.1 ^ 2 ∂bulkMeasure a b L := by
      rw [hdx]
      simp_rw [hx]
      exact l2_norm_sq_of_ae (derivativeMap_ae f (1, 0))
    have hY : ‖W.snd.snd i‖ ^ 2 =
        ∫ p, deriv (v p.1) p.2 ^ 2 ∂bulkMeasure a b L := by
      rw [hdy]
      simp_rw [hy]
      exact l2_norm_sq_of_ae (derivativeMap_ae f (0, 1))
    rw [hX, hY]
    exact h
  have hsum : ‖rectangleDisplacement U - reconstructGrid k (projectGrid k U)‖ ^ 2 ≤
      cx * ‖W.snd.fst‖ ^ 2 + cy * ‖W.snd.snd‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hi i
  change ‖rectangleDisplacement U - reconstructGrid k (projectGrid k U)‖ ^ 2 ≤
    (cx + cy) * ‖W‖ ^ 2
  refine hsum.trans ?_
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  have hcx : 0 ≤ cx := by positivity
  have hcy : 0 ≤ cy := by positivity
  nlinarith only [mul_nonneg hcx (sq_nonneg ‖W.fst‖), mul_nonneg hcy (sq_nonneg ‖W.fst‖),
    mul_nonneg hcx (sq_nonneg ‖W.snd.snd‖), mul_nonneg hcy (sq_nonneg ‖W.snd.fst‖)]

/-- The same error estimate holds on the completed bottom-fixed graph. -/
theorem gridErrorSq (hab : a < b) (hL : 0 < L) {k : ℕ} (hk : 0 < k)
    (U : bottomFixedSpace a b L) :
    ‖rectangleDisplacement U - reconstructGrid k (projectGrid k U)‖ ^ 2 ≤
      (2 * (((b - a) / k) / Real.pi) ^ 2 + 2 * ((L / k) / Real.pi) ^ 2) * ‖U‖ ^ 2 := by
  let R := LinearMap.range (trialGraph a b L)
  let e : Trials a b →ₗ[ℝ] bottomFixedSpace a b L :=
    (trialGraph a b L).codRestrict _ fun u =>
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)
  have hdense : DenseRange e := by
    have hi : DenseRange (Set.inclusion (show (R : Set (Graph a b L)) ⊆ R.topologicalClosure from
        Submodule.le_topologicalClosure R)) := by
      apply (denseRange_inclusion_iff (Submodule.le_topologicalClosure R)).2
      rw [Submodule.topologicalClosure_coe]
    have hs : Function.Surjective (trialGraph a b L).rangeRestrict := by
      rintro ⟨_, u, rfl⟩
      exact ⟨u, rfl⟩
    exact hi.comp hs.denseRange (continuous_inclusion _)
  let A : bottomFixedSpace a b L →L[ℝ] Vec (Interior a b L) :=
    rectangleDisplacement - (reconstructGrid k).comp (projectGrid k)
  let C := 2 * (((b - a) / k) / Real.pi) ^ 2 + 2 * ((L / k) / Real.pi) ^ 2
  have hc : IsClosed {W : bottomFixedSpace a b L | ‖A W‖ ^ 2 ≤ C * ‖W‖ ^ 2} :=
    isClosed_le (A.continuous.norm.pow 2) (continuous_const.mul (continuous_norm.pow 2))
  have htrial (u : Trials a b) : ‖A (e u)‖ ^ 2 ≤ C * ‖e u‖ ^ 2 :=
    gridErrorSq_on_trials hab hL hk u
  exact hdense.induction (fun _ ⟨u, hu⟩ => hu ▸ htrial u) hc U

private theorem tendsto_of_norm_error {V : Type*} [SeminormedAddCommGroup V]
    (f : ℕ → V) (v : V) (h : Tendsto (fun k => ‖f k - v‖) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 v) :=
  tendsto_iff_norm_sub_tendsto_zero.mpr h

set_option maxHeartbeats 800000 in
/-- Rellich compactness for the concrete bottom-fixed rectangular displacement graph. -/
theorem rectangleDisplacement_compact (hab : a < b) (hL : 0 < L) :
    IsCompact (closure (rectangleDisplacement '' {U : bottomFixedSpace a b L | ‖U‖ = 1})) := by
  let C := Real.sqrt (2 * ((b - a) / Real.pi) ^ 2 + 2 * (L / Real.pi) ^ 2)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = 2 * ((b - a) / Real.pi) ^ 2 + 2 * (L / Real.pi) ^ 2 :=
    Real.sq_sqrt (by positivity)
  apply rectangleDisplacement_compact_of_finite_rank_approx
    (fun k => Fin 2 → (Fin (k + 1) × Fin (k + 1)) → ℝ)
    (fun k => projectGrid (k + 1)) (fun k => reconstructGrid (k + 1))
  refine tendsto_of_norm_error (V := bottomFixedSpace a b L →L[ℝ] Vec (Interior a b L))
    (fun k => (reconstructGrid (k + 1)).comp (projectGrid (k + 1))) rectangleDisplacement ?_
  refine squeeze_zero (g := fun k : ℕ => C * (1 / ((k : ℝ) + 1)))
    (fun _ => by positivity) (fun k => ?_) ?_
  · apply ContinuousLinearMap.opNorm_le_bound _ (show 0 ≤ C * (1 / ((k : ℝ) + 1)) by positivity)
    intro U
    change ‖reconstructGrid (k + 1) (projectGrid (k + 1) U) - rectangleDisplacement U‖ ≤ _
    rw [norm_sub_rev]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have h := gridErrorSq hab hL (Nat.succ_pos k) U
    change ‖rectangleDisplacement U - reconstructGrid (k + 1) (projectGrid (k + 1) U)‖ ^ 2 ≤ _
    refine h.trans (le_of_eq ?_)
    push_cast
    rw [mul_pow, mul_pow, hCsq]
    ring
  · simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C

/-- With the rectangular compactness and strain kernel established, the mixed problem
requires only the second Korn bound on the completed graph. -/
theorem existsUnique_rectangle_of_second_korn_bound (hab : a < b) (hL : 0 < L)
    {μ lam C : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam) (hC : 0 < C)
    (hsecond : ∀ U : bottomFixedSpace a b L, ‖U‖ ≤ C *
      (‖rectangleStrain (U : Graph a b L)‖ + ‖rectangleDisplacement U‖))
    (t : Vec (Edge a b)) (body : bottomFixedSpace a b L →L[ℝ] ℝ) :
    ∃! U, IsRectangleWeakSolution hL μ lam t body U :=
  existsUnique_rectangle_of_second_korn hab.le hL hμ hlam hC hsecond
    (rectangleDisplacement_compact hab hL) t body

/-- It suffices to prove second Korn for the smooth bottom-fixed trials. -/
theorem existsUnique_rectangle_of_second_korn_on_trials (hab : a < b) (hL : 0 < L)
    {μ lam C : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam) (hC : 0 < C)
    (hsecond : ∀ u : Trials a b,
      ‖trialGraph a b L u‖ ≤ C *
        (‖rectangleStrain (trialGraph a b L u)‖ + ‖(trialGraph a b L u).fst‖))
    (t : Vec (Edge a b)) (body : bottomFixedSpace a b L →L[ℝ] ℝ) :
    ∃! U, IsRectangleWeakSolution hL μ lam t body U :=
  existsUnique_rectangle_of_second_korn_bound hab hL hμ hlam hC
    (rectangle_second_korn_of_trials hsecond) t body

/-- The concrete grid-averaging operators give the desired compactness once their uniform
approximation error is proved to vanish. -/
theorem rectangleDisplacement_compact_of_grid_convergence
    (h : Filter.Tendsto (fun k => (reconstructGrid k).comp (projectGrid k)) Filter.atTop
      (𝓝 (rectangleDisplacement (a := a) (b := b) (L := L)))) :
    IsCompact (closure (rectangleDisplacement '' {U : bottomFixedSpace a b L | ‖U‖ = 1})) :=
  rectangleDisplacement_compact_of_finite_rank_approx
    (fun k => Fin 2 → (Fin k × Fin k) → ℝ) projectGrid reconstructGrid h

/-- The bottom-fixed rectangular Lamé problem has a unique weak solution for a
square-integrable top traction and any continuous bulk load. -/
theorem existsUnique_rectangle_weak_solution (hab : a < b) (hL : 0 < L)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 ≤ lam)
    (t : Vec (Edge a b)) (body : bottomFixedSpace a b L →L[ℝ] ℝ) :
    ∃! U, IsRectangleWeakSolution hL μ lam t body U := by
  obtain ⟨C, hC, hsecond⟩ := rectangle_second_korn hab hL
  exact existsUnique_rectangle_of_second_korn_bound hab hL hμ hlam hC hsecond t body

end LeanSolid.Elastostatics.Rectangle
