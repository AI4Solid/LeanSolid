module

public import LeanSolid.ContinuumMechanics.Surface
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

open LeanSolid.Math
open Filter MeasureTheory Set
open scoped Matrix Pointwise

namespace LeanSolid.ContinuumMechanics

/-- Oriented area vector of the triangle through the three coordinate intercepts.
For positive intercepts the cyclic order points away from the origin. -/
noncomputable def tetrahedronObliqueArea (a b c : ℝ) : Vector 3 :=
  (1 / 2 : ℝ) • ((![0, b, 0] - ![a, 0, 0]) ⨯₃ (![0, 0, c] - ![a, 0, 0]))

/-- The oblique area components are the signed areas of the coordinate
projections. For positive intercepts these are the three coordinate face areas. -/
theorem tetrahedronObliqueArea_components (a b c : ℝ) :
    tetrahedronObliqueArea a b c = ![b * c / 2, c * a / 2, a * b / 2] := by
  funext i
  fin_cases i <;> simp [tetrahedronObliqueArea, cross_apply] <;> ring

/-- Uniformly scaling the three intercepts scales the oriented area by the
square of the scale. -/
theorem tetrahedronObliqueArea_scale (s a b c : ℝ) :
    tetrahedronObliqueArea (s * a) (s * b) (s * c) =
      s ^ 2 • tetrahedronObliqueArea a b c := by
  rw [tetrahedronObliqueArea_components, tetrahedronObliqueArea_components]
  funext i
  fin_cases i <;> simp <;> ring

/-- The solid tetrahedron spanned by the origin and the three intercepts. -/
def interceptTetrahedron (a b c : ℝ) : Set (Vector 3) :=
  convexHull ℝ {0, ![a, 0, 0], ![0, b, 0], ![0, 0, c]}

theorem isCompact_interceptTetrahedron (a b c : ℝ) :
    IsCompact (interceptTetrahedron a b c) :=
  (by simp : ({0, ![a, 0, 0], ![0, b, 0], ![0, 0, c]} : Set (Vector 3)).Finite)
    |>.isCompact_convexHull ℝ

/-- The Lebesgue volume of a dilated tetrahedron scales by the cube of the scale. -/
theorem volume_interceptTetrahedron_scale (a b c s : ℝ) (hs : 0 ≤ s) :
    volume.real (s • interceptTetrahedron a b c) =
      volume.real (interceptTetrahedron a b c) * s ^ 3 := by
  have hd : Module.finrank ℝ (Vector 3) = 3 := by
    rw [Module.finrank_pi, Fintype.card_fin]
  rw [measureReal_def, Measure.addHaar_smul_of_nonneg volume hs, hd, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hs _), mul_comm, ← measureReal_def]

/-- Specialization of the normalized volume-force limit to actual solid
tetrahedra obtained by dilation about the origin. -/
theorem tendsto_interceptTetrahedron_volumeForce (a b c A M : ℝ) (hA : 0 < A)
    (force : Vector 3 → Vector 3)
    (hBound : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ᵐ x ∂volume.restrict (s • interceptTetrahedron a b c), ‖force x‖ ≤ M) :
    Tendsto (fun s => (A * s ^ 2)⁻¹ • ∫ x in s • interceptTetrahedron a b c, force x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let (s : ℝ) : IsFiniteMeasure (volume.restrict (s • interceptTetrahedron a b c)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact ((isCompact_interceptTetrahedron a b c).smul s).measure_lt_top
  refine tendsto_areaNormalized_volumeForce
    (fun s => volume.restrict (s • interceptTetrahedron a b c))
    force (volume.real (interceptTetrahedron a b c)) A M hA
    ?_ hBound
  · intro s hs
    rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def]
    exact volume_interceptTetrahedron_scale a b c s hs.le

/-- An average on a fixed probability space of face parameters converges to
the traction at the collapse point. The integrand is the pulled-back traction. -/
theorem tendsto_tetrahedron_faceAverage {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (T : ℝ → α → Vector 3) (value : Vector 3)
    (bound : α → ℝ) (hInt : Integrable bound μ)
    (hMeas : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), AEStronglyMeasurable (T s) μ)
    (hBound : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), ∀ᵐ u ∂μ, ‖T s u‖ ≤ bound u)
    (hPoint : ∀ᵐ u ∂μ, Tendsto (fun s => T s u) (nhdsWithin 0 (Ioi 0)) (nhds value)) :
    Tendsto (fun s => ∫ u, T s u ∂μ) (nhdsWithin 0 (Ioi 0)) (nhds value) := by
  have h := tendsto_integral_filter_of_dominated_convergence bound hMeas hBound hInt hPoint
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using h

/-- Once the face averages converge, a normalized shrinking-face force balance
with vanishing volume contribution gives Cauchy's traction formula. The
coordinate averages are signed to correspond to positive coordinate normals. -/
theorem traction_eq_of_tetrahedron_faceAverages
    (traction : Vector 3 → Vector 3) (normal : Vector 3)
    (oblique volumeForce : ℝ → Vector 3) (coordinate : Fin 3 → ℝ → Vector 3)
    (hOblique : Tendsto oblique (nhdsWithin 0 (Ioi 0)) (nhds (traction normal)))
    (hCoordinate : ∀ j, Tendsto (coordinate j) (nhdsWithin 0 (Ioi 0))
      (nhds (traction (Pi.single j 1))))
    (hVolume : Tendsto volumeForce (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hBalance : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      oblique s = (∑ j, normal j • coordinate j s) + volumeForce s) :
    traction normal = stressOfTraction traction *ᵥ normal := by
  have hSum : Tendsto (fun s => ∑ j, normal j • coordinate j s)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (∑ j, normal j • traction (Pi.single j 1))) :=
    tendsto_finsetSum _ fun j _ => tendsto_const_nhds.smul (hCoordinate j)
  let residual (s : ℝ) := ((∑ j, normal j • coordinate j s) -
    (∑ j, normal j • traction (Pi.single j 1))) + (volumeForce s + (traction normal - oblique s))
  have hResidual : Tendsto residual (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [sub_self, add_zero] using
      (hSum.sub (tendsto_const_nhds (x := ∑ j, normal j • traction (Pi.single j 1)))).add
        (hVolume.add ((tendsto_const_nhds (x := traction normal)).sub hOblique))
  apply traction_eq_stressOfTraction_mulVec traction normal residual hResidual
  filter_upwards [hBalance] with s hs
  simp only [residual]
  rw [hs]
  abel

/-- Normalize the integral force balance by the oblique face area. The
coordinate face forces use outward normals, so their averages are the negatives
of the averages measured with the positive coordinate normals. The volume term
is the integral of body force minus inertia. -/
theorem tetrahedron_normalized_forceBalance (a b c s A : ℝ) (hs : 0 < s) (hA : 0 < A)
    (normal oblique bulk : Vector 3) (coordinate : Fin 3 → Vector 3)
    (hArea : tetrahedronObliqueArea a b c = A • normal)
    (hBalance : (A * s ^ 2) • oblique +
      (∑ j, tetrahedronObliqueArea (s * a) (s * b) (s * c) j • (-coordinate j)) +
      bulk = 0) :
    oblique = (∑ j, normal j • coordinate j) - (A * s ^ 2)⁻¹ • bulk := by
  let k := A * s ^ 2
  have hk : k ≠ 0 := mul_ne_zero hA.ne' (pow_ne_zero _ hs.ne')
  have hproject (j : Fin 3) :
      tetrahedronObliqueArea (s * a) (s * b) (s * c) j = k * normal j := by
    rw [tetrahedronObliqueArea_scale, hArea]
    simp only [Pi.smul_apply, smul_eq_mul, k]
    ring
  have hfaces :
      (∑ j, tetrahedronObliqueArea (s * a) (s * b) (s * c) j • (-coordinate j)) =
        -(k • ∑ j, normal j • coordinate j) := by
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hproject j, mul_smul, smul_neg]
  rw [hfaces] at hBalance
  change k • oblique + -(k • ∑ j, normal j • coordinate j) + bulk = 0 at hBalance
  have h := congrArg (fun x : Vector 3 => k⁻¹ • x) hBalance
  simp only [smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hk, one_smul, smul_zero] at h
  exact eq_sub_of_add_eq (by
    calc
      oblique + k⁻¹ • bulk = (∑ j, normal j • coordinate j) +
          (oblique + -(∑ j, normal j • coordinate j) + k⁻¹ • bulk) := by abel
      _ = _ := by rw [h, add_zero])

/-- Cauchy's traction formula from the integral balance on shrinking
intercept tetrahedra and convergence of their signed face averages. -/
theorem traction_eq_of_interceptTetrahedron_balance
    (a b c A M : ℝ) (hA : 0 < A) (traction : Vector 3 → Vector 3) (normal : Vector 3)
    (oblique : ℝ → Vector 3) (coordinate : Fin 3 → ℝ → Vector 3) (force : Vector 3 → Vector 3)
    (hArea : tetrahedronObliqueArea a b c = A • normal)
    (hOblique : Tendsto oblique (nhdsWithin 0 (Ioi 0)) (nhds (traction normal)))
    (hCoordinate : ∀ j, Tendsto (coordinate j) (nhdsWithin 0 (Ioi 0))
      (nhds (traction (Pi.single j 1))))
    (hBound : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ᵐ x ∂volume.restrict (s • interceptTetrahedron a b c), ‖force x‖ ≤ M)
    (hBalance : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      (A * s ^ 2) • oblique s +
      (∑ j, tetrahedronObliqueArea (s * a) (s * b) (s * c) j • (-coordinate j s)) +
      (∫ x in s • interceptTetrahedron a b c, force x) = 0) :
    traction normal = stressOfTraction traction *ᵥ normal := by
  have hVolume := tendsto_interceptTetrahedron_volumeForce a b c A M hA force hBound
  apply traction_eq_of_tetrahedron_faceAverages traction normal oblique
    (fun s => -((A * s ^ 2)⁻¹ • ∫ x in s • interceptTetrahedron a b c, force x))
    coordinate hOblique hCoordinate
  · simpa only [neg_zero] using hVolume.neg
  · filter_upwards [self_mem_nhdsWithin, hBalance] with s hs h
    exact (tetrahedron_normalized_forceBalance a b c s A hs hA normal (oblique s) _
      (fun j => coordinate j s) hArea h).trans (sub_eq_add_neg _ _)

/-- The thin-pillbox balance gives opposing tractions at the collapse point.
The two main-face forces are divided by their common area. The residual
collects the remaining faces and the volume force with the same normalization. -/
theorem traction_neg_of_pillbox_balance
    (traction : Vector 3 → Vector 3) (normal : Vector 3)
    (positive negative residual : ℝ → Vector 3) (C : ℝ)
    (hPositive : Tendsto positive (nhdsWithin 0 (Ioi 0)) (nhds (traction normal)))
    (hNegative : Tendsto negative (nhdsWithin 0 (Ioi 0)) (nhds (traction (-normal))))
    (hResidual : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), ‖residual s‖ ≤ C * s)
    (hBalance : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      positive s + negative s + residual s = 0) :
    traction (-normal) = -traction normal := by
  have hLinear : Tendsto (fun s : ℝ => C * s) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [id_eq, mul_zero] using
      (tendsto_const_nhds (x := C)).mul (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto id (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
  have hZero : Tendsto residual (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    squeeze_zero_norm' hResidual hLinear
  have hSum : Tendsto (fun s => positive s + negative s + residual s)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (traction normal + traction (-normal))) := by
    simpa only [add_zero] using (hPositive.add hNegative).add hZero
  have h := tendsto_nhds_unique_of_eventuallyEq hSum (tendsto_const_nhds (x := (0 : Vector 3)))
    hBalance
  exact eq_neg_of_add_eq_zero_right h

/-- A square pillbox of width s and thickness s² has four sides of area s³
and volume s⁴. After division by the main-face area s², bounded averages
give a residual of order s. -/
theorem norm_pillbox_normalized_residual_le (s M B : ℝ)
    (hs : 0 ≤ s) (hs₁ : s ≤ 1) (hB : 0 ≤ B)
    (side : Fin 4 → Vector 3) (bulk : Vector 3)
    (hSide : ∀ j, ‖side j‖ ≤ M) (hBulk : ‖bulk‖ ≤ B) :
    ‖s • (∑ j, side j) + s ^ 2 • bulk‖ ≤ (4 * M + B) * s := by
  have hSum : ‖∑ j, side j‖ ≤ 4 * M := calc
    _ ≤ ∑ j, ‖side j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 4, M := Finset.sum_le_sum fun j _ => hSide j
    _ = _ := by simp
  have hs₂ : s ^ 2 ≤ s := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hs₁)]
  calc
    _ ≤ ‖s • (∑ j, side j)‖ + ‖s ^ 2 • bulk‖ := norm_add_le _ _
    _ = s * ‖∑ j, side j‖ + s ^ 2 * ‖bulk‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg (sq_nonneg s)]
    _ ≤ s * (4 * M) + s ^ 2 * B :=
      add_le_add (mul_le_mul_of_nonneg_left hSum hs)
        (mul_le_mul_of_nonneg_left hBulk (sq_nonneg s))
    _ ≤ (4 * M + B) * s := by
      rw [add_mul, mul_comm s (4 * M), mul_comm B s]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hs₂ hB)

/-- Action and reaction from the unnormalized rectangular pillbox balance,
with each force written as its geometric weight times its average. -/
theorem traction_neg_of_rectangularPillbox_balance
    (traction : Vector 3 → Vector 3) (normal : Vector 3)
    (positive negative bulk : ℝ → Vector 3) (side : ℝ → Fin 4 → Vector 3)
    (M B : ℝ) (hB : 0 ≤ B)
    (hPositive : Tendsto positive (nhdsWithin 0 (Ioi 0)) (nhds (traction normal)))
    (hNegative : Tendsto negative (nhdsWithin 0 (Ioi 0)) (nhds (traction (-normal))))
    (hSide : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), ∀ j, ‖side s j‖ ≤ M)
    (hBulk : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), ‖bulk s‖ ≤ B)
    (hBalance : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      s ^ 2 • (positive s + negative s) + s ^ 3 • (∑ j, side s j) + s ^ 4 • bulk s = 0) :
    traction (-normal) = -traction normal := by
  apply traction_neg_of_pillbox_balance traction normal positive negative
    (fun s => s • (∑ j, side s j) + s ^ 2 • bulk s) (4 * M + B) hPositive hNegative
  · have hSmall : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), s < 1 :=
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hSmall, hSide, hBulk] with s hs hs₁ hside hbulk
    exact norm_pillbox_normalized_residual_le s M B (show 0 < s from hs).le hs₁.le hB _ _ hside hbulk
  · filter_upwards [self_mem_nhdsWithin, hBalance] with s hs hb
    have hs₀ := (show 0 < s from hs).ne'
    have h₃ : s ^ 2 * s = s ^ 3 := by ring
    have h₄ : s ^ 2 * s ^ 2 = s ^ 4 := by ring
    have h : s ^ 2 • (positive s + negative s +
        (s • (∑ j, side s j) + s ^ 2 • bulk s)) = 0 := by
      simpa only [smul_add, smul_smul, h₃, h₄, add_assoc] using hb
    exact (smul_eq_zero.mp h).resolve_left (pow_ne_zero _ hs₀)

/-- Parameter simplex for a triangular face. -/
def faceParameterTriangle : Set (Vector 2) :=
  {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 0 + u 1 ≤ 1}

/-- The standard closed triangle has area one half. Its vertical sections
are intervals of length 1 − x for x in the unit interval. -/
theorem volume_faceParameterTriangle : volume.real faceParameterTriangle = 1 / 2 := by
  let S : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc 0 (1 - p.1)}
  have hS : MeasurableSet S := (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const) |>.inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_const.sub measurable_fst)))
  have hpre : (MeasurableEquiv.piFinTwo (fun _ => ℝ)) ⁻¹' S = faceParameterTriangle := by
    ext u
    change ((0 ≤ u 0 ∧ u 0 ≤ 1) ∧ (0 ≤ u 1 ∧ u 1 ≤ 1 - u 0)) ↔
      0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 0 + u 1 ≤ 1
    constructor
    · rintro ⟨⟨hx, _⟩, hy, hxy⟩
      exact ⟨hx, hy, by linarith⟩
    · rintro ⟨hx, hy, hxy⟩
      exact ⟨⟨hx, by linarith⟩, hy, by linarith⟩
  have hvol : volume faceParameterTriangle = (volume : Measure (ℝ × ℝ)) S := by
    rw [← hpre]
    exact (volume_preserving_piFinTwo (fun _ => ℝ)).measure_preimage hS.nullMeasurableSet
  have hslice (x : ℝ) : (volume : Measure ℝ) (Prod.mk x ⁻¹' S) =
      (Icc (0 : ℝ) 1).indicator (fun y => ENNReal.ofReal (1 - y)) x := by
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have he : Prod.mk x ⁻¹' S = Icc 0 (1 - x) := by ext y; exact and_iff_right hx
      rw [he, Real.volume_Icc, Set.indicator_of_mem hx, sub_zero]
    · have he : Prod.mk x ⁻¹' S = ∅ := by
        ext y
        change (x ∈ Icc (0 : ℝ) 1 ∧ y ∈ Icc 0 (1 - x)) ↔ y ∈ (∅ : Set ℝ)
        simp only [hx, false_and, mem_empty_iff_false]
      rw [he, measure_empty, Set.indicator_of_notMem hx]
  have hint : IntegrableOn (fun x : ℝ => 1 - x) (Icc (0 : ℝ) 1) :=
    (continuous_const.sub continuous_id).integrableOn_Icc
  have heval : (∫ x in Icc (0 : ℝ) 1, (1 - x)) = 1 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_sub, intervalIntegral.integral_const, integral_id]
    · norm_num
    · exact continuous_const.intervalIntegrable _ _
    · exact continuous_id.intervalIntegrable _ _
  rw [measureReal_def, hvol]
  change ((volume.prod volume) S).toReal = _
  rw [Measure.prod_apply hS, show (fun x => volume (Prod.mk x ⁻¹' S)) = _ from funext hslice,
    lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal hint,
    heval, ENNReal.toReal_ofReal]
  · norm_num
  · exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun _ hx =>
      sub_nonneg.mpr hx.2)

/-- Linear part of the affine chart from the first vertex to the oblique face. -/
noncomputable def obliqueFaceLinear (a b c : ℝ) : Vector 2 →L[ℝ] Vector 3 :=
  (ContinuousLinearMap.proj 0).smulRight (![0, b, 0] - ![a, 0, 0]) +
    (ContinuousLinearMap.proj 1).smulRight (![0, 0, c] - ![a, 0, 0])

/-- The oblique face chart has twice the oriented triangle area as its
constant area density. -/
theorem chartAreaVector_obliqueFace (a b c : ℝ) (u : Vector 2) :
    chartAreaVector (fun v => obliqueFaceLinear a b c v + ![a, 0, 0]) u =
      (2 : ℝ) • tetrahedronObliqueArea a b c := by
  rw [chartAreaVector, ((obliqueFaceLinear a b c).hasFDerivAt.add_const _).fderiv]
  simp [obliqueFaceLinear, ContinuousLinearMap.smulRight_apply, tetrahedronObliqueArea,
    smul_smul]

/-- The scalar area of the oblique chart is the Euclidean length of its
oriented triangle area vector. -/
theorem chartSurfaceIntegral_obliqueFace_one (a b c : ℝ) :
    chartSurfaceIntegral faceParameterTriangle
      (fun u => obliqueFaceLinear a b c u + ![a, 0, 0]) (fun _ => 1) =
      Real.sqrt (tetrahedronObliqueArea a b c ⬝ᵥ tetrahedronObliqueArea a b c) := by
  have hmeasure : (volume.restrict faceParameterTriangle).real univ = 1 / 2 := by
    rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def,
      volume_faceParameterTriangle]
  simp only [chartSurfaceIntegral, one_mul, chartAreaVector_obliqueFace, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, integral_const, hmeasure]
  rw [← mul_assoc (2 : ℝ) 2, Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ) * 2),
    Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The actual oblique chart force is the chart area times the parameter
average of traction. -/
theorem chartSurfaceForce_obliqueFace (a b c : ℝ) (traction : Vector 3 → Vector 3) :
    let r := fun u => obliqueFaceLinear a b c u + ![a, 0, 0]
    chartSurfaceForce faceParameterTriangle r traction =
      chartSurfaceIntegral faceParameterTriangle r (fun _ => 1) •
        ((volume.real faceParameterTriangle)⁻¹ •
          ∫ u in faceParameterTriangle, traction (r u)) :=
  chartSurfaceForce_affine faceParameterTriangle ![a, 0, 0] (obliqueFaceLinear a b c) traction (by
    rw [volume_faceParameterTriangle]
    norm_num)

/-- The coordinate face chart starts at the origin. For positive intercepts,
the order of the other two vertices gives the outward orientation. -/
noncomputable def coordinateFaceLinear (a b c : ℝ) (j : Fin 3) : Vector 2 →L[ℝ] Vector 3 :=
  (ContinuousLinearMap.proj 0).smulRight (![![0, 0, c], ![a, 0, 0], ![0, b, 0]] j) +
    (ContinuousLinearMap.proj 1).smulRight (![![0, b, 0], ![0, 0, c], ![a, 0, 0]] j)

theorem chartAreaVector_coordinateFace (a b c : ℝ) (j : Fin 3) (u : Vector 2) :
    chartAreaVector (coordinateFaceLinear a b c j) u =
      (-2 * tetrahedronObliqueArea a b c j) • Pi.single j 1 := by
  rw [chartAreaVector, (coordinateFaceLinear a b c j).hasFDerivAt.fderiv,
    tetrahedronObliqueArea_components]
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [coordinateFaceLinear, ContinuousLinearMap.smulRight_apply, cross_apply] <;> ring

theorem chartSurfaceIntegral_coordinateFace_one (a b c : ℝ) (j : Fin 3)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    chartSurfaceIntegral faceParameterTriangle (coordinateFaceLinear a b c j) (fun _ => 1) =
      tetrahedronObliqueArea a b c j := by
  have hmeasure : (volume.restrict faceParameterTriangle).real univ = 1 / 2 := by
    rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def,
      volume_faceParameterTriangle]
  have hNonneg : 0 ≤ tetrahedronObliqueArea a b c j := by
    rw [tetrahedronObliqueArea_components]
    fin_cases j <;> simp <;> positivity
  have hunit : (Pi.single j (1 : ℝ)) ⬝ᵥ Pi.single j 1 = 1 := by
    simp [dotProduct, Pi.single_apply]
  simp only [chartSurfaceIntegral, one_mul, chartAreaVector_coordinateFace,
    smul_dotProduct, dotProduct_smul, hunit, smul_eq_mul, mul_one, integral_const, hmeasure]
  rw [Real.sqrt_mul_self_eq_abs, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hNonneg)]
  ring

/-- A coordinate face contributes its projected area times the average of
the traction supplied on that face. -/
theorem chartSurfaceForce_coordinateFace (a b c : ℝ) (j : Fin 3)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (traction : Vector 3 → Vector 3) :
    chartSurfaceForce faceParameterTriangle (coordinateFaceLinear a b c j) traction =
      tetrahedronObliqueArea a b c j •
        ((volume.real faceParameterTriangle)⁻¹ •
          ∫ u in faceParameterTriangle, traction (coordinateFaceLinear a b c j u)) := by
  have h := chartSurfaceForce_affine faceParameterTriangle 0 (coordinateFaceLinear a b c j)
    traction (by rw [volume_faceParameterTriangle]; norm_num)
  simpa only [add_zero, chartSurfaceIntegral_coordinateFace_one a b c j ha hb hc] using h

/-- Average of a traction pulled back from a triangular face. -/
noncomputable def triangularFaceAverage (r : Vector 2 → Vector 3)
    (traction : Vector 3 → Vector 3) : Vector 3 :=
  (volume.real faceParameterTriangle)⁻¹ •
    ∫ u in faceParameterTriangle, traction (r u)

theorem isCompact_faceParameterTriangle : IsCompact faceParameterTriangle := by
  have h₀ : Continuous (fun u : Vector 2 => u 0) := continuous_apply 0
  have h₁ : Continuous (fun u : Vector 2 => u 1) := continuous_apply 1
  refine (isCompact_Icc (α := Vector 2) (a := 0) (b := fun _ => 1)).of_isClosed_subset ?_ ?_
  · have hclosed : IsClosed ({u : Vector 2 | 0 ≤ u 0} ∩
        ({u : Vector 2 | 0 ≤ u 1} ∩ {u : Vector 2 | u 0 + u 1 ≤ 1})) :=
      (isClosed_le continuous_const h₀).inter
        ((isClosed_le continuous_const h₁).inter (isClosed_le (h₀.add h₁) continuous_const))
    exact hclosed
  · intro u hu
    change 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 0 + u 1 ≤ 1 at hu
    exact ⟨fun i => by fin_cases i; exact hu.1; exact hu.2.1,
      fun i => by fin_cases i <;> dsimp <;> linarith [hu.1, hu.2.1, hu.2.2]⟩

set_option maxHeartbeats 400000 in
/-- A continuous traction field on a homothetically shrinking face has
average tending to its value at the collapse point. Compactness supplies
the bound needed by dominated convergence. -/
theorem tendsto_triangularFaceAverage_dilation (r : Vector 2 → Vector 3)
    (hr : Continuous r) (T : Vector 3 → Vector 3) (hT : Continuous T) :
    Tendsto (fun s : ℝ => triangularFaceAverage (fun u => s • r u) T)
      (nhdsWithin 0 (Ioi 0)) (nhds (T 0)) := by
  let μ : Measure (Vector 2) := volume.restrict faceParameterTriangle
  let : IsFiniteMeasure μ := by
    constructor
    rw [show μ univ = volume faceParameterTriangle from Measure.restrict_apply_univ _]
    exact isCompact_faceParameterTriangle.measure_lt_top
  have hnorm : Continuous (fun p : ℝ × Vector 2 => ‖T (p.1 • r p.2)‖) :=
    (hT.comp (continuous_fst.smul (hr.comp continuous_snd))).norm
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    isCompact_faceParameterTriangle).bddAbove_image hnorm.continuousOn
  have hSmall : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), s < 1 :=
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hBound : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), ∀ᵐ u ∂μ, ‖T (s • r u)‖ ≤ M := by
    filter_upwards [self_mem_nhdsWithin, hSmall] with s hs hs₁
    apply (ae_restrict_iff' isCompact_faceParameterTriangle.isClosed.measurableSet).mpr
    exact Eventually.of_forall fun u hu => by
      have hm : (s, u) ∈ Icc (0 : ℝ) 1 ×ˢ faceParameterTriangle :=
        ⟨⟨(show 0 < s from hs).le, hs₁.le⟩, hu⟩
      exact hM (mem_image_of_mem (fun p : ℝ × Vector 2 => ‖T (p.1 • r p.2)‖) hm)
  have hPoint : ∀ᵐ u ∂μ, Tendsto (fun s : ℝ => T (s • r u))
      (nhdsWithin 0 (Ioi 0)) (nhds (T 0)) := by
    apply Eventually.of_forall
    intro u
    have hcont : Continuous (fun s : ℝ => T (s • r u)) :=
      hT.comp (show Continuous (fun s : ℝ => s • r u) from continuous_id.smul continuous_const)
    simpa only [zero_smul] using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hm : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), AEStronglyMeasurable (fun u => T (s • r u)) μ :=
    Eventually.of_forall fun s => (hT.comp (show Continuous (fun u => s • r u) from
      hr.const_smul s)).aestronglyMeasurable
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => M) hm
    hBound (integrable_const M) hPoint
  have hmeasure : μ.real univ = volume.real faceParameterTriangle := by
    simp only [μ, measureReal_def, Measure.restrict_apply_univ]
  have hne : volume.real faceParameterTriangle ≠ 0 := by rw [volume_faceParameterTriangle]; norm_num
  simpa only [triangularFaceAverage, integral_const, hmeasure, smul_smul,
    inv_mul_cancel₀ hne, one_smul] using (tendsto_const_nhds (x := (volume.real faceParameterTriangle)⁻¹)).smul h

theorem obliqueFace_dilation (a b c s : ℝ) (u : Vector 2) :
    obliqueFaceLinear (s * a) (s * b) (s * c) u + ![s * a, 0, 0] =
      s • (obliqueFaceLinear a b c u + ![a, 0, 0]) := by
  funext i
  fin_cases i <;> simp [obliqueFaceLinear, ContinuousLinearMap.smulRight_apply] <;> ring

theorem coordinateFace_dilation (a b c s : ℝ) (j : Fin 3) (u : Vector 2) :
    coordinateFaceLinear (s * a) (s * b) (s * c) j u = s • coordinateFaceLinear a b c j u := by
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [coordinateFaceLinear, ContinuousLinearMap.smulRight_apply] <;> ring

/-- Every strictly positive normal direction is realized by the oblique face
of a positive-intercept tetrahedron. -/
theorem exists_interceptTetrahedron_area (n : Vector 3) (hn : ∀ j, 0 < n j) :
    ∃ a b c A : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < A ∧
      tetrahedronObliqueArea a b c = A • n := by
  refine ⟨(n 0)⁻¹, (n 1)⁻¹, (n 2)⁻¹, (2 * n 0 * n 1 * n 2)⁻¹,
    inv_pos.mpr (hn 0), inv_pos.mpr (hn 1), inv_pos.mpr (hn 2),
    inv_pos.mpr (mul_pos (mul_pos (mul_pos (by norm_num) (hn 0)) (hn 1)) (hn 2)), ?_⟩
  rw [tetrahedronObliqueArea_components]
  funext j
  fin_cases j <;> simp <;> field_simp [(hn 0).ne', (hn 1).ne', (hn 2).ne']

/-- A continuous bulk force is uniformly bounded on the intercept tetrahedra
with scale between zero and one. -/
theorem exists_bound_force_interceptTetrahedron (a b c : ℝ)
    (force : Vector 3 → Vector 3) (hForce : Continuous force) :
    ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ᵐ x ∂volume.restrict (s • interceptTetrahedron a b c), ‖force x‖ ≤ M := by
  have hnorm : Continuous (fun p : ℝ × Vector 3 => ‖force (p.1 • p.2)‖) :=
    (hForce.comp (continuous_fst.smul continuous_snd)).norm
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_interceptTetrahedron a b c)).bddAbove_image hnorm.continuousOn
  refine ⟨M, fun s hs => ?_⟩
  apply (ae_restrict_iff' ((isCompact_interceptTetrahedron a b c).smul s).isClosed.measurableSet).mpr
  exact Eventually.of_forall fun x hx => by
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ interceptTetrahedron a b c, s • y = x := hx
    have hp : (s, y) ∈ Icc (0 : ℝ) 1 ×ˢ interceptTetrahedron a b c := ⟨hs, hy⟩
    exact hM (mem_image_of_mem (fun p : ℝ × Vector 3 => ‖force (p.1 • p.2)‖) hp)

/-- The signed projected face weights give the same stress representation
in any orthant once the signed coordinate-face balance has been established. -/
theorem traction_eq_of_signed_coordinate_balance
    (traction : Vector 3 → Vector 3) (n sign weight : Vector 3)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (hweight : ∀ j, weight j * sign j = n j)
    (hodd : ∀ j, traction (-(Pi.single j 1 : Vector 3)) = -traction (Pi.single j 1))
    (hbalance : traction n = ∑ j, weight j • traction (sign j • Pi.single j 1)) :
    traction n = stressOfTraction traction *ᵥ n := by
  rw [hbalance]
  funext i
  simp only [Matrix.mulVec, dotProduct, stressOfTraction, Matrix.of_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hterm : traction (sign j • Pi.single j 1) = sign j • traction (Pi.single j 1) := by
    rcases hsign j with h | h
    · simp only [h, one_smul]
    · simpa only [h, neg_smul, one_smul] using hodd j
  rw [hterm, Pi.smul_apply, smul_eq_mul, ← mul_assoc, hweight j, mul_comm (n j)]

/-- The four actual face integrals and the bulk integral on the solid
tetrahedron imply the pointwise Cauchy formula at its vertex. Continuity of
traction and bulk force supplies the convergence and boundedness hypotheses
for the shrinking solids. -/
theorem traction_eq_of_interceptTetrahedron_chartBalance
    (a b c A : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 < A)
    (T : Vector 3 → Vector 3 → Vector 3) (normal : Vector 3)
    (hn : normal ⬝ᵥ normal = 1)
    (hArea : tetrahedronObliqueArea a b c = A • normal)
    (hContinuous : ∀ n, Continuous (fun x => T x n))
    (hOpposite : ∀ x j, T x (-(Pi.single j 1 : Vector 3)) = -T x (Pi.single j 1))
    (force : Vector 3 → Vector 3) (hForce : Continuous force) :
    let oblique (s : ℝ) (u : Vector 2) :=
      obliqueFaceLinear (s * a) (s * b) (s * c) u + ![s * a, 0, 0]
    let coordinate (s : ℝ) (j : Fin 3) := coordinateFaceLinear (s * a) (s * b) (s * c) j
    (∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      chartSurfaceForce faceParameterTriangle (oblique s) (fun x => T x normal) +
      (∑ j, chartSurfaceForce faceParameterTriangle (coordinate s j)
        (fun x => T x (-(Pi.single j 1 : Vector 3)))) +
      (∫ x in s • interceptTetrahedron a b c, force x) = 0) →
    T 0 normal = stressOfTraction (T 0) *ᵥ normal := by
  intro oblique coordinate hBalance
  obtain ⟨M, hM⟩ := exists_bound_force_interceptTetrahedron a b c force hForce
  have hBound : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ᵐ x ∂volume.restrict (s • interceptTetrahedron a b c), ‖force x‖ ≤ M := by
    have hSmall : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), s < 1 :=
      (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hSmall] with s hs hs₁
    exact hM s ⟨(show 0 < s from hs).le, hs₁.le⟩
  have hOblique : Tendsto (fun s => triangularFaceAverage (oblique s) (fun x => T x normal))
      (nhdsWithin 0 (Ioi 0)) (nhds (T 0 normal)) := by
    simpa only [oblique, obliqueFace_dilation] using
      tendsto_triangularFaceAverage_dilation (fun u => obliqueFaceLinear a b c u + ![a, 0, 0])
        ((obliqueFaceLinear a b c).continuous.add continuous_const) _ (hContinuous normal)
  have hCoordinate (j : Fin 3) :
      Tendsto (fun s => triangularFaceAverage (coordinate s j) (fun x => T x (Pi.single j 1)))
        (nhdsWithin 0 (Ioi 0)) (nhds (T 0 (Pi.single j 1))) := by
    have he (s : ℝ) : (coordinate s j : Vector 2 → Vector 3) =
        fun u => s • coordinateFaceLinear a b c j u :=
      funext (coordinateFace_dilation a b c s j)
    simpa only [he] using
      tendsto_triangularFaceAverage_dilation (coordinateFaceLinear a b c j)
        (coordinateFaceLinear a b c j).continuous _ (hContinuous (Pi.single j 1))
  apply traction_eq_of_interceptTetrahedron_balance a b c A M hA (T 0) normal
    (fun s => triangularFaceAverage (oblique s) (fun x => T x normal))
    (fun j s => triangularFaceAverage (coordinate s j) (fun x => T x (Pi.single j 1)))
    force hArea hOblique hCoordinate hBound
  filter_upwards [self_mem_nhdsWithin, hBalance] with s hs h
  have hs' : 0 ≤ s := (show 0 < s from hs).le
  have hOb : chartSurfaceForce faceParameterTriangle (oblique s) (fun x => T x normal) =
      (A * s ^ 2) • triangularFaceAverage (oblique s) (fun x => T x normal) := by
    dsimp only [oblique, triangularFaceAverage]
    rw [chartSurfaceForce_obliqueFace, chartSurfaceIntegral_obliqueFace_one,
      tetrahedronObliqueArea_scale, hArea]
    simp only [smul_smul, smul_dotProduct, dotProduct_smul, hn, smul_eq_mul, mul_one]
    rw [Real.sqrt_mul_self (mul_nonneg (sq_nonneg s) hA.le), mul_comm (s ^ 2) A]
  have hCo (j : Fin 3) :
      chartSurfaceForce faceParameterTriangle (coordinate s j)
          (fun x => T x (-(Pi.single j 1 : Vector 3))) =
        tetrahedronObliqueArea (s * a) (s * b) (s * c) j •
          (-triangularFaceAverage (coordinate s j) (fun x => T x (Pi.single j 1))) := by
    dsimp only [coordinate, triangularFaceAverage]
    rw [chartSurfaceForce_coordinateFace _ _ _ j (mul_nonneg hs' ha) (mul_nonneg hs' hb)
      (mul_nonneg hs' hc)]
    simp only [hOpposite, integral_neg, smul_neg]
  simpa only [hOb, hCo] using h

/-- Coordinate reflection taking a reference tetrahedron to a signed orthant. -/
noncomputable def coordinateReflection (sign : Vector 3) : Vector 3 →L[ℝ] Vector 3 :=
  ContinuousLinearMap.pi fun j => sign j • ContinuousLinearMap.proj j

@[simp] theorem coordinateReflection_apply (sign x : Vector 3) (j : Fin 3) :
    coordinateReflection sign x j = sign j * x j := by
  simp [coordinateReflection, smul_eq_mul]

theorem coordinateReflection_dot (sign x y : Vector 3)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1) :
    coordinateReflection sign x ⬝ᵥ coordinateReflection sign y = x ⬝ᵥ y := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hsign j with h | h <;> simp [h]

theorem coordinateReflection_involutive (sign : Vector 3)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1) :
    Function.Involutive (coordinateReflection sign) := by
  intro x
  funext j
  rcases hsign j with h | h <;> simp [h]

/-- The bulk force on a reflected solid can be integrated in the original
solid with the force field composed with the reflection. -/
theorem integral_coordinateReflection_image (sign : Vector 3)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1) (S : Set (Vector 3))
    (force : Vector 3 → Vector 3) :
    (∫ x in coordinateReflection sign '' S, force x) =
      ∫ x in S, force (coordinateReflection sign x) := by
  have hinv := coordinateReflection_involutive sign hsign
  let e : Vector 3 ≃ᵐ Vector 3 :=
    { toFun := coordinateReflection sign
      invFun := coordinateReflection sign
      left_inv := hinv
      right_inv := hinv
      measurable_toFun := (coordinateReflection sign).continuous.measurable
      measurable_invFun := (coordinateReflection sign).continuous.measurable }
  have hpi : MeasurePreserving (fun (x : Vector 3) j => sign j * x j) := by
    apply volume_preserving_pi
    intro j
    rcases hsign j with h | h
    · rw [h]
      convert MeasurePreserving.id (volume : Measure ℝ) using 1
      funext x
      exact one_mul x
    · rw [h]
      refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
      change Measure.map ((-1 : ℝ) • ·) volume = volume
      rw [Measure.map_addHaar_smul volume (show (-1 : ℝ) ≠ 0 by norm_num)]
      simp
  have he : MeasurePreserving e := by
    have hfun : (e : Vector 3 → Vector 3) = (fun x j => sign j * x j) :=
      funext fun x => funext fun j => coordinateReflection_apply sign x j
    rw [hfun]
    exact hpi
  exact he.setIntegral_image_emb e.measurableEmbedding force S

/-- A normal with nonzero components is the reflected oblique area direction
of a positive-intercept tetrahedron. -/
theorem exists_reflected_interceptTetrahedron_area (n : Vector 3)
    (hn : ∀ j, n j ≠ 0) :
    ∃ (sign : Vector 3) (a b c A : ℝ), (∀ j, sign j = 1 ∨ sign j = -1) ∧
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < A ∧
      coordinateReflection sign (tetrahedronObliqueArea a b c) = A • n := by
  let sign (j : Fin 3) : ℝ := if 0 ≤ n j then 1 else -1
  have hsign (j : Fin 3) : sign j = 1 ∨ sign j = -1 := by
    by_cases h : 0 ≤ n j <;> simp [sign, h]
  obtain ⟨a, b, c, A, ha, hb, hc, hA, harea⟩ :=
    exists_interceptTetrahedron_area (fun j => |n j|) (fun j => abs_pos.mpr (hn j))
  refine ⟨sign, a, b, c, A, hsign, ha, hb, hc, hA, ?_⟩
  rw [harea]
  funext j
  simp only [coordinateReflection_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : 0 ≤ n j
  · simp [sign, h, abs_of_nonneg h]
  · simp [sign, h, abs_of_neg (lt_of_not_ge h)]

/-- Reflection changes the cross-product orientation by the determinant sign. -/
theorem coordinateReflection_cross (sign x y : Vector 3)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1) :
    coordinateReflection sign x ⨯₃ coordinateReflection sign y =
      (sign 0 * sign 1 * sign 2) • coordinateReflection sign (x ⨯₃ y) := by
  have hsquare (j : Fin 3) : sign j * sign j = 1 := by
    rcases hsign j with h | h <;> simp [h]
  funext j
  calc
    _ = ![sign 1 * sign 2, sign 2 * sign 0, sign 0 * sign 1] j * (x ⨯₃ y) j := by
      fin_cases j <;> simp [cross_apply] <;> ring
    _ = _ := by
      have hcoef : ![sign 1 * sign 2, sign 2 * sign 0, sign 0 * sign 1] j =
          (sign 0 * sign 1 * sign 2) * sign j := by
        fin_cases j <;> simp <;>
          first
          | linear_combination -(sign 1 * sign 2) * hsquare 0
          | linear_combination -(sign 0 * sign 2) * hsquare 1
          | linear_combination -(sign 0 * sign 1) * hsquare 2
      rw [hcoef]
      simp only [Pi.smul_apply, coordinateReflection_apply, smul_eq_mul, mul_assoc]

/-- Coordinate-reflected charts preserve scalar area and pull traction back
by composition with the reflection. -/
theorem chartSurfaceForce_coordinateReflection (D : Set (Vector 2))
    (sign : Vector 3) (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (r : Vector 2 → Vector 3) (hr : Differentiable ℝ r) (traction : Vector 3 → Vector 3) :
    chartSurfaceForce D (coordinateReflection sign ∘ r) traction =
      chartSurfaceForce D r (traction ∘ coordinateReflection sign) := by
  have hd (u : Vector 2) : chartAreaVector (coordinateReflection sign ∘ r) u =
      (sign 0 * sign 1 * sign 2) • coordinateReflection sign (chartAreaVector r u) := by
    unfold chartAreaVector
    rw [((coordinateReflection sign).hasFDerivAt.comp u (hr u).hasFDerivAt).fderiv]
    exact coordinateReflection_cross _ _ _ hsign
  have hsquare (j : Fin 3) : sign j * sign j = 1 := by
    rcases hsign j with h | h <;> simp [h]
  have hdet : (sign 0 * sign 1 * sign 2) * (sign 0 * sign 1 * sign 2) = 1 := by
    calc
      _ = (sign 0 * sign 0) * (sign 1 * sign 1) * (sign 2 * sign 2) := by ring
      _ = _ := by simp only [hsquare, mul_one]
  unfold chartSurfaceForce
  congr 1
  funext u
  simp only [hd, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← mul_assoc, hdet,
    one_mul, coordinateReflection_dot _ _ _ hsign, Function.comp_apply]

/-- Force balance on the reflected face charts and reflected solid gives the
Cauchy traction formula in the corresponding signed orthant. -/
theorem traction_eq_of_reflectedTetrahedron_chartBalance
    (a b c A : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 < A)
    (T : Vector 3 → Vector 3 → Vector 3) (n sign : Vector 3)
    (hn : n ⬝ᵥ n = 1) (hArea : tetrahedronObliqueArea a b c = A • n)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (hContinuous : ∀ m, Continuous (fun x => T x m))
    (hOdd : ∀ x m, m ⬝ᵥ m = 1 → T x (-m) = -T x m)
    (force : Vector 3 → Vector 3) (hForce : Continuous force) :
    let R := coordinateReflection sign
    let oblique (s : ℝ) (u : Vector 2) :=
      obliqueFaceLinear (s * a) (s * b) (s * c) u + ![s * a, 0, 0]
    let coordinate (s : ℝ) (j : Fin 3) := coordinateFaceLinear (s * a) (s * b) (s * c) j
    (∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      chartSurfaceForce faceParameterTriangle (R ∘ oblique s) (fun x => T x (R n)) +
      (∑ j, chartSurfaceForce faceParameterTriangle (R ∘ coordinate s j)
        (fun x => T x (R (-(Pi.single j 1 : Vector 3))))) +
      (∫ x in R '' (s • interceptTetrahedron a b c), force x) = 0) →
    T 0 (R n) = stressOfTraction (T 0) *ᵥ R n := by
  intro R oblique coordinate hBalance
  let T' (x m : Vector 3) := T (R x) (R m)
  have hunit (j : Fin 3) : (Pi.single j (1 : ℝ)) ⬝ᵥ Pi.single j 1 = 1 := by
    simp
  have hunitR (j : Fin 3) : R (Pi.single j 1) ⬝ᵥ R (Pi.single j 1) = 1 :=
    (coordinateReflection_dot sign _ _ hsign).trans (hunit j)
  have h := traction_eq_of_interceptTetrahedron_chartBalance a b c A ha hb hc hA T' n
    hn hArea (fun m => (hContinuous (R m)).comp R.continuous)
    (fun x j => by simpa only [T', map_neg] using hOdd (R x) (R (Pi.single j 1)) (hunitR j))
    (force ∘ R) (hForce.comp R.continuous)
  have hEq : T' 0 n = stressOfTraction (T' 0) *ᵥ n := by
    apply h
    filter_upwards [hBalance] with s hs
    have hob : Differentiable ℝ (oblique s) :=
      (obliqueFaceLinear (s * a) (s * b) (s * c)).differentiable.add_const _
    have hco (j : Fin 3) : Differentiable ℝ (coordinate s j) := (coordinate s j).differentiable
    have hOb : chartSurfaceForce faceParameterTriangle (R ∘ oblique s) (fun x => T x (R n)) =
        chartSurfaceForce faceParameterTriangle (oblique s) (fun x => T' x n) :=
      chartSurfaceForce_coordinateReflection _ sign hsign _ hob _
    have hCo (j : Fin 3) :
        chartSurfaceForce faceParameterTriangle (R ∘ coordinate s j)
          (fun x => T x (R (-(Pi.single j 1 : Vector 3)))) =
        chartSurfaceForce faceParameterTriangle (coordinate s j)
          (fun x => T' x (-(Pi.single j 1 : Vector 3))) :=
      chartSurfaceForce_coordinateReflection _ sign hsign _ (hco j) _
    have hBulk : (∫ x in R '' (s • interceptTetrahedron a b c), force x) =
        ∫ x in s • interceptTetrahedron a b c, (force ∘ R) x :=
      integral_coordinateReflection_image sign hsign _ _
    simpa only [hOb, hCo, hBulk] using hs
  have hBasis (j : Fin 3) : R (Pi.single j 1) = sign j • (Pi.single j 1 : Vector 3) := by
    funext i
    by_cases hi : i = j
    · subst i
      simp [R, smul_eq_mul]
    · simp [R, Pi.single_eq_of_ne hi, smul_eq_mul]
  have hTraction (j : Fin 3) : T 0 (R (Pi.single j 1)) = sign j • T 0 (Pi.single j 1) := by
    rw [hBasis j]
    rcases hsign j with hs | hs
    · simp [hs]
    · simpa only [hs, neg_smul, one_smul] using hOdd 0 (Pi.single j 1) (hunit j)
  calc
    T 0 (R n) = T' 0 n := by simp [T']
    _ = stressOfTraction (T' 0) *ᵥ n := hEq
    _ = stressOfTraction (T 0) *ᵥ R n := by
      funext i
      simp only [Matrix.mulVec, dotProduct, stressOfTraction, Matrix.of_apply, T', map_zero,
        hTraction, Pi.smul_apply, smul_eq_mul, R, coordinateReflection_apply]
      exact Finset.sum_congr rfl fun j _ => by ring

/-- Continuity of the traction in its normal extends any established stress
representation to the closure of the directions for which it was proved. -/
theorem traction_eq_on_closure (traction : Vector 3 → Vector 3) (S : Set (Vector 3))
    (hContinuous : Continuous traction)
    (hS : ∀ n ∈ S, traction n = stressOfTraction traction *ᵥ n)
    {n : Vector 3} (hn : n ∈ closure S) :
    traction n = stressOfTraction traction *ᵥ n := by
  have hc : Continuous (fun n : Vector 3 => stressOfTraction traction *ᵥ n) := by
    apply continuous_pi
    intro i
    change Continuous (fun n : Vector 3 => ∑ j, stressOfTraction traction i j * n j)
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  exact closure_minimal (t := {n | traction n = stressOfTraction traction *ᵥ n})
    (fun x hx => hS x hx) (isClosed_eq hContinuous hc) hn

/-- Directions with nonzero coordinates are dense on the Euclidean unit
sphere. Normalize the dense set of vectors with no zero coordinates. -/
theorem unitNormal_mem_closure_nonzeroCoordinates (n : Vector 3) (hn : n ⬝ᵥ n = 1) :
    n ∈ closure {x : Vector 3 | x ⬝ᵥ x = 1 ∧ ∀ i, x i ≠ 0} := by
  let S : Set (Vector 3) := Set.pi univ (fun _ => ({0}ᶜ : Set ℝ))
  let N (x : Vector 3) := (Real.sqrt (x ⬝ᵥ x))⁻¹ • x
  have hd : Dense S := dense_pi _ fun _ _ => dense_compl_singleton 0
  have hdot : Continuous (fun x : Vector 3 => x ⬝ᵥ x) := by
    unfold dotProduct
    exact continuous_finsetSum _ fun j _ => (continuous_apply j).mul (continuous_apply j)
  have hroot : Continuous (fun x : Vector 3 => Real.sqrt (x ⬝ᵥ x)) :=
    Real.continuous_sqrt.comp hdot
  have hN : ContinuousAt N n :=
    (hroot.continuousAt.inv₀ (by simp [hn])).smul continuousAt_id
  have hfix : N n = n := by simp [N, hn]
  have himg : N '' S ⊆ {x : Vector 3 | x ⬝ᵥ x = 1 ∧ ∀ i, x i ≠ 0} := by
    rintro _ ⟨x, hx, rfl⟩
    have hx₀ (i : Fin 3) : x i ≠ 0 := by simpa using hx i (mem_univ i)
    have hxne : x ≠ 0 := fun h => hx₀ 0 (congrFun h 0)
    have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
      (Ne.symm fun h => hxne (dotProduct_self_eq_zero.mp h))
    have hr := Real.sqrt_pos.2 hpos
    refine ⟨?_, fun i => mul_ne_zero (inv_ne_zero hr.ne') (hx₀ i)⟩
    simp only [N, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp [hr.ne']
    nlinarith only [Real.sq_sqrt hpos.le]
  rw [← hfix]
  exact closure_mono himg (mem_closure_image hN (hd n))

/-- A continuous traction law represented by the stress tensor on directions
with three nonzero coordinates has the same representation on all unit normals. -/
theorem traction_eq_all_unitNormals (traction : Vector 3 → Vector 3)
    (hContinuous : Continuous traction)
    (hOpen : ∀ n : Vector 3, n ⬝ᵥ n = 1 → (∀ i, n i ≠ 0) →
      traction n = stressOfTraction traction *ᵥ n)
    (n : Vector 3) (hn : n ⬝ᵥ n = 1) :
    traction n = stressOfTraction traction *ᵥ n :=
  traction_eq_on_closure traction {x | x ⬝ᵥ x = 1 ∧ ∀ i, x i ≠ 0}
    hContinuous (fun x hx => hOpen x hx.1 hx.2) (unitNormal_mem_closure_nonzeroCoordinates n hn)

end LeanSolid.ContinuumMechanics
