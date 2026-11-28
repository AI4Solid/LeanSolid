module

public import LeanSolid.ContinuumMechanics.Tetrahedron
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

public section

open Filter MeasureTheory Set LeanSolid.Math
open scoped Matrix Pointwise

namespace LeanSolid.ContinuumMechanics

/-- A square pillbox with edge lengths s, s, and s². -/
def pillboxRegion (s : ℝ) : Set (Vector 3) := Icc 0 ![s, s, s ^ 2]

theorem volume_pillboxRegion (s : ℝ) (hs : 0 ≤ s) :
    volume.real (pillboxRegion s) = s ^ 4 := by
  have h : (0 : Vector 3) ≤ ![s, s, s ^ 2] := by
    intro i
    fin_cases i <;> simp [hs]
  rw [pillboxRegion, measureReal_def, Real.volume_Icc_pi_toReal h]
  simp [Fin.prod_univ_succ]
  ring

def pillboxFaceParameters : Set (Vector 2) := Icc 0 (fun _ => 1)

theorem volume_pillboxFaceParameters : volume.real pillboxFaceParameters = 1 := by
  rw [pillboxFaceParameters, measureReal_def,
    Real.volume_Icc_pi_toReal (a := (0 : Vector 2)) (b := fun _ => 1) (fun _ => zero_le_one)]
  simp

/-- Columns of the rectangular chart use the two cyclic coordinate axes
tangent to the chosen face. -/
noncomputable def pillboxFaceLinear (s : ℝ) (j : Fin 3) : Vector 2 →L[ℝ] Vector 3 :=
  (ContinuousLinearMap.proj 0).smulRight (![![0, s, 0], ![0, 0, s ^ 2], ![s, 0, 0]] j) +
    (ContinuousLinearMap.proj 1).smulRight (![![0, 0, s ^ 2], ![s, 0, 0], ![0, s, 0]] j)

noncomputable def pillboxFaceChart (s : ℝ) (j : Fin 3) (upper : Bool)
    (u : Vector 2) : Vector 3 :=
  pillboxFaceLinear s j u + if upper then (![s, s, s ^ 2] j) • Pi.single j 1 else 0

/-- The four lateral faces have area s³ and the two main faces area s². -/
def pillboxFaceArea (s : ℝ) (j : Fin 3) : ℝ := ![s ^ 3, s ^ 3, s ^ 2] j

theorem chartAreaVector_pillboxFace (s : ℝ) (j : Fin 3) (upper : Bool) (u : Vector 2) :
    chartAreaVector (pillboxFaceChart s j upper) u = pillboxFaceArea s j • Pi.single j 1 := by
  unfold pillboxFaceChart
  rw [chartAreaVector, ((pillboxFaceLinear s j).hasFDerivAt.add_const _).fderiv]
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [pillboxFaceArea, pillboxFaceLinear, ContinuousLinearMap.smulRight_apply, cross_apply] <;> ring

theorem chartSurfaceForce_pillboxFace (s : ℝ) (hs : 0 ≤ s) (j : Fin 3) (upper : Bool)
    (traction : Vector 3 → Vector 3) :
    chartSurfaceForce pillboxFaceParameters (pillboxFaceChart s j upper) traction =
      pillboxFaceArea s j • ∫ u in pillboxFaceParameters, traction (pillboxFaceChart s j upper u) := by
  have hArea : 0 ≤ pillboxFaceArea s j := by
    fin_cases j <;> simp [pillboxFaceArea, pow_nonneg hs]
  have hunit : (Pi.single j (1 : ℝ)) ⬝ᵥ Pi.single j 1 = 1 := by
    simp [dotProduct, Pi.single_apply]
  simp only [chartSurfaceForce, chartAreaVector_pillboxFace, smul_dotProduct, dotProduct_smul,
    hunit, smul_eq_mul, mul_one, Real.sqrt_mul_self hArea, integral_smul]

/-- The bulk integral equals the volume times its spatial average. -/
theorem integral_pillbox_eq_volume_smul_average (s : ℝ) (hs : 0 < s)
    (force : Vector 3 → Vector 3) :
    (∫ x in pillboxRegion s, force x) =
      s ^ 4 • ((volume.real (pillboxRegion s))⁻¹ • ∫ x in pillboxRegion s, force x) := by
  rw [volume_pillboxRegion s hs.le, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hs.ne'), one_smul]

/-- The outward normal supplied to the traction field on a coordinate face. -/
def pillboxFaceNormal (j : Fin 3) (upper : Bool) : Vector 3 :=
  if upper then Pi.single j 1 else -Pi.single j 1

/-- The true face average, since the parameter square has unit area. -/
noncomputable def pillboxFaceAverage (T : Vector 3 → Vector 3 → Vector 3)
    (s : ℝ) (j : Fin 3) (upper : Bool) : Vector 3 :=
  ∫ u in pillboxFaceParameters, T (pillboxFaceChart s j upper u) (pillboxFaceNormal j upper)

noncomputable def pillboxSideAverages (T : Vector 3 → Vector 3 → Vector 3)
    (s : ℝ) : Fin 4 → Vector 3 :=
  ![pillboxFaceAverage T s 0 false, pillboxFaceAverage T s 0 true,
    pillboxFaceAverage T s 1 false, pillboxFaceAverage T s 1 true]

noncomputable def pillboxBulkAverage (force : Vector 3 → Vector 3) (s : ℝ) : Vector 3 :=
  (volume.real (pillboxRegion s))⁻¹ • ∫ x in pillboxRegion s, force x

theorem continuous_pillboxFaceChart (j : Fin 3) (upper : Bool) :
    Continuous (fun p : ℝ × Vector 2 => pillboxFaceChart p.1 j upper p.2) := by
  apply continuous_pi
  intro i
  fin_cases j <;> fin_cases i <;> cases upper <;>
    simp [pillboxFaceChart, pillboxFaceLinear, ContinuousLinearMap.smulRight_apply,
      smul_eq_mul] <;> fun_prop

theorem pillboxFaceChart_zero (j : Fin 3) (upper : Bool) (u : Vector 2) :
    pillboxFaceChart 0 j upper u = 0 := by
  funext i
  fin_cases j <;> fin_cases i <;> cases upper <;>
    simp [pillboxFaceChart, pillboxFaceLinear, ContinuousLinearMap.smulRight_apply]

set_option maxHeartbeats 400000 in
/-- Continuous traction gives the face averages used in the actual force
balance, on all six faces of the anisotropically shrinking pillbox. -/
theorem tendsto_pillboxFaceAverage
    (T : Vector 3 → Vector 3 → Vector 3) (j : Fin 3) (upper : Bool)
    (hT : Continuous (fun x => T x (pillboxFaceNormal j upper))) :
    Tendsto (fun s => pillboxFaceAverage T s j upper) (nhdsWithin 0 (Ioi 0))
      (nhds (T 0 (pillboxFaceNormal j upper))) := by
  let μ : Measure (Vector 2) := volume.restrict pillboxFaceParameters
  have hcompact : IsCompact pillboxFaceParameters := isCompact_Icc
  let : IsFiniteMeasure μ := ⟨by
    rw [show μ univ = volume pillboxFaceParameters from Measure.restrict_apply_univ _]
    exact hcompact.measure_lt_top⟩
  let f (p : ℝ × Vector 2) := T (pillboxFaceChart p.1 j upper p.2) (pillboxFaceNormal j upper)
  have hf : Continuous f := hT.comp (continuous_pillboxFaceChart j upper)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod hcompact)
    |>.bddAbove_image hf.norm.continuousOn
  have hSmall : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), s < 1 :=
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hb : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), ∀ᵐ u ∂μ, ‖f (s, u)‖ ≤ M := by
    filter_upwards [self_mem_nhdsWithin, hSmall] with s hs hsmall
    apply (ae_restrict_iff' hcompact.isClosed.measurableSet).mpr
    exact Eventually.of_forall fun u hu => by
      have hp : (s, u) ∈ Icc (0 : ℝ) 1 ×ˢ pillboxFaceParameters :=
        ⟨⟨(show 0 < s from hs).le, hsmall.le⟩, hu⟩
      exact hM (mem_image_of_mem (fun p => ‖f p‖) hp)
  have hm : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), AEStronglyMeasurable (fun u => f (s, u)) μ :=
    Eventually.of_forall fun _ => (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hp : ∀ᵐ u ∂μ, Tendsto (fun s : ℝ => f (s, u)) (nhdsWithin 0 (Ioi 0))
      (nhds (T 0 (pillboxFaceNormal j upper))) := by
    apply Eventually.of_forall
    intro u
    have h := (hf.comp (continuous_id.prodMk (continuous_const (y := u)))).continuousAt
      (x := (0 : ℝ))
    have he : f (0, u) = T 0 (pillboxFaceNormal j upper) := by
      simp only [f, pillboxFaceChart_zero]
    change ContinuousAt (fun s : ℝ => f (s, u)) 0 at h
    rw [← he]
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => M) hm hb
    (integrable_const M) hp
  have hmeasure : μ.real univ = 1 := by
    rw [measureReal_def, show μ univ = volume pillboxFaceParameters from Measure.restrict_apply_univ _,
      ← measureReal_def, volume_pillboxFaceParameters]
  simpa only [integral_const, hmeasure, one_smul, f, μ, pillboxFaceAverage] using h

/-- Continuity bounds the average bulk force uniformly on small pillboxes. -/
theorem exists_bound_pillboxBulkAverage (force : Vector 3 → Vector 3)
    (hForce : Continuous force) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), ‖pillboxBulkAverage force s‖ ≤ B := by
  let K : Set (Vector 3) := Icc 0 (fun _ => 1)
  have hK : IsCompact K := isCompact_Icc
  obtain ⟨M, hM⟩ := hK.bddAbove_image hForce.norm.continuousOn
  let B := max 0 M
  refine ⟨B, le_max_left _ _, ?_⟩
  have hSmall : ∀ᶠ s : ℝ in nhdsWithin 0 (Ioi 0), s < 1 :=
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hSmall] with s hs hs₁
  have hs' : 0 < s := hs
  have hIncl : pillboxRegion s ⊆ K := by
    intro x hx
    refine ⟨hx.1, fun i => (hx.2 i).trans ?_⟩
    have hsq : s ^ 2 ≤ 1 := by nlinarith [mul_nonneg hs'.le (sub_nonneg.mpr hs₁.le)]
    fin_cases i <;> simp [hs₁.le, hsq]
  let μ : Measure (Vector 3) := volume.restrict (pillboxRegion s)
  let : IsFiniteMeasure μ := ⟨by
    rw [show μ univ = volume (pillboxRegion s) from Measure.restrict_apply_univ _]
    exact (isCompact_Icc (a := (0 : Vector 3)) (b := ![s, s, s ^ 2])).measure_lt_top⟩
  have hbound : ∀ᵐ x ∂μ, ‖force x‖ ≤ B := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    exact Eventually.of_forall fun x hx =>
      (hM (mem_image_of_mem (fun x => ‖force x‖) (hIncl hx))).trans (le_max_right _ _)
  have hmeasure : μ.real univ = s ^ 4 := by
    rw [measureReal_def, show μ univ = volume (pillboxRegion s) from Measure.restrict_apply_univ _,
      ← measureReal_def, volume_pillboxRegion s hs'.le]
  have hnorm := norm_integral_le_of_norm_le_const hbound
  rw [hmeasure] at hnorm
  have hp : 0 < s ^ 4 := pow_pos hs' _
  rw [pillboxBulkAverage, volume_pillboxRegion s hs'.le, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (s ^ 4)⁻¹ * (B * s ^ 4) := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hp.le)
    _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

def pillboxForceBalance (T : Vector 3 → Vector 3 → Vector 3)
    (force : Vector 3 → Vector 3) (s : ℝ) : Prop :=
  (∑ j, (chartSurfaceForce pillboxFaceParameters (pillboxFaceChart s j false)
      (fun x => T x (pillboxFaceNormal j false)) +
    chartSurfaceForce pillboxFaceParameters (pillboxFaceChart s j true)
      (fun x => T x (pillboxFaceNormal j true)))) +
  (∫ x in pillboxRegion s, force x) = 0

/-- The force balance for the six actual face integrals and the actual bulk
integral implies action and reaction on the two main faces. -/
theorem traction_neg_of_pillbox_chartBalance
    (T : Vector 3 → Vector 3 → Vector 3) (force : Vector 3 → Vector 3)
    (M B : ℝ) (hB : 0 ≤ B)
    (hPositive : Tendsto (fun s => pillboxFaceAverage T s 2 true)
      (nhdsWithin 0 (Ioi 0)) (nhds (T 0 (Pi.single 2 1))))
    (hNegative : Tendsto (fun s => pillboxFaceAverage T s 2 false)
      (nhdsWithin 0 (Ioi 0)) (nhds (T 0 (-(Pi.single 2 1 : Vector 3)))))
    (hSide : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), ∀ j, ‖pillboxSideAverages T s j‖ ≤ M)
    (hBulk : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), ‖pillboxBulkAverage force s‖ ≤ B)
    (hBalance : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), pillboxForceBalance T force s) :
    T 0 (-(Pi.single 2 1 : Vector 3)) = -T 0 (Pi.single 2 1) := by
  apply traction_neg_of_rectangularPillbox_balance (T 0) (Pi.single 2 1)
    (fun s => pillboxFaceAverage T s 2 true) (fun s => pillboxFaceAverage T s 2 false)
    (pillboxBulkAverage force) (pillboxSideAverages T) M B hB hPositive hNegative hSide hBulk
  filter_upwards [hBalance, self_mem_nhdsWithin] with s h hs
  have hs' : 0 < s := hs
  have hface (j : Fin 3) (upper : Bool) :
      chartSurfaceForce pillboxFaceParameters (pillboxFaceChart s j upper)
        (fun x => T x (pillboxFaceNormal j upper)) =
      pillboxFaceArea s j • pillboxFaceAverage T s j upper :=
    chartSurfaceForce_pillboxFace s hs'.le j upper _
  have hForce : (∫ x in pillboxRegion s, force x) = s ^ 4 • pillboxBulkAverage force s :=
    integral_pillbox_eq_volume_smul_average s hs' force
  have hBoundary :
      (∑ j, (pillboxFaceArea s j • pillboxFaceAverage T s j false +
        pillboxFaceArea s j • pillboxFaceAverage T s j true)) =
      s ^ 2 • (pillboxFaceAverage T s 2 true + pillboxFaceAverage T s 2 false) +
      s ^ 3 • ∑ j, pillboxSideAverages T s j := by
    simp [Fin.sum_univ_succ, pillboxFaceArea, pillboxSideAverages, smul_add]
    abel
  simpa only [pillboxForceBalance, hface, hForce, hBoundary] using h

/-- Continuity supplies all face-average limits and bounds needed to deduce
opposite tractions from the coordinate pillbox force balances. -/
theorem traction_neg_of_continuous_pillboxBalance
    (T : Vector 3 → Vector 3 → Vector 3) (force : Vector 3 → Vector 3)
    (hT : ∀ n, Continuous (fun x => T x n)) (hForce : Continuous force)
    (hBalance : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), pillboxForceBalance T force s) :
    T 0 (-(Pi.single 2 1 : Vector 3)) = -T 0 (Pi.single 2 1) := by
  have hLimit (j : Fin 3) (upper : Bool) :=
    tendsto_pillboxFaceAverage T j upper (hT (pillboxFaceNormal j upper))
  let total := ∑ p : Fin 3 × Bool, ‖T 0 (pillboxFaceNormal p.1 p.2)‖
  let M := total + 1
  have hAll : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ p : Fin 3 × Bool, ‖pillboxFaceAverage T s p.1 p.2‖ < M := by
    apply eventually_all.mpr
    intro p
    have hle : ‖T 0 (pillboxFaceNormal p.1 p.2)‖ ≤ total :=
      Finset.single_le_sum (f := fun q : Fin 3 × Bool => ‖T 0 (pillboxFaceNormal q.1 q.2)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p)
    exact (hLimit p.1 p.2).norm.eventually (gt_mem_nhds (lt_of_le_of_lt hle (lt_add_one total)))
  have hSide : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), ∀ j, ‖pillboxSideAverages T s j‖ ≤ M := by
    filter_upwards [hAll] with s hs
    intro j
    fin_cases j
    · exact (hs (0, false)).le
    · exact (hs (0, true)).le
    · exact (hs (1, false)).le
    · exact (hs (1, true)).le
  obtain ⟨B, hB, hBulk⟩ := exists_bound_pillboxBulkAverage force hForce
  exact traction_neg_of_pillbox_chartBalance T force M B hB
    (hLimit 2 true) (hLimit 2 false) hSide hBulk hBalance

/-- A Cartesian matrix acting as a continuous linear map on chart coordinates. -/
noncomputable def cartesianMatrixMap (Q : Tensor 3) : Vector 3 →L[ℝ] Vector 3 :=
  Q.toLin'.toContinuousLinearMap

theorem cartesianMatrixMap_apply (Q : Tensor 3) (x : Vector 3) :
    cartesianMatrixMap Q x = Q *ᵥ x := by
  simp [cartesianMatrixMap, Matrix.toLin'_apply]

private theorem orthogonal_det_mul_self (Q : Tensor 3) (hQ : Q.transpose * Q = 1) :
    Q.det * Q.det = 1 := by
  simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using congrArg Matrix.det hQ

/-- Orthogonal placement preserves surface area and pulls back the traction
field on the placed face. -/
theorem chartSurfaceForce_orthogonal (D : Set (Vector 2)) (Q : Tensor 3)
    (hQ : Q.transpose * Q = 1) (r : Vector 2 → Vector 3) (hr : Differentiable ℝ r)
    (traction : Vector 3 → Vector 3) :
    chartSurfaceForce D (cartesianMatrixMap Q ∘ r) traction =
      chartSurfaceForce D r (traction ∘ cartesianMatrixMap Q) := by
  have hdet := orthogonal_det_mul_self Q hQ
  have hne : Q.det ≠ 0 := by
    intro h
    simp [h] at hdet
  have hInv : Q⁻¹ = Q.transpose := Matrix.inv_eq_left_inv hQ
  have hCof : Q.adjugate.transpose = Q.det • Q := by
    rw [cofactor_eq_jacobian_smul_invTranspose Q hne, hInv, Matrix.transpose_transpose]
    rfl
  have hArea (u : Vector 2) : chartAreaVector (cartesianMatrixMap Q ∘ r) u =
      Q.det • (Q *ᵥ chartAreaVector r u) := by
    unfold chartAreaVector
    rw [((cartesianMatrixMap Q).hasFDerivAt.comp u (hr u).hasFDerivAt).fderiv]
    change (cartesianMatrixMap Q ((fderiv ℝ r u) (Pi.single 0 1))) ⨯₃
      (cartesianMatrixMap Q ((fderiv ℝ r u) (Pi.single 1 1))) = _
    rw [cartesianMatrixMap_apply, cartesianMatrixMap_apply, areaVector_transform, hCof,
      Matrix.smul_mulVec]
  have hdot (x : Vector 3) : (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ x := by
    rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  unfold chartSurfaceForce
  congr 1
  funext u
  simp only [hArea, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← mul_assoc, hdet,
    one_mul, hdot, Function.comp_apply]

/-- Orthogonal placement preserves volume and transforms the volume-force
integral by composition with the placement. -/
theorem integral_orthogonal_image (Q : Tensor 3) (hQ : Q.transpose * Q = 1)
    (S : Set (Vector 3)) (force : Vector 3 → Vector 3) :
    (∫ x in cartesianMatrixMap Q '' S, force x) =
      ∫ x in S, force (cartesianMatrixMap Q x) := by
  let L := cartesianMatrixMap Q
  let K := cartesianMatrixMap Q.transpose
  have hleft : Function.LeftInverse K L := by
    intro x
    simp only [L, K, cartesianMatrixMap_apply, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  have hright : Function.RightInverse K L := by
    intro x
    have hJ : Q.det ≠ 0 := by
      have hd := orthogonal_det_mul_self Q hQ
      intro h
      simp [h] at hd
    have hQQ : Q * Q.transpose = 1 := by
      rw [← Matrix.inv_eq_left_inv hQ]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ)
    simp only [L, K, cartesianMatrixMap_apply, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
  let e : Vector 3 ≃ᵐ Vector 3 :=
    { toFun := L, invFun := K, left_inv := hleft, right_inv := hright
      measurable_toFun := L.continuous.measurable, measurable_invFun := K.continuous.measurable }
  have hd : Q.det = 1 ∨ Q.det = -1 :=
    mul_self_eq_one_iff.mp (orthogonal_det_mul_self Q hQ)
  have hne : LinearMap.det Q.toLin' ≠ 0 := by
    rw [LinearMap.det_toLin']
    rcases hd with h | h <;> simp [h]
  have hp : MeasurePreserving e := by
    refine ⟨e.measurable, ?_⟩
    change Measure.map (Q.toLin' : Vector 3 → Vector 3) volume = volume
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, LinearMap.det_toLin']
    rcases hd with h | h <;> simp [h]
  exact hp.setIntegral_image_emb e.measurableEmbedding force S

def orthogonalPillboxForceBalance (Q : Tensor 3) (T : Vector 3 → Vector 3 → Vector 3)
    (force : Vector 3 → Vector 3) (s : ℝ) : Prop :=
    let L := cartesianMatrixMap Q
    (∑ j, (chartSurfaceForce pillboxFaceParameters (L ∘ pillboxFaceChart s j false)
        (fun x => T x (L (pillboxFaceNormal j false))) +
      chartSurfaceForce pillboxFaceParameters (L ∘ pillboxFaceChart s j true)
        (fun x => T x (L (pillboxFaceNormal j true))))) +
    (∫ x in L '' pillboxRegion s, force x) = 0

/-- Force balance on an orthogonally placed pillbox gives opposite tractions
in the direction of its placed main-face normal. -/
theorem traction_neg_of_orthogonalPillboxBalance (Q : Tensor 3) (hQ : Q.transpose * Q = 1)
    (T : Vector 3 → Vector 3 → Vector 3) (force : Vector 3 → Vector 3)
    (hT : ∀ n, Continuous (fun x => T x n)) (hForce : Continuous force)
    (hBalance : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), orthogonalPillboxForceBalance Q T force s) :
    T 0 (-(cartesianMatrixMap Q (Pi.single 2 1))) = -T 0 (cartesianMatrixMap Q (Pi.single 2 1)) := by
  let L := cartesianMatrixMap Q
  let T' (x n : Vector 3) := T (L x) (L n)
  have h : ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), pillboxForceBalance T' (force ∘ L) s := by
    filter_upwards [hBalance] with s hs
    have hface (j : Fin 3) (b : Bool) :
        chartSurfaceForce pillboxFaceParameters (cartesianMatrixMap Q ∘ pillboxFaceChart s j b)
          (fun x => T x (cartesianMatrixMap Q (pillboxFaceNormal j b))) =
        chartSurfaceForce pillboxFaceParameters (pillboxFaceChart s j b)
          (fun x => T' x (pillboxFaceNormal j b)) :=
      chartSurfaceForce_orthogonal _ Q hQ _
        ((pillboxFaceLinear s j).differentiable.add_const _) _
    have hbulk : (∫ x in cartesianMatrixMap Q '' pillboxRegion s, force x) =
        ∫ x in pillboxRegion s, (force ∘ L) x :=
      integral_orthogonal_image Q hQ _ _
    simpa only [orthogonalPillboxForceBalance, pillboxForceBalance, hface, hbulk] using hs
  have ht := traction_neg_of_continuous_pillboxBalance T' (force ∘ L)
    (fun n => (hT (L n)).comp L.continuous) (hForce.comp L.continuous) h
  simpa only [T', map_zero, map_neg] using ht

/-- Every unit normal can be obtained by placing the coordinate pillbox
with an orthogonal map. A Householder reflection gives an explicit map. -/
theorem exists_orthogonalPillbox_normal (n : Vector 3) (hn : n ⬝ᵥ n = 1) :
    ∃ Q : Tensor 3, Q.transpose * Q = 1 ∧ cartesianMatrixMap Q (Pi.single 2 1) = n := by
  let e : Vector 3 := Pi.single 2 1
  by_cases he : e = n
  · refine ⟨1, by simp, ?_⟩
    rw [cartesianMatrixMap_apply, Matrix.one_mulVec]
    exact he
  let v := e - n
  let d := v ⬝ᵥ v
  let k := 2 / d
  let P := Matrix.vecMulVec v v
  have hv : v ≠ 0 := sub_ne_zero.mpr he
  have hd : d ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
  have hee : e ⬝ᵥ e = 1 := by simp [e]
  have hde : d = 2 * (v ⬝ᵥ e) := by
    dsimp only [d, v]
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, sub_dotProduct,
      hee, hn, dotProduct_comm e n]
    ring
  have hk : k * (v ⬝ᵥ e) = 1 := by
    dsimp only [k]
    field_simp
    exact hde.symm
  have hP : P * P = d • P := by
    simp only [P, Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp [Matrix.vecMulVec_apply, d, smul_eq_mul]
    ring
  have hscale : (k • P) * (k • P) = (2 * k) • P := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul, smul_smul]
    have hcoef : k * (k * d) = 2 * k := by
      have hkd : k * d = 2 := div_mul_cancel₀ 2 hd
      rw [hkd, mul_comm]
    rw [mul_assoc k k d, hcoef]
  refine ⟨1 - k • P, ?_, ?_⟩
  · have hPt : P.transpose = P := Matrix.transpose_vecMulVec _ _
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPt,
      Matrix.sub_mul, Matrix.mul_sub, mul_one, one_mul, hscale, mul_smul, two_smul]
    abel
  · rw [cartesianMatrixMap_apply]
    change (1 - k • P) *ᵥ e = n
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    have hPe : P *ᵥ e = (v ⬝ᵥ e) • v := by
      simpa only [op_smul_eq_smul] using Matrix.vecMulVec_mulVec v v e
    rw [hPe, smul_smul, hk, one_smul]
    dsimp only [v]
    abel

/-- If the integral balance holds on shrinking pillboxes of all orthogonal
placements, the traction law is odd on the entire unit sphere. -/
theorem traction_neg_all_unitNormals
    (T : Vector 3 → Vector 3 → Vector 3) (force : Vector 3 → Vector 3)
    (hT : ∀ n, Continuous (fun x => T x n)) (hForce : Continuous force)
    (hBalance : ∀ Q : Tensor 3, Q.transpose * Q = 1 →
      ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), orthogonalPillboxForceBalance Q T force s)
    (n : Vector 3) (hn : n ⬝ᵥ n = 1) :
    T 0 (-n) = -T 0 n := by
  obtain ⟨Q, hQ, hnormal⟩ := exists_orthogonalPillbox_normal n hn
  have h := traction_neg_of_orthogonalPillboxBalance Q hQ T force hT hForce (hBalance Q hQ)
  rwa [hnormal] at h

/-- Pillbox balances centered at each material point supply the
opposite-normal condition used on the coordinate faces of a tetrahedron. -/
theorem traction_neg_at_of_pillboxBalances
    (T : Vector 3 → Vector 3 → Vector 3) (force : Vector 3 → Vector 3)
    (hT : ∀ n, Continuous (fun x => T x n)) (hForce : Continuous force)
    (x : Vector 3)
    (hBalance : ∀ Q : Tensor 3, Q.transpose * Q = 1 →
      ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
        orthogonalPillboxForceBalance Q (fun y n => T (x + y) n) (fun y => force (x + y)) s)
    (n : Vector 3) (hn : n ⬝ᵥ n = 1) :
    T x (-n) = -T x n := by
  have hShift : Continuous (fun y : Vector 3 => x + y) :=
    continuous_const.add continuous_id
  simpa only [add_zero] using
    traction_neg_all_unitNormals (fun y m => T (x + y) m) (fun y => force (x + y))
      (fun m => (hT m).comp hShift) (hForce.comp hShift) hBalance n hn

/-- The sum of the four face forces and the bulk force on a reflected
intercept tetrahedron. The reference oblique normal is n. -/
def reflectedTetrahedronForceBalance (a b c : ℝ) (n sign : Vector 3)
    (T : Vector 3 → Vector 3 → Vector 3) (force : Vector 3 → Vector 3) (s : ℝ) : Prop :=
  let R := coordinateReflection sign
  let oblique (u : Vector 2) := obliqueFaceLinear (s * a) (s * b) (s * c) u + ![s * a, 0, 0]
  let coordinate (j : Fin 3) := coordinateFaceLinear (s * a) (s * b) (s * c) j
  chartSurfaceForce faceParameterTriangle (R ∘ oblique) (fun x => T x (R n)) +
    (∑ j, chartSurfaceForce faceParameterTriangle (R ∘ coordinate j)
      (fun x => T x (R (-(Pi.single j 1 : Vector 3))))) +
    (∫ x in R '' (s • interceptTetrahedron a b c), force x) = 0

/-- Cauchy's pointwise traction theorem from pillbox and tetrahedron
integral balances. Spatial continuity controls the forces on shrinking
regions, and normal continuity extends the representation to their limiting
directions on the unit sphere. -/
theorem traction_eq_of_pillbox_and_tetrahedronBalances
    (T : Vector 3 → Vector 3 → Vector 3) (force : Vector 3 → Vector 3)
    (hT : ∀ n, Continuous (fun x => T x n)) (hForce : Continuous force)
    (hNormal : Continuous (T 0))
    (hPillbox : ∀ x (Q : Tensor 3), Q.transpose * Q = 1 →
      ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0),
        orthogonalPillboxForceBalance Q (fun y n => T (x + y) n) (fun y => force (x + y)) s)
    (hTetrahedron : ∀ (a b c A : ℝ) (n sign : Vector 3),
      0 < a → 0 < b → 0 < c → 0 < A → n ⬝ᵥ n = 1 →
      tetrahedronObliqueArea a b c = A • n →
      (∀ j, sign j = 1 ∨ sign j = -1) →
      ∀ᶠ s in nhdsWithin (0 : ℝ) (Ioi 0), reflectedTetrahedronForceBalance a b c n sign T force s)
    (n : Vector 3) (hn : n ⬝ᵥ n = 1) :
    T 0 n = stressOfTraction (T 0) *ᵥ n := by
  apply traction_eq_all_unitNormals (T 0) hNormal _ n hn
  intro m hm hm₀
  obtain ⟨sign, a, b, c, A, hsign, ha, hb, hc, hA, hArea⟩ :=
    exists_reflected_interceptTetrahedron_area m hm₀
  let R := coordinateReflection sign
  have hinv := coordinateReflection_involutive sign hsign
  have hUnit : R m ⬝ᵥ R m = 1 := (coordinateReflection_dot sign m m hsign).trans hm
  have hReferenceArea : tetrahedronObliqueArea a b c = A • R m := by
    have he := congrArg (fun x => R x) hArea
    change R (R (tetrahedronObliqueArea a b c)) = R (A • m) at he
    rw [hinv _, map_smul] at he
    exact he
  have hOdd (x v : Vector 3) (hv : v ⬝ᵥ v = 1) : T x (-v) = -T x v :=
    traction_neg_at_of_pillboxBalances T force hT hForce x (hPillbox x) v hv
  have h := traction_eq_of_reflectedTetrahedron_chartBalance a b c A ha.le hb.le hc.le hA
    T (R m) sign hUnit hReferenceArea hsign hT hOdd force hForce
    (by simpa only [reflectedTetrahedronForceBalance] using
      hTetrahedron a b c A (R m) sign ha hb hc hA hUnit hReferenceArea hsign)
  change T 0 (R (R m)) = stressOfTraction (T 0) *ᵥ R (R m) at h
  rwa [hinv m] at h

end LeanSolid.ContinuumMechanics
