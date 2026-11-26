/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Elastostatics/Korn.lean at 7e41dfe (Apache-2.0). -/
module

public import LeanSolid.Elastostatics.Korn.Definitions
public import LeanSolid.Math.Calculus.Theorems
public import LeanSolid.LinearElasticity.Kinematics
import LeanSolid.Math.Calculus.Mollifier
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

noncomputable section

namespace LeanSolid.Elastostatics.Korn

open LeanSolid.Math
open MeasureTheory Filter Set
open scoped ContDiff Convolution Topology Pointwise

variable {n : ℕ}

variable {f g : (Fin n → ℝ) → ℝ}

theorem continuous_pd (hf : ContDiff ℝ 1 f) (j : Fin n) : Continuous (partialDeriv f j) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem contDiff_pd (hf : ContDiff ℝ 2 f) (j : Fin n) : ContDiff ℝ 1 (partialDeriv f j) :=
  contDiff_partial hf (by norm_num) j

theorem hasCompactSupport_pd (hf : HasCompactSupport f) (j : Fin n) :
    HasCompactSupport (partialDeriv f j) := by
  refine (hf.fderiv (𝕜 := ℝ)).mono' fun x hx => subset_tsupport _ ?_
  rw [Function.mem_support] at hx ⊢
  exact fun h => hx (by simp [partialDeriv, h])

/-- **Integration by parts**: `∫ f ∂ⱼg = -∫ ∂ⱼf g` for `C¹` functions with compact support. -/
theorem integral_mul_pd (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f)
    (j : Fin n) : ∫ x, f x * partialDeriv g j x = -∫ x, partialDeriv f j x * g x := by
  have cf := hf.continuous; have cg := hg.continuous
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((continuous_pd hf j).mul cg).integrable_of_hasCompactSupport
      ((hasCompactSupport_pd hfc j).mul_right))
    ((cf.mul (continuous_pd hg j)).integrable_of_hasCompactSupport hfc.mul_right)
    ((cf.mul cg).integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)
/-- `∫ ∂ⱼuᵢ ∂ᵢuⱼ = ∫ ∂ᵢuᵢ ∂ⱼuⱼ` for `C²` fields with compact support. -/
theorem integral_cross {ui uj : (Fin n → ℝ) → ℝ} (hi : ContDiff ℝ 2 ui) (hj : ContDiff ℝ 2 uj)
    (hic : HasCompactSupport ui) (i j : Fin n) :
    ∫ x, partialDeriv ui j x * partialDeriv uj i x = ∫ x, partialDeriv ui i x * partialDeriv uj j x := by
  have h1 := hi.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  -- `∫ ∂ⱼuᵢ ∂ᵢuⱼ = -∫ uᵢ ∂ⱼ∂ᵢuⱼ`
  have e1 : ∫ x, partialDeriv ui j x * partialDeriv uj i x = -∫ x, ui x * partialDeriv (partialDeriv uj i) j x := by
    rw [integral_mul_pd h1 (contDiff_partial hj (by norm_num) i) hic j, neg_neg]
  -- `∫ uᵢ ∂ᵢ∂ⱼuⱼ = -∫ ∂ᵢuᵢ ∂ⱼuⱼ`
  have e2 : ∫ x, ui x * partialDeriv (partialDeriv uj j) i x = -∫ x, partialDeriv ui i x * partialDeriv uj j x :=
    integral_mul_pd h1 (contDiff_partial hj (by norm_num) j) hic i
  rw [e1, partial_partial_comm hj, e2, neg_neg]

/-- The integrated cross-term identity for compactly supported C¹ fields. -/
theorem integral_cross_c1 {ui uj : (Fin n → ℝ) → ℝ}
    (hi : ContDiff ℝ 1 ui) (hj : ContDiff ℝ 1 uj)
    (hic : HasCompactSupport ui) (hjc : HasCompactSupport uj) (i j : Fin n) :
    ∫ x, partialDeriv ui j x * partialDeriv uj i x = ∫ x, partialDeriv ui i x * partialDeriv uj j x := by
  let r (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; positivity
  have hrle (k : ℕ) : r k ≤ 1 := by
    exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg k))
  let φ (k : ℕ) : ContDiffBump (0 : Fin n → ℝ) :=
    ⟨r k / 2, r k, half_pos (hr k), half_lt_self (hr k)⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
    change Tendsto r atTop (𝓝 0)
    simpa [r, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
  let smooth (f : (Fin n → ℝ) → ℝ) (k : ℕ) :=
    (φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have hsm {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (k : ℕ) :
      ContDiff ℝ 2 (smooth f k) :=
    (φ k).hasCompactSupport_normed.contDiff_convolution_left _
      (φ k).contDiff_normed hf.locallyIntegrable
  let K := Metric.closedBall (0 : Fin n → ℝ) 1 + tsupport ui
  have hK : IsCompact K := (isCompact_closedBall _ _).add hic.isCompact
  have hs (k : ℕ) : HasCompactSupport (smooth ui k) :=
    hK.of_isClosed_subset isClosed_closure (tsupport_normed_convolution_subset hic (φ k) (hrle k))
  obtain ⟨Mi, hMi⟩ := (hic.fderiv ℝ).exists_bound_of_continuous (hi.continuous_fderiv one_ne_zero)
  obtain ⟨Mj, hMj⟩ := (hjc.fderiv ℝ).exists_bound_of_continuous (hj.continuous_fderiv one_ne_zero)
  have hMi0 : 0 ≤ Mi := (norm_nonneg _).trans (hMi 0)
  have hMj0 : 0 ≤ Mj := (norm_nonneg _).trans (hMj 0)
  have hpd {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
      (a : Fin n) (x : Fin n → ℝ) :
      Tendsto (fun k => partialDeriv (smooth f k) a x) atTop (𝓝 (partialDeriv f a x)) := by
    have he : Continuous (fun A : (Fin n → ℝ) →L[ℝ] ℝ => A (Pi.single a 1)) := by fun_prop
    exact (he.tendsto _).comp (tendsto_fderiv_normed_convolution hφ hf hc x)
  have hb {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
      {M : ℝ} (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) (hM0 : 0 ≤ M)
      (k : ℕ) (a : Fin n) (x : Fin n → ℝ) :
      ‖partialDeriv (smooth f k) a x‖ ≤ 3 * M := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have he : ‖(Pi.single a (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro b
      by_cases h : b = a <;> simp [Pi.single, h]
    exact (mul_le_mul (norm_fderiv_normed_convolution_le hf hc (φ k) hM x)
      he (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hlim (a b : Fin n) :
      Tendsto (fun k => ∫ x, partialDeriv (smooth ui k) a x * partialDeriv (smooth uj k) b x)
        atTop (𝓝 (∫ x, partialDeriv ui a x * partialDeriv uj b x)) := by
    let B := K.indicator (fun _ => (3 * Mi) * (3 * Mj))
    refine tendsto_integral_of_dominated_convergence B (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((continuous_pd ((hsm hi.continuous k).of_le (by norm_num)) a).mul
        (continuous_pd ((hsm hj.continuous k).of_le (by norm_num)) b)).aestronglyMeasurable
    · exact (integrableOn_const (hs := hK.measure_lt_top.ne)).integrable_indicator hK.measurableSet
    · filter_upwards with x
      by_cases hx : x ∈ K
      · rw [show B x = _ from Set.indicator_of_mem hx _, norm_mul]
        exact mul_le_mul (hb hi hic hMi hMi0 k a x) (hb hj hjc hMj hMj0 k b x)
          (norm_nonneg _) (by positivity)
      · have hz : fderiv ℝ (smooth ui k) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun h =>
            hx (tsupport_normed_convolution_subset hic (φ k) (hrle k) (tsupport_fderiv_subset ℝ h))
        simp [B, hx, partialDeriv, hz]
    · exact Eventually.of_forall fun x => (hpd hi hic a x).mul (hpd hj hjc b x)
  exact tendsto_nhds_unique (hlim j i) ((hlim i j).congr fun k =>
    (integral_cross (hsm hi.continuous k) (hsm hj.continuous k) (hs k) i j).symm)

variable {u : Fin n → (Fin n → ℝ) → ℝ}

/-- Pointwise: `2|ε|² = |∇u|² + ∇u : ∇uᵀ`. -/
theorem two_strainSq (x : Fin n → ℝ) :
    2 * strainSq u x = gradSq u x + ∑ i, ∑ j, partialDeriv (u i) j x * partialDeriv (u j) i x := by
  have h1 : 2 * strainSq u x = ∑ i, ∑ j, (partialDeriv (u i) j x ^ 2 / 2 + partialDeriv (u j) i x ^ 2 / 2 +
      partialDeriv (u i) j x * partialDeriv (u j) i x) := by
    rw [strainSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : ∑ i, ∑ j, partialDeriv (u i) j x ^ 2 / 2 = gradSq u x / 2 := by
    simp only [gradSq, Finset.sum_div]
  have h3 : ∑ i, ∑ j, partialDeriv (u j) i x ^ 2 / 2 = gradSq u x / 2 := by
    rw [Finset.sum_comm, h2]
  rw [h1]
  simp only [Finset.sum_add_distrib]
  rw [h2, h3]
  ring

/-- **Korn's identity** for compactly supported `C¹` fields:
`∫ |∇u|² + ∫ (div u)² = 2 ∫ |ε(u)|²`. -/
theorem korn_identity_c1 (hu : ∀ i, ContDiff ℝ 1 (u i)) (hc : ∀ i, HasCompactSupport (u i)) :
    (∫ x, gradSq u x) + ∫ x, div u x ^ 2 = 2 * ∫ x, strainSq u x := by
  have cpd : ∀ i j, Continuous (partialDeriv (u i) j) := fun i j => continuous_pd (hu i) j
  have spd : ∀ i j, HasCompactSupport (partialDeriv (u i) j) := fun i j => hasCompactSupport_pd (hc i) j
  have ipp : ∀ i j k l, Integrable (fun x => partialDeriv (u i) j x * partialDeriv (u k) l x) :=
    fun i j k l => ((cpd i j).mul (cpd k l)).integrable_of_hasCompactSupport
      (spd i j).mul_right
  have isq : ∀ i j, Integrable (fun x => partialDeriv (u i) j x ^ 2) := fun i j => by
    simpa [sq] using ipp i j i j
  -- `(div u)² = Σᵢⱼ ∂ᵢuᵢ ∂ⱼuⱼ`
  have hdiv : ∀ x, div u x ^ 2 = ∑ i, ∑ j, partialDeriv (u i) i x * partialDeriv (u j) j x := fun x => by
    rw [div, sq, Finset.sum_mul_sum]
  have e2 : ∫ x, strainSq u x = (∫ x, gradSq u x + ∑ i, ∑ j, partialDeriv (u i) j x * partialDeriv (u j) i x) / 2 := by
    rw [eq_div_iff (two_ne_zero), mul_comm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => two_strainSq x)
  have igrad : Integrable (gradSq u) := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => isq i j
  have icross : Integrable (fun x => ∑ i, ∑ j, partialDeriv (u i) j x * partialDeriv (u j) i x) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ipp i j j i
  rw [e2, integral_add igrad icross, mul_div_cancel₀ _ two_ne_zero]
  congr 1
  simp_rw [hdiv]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ipp i i j j,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ipp i j j i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ipp i i j j,
    integral_finsetSum _ fun j _ => ipp i j j i]
  exact Finset.sum_congr rfl fun j _ => (integral_cross_c1 (hu i) (hu j) (hc i) (hc j) i j).symm

/-- Korn's identity for compactly supported C² fields. -/
theorem korn_identity (hu : ∀ i, ContDiff ℝ 2 (u i)) (hc : ∀ i, HasCompactSupport (u i)) :
    (∫ x, gradSq u x) + ∫ x, div u x ^ 2 = 2 * ∫ x, strainSq u x :=
  korn_identity_c1 (fun i => (hu i).of_le (by norm_num)) hc

/-- The whole-space first Korn estimate for compactly supported C¹ fields. -/
theorem korn_first_c1 (hu : ∀ i, ContDiff ℝ 1 (u i)) (hc : ∀ i, HasCompactSupport (u i)) :
    ∫ x, gradSq u x ≤ 2 * ∫ x, strainSq u x := by
  rw [← korn_identity_c1 hu hc]
  have : 0 ≤ ∫ x, div u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  linarith

/-- **Korn's first inequality** for compactly supported `C²` fields:
`∫ |∇u|² ≤ 2 ∫ |ε(u)|²`. -/
theorem korn_first (hu : ∀ i, ContDiff ℝ 2 (u i)) (hc : ∀ i, HasCompactSupport (u i)) :
    ∫ x, gradSq u x ≤ 2 * ∫ x, strainSq u x := by
  rw [← korn_identity hu hc]
  have : 0 ≤ ∫ x, div u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  linarith

/-- The integrand in Korn's estimate is the same small-strain contraction used in the material law. -/
theorem strainSq_eq_contract (u : Fin n → (Fin n → ℝ) → ℝ) (x : Vector n) :
    strainSq u x =
      contract (LinearElasticity.strainField (fun y i => u i y) x)
        (LinearElasticity.strainField (fun y i => u i y) x) := by
  unfold strainSq contract
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [LinearElasticity.strainField_apply]
  ring

end LeanSolid.Elastostatics.Korn
