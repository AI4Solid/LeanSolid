module

public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

public section

open Filter Set
open scoped Topology

namespace LeanSolid.Math

/-- A compact lower-order term can be removed from a norm estimate when the principal
operator has trivial kernel. Compactness is required only on the image of the unit sphere. -/
theorem exists_norm_le_of_compact_remainder
    {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : V →L[ℝ] E) (B : V →L[ℝ] F)
    {C : ℝ} (hC : 0 < C)
    (hest : ∀ v, ‖v‖ ≤ C * (‖A v‖ + ‖B v‖))
    (hcompact : IsCompact (closure (B '' {v : V | ‖v‖ = 1})))
    (hker : ∀ v, A v = 0 → v = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ v, ‖v‖ ≤ K * ‖A v‖ := by
  by_contra! h
  have hw (n : ℕ) : ∃ v : V, ((n : ℝ) + 1) * ‖A v‖ < ‖v‖ :=
    h ((n : ℝ) + 1) (by positivity)
  choose w hw using hw
  have hnorm (n : ℕ) : 0 < ‖w n‖ :=
    (mul_nonneg (by positivity) (norm_nonneg (A (w n)))).trans_lt (hw n)
  let u := fun n => (‖w n‖)⁻¹ • w n
  have hu (n : ℕ) : ‖u n‖ = 1 := by
    simp [u, norm_smul, (hnorm n).ne']
  have hsmall (n : ℕ) : ‖A (u n)‖ ≤ 1 / ((n : ℝ) + 1) := by
    simp only [u, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (hnorm n).le)]
    rw [inv_mul_eq_div, div_le_div_iff₀ (hnorm n) (by positivity)]
    simpa only [mul_comm ‖A (w n)‖, one_mul] using (hw n).le
  have hzeroNorm := squeeze_zero (fun n => norm_nonneg (A (u n))) hsmall
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hzero : Tendsto (fun n => A (u n)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hzeroNorm
  obtain ⟨b, _, φ, hφ, hb⟩ := hcompact.tendsto_subseq (x := fun n => B (u n))
    (fun n => subset_closure ⟨u n, hu n, rfl⟩)
  have ha : Tendsto (fun n => A (u (φ n))) atTop (𝓝 0) :=
    hzero.comp hφ.tendsto_atTop
  have hcauchy : CauchySeq (fun n => u (φ n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hδ : 0 < ε / (2 * C) := by positivity
    obtain ⟨NA, hNA⟩ := Metric.cauchySeq_iff.mp ha.cauchySeq _ hδ
    obtain ⟨NB, hNB⟩ := Metric.cauchySeq_iff.mp hb.cauchySeq _ hδ
    refine ⟨max NA NB, fun m hm n hn => ?_⟩
    have hA := hNA m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
    have hB := hNB m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
    simp only [Function.comp_apply, dist_eq_norm] at hA hB ⊢
    refine (hest (u (φ m) - u (φ n))).trans_lt ?_
    rw [map_sub, map_sub]
    have hsum := mul_lt_mul_of_pos_left (add_lt_add hA hB) hC
    convert hsum using 1
    field_simp [hC.ne']
    ring
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hav : A v = 0 := tendsto_nhds_unique ((A.continuous.tendsto v).comp hv) ha
  have hnv : ‖v‖ = 1 := by
    apply tendsto_nhds_unique (continuous_norm.continuousAt.tendsto.comp hv)
    rw [show ((fun a : V => ‖a‖) ∘ fun n : ℕ => u (φ n)) = fun _ => (1 : ℝ) from
      funext fun n => hu (φ n)]
    exact tendsto_const_nhds
  simp [hker v hav] at hnv

end LeanSolid.Math
