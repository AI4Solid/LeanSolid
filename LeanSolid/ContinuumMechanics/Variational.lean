module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Theorems
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

public section

open MeasureTheory Filter Set LeanSolid.Math
open scoped Topology

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

theorem hasDerivAt_affineEnergy {n : ℕ} {W : Tensor n → ℝ} {F H P : Tensor n} {t : ℝ}
    (hW : HasEnergyGradient W (F + t • H) P) :
    HasDerivAt (fun s : ℝ => W (F + s • H)) (contract P H) t := by
  have hPath : HasTensorDerivative (fun r : ℝ => F + (t + r) • H) H := by
    intro i j
    change HasDerivAt (fun r : ℝ => F i j + (t + r) * H i j) (H i j) 0
    have h := (((hasDerivAt_id (0 : ℝ)).const_add t).mul_const (H i j)).const_add (F i j)
    simpa using h
  have h := hW _ H (by simp) hPath
  have ht := (hasDerivAt_id t).sub_const t
  have h' := h.comp_of_eq t ht (sub_self t).symm
  have he : ((fun r : ℝ => W (F + (t + r) • H)) ∘ fun r => id r - t) =
      (fun r : ℝ => W (F + r • H)) := by
    funext r
    simp
  rw [he] at h'
  simpa only [mul_one] using h'

/-- First variation of finite-strain potential under an affine deformation-gradient
variation and a dead load. Vanishing internal minus external virtual work gives stationarity. -/
theorem hasDerivAt_totalPotential {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    (W : Tensor n → ℝ) (F H : α → Tensor n) (P : ℝ → α → Tensor n)
    (work L₀ : ℝ) {s : Set ℝ} (hs : s ∈ 𝓝 (0 : ℝ))
    (hMeas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun X => W (F X + t • H X)) μ)
    (hInt : Integrable (fun X => W (F X)) μ)
    (hGrad : ∀ᵐ X ∂μ, ∀ t ∈ s, HasEnergyGradient W (F X + t • H X) (P t X))
    (hRateMeas : AEStronglyMeasurable (fun X => contract (P 0 X) (H X)) μ)
    (bound : α → ℝ) (hBoundInt : Integrable bound μ)
    (hBound : ∀ᵐ X ∂μ, ∀ t ∈ s, ‖contract (P t X) (H X)‖ ≤ bound X) :
    HasDerivAt (fun t : ℝ => (∫ X, W (F X + t • H X) ∂μ) - (L₀ + t * work))
      ((∫ X, contract (P 0 X) (H X) ∂μ) - work) 0 := by
  have hInt₀ : Integrable (fun X => W (F X + (0 : ℝ) • H X)) μ := by simpa using hInt
  have hDiff : ∀ᵐ X ∂μ, ∀ t ∈ s,
      HasDerivAt (fun r : ℝ => W (F X + r • H X)) (contract (P t X) (H X)) t :=
    hGrad.mono fun _ h t ht => hasDerivAt_affineEnergy (h t ht)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hMeas hInt₀
    hRateMeas hBound hBoundInt hDiff).2
  have hLoad : HasDerivAt (fun t : ℝ => L₀ + t * work) work 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const work).const_add L₀)
  exact h.sub hLoad

end LeanSolid.ContinuumMechanics.Hyperelasticity
