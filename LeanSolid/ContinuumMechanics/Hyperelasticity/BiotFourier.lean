module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Biot
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory Filter
open scoped FourierTransform Topology

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

private noncomputable def fourierKernel (ξ x : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * (x * ξ : ℝ)))

private theorem fourier_as_integral (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 g ξ = ∫ x, fourierKernel ξ x * g x := by
  simp [Real.fourier_real_eq_integral_exp_smul, fourierKernel, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

private theorem norm_fourierKernel (ξ x : ℝ) : ‖fourierKernel ξ x‖ = 1 := by
  simp [fourierKernel, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem integrable_kernel_mul {g : ℝ → ℂ} (hg : Integrable g) (ξ : ℝ) :
    Integrable (fun x => fourierKernel ξ x * g x) := by
  refine hg.norm.mono' (?_) (Eventually.of_forall ?_)
  · exact (by unfold fourierKernel; fun_prop : Continuous (fourierKernel ξ)).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · intro x
    simp [norm_fourierKernel]

private theorem horizontalFourier_add {g h : ℝ → ℂ} (hg : Integrable g) (hh : Integrable h)
    (ξ : ℝ) : 𝓕 (fun x => g x + h x) ξ = 𝓕 g ξ + 𝓕 h ξ := by
  simp only [fourier_as_integral, mul_add]
  exact integral_add (integrable_kernel_mul hg ξ) (integrable_kernel_mul hh ξ)

private theorem horizontalFourier_mul (a : ℂ) (g : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x => a * g x) ξ = a * 𝓕 g ξ := by
  simp only [fourier_as_integral, ← integral_const_mul]; congr 1
  funext x
  ring

private theorem horizontalFourier_zero (ξ : ℝ) : 𝓕 (fun _ : ℝ => (0 : ℂ)) ξ = 0 := by
  simp [fourier_as_integral]

/-- Depth differentiation commutes with the horizontal Fourier integral under a locally
integrable bound on the depth derivative. -/
theorem biot_hasDerivAt_horizontalFourier {g g' : ℝ → ℝ → ℂ} {y : ℝ}
    {s : Set ℝ} (hs : s ∈ 𝓝 y) {bound : ℝ → ℝ} (hb : Integrable bound)
    (hg : ∀ z, Integrable (g z)) (hg' : Integrable (g' y))
    (hd : ∀ᵐ x : ℝ, ∀ z ∈ s, HasDerivAt (fun t => g t x) (g' z x) z)
    (hbound : ∀ᵐ x : ℝ, ∀ z ∈ s, ‖g' z x‖ ≤ bound x) (ξ : ℝ) :
    HasDerivAt (fun t => 𝓕 (g t) ξ) (𝓕 (g' y) ξ) y := by
  simp only [fourier_as_integral]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x => fourierKernel ξ x * g z x)
    (F' := fun z x => fourierKernel ξ x * g' z x) hs
    (Eventually.of_forall fun z => (integrable_kernel_mul (hg z) ξ).aestronglyMeasurable)
    (integrable_kernel_mul (hg y) ξ) (integrable_kernel_mul hg' ξ).aestronglyMeasurable
    ?_ hb ?_).2
  · filter_upwards [hbound] with x hx z hz
    simpa [norm_mul, norm_fourierKernel] using hx z hz
  · filter_upwards [hd] with x hx z hz
    exact (hx z hz).const_mul (fourierKernel ξ x)

/-- The physical wavenumber associated with Mathlib's Fourier frequency. -/
noncomputable def biotWavenumber (ξ : ℝ) : ℝ := |2 * Real.pi * ξ|

private theorem multiplier_sq (ξ : ℝ) :
    (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ 2 = -((biotWavenumber ξ ^ 2 : ℝ) : ℂ) := by
  rw [biotWavenumber, sq_abs]
  push_cast
  calc
    _ = (2 * (Real.pi : ℂ) * (ξ : ℂ)) ^ 2 * Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

private theorem multiplier_four (ξ : ℝ) :
    (2 * Real.pi * Complex.I * (ξ : ℂ)) ^ 4 = ((biotWavenumber ξ ^ 4 : ℝ) : ℂ) := by
  calc
    _ = ((2 * Real.pi * Complex.I * (ξ : ℂ)) ^ 2) ^ 2 := by ring
    _ = _ := by rw [multiplier_sq]; push_cast; ring

/-- The integrable horizontal slices needed to Fourier transform the reduced Biot equations. -/
def BiotFourierSlice (g : ℝ → ℂ) : Prop :=
  ContDiff ℝ 4 g ∧ (∀ n : ℕ, n ≤ (4 : ℕ∞) → Integrable (iteratedDeriv n g))

theorem BiotFourierSlice.integrable {g : ℝ → ℂ} (h : BiotFourierSlice g) : Integrable g := by
  simpa using h.2 0 (by decide)

theorem BiotFourierSlice.spectrum_integrable {g : ℝ → ℂ} (h : BiotFourierSlice g) :
    Integrable (𝓕 g) := by
  let C := (∫ x, ‖g x‖) + (4 * Real.pi ^ 2)⁻¹ * ∫ x, ‖iteratedDeriv 2 g x‖
  have hcont : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h.integrable
  refine (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  have hbound := Real.one_add_sq_mul_norm_fourier_le (h.1.of_le (by decide))
    (fun n hn => h.2 n (le_trans (by exact_mod_cast hn) (by decide : (2 : ℕ∞) ≤ 4))) ξ
  change ‖𝓕 g ξ‖ ≤ C * (1 + ξ ^ 2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa [C, mul_comm (1 + ξ ^ 2)] using hbound

private theorem horizontalFourier_second {g : ℝ → ℂ} (h : BiotFourierSlice g) (ξ : ℝ) :
    𝓕 (iteratedDeriv 2 g) ξ = -((biotWavenumber ξ ^ 2 : ℝ) : ℂ) * 𝓕 g ξ := by
  rw [Real.fourier_iteratedDeriv h.1 h.2 (by decide : (2 : ℕ) ≤ (4 : ℕ∞))]
  simp only [smul_eq_mul, multiplier_sq]

private theorem horizontalFourier_fourth {g : ℝ → ℂ} (h : BiotFourierSlice g) (ξ : ℝ) :
    𝓕 (iteratedDeriv 4 g) ξ = ((biotWavenumber ξ ^ 4 : ℝ) : ℂ) * 𝓕 g ξ := by
  rw [Real.fourier_iteratedDeriv h.1 h.2 (by decide : (4 : ℕ) ≤ (4 : ℕ∞))]
  simp only [smul_eq_mul, multiplier_four]

/-- The bulk equation and free-surface conditions for the Biot stream function in physical
coordinates. The first argument of each field is depth, and the second is horizontal position. -/
structure BiotFourierProblem (stretch : ℝ) (f : ℕ → ℝ → ℝ → ℂ) : Prop where
  integrable : ∀ j y, j ≤ 4 → Integrable (f j y)
  horizontal : ∀ j y, j ≤ 2 → y ≤ 0 → BiotFourierSlice (f j y)
  depth : ∀ j < 4, ∀ y ≤ 0, ∃ (s : Set ℝ) (bound : ℝ → ℝ),
    s ∈ 𝓝 y ∧ Integrable bound ∧
    (∀ᵐ x : ℝ, ∀ z ∈ s, HasDerivAt (fun t => f j t x) (f (j + 1) z x) z) ∧
    (∀ᵐ x : ℝ, ∀ z ∈ s, ‖f (j + 1) z x‖ ≤ bound x)
  bulk : ∀ y < 0, ∀ x, f 4 y x + (1 + (stretch : ℂ) ^ 4) * iteratedDeriv 2 (f 2 y) x +
    (stretch : ℂ) ^ 4 * iteratedDeriv 4 (f 0 y) x = 0
  shear : ∀ x, f 2 0 x = iteratedDeriv 2 (f 0 0) x
  normal : ∀ x, f 3 0 x + (2 + (stretch : ℂ) ^ 4) * iteratedDeriv 2 (f 1 0) x = 0
  decay : Tendsto (fun y => ∫ x, ‖f 0 y x‖) atBot (𝓝 0)

/-- Fourier decomposition of the reduced Biot system at every horizontal frequency,
together with pointwise recovery of the stream function by Fourier inversion. -/
theorem BiotFourierProblem.decompose {stretch : ℝ} {f : ℕ → ℝ → ℝ → ℂ}
    (h : BiotFourierProblem stretch f) (ξ : ℝ) :
    let F := fun j y => 𝓕 (f j y) ξ
    let k : ℂ := biotWavenumber ξ
    (∀ j < 4, ∀ y ≤ 0, HasDerivAt (F j) (F (j + 1) y) y) ∧
    (∀ y < 0, F 4 y - (1 + (stretch : ℂ)^4) * k^2 * F 2 y +
      (stretch : ℂ)^4 * k^4 * F 0 y = 0) ∧
    Tendsto (F 0) atBot (𝓝 0) ∧
    F 2 0 + k^2 * F 0 0 = 0 ∧
    F 3 0 = (2 + (stretch : ℂ)^4) * k^2 * F 1 0 ∧
    (∀ y ≤ 0, 𝓕⁻ (𝓕 (f 0 y)) = f 0 y) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj y hy
    obtain ⟨s, b, hs, hb, hd, hbound⟩ := h.depth j hj y hy
    exact biot_hasDerivAt_horizontalFourier hs hb (fun z => h.integrable j z (by omega))
      (h.integrable (j + 1) y (by omega)) hd hbound ξ
  · intro y hy
    have h₂ := h.horizontal 2 y (by decide) hy.le
    have h₀ := h.horizontal 0 y (by decide) hy.le
    have e := congrArg (fun g : ℝ → ℂ => 𝓕 g ξ) (funext (h.bulk y hy))
    have hsum : Integrable (fun x => f 4 y x +
        (1 + (stretch : ℂ)^4) * iteratedDeriv 2 (f 2 y) x) :=
      (h.integrable 4 y (by decide)).add ((h₂.2 2 (by decide)).const_mul _)
    rw [horizontalFourier_add hsum ((h₀.2 4 (by decide)).const_mul _),
      horizontalFourier_add (h.integrable 4 y (by decide)) ((h₂.2 2 (by decide)).const_mul _),
      horizontalFourier_mul, horizontalFourier_mul, horizontalFourier_second h₂,
      horizontalFourier_fourth h₀, horizontalFourier_zero] at e
    push_cast at e
    linear_combination e
  · apply squeeze_zero_norm (fun y => Real.norm_fourier_le_integral_norm (f 0 y) ξ) h.decay
  · have e := congrArg (fun g : ℝ → ℂ => 𝓕 g ξ) (funext h.shear)
    rw [horizontalFourier_second (h.horizontal 0 0 (by decide) le_rfl)] at e
    push_cast at e
    linear_combination e
  · have h₁ := h.horizontal 1 0 (by decide) le_rfl
    have e := congrArg (fun g : ℝ → ℂ => 𝓕 g ξ) (funext h.normal)
    rw [horizontalFourier_add (h.integrable 3 0 (by decide)) ((h₁.2 2 (by decide)).const_mul _),
      horizontalFourier_mul, horizontalFourier_second h₁, horizontalFourier_zero] at e
    push_cast at e
    linear_combination e
  · intro y hy
    have h₀ := h.horizontal 0 y (by decide) hy
    exact h₀.1.continuous.fourierInv_fourier_eq h₀.integrable h₀.spectrum_integrable

private theorem biot_quartic_of_complex_fourier_mode
    (stretch k : ℝ) (hs : 0 < stretch) (hc : stretch ≤ 1) (hk : 0 < k)
    (F : ℕ → ℝ → ℂ)
    (hd : ∀ j < 4, ∀ y ≤ 0, HasDerivAt (F j) (F (j + 1) y) y)
    (hODE : ∀ y < 0, F 4 y - (1 + (stretch : ℂ)^4) * (k : ℂ)^2 * F 2 y +
      (stretch : ℂ)^4 * (k : ℂ)^4 * F 0 y = 0)
    (hDecay : Tendsto (F 0) atBot (𝓝 0))
    (hShear : F 2 0 + (k : ℂ)^2 * F 0 0 = 0)
    (hNormal : F 3 0 = (2 + (stretch : ℂ)^4) * (k : ℂ)^2 * F 1 0)
    (hNonzero : ∃ y < 0, F 0 y ≠ 0) :
    stretch < 1 ∧ stretch ^ 4 - 2 * stretch + 1 = 0 := by
  have reduce (L : ℂ →L[ℝ] ℝ) (hn : ∃ y < 0, L (F 0 y) ≠ 0) :
      stretch < 1 ∧ stretch ^ 4 - 2 * stretch + 1 = 0 := by
    have hderiv (j : ℕ) (hj : j < 4) (y : ℝ) (hy : y ≤ 0) :=
      L.hasFDerivAt.comp_hasDerivAt y (hd j hj y hy)
    have hl (a : ℝ) (z : ℂ) : L ((a : ℂ) * z) = a * L z := by
      change L (a • z) = a • L z
      exact map_smul L a z
    have ode (y : ℝ) (hy : y < 0) := congrArg L (hODE y hy)
    have shear := congrArg L hShear
    have normal := congrArg L hNormal
    push_cast [← Complex.ofReal_pow, ← Complex.ofReal_add, ← Complex.ofReal_mul] at *
    simp only [← Complex.ofReal_one, ← Complex.ofReal_ofNat,
      ← Complex.ofReal_add, ← Complex.ofReal_mul, hl, map_add, map_sub, map_zero] at ode shear normal
    apply biot_quartic_of_positiveWavenumber_profile stretch k hs hc hk
      (fun y => L (F 0 y)) (fun y => L (F 1 y)) (fun y => L (F 2 y))
      (fun y => L (F 3 y)) (fun y => L (F 4 y))
      (hderiv 0 (by decide)) (hderiv 1 (by decide)) (hderiv 2 (by decide))
      (hderiv 3 (by decide)) _ _ hn shear normal
    · intro y hy
      linear_combination ode y hy
    · simpa [Function.comp_def] using (L.continuous.tendsto 0).comp hDecay
  obtain ⟨y, hy, hn⟩ := hNonzero
  by_cases hr : (F 0 y).re = 0
  · exact reduce Complex.imCLM ⟨y, hy, fun hi => hn (Complex.ext hr hi)⟩
  · exact reduce Complex.reCLM ⟨y, hy, hr⟩

/-- A nonzero localized perturbation on the half-space forces the Biot critical equation.
No restriction to a single horizontal frequency is imposed on the physical field. -/
theorem BiotFourierProblem.critical_of_nonzero {stretch : ℝ} {f : ℕ → ℝ → ℝ → ℂ}
    (h : BiotFourierProblem stretch f) (hs : 0 < stretch) (hc : stretch ≤ 1)
    (hn : ∃ y < 0, ∃ x, f 0 y x ≠ 0) :
    stretch < 1 ∧ stretch ^ 4 - 2 * stretch + 1 = 0 := by
  by_contra hcritical
  obtain ⟨y, hy, x, hx⟩ := hn
  have hzero (ξ : ℝ) (hξ : ξ ≠ 0) : 𝓕 (f 0 y) ξ = 0 := by
    by_contra hmode
    obtain ⟨hd, hODE, hDecay, hShear, hNormal, _⟩ := h.decompose ξ
    have hk : 0 < biotWavenumber ξ :=
      abs_pos.mpr (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ)
    exact hcritical (biot_quartic_of_complex_fourier_mode stretch (biotWavenumber ξ)
      hs hc hk (fun j z => 𝓕 (f j z) ξ) hd hODE hDecay hShear hNormal ⟨y, hy, hmode⟩)
  have hae : (𝓕 (f 0 y)) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with ξ hξ
    exact hzero ξ hξ
  have hinv := (h.decompose 0).2.2.2.2.2 y hy.le
  apply hx
  rw [← congrFun hinv x, Real.fourierInv_congr_ae hae]
  simp [Real.fourierInv_eq]

end LeanSolid.ContinuumMechanics.Hyperelasticity
