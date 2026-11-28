module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Applications
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open LeanSolid.Math Filter Set
open scoped Matrix Topology

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

/-- A mode with horizontal wavenumber one and decay exponent s in x₂ < 0
has displacement A exp(s x₂) (s cos x₁, sin x₁). Pressure is normalized by
the base shear coefficient μ B₂₂. These are its two momentum amplitudes. -/
def BiotModalMomentum (stretch s A pressure : ℝ) : Prop :=
  pressure = s * (s ^ 2 - stretch ^ 4) * A ∧
    s * pressure = (s ^ 2 - stretch ^ 4) * A

theorem biot_modal_pressure_and_decay (stretch s A pressure : ℝ)
    (hst : 0 < stretch) (hs : 0 < s) (hA : A ≠ 0) :
    BiotModalMomentum stretch s A pressure ↔
      (s = 1 ∧ pressure = (1 - stretch ^ 4) * A) ∨
        (s = stretch ^ 2 ∧ pressure = 0) := by
  constructor
  · rintro ⟨hp, hm⟩
    have he : (s ^ 2 - 1) * (s ^ 2 - stretch ^ 4) * A = 0 := by
      linear_combination -s * hp + hm
    rcases mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hA) with h | h
    · have hs₁ : s = 1 := by nlinarith
      left
      exact ⟨hs₁, by simpa [hs₁] using hp⟩
    · have hs₂ : s = stretch ^ 2 := by
        have hfac : (s - stretch ^ 2) * (s + stretch ^ 2) = 0 := by linear_combination h
        exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right (by positivity))
      right
      exact ⟨hs₂, by rw [hp, hs₂]; ring⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals constructor <;> ring

noncomputable section

/-- Displacement of a real plane-strain mode in the half-space. -/
def biotModeDisplacement (s A x y : ℝ) : Vector 2 :=
  ![s * A * Real.cos x * Real.exp (s * y), A * Real.sin x * Real.exp (s * y)]

/-- Plane-strain gradient of the unit-wavenumber displacement mode. -/
def biotModeGradient (s A x y : ℝ) : Tensor 2 :=
  let sn := Real.sin x * Real.exp (s * y)
  let cs := Real.cos x * Real.exp (s * y)
  !![-s * A * sn, s ^ 2 * A * cs; A * cs, s * A * sn]

/-- Pushed nominal stress normalized by μ B₂₂. -/
def biotModeStress (stretch s A p x y : ℝ) : Tensor 2 :=
  let L := biotModeGradient s A x y
  L * Matrix.diagonal ![stretch ^ 4, 1] + L.transpose -
    (p * Real.sin x * Real.exp (s * y)) • (1 : Tensor 2)

theorem biotModeStress_components (stretch s A p x y : ℝ) :
    biotModeStress stretch s A p x y =
      !![(-s * (stretch ^ 4 + 1) * A - p) * Real.sin x * Real.exp (s * y),
          (s ^ 2 + 1) * A * Real.cos x * Real.exp (s * y);
        (stretch ^ 4 + s ^ 2) * A * Real.cos x * Real.exp (s * y),
          (2 * s * A - p) * Real.sin x * Real.exp (s * y)] := by
  ext i j
  simp only [biotModeStress, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [biotModeGradient] <;> ring

private theorem hasDerivAt_biotExp (s y : ℝ) :
    HasDerivAt (fun z => Real.exp (s * z)) (Real.exp (s * y) * s) y := by
  have h := (Real.hasDerivAt_exp (s * y)).comp y ((hasDerivAt_id y).const_mul s)
  change HasDerivAt (fun z => Real.exp (s * z)) _ y at h
  simpa only [mul_one] using h

/-- The mode gradient is obtained by differentiating the displacement
with respect to the horizontal and depth coordinates. -/
theorem biotModeGradient_eq_deriv (s A x y : ℝ) (i : Fin 2) :
    deriv (fun z => biotModeDisplacement s A z y i) x = biotModeGradient s A x y i 0 ∧
    deriv (fun z => biotModeDisplacement s A x z i) y = biotModeGradient s A x y i 1 := by
  have hcos := (((Real.hasDerivAt_cos x).const_mul (s * A)).mul_const (Real.exp (s * y))).deriv
  have hsin := (((Real.hasDerivAt_sin x).const_mul A).mul_const (Real.exp (s * y))).deriv
  have he₀ := ((hasDerivAt_biotExp s y).const_mul (s * A * Real.cos x)).deriv
  have he₁ := ((hasDerivAt_biotExp s y).const_mul (A * Real.sin x)).deriv
  fin_cases i
  · constructor
    · change deriv (fun z => s * A * Real.cos z * Real.exp (s * y)) x = _
      rw [hcos]
      change _ = -s * A * (Real.sin x * Real.exp (s * y))
      ring
    · change deriv (fun z => s * A * Real.cos x * Real.exp (s * z)) y = _
      rw [he₀]
      change _ = s ^ 2 * A * (Real.cos x * Real.exp (s * y))
      ring
  · constructor
    · change deriv (fun z => A * Real.sin z * Real.exp (s * y)) x =
        A * (Real.cos x * Real.exp (s * y))
      rw [hsin]
      ring
    · change deriv (fun z => A * Real.sin x * Real.exp (s * z)) y = _
      rw [he₁]
      change _ = s * A * (Real.sin x * Real.exp (s * y))
      ring

theorem biotModeGradient_trace (s A x y : ℝ) : (biotModeGradient s A x y).trace = 0 := by
  change (-s * A * (Real.sin x * Real.exp (s * y))) +
    (s * A * (Real.sin x * Real.exp (s * y)) + 0) = 0
  ring

/-- Differentiation of the two stress rows gives precisely the modal
momentum residuals, multiplied by their spatial shape factors. -/
theorem biotModeStress_divergence (stretch s A p x y : ℝ) :
    (deriv (fun z => biotModeStress stretch s A p z y 0 0) x +
        deriv (fun z => biotModeStress stretch s A p x z 0 1) y =
      (s * (s ^ 2 - stretch ^ 4) * A - p) * Real.cos x * Real.exp (s * y)) ∧
    (deriv (fun z => biotModeStress stretch s A p z y 1 0) x +
        deriv (fun z => biotModeStress stretch s A p x z 1 1) y =
      ((s ^ 2 - stretch ^ 4) * A - s * p) * Real.sin x * Real.exp (s * y)) := by
  have he := hasDerivAt_biotExp s y
  have hsin (c : ℝ) : deriv (fun z => c * Real.sin z * Real.exp (s * y)) x =
      c * Real.cos x * Real.exp (s * y) :=
    (((Real.hasDerivAt_sin x).const_mul c).mul_const _).deriv
  have hcos (c : ℝ) : deriv (fun z => c * Real.cos z * Real.exp (s * y)) x =
      c * (-Real.sin x) * Real.exp (s * y) :=
    (((Real.hasDerivAt_cos x).const_mul c).mul_const _).deriv
  have hExp (c : ℝ) : deriv (fun z => c * Real.exp (s * z)) y =
      c * (Real.exp (s * y) * s) := (he.const_mul c).deriv
  have h₀₀ (z : ℝ) : biotModeStress stretch s A p z y 0 0 =
      (-s * (stretch ^ 4 + 1) * A - p) * Real.sin z * Real.exp (s * y) :=
    congrArg (fun M : Tensor 2 => M 0 0) (biotModeStress_components stretch s A p z y)
  have h₀₁ (z : ℝ) : biotModeStress stretch s A p x z 0 1 =
      ((s ^ 2 + 1) * A * Real.cos x) * Real.exp (s * z) :=
    congrArg (fun M : Tensor 2 => M 0 1) (biotModeStress_components stretch s A p x z)
  have h₁₀ (z : ℝ) : biotModeStress stretch s A p z y 1 0 =
      (stretch ^ 4 + s ^ 2) * A * Real.cos z * Real.exp (s * y) :=
    congrArg (fun M : Tensor 2 => M 1 0) (biotModeStress_components stretch s A p z y)
  have h₁₁ (z : ℝ) : biotModeStress stretch s A p x z 1 1 =
      ((2 * s * A - p) * Real.sin x) * Real.exp (s * z) :=
    congrArg (fun M : Tensor 2 => M 1 1) (biotModeStress_components stretch s A p x z)
  simp only [h₀₀, h₀₁, h₁₀, h₁₁, hsin, hcos, hExp]
  constructor <;> ring

end

/-- Free-surface traction amplitudes after combining the two decaying
modes. Their column vectors are (2, 1 + λ⁴) and (1 + λ⁴, 2λ²). -/
def BiotFreeSurface (stretch A B : ℝ) : Prop :=
  2 * A + (1 + stretch ^ 4) * B = 0 ∧
    (1 + stretch ^ 4) * A + 2 * stretch ^ 2 * B = 0

/-- Evaluating the actual modal stresses at the free surface yields the
two algebraic traction amplitudes. -/
theorem biot_freeSurface_iff_traction (stretch A B : ℝ) :
    BiotFreeSurface stretch A B ↔
    ∀ x : ℝ, (biotModeStress stretch 1 A ((1 - stretch ^ 4) * A) x 0 +
        biotModeStress stretch (stretch ^ 2) B 0 x 0) 0 1 = 0 ∧
      (biotModeStress stretch 1 A ((1 - stretch ^ 4) * A) x 0 +
        biotModeStress stretch (stretch ^ 2) B 0 x 0) 1 1 = 0 := by
  have h₁ (x : ℝ) : (biotModeStress stretch 1 A ((1 - stretch ^ 4) * A) x 0 +
      biotModeStress stretch (stretch ^ 2) B 0 x 0) 0 1 =
      (2 * A + (1 + stretch ^ 4) * B) * Real.cos x := by
    simp only [Matrix.add_apply, biotModeStress_components, mul_zero, Real.exp_zero, mul_one]
    change ((1 : ℝ) ^ 2 + 1) * A * Real.cos x +
      ((stretch ^ 2) ^ 2 + 1) * B * Real.cos x = _
    ring
  have h₂ (x : ℝ) : (biotModeStress stretch 1 A ((1 - stretch ^ 4) * A) x 0 +
      biotModeStress stretch (stretch ^ 2) B 0 x 0) 1 1 =
      ((1 + stretch ^ 4) * A + 2 * stretch ^ 2 * B) * Real.sin x := by
    simp only [Matrix.add_apply, biotModeStress_components, mul_zero, Real.exp_zero, mul_one]
    change (2 * A - (1 - stretch ^ 4) * A) * Real.sin x +
      (2 * stretch ^ 2 * B - 0) * Real.sin x = _
    ring
  constructor
  · rintro ⟨hA, hB⟩ x
    simp only [h₁, h₂, hA, hB, zero_mul, and_self]
  · intro h
    constructor
    · simpa only [h₁, Real.cos_zero, mul_one] using (h 0).1
    · simpa only [h₂, Real.sin_pi_div_two, mul_one] using (h (Real.pi / 2)).2

/-- The two-mode boundary system has a nonzero amplitude exactly at a
root of the displayed quartic on the positive, strictly compressed branch. -/
theorem biot_freeSurface_nontrivial_iff (stretch : ℝ) (hs : 0 < stretch) :
    (∃ A B : ℝ, (A ≠ 0 ∨ B ≠ 0) ∧ BiotFreeSurface stretch A B) ↔
      stretch ^ 4 - 2 * stretch + 1 = 0 := by
  constructor
  · rintro ⟨A, B, hn, h₁, h₂⟩
    have hB : B ≠ 0 := by
      intro h
      have hA : A = 0 := by rw [h, mul_zero, add_zero] at h₁; linarith
      exact hn.elim (fun ha => ha hA) (fun hb => hb h)
    have hdet : (4 * stretch ^ 2 - (1 + stretch ^ 4) ^ 2) * B = 0 := by
      linear_combination 2 * h₂ - (1 + stretch ^ 4) * h₁
    have hd := (mul_eq_zero.mp hdet).resolve_right hB
    have hf : (stretch ^ 4 - 2 * stretch + 1) * (stretch ^ 4 + 2 * stretch + 1) = 0 := by
      linear_combination -hd
    exact (mul_eq_zero.mp hf).resolve_right (by positivity)
  · intro h
    refine ⟨-(1 + stretch ^ 4), 2, Or.inr (by norm_num), ?_, ?_⟩
    · ring
    · linear_combination -(stretch ^ 4 + 2 * stretch + 1) * h

/-- The decay exponents are distinct throughout strict compression. -/
theorem biot_decay_modes_distinct (stretch : ℝ) (hs : 0 < stretch) (h : stretch < 1) :
    stretch ^ 2 ≠ 1 := by
  intro he
  nlinarith [mul_pos (sub_pos.mpr h) (show 0 < 1 + stretch by positivity)]

/-- The decaying profiles are linearly independent on the half-space;
nonzero amplitudes therefore give a nonzero displacement perturbation. -/
theorem biot_decay_profiles_independent (stretch A B : ℝ) (hs : 0 < stretch) (h : stretch < 1)
    (hz : ∀ y < 0, A * Real.exp y + B * Real.exp (stretch ^ 2 * y) = 0) :
    A = 0 ∧ B = 0 := by
  let y : ℝ := -1
  have hy : y < 0 := by norm_num [y]
  have hDiff := ((Real.hasDerivAt_exp y).const_mul A).add
    ((hasDerivAt_biotExp (stretch ^ 2) y).const_mul B)
  have hZero : HasDerivAt (fun z => A * Real.exp z + B * Real.exp (stretch ^ 2 * z)) 0 y := by
    apply (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hy] with z hz'
    exact hz z hz'
  have hd := hDiff.unique hZero
  have he : (stretch ^ 2 - 1) * (B * Real.exp (stretch ^ 2 * y)) = 0 := by
    linear_combination hd - hz y hy
  have hB := (mul_eq_zero.mp he).resolve_left
    (sub_ne_zero.mpr (biot_decay_modes_distinct stretch hs h))
  have hB' := (mul_eq_zero.mp hB).resolve_right (Real.exp_ne_zero _)
  have hA := hz y hy
  rw [hB', zero_mul, add_zero] at hA
  exact ⟨(mul_eq_zero.mp hA).resolve_right (Real.exp_ne_zero _), hB'⟩

/-- For strict compression, a nonzero two-mode displacement satisfies
the homogeneous free-face conditions exactly at a root of the quartic. -/
theorem biot_halfSpace_twoMode_iff (stretch : ℝ) (hs : 0 < stretch) (hc : stretch < 1) :
    (∃ A B : ℝ,
      (∃ x y : ℝ, y < 0 ∧ biotModeDisplacement 1 A x y +
        biotModeDisplacement (stretch ^ 2) B x y ≠ 0) ∧ BiotFreeSurface stretch A B) ↔
    stretch ^ 4 - 2 * stretch + 1 = 0 := by
  rw [← biot_freeSurface_nontrivial_iff stretch hs]
  constructor
  · rintro ⟨A, B, ⟨x, y, _, h⟩, hb⟩
    refine ⟨A, B, ?_, hb⟩
    by_contra! hn
    apply h
    simp [biotModeDisplacement, hn.1, hn.2]
  · rintro ⟨A, B, hn, hb⟩
    refine ⟨A, B, ?_, hb⟩
    by_contra! hzero
    have hz (y : ℝ) (hy : y < 0) : A * Real.exp y + B * Real.exp (stretch ^ 2 * y) = 0 := by
      have h := congrFun (hzero (Real.pi / 2) y hy) (1 : Fin 2)
      change A * Real.sin (Real.pi / 2) * Real.exp (1 * y) +
        B * Real.sin (Real.pi / 2) * Real.exp (stretch ^ 2 * y) = 0 at h
      simpa only [Real.sin_pi_div_two, mul_one, one_mul] using h
    obtain ⟨ha, hb'⟩ := biot_decay_profiles_independent stretch A B hs hc hz
    exact hn.elim (fun h => h ha) (fun h => h hb')

noncomputable section

/-- The generalized mode at the repeated decay exponent one. -/
def biotRepeatedDisplacement (x y : ℝ) : Vector 2 :=
  ![(1 + y) * Real.cos x * Real.exp y, y * Real.sin x * Real.exp y]

def biotRepeatedGradient (x y : ℝ) : Tensor 2 :=
  !![-(1 + y) * Real.sin x * Real.exp y, (2 + y) * Real.cos x * Real.exp y;
    y * Real.cos x * Real.exp y, (1 + y) * Real.sin x * Real.exp y]

def biotRepeatedStress (x y : ℝ) : Tensor 2 :=
  biotRepeatedGradient x y + (biotRepeatedGradient x y).transpose -
    (2 * Real.sin x * Real.exp y) • (1 : Tensor 2)

theorem biotRepeatedStress_components (x y : ℝ) :
    biotRepeatedStress x y =
      !![(-4 - 2 * y) * Real.sin x * Real.exp y, (2 + 2 * y) * Real.cos x * Real.exp y;
        (2 + 2 * y) * Real.cos x * Real.exp y, (2 * y) * Real.sin x * Real.exp y] := by
  ext i j
  simp only [biotRepeatedStress, Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [biotRepeatedGradient] <;> ring

private theorem hasDerivAt_affine_times_exp (a b c y : ℝ) :
    HasDerivAt (fun z => (a + b * z) * c * Real.exp z)
      ((a + b * y + b) * c * Real.exp y) y := by
  have h := ((((hasDerivAt_id y).const_mul b).const_add a).mul_const c).mul (Real.hasDerivAt_exp y)
  change HasDerivAt (fun z => (a + b * z) * c * Real.exp z)
    (b * 1 * c * Real.exp y + (a + b * y) * c * Real.exp y) y at h
  convert h using 1
  ring

theorem biotRepeatedGradient_eq_deriv (x y : ℝ) (i : Fin 2) :
    deriv (fun z => biotRepeatedDisplacement z y i) x = biotRepeatedGradient x y i 0 ∧
      deriv (fun z => biotRepeatedDisplacement x z i) y = biotRepeatedGradient x y i 1 := by
  fin_cases i
  · constructor
    · change deriv (fun z => (1 + y) * Real.cos z * Real.exp y) x = _
      rw [(((Real.hasDerivAt_cos x).const_mul (1 + y)).mul_const _).deriv]
      change (1 + y) * -Real.sin x * Real.exp y = -(1 + y) * Real.sin x * Real.exp y
      ring
    · change deriv (fun z => (1 + z) * Real.cos x * Real.exp z) y =
        (2 + y) * Real.cos x * Real.exp y
      have h := (hasDerivAt_affine_times_exp 1 1 (Real.cos x) y).deriv
      rw [show (1 : ℝ) + 1 * y + 1 = 2 + y by ring] at h
      simpa only [one_mul] using h
  · constructor
    · change deriv (fun z => y * Real.sin z * Real.exp y) x = y * Real.cos x * Real.exp y
      exact (((Real.hasDerivAt_sin x).const_mul y).mul_const _).deriv
    · change deriv (fun z => z * Real.sin x * Real.exp z) y =
        (1 + y) * Real.sin x * Real.exp y
      have h := (hasDerivAt_affine_times_exp 0 1 (Real.sin x) y).deriv
      rw [show (0 : ℝ) + 1 * y + 1 = 1 + y by ring] at h
      simpa only [one_mul, zero_add] using h

theorem biotRepeatedGradient_trace (x y : ℝ) : (biotRepeatedGradient x y).trace = 0 := by
  change -(1 + y) * Real.sin x * Real.exp y + ((1 + y) * Real.sin x * Real.exp y + 0) = 0
  ring

/-- The generalized mode also vanishes at infinite depth. -/
theorem biotRepeatedDisplacement_tendsto_zero (x : ℝ) :
    Tendsto (fun y => biotRepeatedDisplacement x y) atBot (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_neg_atBot_atTop : Tendsto (fun y : ℝ => -y) atBot atTop)
  have hy : Tendsto (fun y : ℝ => y * Real.exp y) atBot (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, neg_neg, neg_mul, neg_zero] using h.neg
  have h₀ : Tendsto (fun y => (1 + y) * Real.cos x * Real.exp y) atBot (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.add hy).const_mul (Real.cos x)
    have he : (fun y => Real.cos x * (Real.exp y + y * Real.exp y)) =
        fun y => (1 + y) * Real.cos x * Real.exp y := by funext y; ring
    simpa only [he, add_zero, mul_zero] using h
  have h₁ : Tendsto (fun y => y * Real.sin x * Real.exp y) atBot (𝓝 0) := by
    have he : (fun y => Real.sin x * (y * Real.exp y)) =
        fun y => y * Real.sin x * Real.exp y := by funext y; ring
    simpa only [he, mul_zero] using hy.const_mul (Real.sin x)
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact h₀
  · exact h₁

theorem biotRepeatedStress_divergence (x y : ℝ) :
    (deriv (fun z => biotRepeatedStress z y 0 0) x +
        deriv (fun z => biotRepeatedStress x z 0 1) y = 0) ∧
    (deriv (fun z => biotRepeatedStress z y 1 0) x +
        deriv (fun z => biotRepeatedStress x z 1 1) y = 0) := by
  have e₀ (z : ℝ) : biotRepeatedStress z y 0 0 = (-4 - 2 * y) * Real.sin z * Real.exp y :=
    congrArg (fun M : Tensor 2 => M 0 0) (biotRepeatedStress_components z y)
  have e₁ (z : ℝ) : biotRepeatedStress x z 0 1 = (2 + 2 * z) * Real.cos x * Real.exp z :=
    congrArg (fun M : Tensor 2 => M 0 1) (biotRepeatedStress_components x z)
  have e₂ (z : ℝ) : biotRepeatedStress z y 1 0 = (2 + 2 * y) * Real.cos z * Real.exp y :=
    congrArg (fun M : Tensor 2 => M 1 0) (biotRepeatedStress_components z y)
  have e₃ (z : ℝ) : biotRepeatedStress x z 1 1 = (2 * z) * Real.sin x * Real.exp z :=
    congrArg (fun M : Tensor 2 => M 1 1) (biotRepeatedStress_components x z)
  have h₀ := (((Real.hasDerivAt_sin x).const_mul (-4 - 2 * y)).mul_const (Real.exp y)).deriv
  have h₁ := (hasDerivAt_affine_times_exp 2 2 (Real.cos x) y).deriv
  have h₂ := (((Real.hasDerivAt_cos x).const_mul (2 + 2 * y)).mul_const (Real.exp y)).deriv
  have h₃ := (hasDerivAt_affine_times_exp 0 2 (Real.sin x) y).deriv
  have h₃' : deriv (fun z => (2 * z) * Real.sin x * Real.exp z) y =
      (2 * y + 2) * Real.sin x * Real.exp y := by
    simpa only [zero_add] using h₃
  simp only [e₀, e₁, e₂, e₃, h₀, h₁, h₂, h₃']
  constructor <;> ring

/-- At the repeated root the two independent profiles have surface
traction amplitudes (2, 2) and (2, 0). Their combination cannot give
a nonzero traction-free mode. -/
theorem biot_repeated_freeSurface_trivial (A B : ℝ)
    (h : ∀ x : ℝ, (biotModeStress 1 1 A 0 x 0 + B • biotRepeatedStress x 0) 0 1 = 0 ∧
      (biotModeStress 1 1 A 0 x 0 + B • biotRepeatedStress x 0) 1 1 = 0) :
    A = 0 ∧ B = 0 := by
  have h₁ := (h 0).1
  have h₂ := (h (Real.pi / 2)).2
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, biotModeStress_components,
    biotRepeatedStress_components] at h₁ h₂
  change ((1 : ℝ) ^ 2 + 1) * A * Real.cos 0 * Real.exp (1 * 0) +
    B * ((2 + 2 * 0) * Real.cos 0 * Real.exp 0) = 0 at h₁
  change (2 * 1 * A - 0) * Real.sin (Real.pi / 2) * Real.exp (1 * 0) +
    B * ((2 * 0) * Real.sin (Real.pi / 2) * Real.exp 0) = 0 at h₂
  norm_num [Real.sin_pi_div_two] at h₁ h₂
  constructor <;> linarith

end

noncomputable section

/-- Normalized stress for a general unit-wavenumber depth profile.
The displacement is (f′(y) cos x, f(y) sin x). -/
def biotProfileStress (stretch : ℝ) (f f₁ f₂ p : ℝ → ℝ) (x y : ℝ) : Tensor 2 :=
  !![(-(1 + stretch ^ 4) * f₁ y - p y) * Real.sin x,
      (f₂ y + f y) * Real.cos x;
    (stretch ^ 4 * f y + f₂ y) * Real.cos x,
      (2 * f₁ y - p y) * Real.sin x]

/-- Differentiating the stress of a general Fourier profile reduces both
momentum equations to scalar equations in depth. -/
theorem biotProfileStress_divergence (stretch : ℝ) (f f₁ f₂ f₃ p : ℝ → ℝ) (x y pdot : ℝ)
    (h₀ : HasDerivAt f (f₁ y) y) (h₁ : HasDerivAt f₁ (f₂ y) y)
    (h₂ : HasDerivAt f₂ (f₃ y) y) (hp : HasDerivAt p pdot y) :
    (deriv (fun z => biotProfileStress stretch f f₁ f₂ p z y 0 0) x +
        deriv (fun z => biotProfileStress stretch f f₁ f₂ p x z 0 1) y =
      (f₃ y - stretch ^ 4 * f₁ y - p y) * Real.cos x) ∧
    (deriv (fun z => biotProfileStress stretch f f₁ f₂ p z y 1 0) x +
        deriv (fun z => biotProfileStress stretch f f₁ f₂ p x z 1 1) y =
      (f₂ y - stretch ^ 4 * f y - pdot) * Real.sin x) := by
  have h00 := ((Real.hasDerivAt_sin x).const_mul (-(1 + stretch ^ 4) * f₁ y - p y)).deriv
  have h01 := ((h₂.add h₀).mul_const (Real.cos x)).deriv
  have h10 := ((Real.hasDerivAt_cos x).const_mul (stretch ^ 4 * f y + f₂ y)).deriv
  have h11 := (((h₁.const_mul (2 : ℝ)).sub hp).mul_const (Real.sin x)).deriv
  constructor
  · change deriv (fun z => (-(1 + stretch ^ 4) * f₁ y - p y) * Real.sin z) x +
      deriv (fun z => (f₂ z + f z) * Real.cos x) y = _
    change deriv (fun z => (f₂ z + f z) * Real.cos x) y = _ at h01
    rw [h00, h01]
    ring
  · change deriv (fun z => (stretch ^ 4 * f y + f₂ y) * Real.cos z) x +
      deriv (fun z => (2 * f₁ z - p z) * Real.sin x) y = _
    change deriv (fun z => (2 * f₁ z - p z) * Real.sin x) y = _ at h11
    rw [h10, h11]
    ring

/-- Vanishing divergence for all horizontal positions at a given depth is
equivalent to the two pressure–profile equations. -/
theorem biotProfile_equilibrium_iff (stretch : ℝ) (f f₁ f₂ f₃ p : ℝ → ℝ) (y pdot : ℝ)
    (h₀ : HasDerivAt f (f₁ y) y) (h₁ : HasDerivAt f₁ (f₂ y) y)
    (h₂ : HasDerivAt f₂ (f₃ y) y) (hp : HasDerivAt p pdot y) :
    (∀ x : ℝ,
      (deriv (fun z => biotProfileStress stretch f f₁ f₂ p z y 0 0) x +
        deriv (fun z => biotProfileStress stretch f f₁ f₂ p x z 0 1) y = 0) ∧
      (deriv (fun z => biotProfileStress stretch f f₁ f₂ p z y 1 0) x +
        deriv (fun z => biotProfileStress stretch f f₁ f₂ p x z 1 1) y = 0)) ↔
      p y = f₃ y - stretch ^ 4 * f₁ y ∧ pdot = f₂ y - stretch ^ 4 * f y := by
  have hd (x : ℝ) := biotProfileStress_divergence stretch f f₁ f₂ f₃ p x y pdot h₀ h₁ h₂ hp
  constructor
  · intro h
    have he := ((hd 0).1).symm.trans (h 0).1
    have hf := ((hd (Real.pi / 2)).2).symm.trans (h (Real.pi / 2)).2
    simp only [Real.cos_zero, mul_one] at he
    simp only [Real.sin_pi_div_two, mul_one] at hf
    exact ⟨(sub_eq_zero.mp he).symm, (sub_eq_zero.mp hf).symm⟩
  · rintro ⟨he, hf⟩ x
    exact ⟨(hd x).1.trans (by rw [he, sub_self, zero_mul]),
      (hd x).2.trans (by rw [hf, sub_self, zero_mul])⟩

/-- Eliminating pressure from the Fourier equations gives the fourth-order
depth equation. The pressure reconstruction has the converse implication. -/
theorem biotProfile_pressure_elimination (stretch : ℝ) (f f₁ f₂ f₃ p : ℝ → ℝ)
    (y f₄ : ℝ) (h₁ : HasDerivAt f₁ (f₂ y) y) (h₃ : HasDerivAt f₃ f₄ y)
    (hPressure : p = fun z => f₃ z - stretch ^ 4 * f₁ z) :
    HasDerivAt p (f₂ y - stretch ^ 4 * f y) y ↔
      f₄ - (1 + stretch ^ 4) * f₂ y + stretch ^ 4 * f y = 0 := by
  have hd := h₃.sub (h₁.const_mul (stretch ^ 4))
  change HasDerivAt (fun z => f₃ z - stretch ^ 4 * f₁ z) (f₄ - stretch ^ 4 * f₂ y) y at hd
  rw [← hPressure] at hd
  constructor
  · intro h
    linear_combination hd.unique h
  · intro h
    have he : f₄ - stretch ^ 4 * f₂ y = f₂ y - stretch ^ 4 * f y := by
      linear_combination h
    rwa [he] at hd

/-- The depth equation factors into the two second-order operators,
including the squared factor at the repeated root. -/
theorem biotProfile_depth_operator_factor (stretch f f₂ f₄ : ℝ) :
    f₄ - (1 + stretch ^ 4) * f₂ + stretch ^ 4 * f =
      (f₄ - stretch ^ 4 * f₂) - (f₂ - stretch ^ 4 * f) := by ring

/-- With the reconstructed pressure, the free-surface conditions on an
arbitrary profile are f″ + f = 0 and f‴ = (2 + λ⁴) f′ at depth zero. -/
theorem biotProfile_freeSurface_iff (stretch : ℝ) (f f₁ f₂ f₃ p : ℝ → ℝ)
    (hp : p 0 = f₃ 0 - stretch ^ 4 * f₁ 0) :
    (∀ x : ℝ, biotProfileStress stretch f f₁ f₂ p x 0 0 1 = 0 ∧
      biotProfileStress stretch f f₁ f₂ p x 0 1 1 = 0) ↔
      f₂ 0 + f 0 = 0 ∧ f₃ 0 = (2 + stretch ^ 4) * f₁ 0 := by
  constructor
  · intro h
    have h₁ := (h 0).1
    have h₂ := (h (Real.pi / 2)).2
    change (f₂ 0 + f 0) * Real.cos 0 = 0 at h₁
    change (2 * f₁ 0 - p 0) * Real.sin (Real.pi / 2) = 0 at h₂
    rw [Real.cos_zero, mul_one] at h₁
    rw [Real.sin_pi_div_two, mul_one, hp] at h₂
    exact ⟨h₁, by linear_combination -h₂⟩
  · rintro ⟨h₁, h₂⟩ x
    change (f₂ 0 + f 0) * Real.cos x = 0 ∧ (2 * f₁ 0 - p 0) * Real.sin x = 0
    have he : 2 * f₁ 0 - p 0 = 0 := by rw [hp]; linear_combination -h₂
    rw [h₁, he, zero_mul, zero_mul]
    exact ⟨rfl, rfl⟩

end

private theorem biot_firstOrder_profile (f : ℝ → ℝ) (k : ℝ)
    (hf : ∀ y < 0, HasDerivAt f (k * f y) y) :
    ∃ A : ℝ, ∀ y < 0, f y = A * Real.exp (k * y) := by
  let g (y : ℝ) := f y * Real.exp (-k * y)
  have hg (y : ℝ) (hy : y < 0) : HasDerivAt g 0 y := by
    have h := (hf y hy).mul (hasDerivAt_biotExp (-k) y)
    change HasDerivAt g
      (k * f y * Real.exp (-k * y) + f y * (Real.exp (-k * y) * -k)) y at h
    convert h using 1
    ring
  let A := g (-1)
  have he : EqOn g (fun _ => A) (Iio 0) :=
    isOpen_Iio.eqOn_of_deriv_eq isPreconnected_Iio
      (fun y hy => (hg y hy).differentiableAt.differentiableWithinAt)
      (differentiableOn_const A)
      (fun y hy => by rw [(hg y hy).deriv, deriv_const])
      (show (-1 : ℝ) ∈ Iio 0 by norm_num) rfl
  refine ⟨A, fun y hy => ?_⟩
  have he' : f y * Real.exp (-k * y) = A := he hy
  calc
    f y = (f y * Real.exp (-k * y)) * Real.exp (k * y) := by
      rw [mul_assoc, ← Real.exp_add, show -k * y + k * y = 0 by ring, Real.exp_zero, mul_one]
    _ = _ := by rw [he']

/-- All solutions of the second-order constant-coefficient depth equation
on the open half-space are combinations of its two exponential profiles. -/
theorem biot_secondOrder_profiles (f f₁ : ℝ → ℝ) (k : ℝ) (hk : k ≠ 0)
    (h₀ : ∀ y < 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y < 0, HasDerivAt f₁ (k ^ 2 * f y) y) :
    ∃ A B : ℝ, ∀ y < 0, f y = A * Real.exp (k * y) + B * Real.exp (-k * y) := by
  let g (y : ℝ) := f₁ y + k * f y
  let h (y : ℝ) := f₁ y - k * f y
  have hg (y : ℝ) (hy : y < 0) : HasDerivAt g (k * g y) y := by
    have hd := (h₁ y hy).add ((h₀ y hy).const_mul k)
    change HasDerivAt g (k ^ 2 * f y + k * f₁ y) y at hd
    convert hd using 1
    dsimp only [g]
    ring
  have hh (y : ℝ) (hy : y < 0) : HasDerivAt h (-k * h y) y := by
    have hd := (h₁ y hy).sub ((h₀ y hy).const_mul k)
    change HasDerivAt h (k ^ 2 * f y - k * f₁ y) y at hd
    convert hd using 1
    dsimp only [h]
    ring
  obtain ⟨A, hA⟩ := biot_firstOrder_profile g k hg
  obtain ⟨B, hB⟩ := biot_firstOrder_profile h (-k) hh
  refine ⟨A / (2 * k), -B / (2 * k), fun y hy => ?_⟩
  have heA := hA y hy
  have heB := hB y hy
  dsimp only [g] at heA
  dsimp only [h] at heB
  rw [neg_mul] at heB
  field_simp
  linear_combination heA - heB

/-- For distinct depth roots, the fourth-order Fourier equation has
exactly the four exponential profiles as its solution form. -/
theorem biot_fourthOrder_profiles (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (k : ℝ)
    (hk : k ≠ 0) (hk₁ : k ^ 2 ≠ 1)
    (h₀ : ∀ y < 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y < 0, HasDerivAt f₁ (f₂ y) y)
    (h₂ : ∀ y < 0, HasDerivAt f₂ (f₃ y) y)
    (h₃ : ∀ y < 0, HasDerivAt f₃ (f₄ y) y)
    (hODE : ∀ y < 0, f₄ y - (1 + k ^ 2) * f₂ y + k ^ 2 * f y = 0) :
    ∃ A B C D : ℝ, ∀ y < 0, f y =
      A * Real.exp y + B * Real.exp (-y) + (C * Real.exp (k * y) + D * Real.exp (-k * y)) := by
  have hPair (c : ℝ) (y : ℝ) (hy : y < 0) :
      HasDerivAt (fun z => f₂ z - c * f z) (f₃ y - c * f₁ y) y ∧
      HasDerivAt (fun z => f₃ z - c * f₁ z) (f₄ y - c * f₂ y) y := by
    exact ⟨(h₂ y hy).sub ((h₀ y hy).const_mul c), (h₃ y hy).sub ((h₁ y hy).const_mul c)⟩
  have hg (y : ℝ) (hy : y < 0) :
      HasDerivAt (fun z => f₃ z - k ^ 2 * f₁ z) (1 ^ 2 * (f₂ y - k ^ 2 * f y)) y := by
    have he : f₄ y - k ^ 2 * f₂ y = 1 ^ 2 * (f₂ y - k ^ 2 * f y) := by
      linear_combination hODE y hy
    rw [← he]
    exact (hPair (k ^ 2) y hy).2
  have hh (y : ℝ) (hy : y < 0) :
      HasDerivAt (fun z => f₃ z - 1 * f₁ z) (k ^ 2 * (f₂ y - 1 * f y)) y := by
    have he : f₄ y - 1 * f₂ y = k ^ 2 * (f₂ y - 1 * f y) := by
      linear_combination hODE y hy
    rw [← he]
    exact (hPair 1 y hy).2
  obtain ⟨A, B, hAB⟩ := biot_secondOrder_profiles _ _ 1 one_ne_zero
    (fun y hy => (hPair (k ^ 2) y hy).1) hg
  obtain ⟨C, D, hCD⟩ := biot_secondOrder_profiles _ _ k hk (fun y hy => (hPair 1 y hy).1) hh
  refine ⟨A / (1 - k ^ 2), B / (1 - k ^ 2), -C / (1 - k ^ 2), -D / (1 - k ^ 2), ?_⟩
  intro y hy
  have he₁ := hAB y hy
  have he₂ := hCD y hy
  simp only [one_mul, neg_one_mul] at he₁
  rw [neg_mul] at he₂
  field_simp [sub_ne_zero.mpr (Ne.symm hk₁)]
  linear_combination he₁ - he₂

/-- Decay at infinite depth removes both growing exponentials for the two
distinct positive exponents on the strictly compressed branch. -/
theorem biot_decaying_fourthOrder_profiles (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (k : ℝ)
    (hk : 0 < k) (hk₁ : k < 1)
    (h₀ : ∀ y < 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y < 0, HasDerivAt f₁ (f₂ y) y)
    (h₂ : ∀ y < 0, HasDerivAt f₂ (f₃ y) y)
    (h₃ : ∀ y < 0, HasDerivAt f₃ (f₄ y) y)
    (hODE : ∀ y < 0, f₄ y - (1 + k ^ 2) * f₂ y + k ^ 2 * f y = 0)
    (hDecay : Tendsto f atBot (𝓝 0)) :
    ∃ A C : ℝ, ∀ y < 0, f y = A * Real.exp y + C * Real.exp (k * y) := by
  have hSq : k ^ 2 ≠ 1 := by
    intro he
    nlinarith [mul_pos (sub_pos.mpr hk₁) (show 0 < 1 + k by positivity)]
  obtain ⟨A, B, C, D, h⟩ := biot_fourthOrder_profiles f f₁ f₂ f₃ f₄ k hk.ne' hSq
    h₀ h₁ h₂ h₃ hODE
  have hExp (c : ℝ) (hc : 0 < c) : Tendsto (fun y => Real.exp (c * y)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos hc).mpr tendsto_id)
  have hB : B = 0 := by
    let g (y : ℝ) := A * Real.exp (2 * y) + B +
      (C * Real.exp ((k + 1) * y) + D * Real.exp ((1 - k) * y))
    have hlim : Tendsto g atBot (𝓝 B) := by
      have hd := (((hExp 2 (by norm_num)).const_mul A).add
        (tendsto_const_nhds (x := B))).add
        (((hExp (k + 1) (by positivity)).const_mul C).add
          ((hExp (1 - k) (sub_pos.mpr hk₁)).const_mul D))
      simpa only [g, mul_zero, zero_add, add_zero] using hd
    have hlim₀ : Tendsto (fun y => f y * Real.exp y) atBot (𝓝 0) := by
      simpa only [mul_zero] using hDecay.mul Real.tendsto_exp_atBot
    have he : (fun y => f y * Real.exp y) =ᶠ[atBot] g := by
      filter_upwards [eventually_lt_atBot 0] with y hy
      rw [h y hy]
      calc
        _ = A * (Real.exp y * Real.exp y) + B * (Real.exp (-y) * Real.exp y) +
            (C * (Real.exp (k * y) * Real.exp y) + D * (Real.exp (-k * y) * Real.exp y)) := by ring
        _ = _ := by
          simp only [g, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one,
            show y + y = 2 * y by ring, show k * y + y = (k + 1) * y by ring,
            show -k * y + y = (1 - k) * y by ring]
    exact tendsto_nhds_unique hlim (hlim₀.congr' he)
  have hD : D = 0 := by
    let g (y : ℝ) := A * Real.exp ((1 + k) * y) + C * Real.exp ((2 * k) * y) + D
    have hlim : Tendsto g atBot (𝓝 D) := by
      have hd := (((hExp (1 + k) (by positivity)).const_mul A).add
        ((hExp (2 * k) (by positivity)).const_mul C)).add (tendsto_const_nhds (x := D))
      simpa only [g, mul_zero, zero_add] using hd
    have hlim₀ : Tendsto (fun y => f y * Real.exp (k * y)) atBot (𝓝 0) := by
      simpa only [mul_zero] using hDecay.mul (hExp k hk)
    have he : (fun y => f y * Real.exp (k * y)) =ᶠ[atBot] g := by
      filter_upwards [eventually_lt_atBot 0] with y hy
      rw [h y hy, hB, zero_mul, add_zero]
      calc
        _ = A * (Real.exp y * Real.exp (k * y)) + C * (Real.exp (k * y) * Real.exp (k * y)) +
            D * (Real.exp (-k * y) * Real.exp (k * y)) := by ring
        _ = _ := by
          simp only [g, ← Real.exp_add,
            show -k * y + k * y = 0 by ring, Real.exp_zero, mul_one,
            show y + k * y = (1 + k) * y by ring, show k * y + k * y = (2 * k) * y by ring]
    exact tendsto_nhds_unique hlim (hlim₀.congr' he)
  refine ⟨A, C, fun y hy => ?_⟩
  simpa only [hB, hD, zero_mul, add_zero] using h y hy

private theorem eq_rate_of_eqOn_depth {f g : ℝ → ℝ} {u v y : ℝ}
    (h : ∀ z < 0, f z = g z) (hy : y < 0) (hf : HasDerivAt f u y) (hg : HasDerivAt g v y) :
    u = v := by
  apply hf.unique
  apply hg.congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds hy] with z hz
  exact h z hz

private theorem eq_surface_of_eqOn_depth {f g : ℝ → ℝ}
    (h : ∀ z < 0, f z = g z) (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) :
    f 0 = g 0 := by
  have he : f =ᶠ[nhdsWithin (0 : ℝ) (Iio 0)] g := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h y hy
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.tendsto.mono_left nhdsWithin_le_nhds) (hg.tendsto.mono_left nhdsWithin_le_nhds) he

/-- For the strictly compressed single Fourier harmonic, every nonzero
decaying solution of the depth equation with free-surface conditions
forces the Biot quartic. No exponential ansatz is imposed on the profile. -/
theorem biot_quartic_of_decaying_depth_solution (stretch : ℝ) (hs : 0 < stretch) (hsc : stretch < 1)
    (f f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (h₀ : ∀ y ≤ 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y ≤ 0, HasDerivAt f₁ (f₂ y) y)
    (h₂ : ∀ y ≤ 0, HasDerivAt f₂ (f₃ y) y)
    (h₃ : ∀ y ≤ 0, HasDerivAt f₃ (f₄ y) y)
    (hODE : ∀ y < 0, f₄ y - (1 + stretch ^ 4) * f₂ y + stretch ^ 4 * f y = 0)
    (hDecay : Tendsto f atBot (𝓝 0)) (hNonzero : ∃ y < 0, f y ≠ 0)
    (hShear : f₂ 0 + f 0 = 0) (hNormal : f₃ 0 = (2 + stretch ^ 4) * f₁ 0) :
    stretch ^ 4 - 2 * stretch + 1 = 0 := by
  let k := stretch ^ 2
  have hk : 0 < k := pow_pos hs _
  have hk₁ : k < 1 := by
    dsimp only [k]
    nlinarith [mul_pos (sub_pos.mpr hsc) (show 0 < 1 + stretch by positivity)]
  have hk₂ : k ^ 2 = stretch ^ 4 := by dsimp only [k]; ring
  obtain ⟨A, B, hRep⟩ := biot_decaying_fourthOrder_profiles f f₁ f₂ f₃ f₄ k hk hk₁
    (fun y hy => h₀ y hy.le) (fun y hy => h₁ y hy.le) (fun y hy => h₂ y hy.le)
    (fun y hy => h₃ y hy.le) (by simpa only [hk₂] using hODE) hDecay
  let g (j : ℕ) (y : ℝ) := A * Real.exp y + (B * k ^ j) * Real.exp (k * y)
  have hg (j : ℕ) (y : ℝ) : HasDerivAt (g j) (g (j + 1) y) y := by
    have h := ((Real.hasDerivAt_exp y).const_mul A).add
      ((hasDerivAt_biotExp k y).const_mul (B * k ^ j))
    change HasDerivAt (g j) (A * Real.exp y + (B * k ^ j) * (Real.exp (k * y) * k)) y at h
    have he : A * Real.exp y + (B * k ^ j) * (Real.exp (k * y) * k) = g (j + 1) y := by
      dsimp only [g]
      rw [pow_succ]
      ring
    rwa [he] at h
  have hEq₀ (y : ℝ) (hy : y < 0) : f y = g 0 y := by simpa [g] using hRep y hy
  have hEq₁ (y : ℝ) (hy : y < 0) : f₁ y = g 1 y :=
    eq_rate_of_eqOn_depth hEq₀ hy (h₀ y hy.le) (hg 0 y)
  have hEq₂ (y : ℝ) (hy : y < 0) : f₂ y = g 2 y :=
    eq_rate_of_eqOn_depth hEq₁ hy (h₁ y hy.le) (hg 1 y)
  have hEq₃ (y : ℝ) (hy : y < 0) : f₃ y = g 3 y :=
    eq_rate_of_eqOn_depth hEq₂ hy (h₂ y hy.le) (hg 2 y)
  have hs₀ := eq_surface_of_eqOn_depth hEq₀ (h₀ 0 le_rfl).continuousAt (hg 0 0).continuousAt
  have hs₁ := eq_surface_of_eqOn_depth hEq₁ (h₁ 0 le_rfl).continuousAt (hg 1 0).continuousAt
  have hs₂ := eq_surface_of_eqOn_depth hEq₂ (h₂ 0 le_rfl).continuousAt (hg 2 0).continuousAt
  have hs₃ := eq_surface_of_eqOn_depth hEq₃ (h₃ 0 le_rfl).continuousAt (hg 3 0).continuousAt
  rw [hs₂, hs₀] at hShear
  rw [hs₃, hs₁] at hNormal
  simp only [g, mul_zero, Real.exp_zero, mul_one, pow_zero, pow_one] at hShear hNormal
  have hAmp : A ≠ 0 ∨ B ≠ 0 := by
    obtain ⟨y, hy, hz⟩ := hNonzero
    by_contra! h
    exact hz (by simpa only [h.1, h.2, zero_mul, add_zero] using hRep y hy)
  apply (biot_freeSurface_nontrivial_iff stretch hs).mp
  refine ⟨A, B, hAmp, ?_, ?_⟩
  · rw [← hk₂]
    linear_combination hShear
  · rw [← hk₂] at hNormal ⊢
    change (1 + k ^ 2) * A + 2 * k * B = 0
    linear_combination -hNormal

private theorem hasDerivAt_affine_times_scaled_exp (a b k y : ℝ) :
    HasDerivAt (fun z => (a + b * z) * Real.exp (k * z))
      ((b + k * (a + b * y)) * Real.exp (k * y)) y := by
  have h := (((hasDerivAt_id y).const_mul b).const_add a).mul (hasDerivAt_biotExp k y)
  change HasDerivAt (fun z => (a + b * z) * Real.exp (k * z))
    (b * 1 * Real.exp (k * y) + (a + b * y) * (Real.exp (k * y) * k)) y at h
  convert h using 1
  ring

/-- Every solution of the repeated-root depth equation has two affine
coefficients, one multiplying each of exp(y) and exp(−y). -/
theorem biot_repeated_fourthOrder_profiles (f f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (h₀ : ∀ y < 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y < 0, HasDerivAt f₁ (f₂ y) y)
    (h₂ : ∀ y < 0, HasDerivAt f₂ (f₃ y) y)
    (h₃ : ∀ y < 0, HasDerivAt f₃ (f₄ y) y)
    (hODE : ∀ y < 0, f₄ y - 2 * f₂ y + f y = 0) :
    ∃ A B C D : ℝ, ∀ y < 0, f y =
      (A + B * y) * Real.exp y + (C + D * y) * Real.exp (-y) := by
  have hg₀ (y : ℝ) (hy : y < 0) :
      HasDerivAt (fun z => f₂ z - f z) (f₃ y - f₁ y) y :=
    (h₂ y hy).sub (h₀ y hy)
  have hg₁ (y : ℝ) (hy : y < 0) :
      HasDerivAt (fun z => f₃ z - f₁ z) ((1 : ℝ) ^ 2 * (f₂ y - f y)) y := by
    have he : f₄ y - f₂ y = (1 : ℝ) ^ 2 * (f₂ y - f y) := by
      linear_combination hODE y hy
    rw [← he]
    exact (h₃ y hy).sub (h₁ y hy)
  obtain ⟨U, V, hUV⟩ := biot_secondOrder_profiles _ _ 1 one_ne_zero hg₀ hg₁
  let b := U / 2
  let d := -V / 2
  let q (y : ℝ) := (b * y) * Real.exp y + (d * y) * Real.exp (-y)
  let q₁ (y : ℝ) := (b + b * y) * Real.exp y + (d - d * y) * Real.exp (-y)
  have hq₀ (y : ℝ) : HasDerivAt q (q₁ y) y := by
    have h := (hasDerivAt_affine_times_scaled_exp 0 b 1 y).add
      (hasDerivAt_affine_times_scaled_exp 0 d (-1) y)
    simp only [zero_add, one_mul, neg_one_mul, ← sub_eq_add_neg] at h
    exact h
  have hq₁ (y : ℝ) : HasDerivAt q₁ (q y + U * Real.exp y + V * Real.exp (-y)) y := by
    have h := (hasDerivAt_affine_times_scaled_exp b b 1 y).add
      (hasDerivAt_affine_times_scaled_exp d (-d) (-1) y)
    simp only [one_mul, neg_mul] at h
    have he : q₁ = fun z => (b + b * z) * Real.exp z + (d + -(d * z)) * Real.exp (-z) := by
      funext z
      simp only [q₁, sub_eq_add_neg]
    rw [he]
    convert h using 1
    dsimp only [q, b, d]
    ring
  have hh₀ (y : ℝ) (hy : y < 0) :
      HasDerivAt (fun z => f z - q z) (f₁ y - q₁ y) y := (h₀ y hy).sub (hq₀ y)
  have hh₁ (y : ℝ) (hy : y < 0) :
      HasDerivAt (fun z => f₁ z - q₁ z) ((1 : ℝ) ^ 2 * (f y - q y)) y := by
    have h := (h₁ y hy).sub (hq₁ y)
    have he := hUV y hy
    simp only [one_mul, neg_one_mul] at he
    have he' : f₂ y - (q y + U * Real.exp y + V * Real.exp (-y)) =
        (1 : ℝ) ^ 2 * (f y - q y) := by linear_combination he
    rw [← he']
    exact h
  obtain ⟨A, C, hAC⟩ := biot_secondOrder_profiles _ _ 1 one_ne_zero hh₀ hh₁
  refine ⟨A, b, C, d, fun y hy => ?_⟩
  have h := hAC y hy
  simp only [one_mul, neg_one_mul] at h
  dsimp only [q] at h
  linear_combination h

/-- The growing affine-exponential branch is excluded by decay. -/
theorem biot_repeated_decaying_profiles (f f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (h₀ : ∀ y < 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y < 0, HasDerivAt f₁ (f₂ y) y)
    (h₂ : ∀ y < 0, HasDerivAt f₂ (f₃ y) y)
    (h₃ : ∀ y < 0, HasDerivAt f₃ (f₄ y) y)
    (hODE : ∀ y < 0, f₄ y - 2 * f₂ y + f y = 0)
    (hDecay : Tendsto f atBot (𝓝 0)) :
    ∃ A B : ℝ, ∀ y < 0, f y = (A + B * y) * Real.exp y := by
  obtain ⟨A, B, C, D, hRep⟩ := biot_repeated_fourthOrder_profiles f f₁ f₂ f₃ f₄ h₀ h₁ h₂ h₃ hODE
  have hScale : Tendsto (fun y : ℝ => 2 * y) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have hExp : Tendsto (fun y : ℝ => Real.exp (2 * y)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hScale
  have hpoly := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_neg_atBot_atTop : Tendsto (fun y : ℝ => -y) atBot atTop)
  have hy : Tendsto (fun y : ℝ => y * Real.exp y) atBot (𝓝 0) := by
    simpa only [Function.comp_apply, pow_one, neg_neg, neg_mul, neg_zero] using hpoly.neg
  have hY : Tendsto (fun y : ℝ => y * Real.exp (2 * y)) atBot (𝓝 0) := by
    have h := (hy.comp hScale).const_mul (1 / 2 : ℝ)
    have he (y : ℝ) : (1 / 2 : ℝ) * ((2 * y) * Real.exp (2 * y)) = y * Real.exp (2 * y) := by ring
    simpa only [Function.comp_apply, he, mul_zero] using h
  have hA : Tendsto (fun y : ℝ => (A + B * y) * Real.exp (2 * y)) atBot (𝓝 0) := by
    simpa only [← mul_assoc, ← add_mul, mul_zero, add_zero] using
      (hExp.const_mul A).add (hY.const_mul B)
  have hF : Tendsto (fun y => f y * Real.exp y) atBot (𝓝 0) := by
    simpa only [mul_zero] using hDecay.mul Real.tendsto_exp_atBot
  have hAff : Tendsto (fun y : ℝ => C + D * y) atBot (𝓝 0) := by
    have h := hF.sub hA
    rw [sub_self] at h
    apply h.congr'
    filter_upwards [eventually_lt_atBot 0] with y hy'
    rw [hRep y hy']
    have he : Real.exp y * Real.exp y = Real.exp (2 * y) := by
      rw [← Real.exp_add, two_mul]
    have hn : Real.exp (-y) * Real.exp y = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      _ = (A + B * y) * (Real.exp y * Real.exp y) +
          (C + D * y) * (Real.exp (-y) * Real.exp y) -
          (A + B * y) * Real.exp (2 * y) := by ring
      _ = _ := by rw [he, hn, mul_one]; ring
  have hShift : Tendsto (fun y : ℝ => y + (-1)) atBot atBot :=
    tendsto_atBot_add_const_right _ (-1) tendsto_id
  have hD : D = 0 := by
    have hd := hAff.sub (hAff.comp hShift)
    have he : Tendsto (fun _ : ℝ => D) atBot (𝓝 0) := by
      rw [sub_self] at hd
      apply hd.congr
      intro y
      change (C + D * y) - (C + D * (y + -1)) = D
      ring
    exact tendsto_nhds_unique tendsto_const_nhds he
  have hC : C = 0 := by
    have he : Tendsto (fun _ : ℝ => C) atBot (𝓝 0) := by
      simpa only [hD, zero_mul, add_zero] using hAff
    exact tendsto_nhds_unique tendsto_const_nhds he
  refine ⟨A, B, fun y hy' => ?_⟩
  simpa only [hC, hD, zero_mul, add_zero] using hRep y hy'

/-- At unit stretch the general decaying single-harmonic depth solution
with vanishing surface traction is zero on the whole half-space. -/
theorem biot_repeated_depth_solution_trivial (f f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (h₀ : ∀ y ≤ 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y ≤ 0, HasDerivAt f₁ (f₂ y) y)
    (h₂ : ∀ y ≤ 0, HasDerivAt f₂ (f₃ y) y)
    (h₃ : ∀ y ≤ 0, HasDerivAt f₃ (f₄ y) y)
    (hODE : ∀ y < 0, f₄ y - 2 * f₂ y + f y = 0)
    (hDecay : Tendsto f atBot (𝓝 0))
    (hShear : f₂ 0 + f 0 = 0) (hNormal : f₃ 0 = 3 * f₁ 0) :
    ∀ y ≤ 0, f y = 0 := by
  obtain ⟨A, B, hRep⟩ := biot_repeated_decaying_profiles f f₁ f₂ f₃ f₄
    (fun y hy => h₀ y hy.le) (fun y hy => h₁ y hy.le)
    (fun y hy => h₂ y hy.le) (fun y hy => h₃ y hy.le) hODE hDecay
  let g (j : ℕ) (y : ℝ) := (A + B * (y + (j : ℝ))) * Real.exp y
  have hg (j : ℕ) (y : ℝ) : HasDerivAt (g j) (g (j + 1) y) y := by
    have h := hasDerivAt_affine_times_exp (A + B * (j : ℝ)) B 1 y
    have he : (fun z => (A + B * (j : ℝ) + B * z) * 1 * Real.exp z) = g j := by
      funext z
      dsimp only [g]
      ring
    rw [he] at h
    convert h using 1
    simp only [g, Nat.cast_add, Nat.cast_one, mul_one]
    ring
  have h0 (y : ℝ) (hy : y < 0) : f y = g 0 y := by simpa [g] using hRep y hy
  have h1 (y : ℝ) (hy : y < 0) : f₁ y = g 1 y :=
    eq_rate_of_eqOn_depth h0 hy (h₀ y hy.le) (hg 0 y)
  have h2 (y : ℝ) (hy : y < 0) : f₂ y = g 2 y :=
    eq_rate_of_eqOn_depth h1 hy (h₁ y hy.le) (hg 1 y)
  have h3 (y : ℝ) (hy : y < 0) : f₃ y = g 3 y :=
    eq_rate_of_eqOn_depth h2 hy (h₂ y hy.le) (hg 2 y)
  have hs₀ := eq_surface_of_eqOn_depth h0 (h₀ 0 le_rfl).continuousAt (hg 0 0).continuousAt
  have hs₁ := eq_surface_of_eqOn_depth h1 (h₁ 0 le_rfl).continuousAt (hg 1 0).continuousAt
  have hs₂ := eq_surface_of_eqOn_depth h2 (h₂ 0 le_rfl).continuousAt (hg 2 0).continuousAt
  have hs₃ := eq_surface_of_eqOn_depth h3 (h₃ 0 le_rfl).continuousAt (hg 3 0).continuousAt
  rw [hs₂, hs₀] at hShear
  rw [hs₃, hs₁] at hNormal
  norm_num [g, Real.exp_zero] at hShear hNormal
  have ha : A = 0 := by linarith
  have hb : B = 0 := by linarith
  intro y hy
  rcases hy.lt_or_eq with ht | rfl
  · simpa only [ha, hb, zero_mul, add_zero] using hRep y ht
  · simp only [hs₀, g, ha, hb, zero_mul, add_zero]

/-- The dimensional profile equations at wavenumber k eliminate the pressure
in favor of the fourth-order depth equation with factors k² and λ⁴k². -/
theorem biot_wavenumber_pressure_elimination (stretch k : ℝ) (f f₁ f₂ f₃ p : ℝ → ℝ)
    (y f₄ : ℝ) (hk : k ≠ 0)
    (h₁ : HasDerivAt f₁ (f₂ y) y) (h₃ : HasDerivAt f₃ f₄ y)
    (hPressure : p = fun z => (f₃ z - stretch ^ 4 * k ^ 2 * f₁ z) / k) :
    HasDerivAt p (k * (f₂ y - stretch ^ 4 * k ^ 2 * f y)) y ↔
      f₄ - (1 + stretch ^ 4) * k ^ 2 * f₂ y + stretch ^ 4 * k ^ 4 * f y = 0 := by
  have hd := (h₃.sub (h₁.const_mul (stretch ^ 4 * k ^ 2))).div_const k
  change HasDerivAt (fun z => (f₃ z - stretch ^ 4 * k ^ 2 * f₁ z) / k)
    ((f₄ - stretch ^ 4 * k ^ 2 * f₂ y) / k) y at hd
  rw [← hPressure] at hd
  constructor
  · intro h
    have he := (div_eq_iff hk).mp (hd.unique h)
    linear_combination he
  · intro h
    have he : (f₄ - stretch ^ 4 * k ^ 2 * f₂ y) / k =
        k * (f₂ y - stretch ^ 4 * k ^ 2 * f y) := by
      apply (div_eq_iff hk).mpr
      linear_combination h
    rwa [he] at hd

private noncomputable def rescaledBiotDepth (k : ℝ) (j : ℕ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  f (k⁻¹ * z) / k ^ j

private theorem hasDerivAt_rescaledBiotDepth (k : ℝ) (hk : k ≠ 0) (j : ℕ)
    {f : ℝ → ℝ} {z f' : ℝ} (hf : HasDerivAt f f' (k⁻¹ * z)) :
    HasDerivAt (rescaledBiotDepth k j f) (f' / k ^ (j + 1)) z := by
  have hz : HasDerivAt (fun y : ℝ => k⁻¹ * y) k⁻¹ z := by
    have hd := (hasDerivAt_id z).const_mul k⁻¹
    change HasDerivAt (fun y : ℝ => k⁻¹ * y) (k⁻¹ * 1) z at hd
    rwa [mul_one] at hd
  have hd := (hf.comp z hz).div_const (k ^ j)
  have he : f' * k⁻¹ / k ^ j = f' / k ^ (j + 1) := by
    rw [pow_succ]
    field_simp
  rw [he] at hd
  exact hd

/-- The strictly compressed branch and the repeated root are covered by the
same rescaling. A nonzero decaying free-surface profile with k > 0 forces
strict compression and the original wavenumber-independent quartic. -/
theorem biot_quartic_of_positiveWavenumber_profile
    (stretch k : ℝ) (hs : 0 < stretch) (hc : stretch ≤ 1) (hk : 0 < k)
    (f f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (h₀ : ∀ y ≤ 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y ≤ 0, HasDerivAt f₁ (f₂ y) y)
    (h₂ : ∀ y ≤ 0, HasDerivAt f₂ (f₃ y) y)
    (h₃ : ∀ y ≤ 0, HasDerivAt f₃ (f₄ y) y)
    (hODE : ∀ y < 0, f₄ y - (1 + stretch ^ 4) * k ^ 2 * f₂ y + stretch ^ 4 * k ^ 4 * f y = 0)
    (hDecay : Tendsto f atBot (𝓝 0)) (hNonzero : ∃ y < 0, f y ≠ 0)
    (hShear : f₂ 0 + k ^ 2 * f 0 = 0) (hNormal : f₃ 0 = (2 + stretch ^ 4) * k ^ 2 * f₁ 0) :
    stretch < 1 ∧ stretch ^ 4 - 2 * stretch + 1 = 0 := by
  let g := rescaledBiotDepth k 0 f
  let g₁ := rescaledBiotDepth k 1 f₁
  let g₂ := rescaledBiotDepth k 2 f₂
  let g₃ := rescaledBiotDepth k 3 f₃
  let g₄ := rescaledBiotDepth k 4 f₄
  have hnonpos (z : ℝ) (hz : z ≤ 0) : k⁻¹ * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hk).le hz
  have hneg (z : ℝ) (hz : z < 0) : k⁻¹ * z < 0 := mul_neg_of_pos_of_neg (inv_pos.mpr hk) hz
  have hg₀ (z : ℝ) (hz : z ≤ 0) : HasDerivAt g (g₁ z) z :=
    hasDerivAt_rescaledBiotDepth k hk.ne' 0 (h₀ _ (hnonpos z hz))
  have hg₁ (z : ℝ) (hz : z ≤ 0) : HasDerivAt g₁ (g₂ z) z :=
    hasDerivAt_rescaledBiotDepth k hk.ne' 1 (h₁ _ (hnonpos z hz))
  have hg₂ (z : ℝ) (hz : z ≤ 0) : HasDerivAt g₂ (g₃ z) z :=
    hasDerivAt_rescaledBiotDepth k hk.ne' 2 (h₂ _ (hnonpos z hz))
  have hg₃ (z : ℝ) (hz : z ≤ 0) : HasDerivAt g₃ (g₄ z) z :=
    hasDerivAt_rescaledBiotDepth k hk.ne' 3 (h₃ _ (hnonpos z hz))
  have hgODE (z : ℝ) (hz : z < 0) :
      g₄ z - (1 + stretch ^ 4) * g₂ z + stretch ^ 4 * g z = 0 := by
    dsimp only [g, g₂, g₄, rescaledBiotDepth]
    field_simp [hk.ne']
    have he := hODE _ (hneg z hz)
    rw [show k⁻¹ * z = z / k by rw [div_eq_mul_inv, mul_comm]] at he
    linear_combination he
  have hgShear : g₂ 0 + g 0 = 0 := by
    simp only [g, g₂, rescaledBiotDepth, mul_zero, pow_zero, div_one]
    field_simp [hk.ne']
    linear_combination hShear
  have hgNormal : g₃ 0 = (2 + stretch ^ 4) * g₁ 0 := by
    simp only [g₁, g₃, rescaledBiotDepth, mul_zero, pow_one]
    field_simp [hk.ne']
    linear_combination hNormal
  have hgDecay : Tendsto g atBot (𝓝 0) := by
    have he : g = f ∘ (fun z : ℝ => k⁻¹ * z) := by
      funext z
      simp [g, rescaledBiotDepth]
    rw [he]
    exact hDecay.comp ((tendsto_const_mul_atBot_of_pos (inv_pos.mpr hk)).mpr tendsto_id)
  have hgNonzero : ∃ z < 0, g z ≠ 0 := by
    obtain ⟨y, hy, hy'⟩ := hNonzero
    refine ⟨k * y, mul_neg_of_pos_of_neg hk hy, ?_⟩
    simpa only [g, rescaledBiotDepth, pow_zero, div_one, ← mul_assoc, inv_mul_cancel₀ hk.ne',
      one_mul] using hy'
  rcases hc.lt_or_eq with hst | hst
  · exact ⟨hst, biot_quartic_of_decaying_depth_solution stretch hs hst g g₁ g₂ g₃ g₄
      hg₀ hg₁ hg₂ hg₃ hgODE hgDecay hgNonzero hgShear hgNormal⟩
  · have hz := biot_repeated_depth_solution_trivial g g₁ g₂ g₃ g₄ hg₀ hg₁ hg₂ hg₃
      (by simpa only [hst, one_pow, show (1 : ℝ) + 1 = 2 by norm_num, one_mul] using hgODE) hgDecay hgShear
      (by simpa only [hst, one_pow, show (2 : ℝ) + 1 = 3 by norm_num] using hgNormal)
    obtain ⟨z, hz', hn⟩ := hgNonzero
    exact False.elim (hn (hz z hz'.le))

/-- A quartic root in strict compression produces a nonzero decaying
profile satisfying the free-surface conditions at every positive wavenumber. -/
theorem biot_exists_profile_of_quartic_positiveWavenumber
    (stretch k : ℝ) (hs : 0 < stretch) (hc : stretch < 1) (hk : 0 < k)
    (hRoot : stretch ^ 4 - 2 * stretch + 1 = 0) :
    ∃ f f₁ f₂ f₃ f₄ : ℝ → ℝ,
      (∀ y, HasDerivAt f (f₁ y) y) ∧
      (∀ y, HasDerivAt f₁ (f₂ y) y) ∧
      (∀ y, HasDerivAt f₂ (f₃ y) y) ∧
      (∀ y, HasDerivAt f₃ (f₄ y) y) ∧
      (∀ y, f₄ y - (1 + stretch ^ 4) * k ^ 2 * f₂ y + stretch ^ 4 * k ^ 4 * f y = 0) ∧
      Tendsto f atBot (𝓝 0) ∧ (∃ y < 0, f y ≠ 0) ∧
      f₂ 0 + k ^ 2 * f 0 = 0 ∧ f₃ 0 = (2 + stretch ^ 4) * k ^ 2 * f₁ 0 := by
  obtain ⟨A, B, hn, hShear, hNormal⟩ := (biot_freeSurface_nontrivial_iff stretch hs).mpr hRoot
  let g (j : ℕ) (y : ℝ) :=
    (A * k ^ j) * Real.exp (k * y) + (B * (k * stretch ^ 2) ^ j) * Real.exp (k * stretch ^ 2 * y)
  have hg (j : ℕ) (y : ℝ) : HasDerivAt (g j) (g (j + 1) y) y := by
    have h := ((hasDerivAt_biotExp k y).const_mul (A * k ^ j)).add
      ((hasDerivAt_biotExp (k * stretch ^ 2) y).const_mul (B * (k * stretch ^ 2) ^ j))
    change HasDerivAt (g j) _ y at h
    convert h using 1
    dsimp only [g]
    rw [pow_succ, pow_succ]
    ring
  refine ⟨g 0, g 1, g 2, g 3, g 4, hg 0, hg 1, hg 2, hg 3, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    simp only [g, pow_zero, mul_one]
    ring
  · have hExp (c : ℝ) (h : 0 < c) : Tendsto (fun y => Real.exp (c * y)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_pos h).mpr tendsto_id)
    have h := ((hExp k hk).const_mul A).add
      ((hExp (k * stretch ^ 2) (mul_pos hk (pow_pos hs _))).const_mul B)
    simpa only [g, pow_zero, mul_one, mul_zero, add_zero] using h
  · by_contra! h
    have he (z : ℝ) (hz : z < 0) : A * Real.exp z + B * Real.exp (stretch ^ 2 * z) = 0 := by
      have hh := h (k⁻¹ * z) (mul_neg_of_pos_of_neg (inv_pos.mpr hk) hz)
      have h₁ : k * (k⁻¹ * z) = z := by rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]
      have h₂ : k * stretch ^ 2 * (k⁻¹ * z) = stretch ^ 2 * z := by
        calc
          _ = stretch ^ 2 * (k * (k⁻¹ * z)) := by ring
          _ = _ := by rw [h₁]
      simpa only [g, pow_zero, mul_one, h₁, h₂] using hh
    obtain ⟨ha, hb⟩ := biot_decay_profiles_independent stretch A B hs hc he
    exact hn.elim (fun hh => hh ha) (fun hh => hh hb)
  · simp only [g, mul_zero, Real.exp_zero, mul_one, pow_zero]
    linear_combination k ^ 2 * hShear
  · simp only [g, mul_zero, Real.exp_zero, mul_one, pow_one]
    linear_combination -(k ^ 3) * hNormal

noncomputable section

/-- Plane-strain incremental stress of a Fourier harmonic with horizontal
wavenumber k, in the current configuration and normalized by μ B₂₂. -/
def biotWavenumberStress (stretch k : ℝ) (f f₁ f₂ p : ℝ → ℝ) (x y : ℝ) : Tensor 2 :=
  !![(-(1 + stretch ^ 4) * k * f₁ y - p y) * Real.sin (k * x),
      (f₂ y + k ^ 2 * f y) * Real.cos (k * x);
    (stretch ^ 4 * k ^ 2 * f y + f₂ y) * Real.cos (k * x),
      (2 * k * f₁ y - p y) * Real.sin (k * x)]

theorem biotWavenumberStress_divergence (stretch k : ℝ) (f f₁ f₂ f₃ p : ℝ → ℝ)
    (x y pdot : ℝ) (h₀ : HasDerivAt f (f₁ y) y)
    (h₁ : HasDerivAt f₁ (f₂ y) y) (h₂ : HasDerivAt f₂ (f₃ y) y) (hp : HasDerivAt p pdot y) :
    (deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p z y 0 0) x +
        deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p x z 0 1) y =
      (f₃ y - stretch ^ 4 * k ^ 2 * f₁ y - k * p y) * Real.cos (k * x)) ∧
    (deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p z y 1 0) x +
        deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p x z 1 1) y =
      (k * (f₂ y - stretch ^ 4 * k ^ 2 * f y) - pdot) * Real.sin (k * x)) := by
  have hk : HasDerivAt (fun z : ℝ => k * z) k x := by
    have h := (hasDerivAt_id x).const_mul k
    change HasDerivAt (fun z => k * z) (k * 1) x at h
    rwa [mul_one] at h
  have hs := (((Real.hasDerivAt_sin (k * x)).comp x hk).const_mul
    (-(1 + stretch ^ 4) * k * f₁ y - p y)).deriv
  have hc := (((Real.hasDerivAt_cos (k * x)).comp x hk).const_mul
    (stretch ^ 4 * k ^ 2 * f y + f₂ y)).deriv
  have h01 := ((h₂.add (h₀.const_mul (k ^ 2))).mul_const (Real.cos (k * x))).deriv
  have h11 := (((h₁.const_mul (2 * k)).sub hp).mul_const (Real.sin (k * x))).deriv
  constructor
  · change deriv (fun z => (-(1 + stretch ^ 4) * k * f₁ y - p y) * Real.sin (k * z)) x +
      deriv (fun z => (f₂ z + k ^ 2 * f z) * Real.cos (k * x)) y = _
    change deriv (fun z => (-(1 + stretch ^ 4) * k * f₁ y - p y) * Real.sin (k * z)) x = _ at hs
    change deriv (fun z => (f₂ z + k ^ 2 * f z) * Real.cos (k * x)) y = _ at h01
    rw [hs, h01]
    ring
  · change deriv (fun z => (stretch ^ 4 * k ^ 2 * f y + f₂ y) * Real.cos (k * z)) x +
      deriv (fun z => (2 * k * f₁ z - p z) * Real.sin (k * x)) y = _
    change deriv (fun z => (stretch ^ 4 * k ^ 2 * f y + f₂ y) * Real.cos (k * z)) x = _ at hc
    change deriv (fun z => (2 * k * f₁ z - p z) * Real.sin (k * x)) y = _ at h11
    rw [hc, h11]
    ring

/-- For a nonzero Fourier wavenumber, the traction-free plane gives the
two dimensional boundary conditions used by the depth equation. -/
theorem biotWavenumber_freeSurface_iff (stretch k : ℝ) (hk : k ≠ 0)
    (f f₁ f₂ f₃ p : ℝ → ℝ)
    (hp : p 0 = (f₃ 0 - stretch ^ 4 * k ^ 2 * f₁ 0) / k) :
    (∀ x : ℝ, biotWavenumberStress stretch k f f₁ f₂ p x 0 0 1 = 0 ∧
      biotWavenumberStress stretch k f f₁ f₂ p x 0 1 1 = 0) ↔
      f₂ 0 + k ^ 2 * f 0 = 0 ∧ f₃ 0 = (2 + stretch ^ 4) * k ^ 2 * f₁ 0 := by
  have hPi : k * ((Real.pi / 2) / k) = Real.pi / 2 := by
    rw [mul_comm, div_mul_cancel₀ _ hk]
  constructor
  · intro h
    have h₁ := (h 0).1
    have h₂ := (h ((Real.pi / 2) / k)).2
    change (f₂ 0 + k ^ 2 * f 0) * Real.cos (k * 0) = 0 at h₁
    change (2 * k * f₁ 0 - p 0) * Real.sin (k * ((Real.pi / 2) / k)) = 0 at h₂
    rw [mul_zero, Real.cos_zero, mul_one] at h₁
    rw [hPi, Real.sin_pi_div_two, mul_one, hp] at h₂
    refine ⟨h₁, ?_⟩
    field_simp [hk] at h₂
    linear_combination -h₂
  · rintro ⟨h₁, h₂⟩ x
    change (f₂ 0 + k ^ 2 * f 0) * Real.cos (k * x) = 0 ∧ (2 * k * f₁ 0 - p 0) * Real.sin (k * x) = 0
    have he : 2 * k * f₁ 0 - p 0 = 0 := by
      rw [hp]
      field_simp [hk]
      linear_combination -h₂
    exact ⟨by rw [h₁, zero_mul], by rw [he, zero_mul]⟩

/-- The stress-divergence equations imply the pressure relations used by
the reduced profile system. -/
theorem biotWavenumber_pressure_of_equilibrium (stretch k : ℝ) (hk : k ≠ 0)
    (f f₁ f₂ f₃ p : ℝ → ℝ) (y pdot : ℝ)
    (h₀ : HasDerivAt f (f₁ y) y) (h₁ : HasDerivAt f₁ (f₂ y) y)
    (h₂ : HasDerivAt f₂ (f₃ y) y) (hp : HasDerivAt p pdot y)
    (hEq : ∀ x : ℝ,
      (deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p z y 0 0) x +
        deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p x z 0 1) y = 0) ∧
      (deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p z y 1 0) x +
        deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p x z 1 1) y = 0)) :
    p y = (f₃ y - stretch ^ 4 * k ^ 2 * f₁ y) / k ∧
      pdot = k * (f₂ y - stretch ^ 4 * k ^ 2 * f y) := by
  have hPi : k * ((Real.pi / 2) / k) = Real.pi / 2 := by
    rw [mul_comm, div_mul_cancel₀ _ hk]
  have hd (x : ℝ) := biotWavenumberStress_divergence stretch k f f₁ f₂ f₃ p x y pdot h₀ h₁ h₂ hp
  have he := (hd 0).1.symm.trans (hEq 0).1
  have hf := (hd ((Real.pi / 2) / k)).2.symm.trans (hEq ((Real.pi / 2) / k)).2
  rw [mul_zero, Real.cos_zero, mul_one] at he
  rw [hPi, Real.sin_pi_div_two, mul_one] at hf
  exact ⟨(eq_div_iff hk).mpr (by linear_combination -he), (sub_eq_zero.mp hf).symm⟩

/-- Necessity of the Biot quartic directly from the stress divergence,
zero surface traction and deep decay for a positive Fourier wavenumber. -/
theorem biot_quartic_of_wavenumber_stress_equilibrium
    (stretch k : ℝ) (hs : 0 < stretch) (hc : stretch ≤ 1) (hk : 0 < k)
    (f f₁ f₂ f₃ f₄ p pdot : ℝ → ℝ)
    (h₀ : ∀ y ≤ 0, HasDerivAt f (f₁ y) y)
    (h₁ : ∀ y ≤ 0, HasDerivAt f₁ (f₂ y) y)
    (h₂ : ∀ y ≤ 0, HasDerivAt f₂ (f₃ y) y)
    (h₃ : ∀ y ≤ 0, HasDerivAt f₃ (f₄ y) y) (hp : ∀ y ≤ 0, HasDerivAt p (pdot y) y)
    (hEq : ∀ y ≤ 0, ∀ x : ℝ,
      (deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p z y 0 0) x +
        deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p x z 0 1) y = 0) ∧
      (deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p z y 1 0) x +
        deriv (fun z => biotWavenumberStress stretch k f f₁ f₂ p x z 1 1) y = 0))
    (hTraction : ∀ x : ℝ, biotWavenumberStress stretch k f f₁ f₂ p x 0 0 1 = 0 ∧
      biotWavenumberStress stretch k f f₁ f₂ p x 0 1 1 = 0)
    (hDecay : Tendsto f atBot (𝓝 0)) (hNonzero : ∃ y < 0, f y ≠ 0) :
    stretch < 1 ∧ stretch ^ 4 - 2 * stretch + 1 = 0 := by
  have hPressure (y : ℝ) (hy : y ≤ 0) :=
    biotWavenumber_pressure_of_equilibrium stretch k hk.ne' f f₁ f₂ f₃ p y (pdot y)
      (h₀ y hy) (h₁ y hy) (h₂ y hy) (hp y hy) (hEq y hy)
  have hODE (y : ℝ) (hy : y < 0) :
      f₄ y - (1 + stretch ^ 4) * k ^ 2 * f₂ y + stretch ^ 4 * k ^ 4 * f y = 0 := by
    let q (z : ℝ) := (f₃ z - stretch ^ 4 * k ^ 2 * f₁ z) / k
    have hq : HasDerivAt q ((f₄ y - stretch ^ 4 * k ^ 2 * f₂ y) / k) y := by
      exact ((h₃ y hy.le).sub ((h₁ y hy.le).const_mul (stretch ^ 4 * k ^ 2))).div_const k
    have he := eq_rate_of_eqOn_depth (fun z hz => (hPressure z hz.le).1) hy (hp y hy.le) hq
    rw [(hPressure y hy.le).2] at he
    have h := (div_eq_iff hk.ne').mp he.symm
    linear_combination h
  obtain ⟨hShear, hNormal⟩ := (biotWavenumber_freeSurface_iff stretch k hk.ne' f f₁ f₂ f₃ p
    (hPressure 0 le_rfl).1).mp hTraction
  exact biot_quartic_of_positiveWavenumber_profile stretch k hs hc hk f f₁ f₂ f₃ f₄
    h₀ h₁ h₂ h₃ hODE hDecay hNonzero hShear hNormal

end

/-- The horizontally constant mode cannot decay at infinite depth unless its
displacement and incremental pressure vanish. The profile equations express
zero shear-stress divergence, incompressibility and constant pressure. -/
theorem biot_zeroWavenumber_trivial (u du w p : ℝ → ℝ)
    (hu : ∀ y ≤ 0, HasDerivAt u (du y) y)
    (hdu : ∀ y ≤ 0, HasDerivAt du 0 y)
    (hw : ∀ y ≤ 0, HasDerivAt w 0 y)
    (hp : ∀ y ≤ 0, HasDerivAt p 0 y)
    (hShear : du 0 = 0) (hNormal : p 0 = 0)
    (hU : Tendsto u atBot (𝓝 0)) (hW : Tendsto w atBot (𝓝 0)) :
    ∀ y ≤ 0, u y = 0 ∧ w y = 0 ∧ p y = 0 := by
  have hconst (f : ℝ → ℝ) (hf : ∀ y ≤ 0, HasDerivAt f 0 y) :
      ∀ y ≤ 0, f y = f 0 := by
    obtain ⟨A, hA⟩ := biot_firstOrder_profile f 0 (fun y hy => by simpa only [zero_mul] using hf y hy.le)
    have he (y : ℝ) (hy : y < 0) : f y = A := by
      simpa only [zero_mul, Real.exp_zero, mul_one] using hA y hy
    have h0 := eq_surface_of_eqOn_depth he (hf 0 le_rfl).continuousAt continuousAt_const
    intro y hy
    rcases hy.lt_or_eq with hy' | rfl
    · exact (he y hy').trans h0.symm
    · rfl
  have hu' (y : ℝ) (hy : y ≤ 0) : HasDerivAt u 0 y := by
    rw [← hShear, ← hconst du hdu y hy]
    exact hu y hy
  have hlim (f : ℝ → ℝ) (hf : ∀ y ≤ 0, HasDerivAt f 0 y)
      (hd : Tendsto f atBot (𝓝 0)) : f 0 = 0 := by
    have he : f =ᶠ[atBot] fun _ => f 0 := (eventually_lt_atBot 0).mono fun y hy =>
      hconst f hf y hy.le
    exact tendsto_nhds_unique tendsto_const_nhds (hd.congr' he)
  intro y hy
  exact ⟨(hconst u hu' y hy).trans (hlim u hu' hU), (hconst w hw y hy).trans (hlim w hw hW),
    (hconst p hp y hy).trans hNormal⟩

end LeanSolid.ContinuumMechanics.Hyperelasticity
