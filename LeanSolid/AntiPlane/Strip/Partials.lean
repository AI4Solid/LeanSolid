/- Selected and adapted from raphos-com/lean-mechanics, ContinuumMechanics/Beams/String.lean at 7e41dfe (Apache-2.0). -/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.OpenPos

open Set Real MeasureTheory
@[expose] public section
noncomputable section
namespace LeanSolid.AntiPlane.Strip.Partials
/-- Time derivative `∂ₜu(t, x)` of a field `u : ℝ → ℝ → ℝ` (arguments `t`, then `x`). -/
def dt (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t x => deriv (fun s => u s x) t

/-- Space derivative `∂ₓu(t, x)` of a field `u : ℝ → ℝ → ℝ`. -/
def dx (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t x => deriv (u t) x
variable {ψ φ : ℝ → ℝ}

/-- The primitive `Ψ(y) = ∫₀ʸ ψ`. -/
def primitive (ψ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ z in (0 : ℝ)..y, ψ z

/-- Fundamental theorem of calculus: `Ψ' = ψ` for continuous `ψ`. -/
theorem hasDerivAt_primitive (hψ : Continuous ψ) (y : ℝ) :
    HasDerivAt (primitive ψ) (ψ y) y :=
  (hψ.integral_hasStrictDerivAt 0 y).hasDerivAt

/-- The primitive of a `C¹` function is `C²`. -/
theorem contDiff_primitive (hψ : ContDiff ℝ 1 ψ) : ContDiff ℝ 2 (primitive ψ) := by
  have hd : deriv (primitive ψ) = ψ :=
    funext fun y => (hasDerivAt_primitive hψ.continuous y).deriv
  refine (contDiff_succ_iff_deriv (n := 1)).mpr
    ⟨fun y => (hasDerivAt_primitive hψ.continuous y).differentiableAt, by simp, ?_⟩
  rwa [hd]


/-- `∫₀ᴸ cos(kπx / L) dx = L δ_{k0}` for integer `k`. -/
theorem integral_cos_int {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    ∫ x in (0 : ℝ)..L, cos (k * π / L * x) = if k = 0 then L else 0 := by
  split_ifs with hk
  · simp [hk]
  have hc : (k : ℝ) * π / L ≠ 0 := div_ne_zero (mul_ne_zero (by exact_mod_cast hk) pi_ne_zero) hL
  rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hc, integral_cos,
    div_mul_cancel₀ _ hL, sin_int_mul_pi]
  simp

section Partials

variable {U : ℝ × ℝ → ℝ}

/-- The time partial derivative of a differentiable `U(t, x)` is `DU(t, x)(1, 0)`. -/
theorem hasDerivAt_fst_of_differentiable (hU : Differentiable ℝ U) (t x : ℝ) :
    HasDerivAt (fun s => U (s, x)) (fderiv ℝ U (t, x) (1, 0)) t :=
  (hU (t, x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))

/-- The space partial derivative of a differentiable `U(t, x)` is `DU(t, x)(0, 1)`. -/
theorem hasDerivAt_snd_of_differentiable (hU : Differentiable ℝ U) (t x : ℝ) :
    HasDerivAt (fun y => U (t, y)) (fderiv ℝ U (t, x) (0, 1)) x :=
  (hU (t, x)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_const x t).prodMk (hasDerivAt_id' x))

/-- The directional derivative field `p ↦ DU(p) v`. -/
def dirDeriv (U : ℝ × ℝ → ℝ) (v p : ℝ × ℝ) : ℝ := fderiv ℝ U p v

/-- Directional derivatives of a `C²` field are `C¹`. -/
theorem contDiff_dirDeriv (hU : ContDiff ℝ 2 U) (v : ℝ × ℝ) : ContDiff ℝ 1 (dirDeriv U v) :=
  (hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- Derivative of a directional derivative field: `D(DU · v)(p) w = D²U(p) w v`. -/
theorem fderiv_dirDeriv (hU : ContDiff ℝ 2 U) (v w p : ℝ × ℝ) :
    fderiv ℝ (dirDeriv U v) p w = fderiv ℝ (fderiv ℝ U) p w v := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ U) p :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero p
  rw [show dirDeriv U v = fun p => fderiv ℝ U p v from rfl,
    fderiv_clm_apply h1 (differentiableAt_const v)]
  simp

/-- **Symmetry of mixed partials** (Schwarz) for `C²` fields. -/
theorem fderiv_dirDeriv_comm (hU : ContDiff ℝ 2 U) (v w p : ℝ × ℝ) :
    fderiv ℝ (dirDeriv U v) p w = fderiv ℝ (dirDeriv U w) p v := by
  rw [fderiv_dirDeriv hU, fderiv_dirDeriv hU]
  exact (hU.contDiffAt.isSymmSndFDerivAt (by simp)) w v

variable {u : ℝ → ℝ → ℝ}

/-- `u_t(t, x) = DU(t, x)(1, 0)` for `U = uncurry u` of class `C²`. -/
theorem dt_eq_dirDeriv (hU : ContDiff ℝ 2 (Function.uncurry u)) :
    dt u = fun t x => dirDeriv (Function.uncurry u) (1, 0) (t, x) :=
  funext fun t => funext fun x =>
    (hasDerivAt_fst_of_differentiable (hU.differentiable (by norm_num)) t x).deriv

/-- `u_x(t, x) = DU(t, x)(0, 1)` for `U = uncurry u` of class `C²`. -/
theorem dx_eq_dirDeriv (hU : ContDiff ℝ 2 (Function.uncurry u)) :
    dx u = fun t x => dirDeriv (Function.uncurry u) (0, 1) (t, x) :=
  funext fun t => funext fun x =>
    (hasDerivAt_snd_of_differentiable (hU.differentiable (by norm_num)) t x).deriv

/-- `u_tt(t, x)` in terms of the directional derivative field `u_t`. -/
theorem dt_dt_eq (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    dt (dt u) t x = fderiv ℝ (dirDeriv (Function.uncurry u) (1, 0)) (t, x) (1, 0) := by
  rw [dt_eq_dirDeriv hU]
  exact (hasDerivAt_fst_of_differentiable
    ((contDiff_dirDeriv hU _).differentiable one_ne_zero) t x).deriv

/-- `u_xx(t, x)` in terms of the directional derivative field `u_x`. -/
theorem dx_dx_eq (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    dx (dx u) t x = fderiv ℝ (dirDeriv (Function.uncurry u) (0, 1)) (t, x) (0, 1) := by
  rw [dx_eq_dirDeriv hU]
  exact (hasDerivAt_snd_of_differentiable
    ((contDiff_dirDeriv hU _).differentiable one_ne_zero) t x).deriv

/-- A `C²` field is differentiable in time. -/
theorem differentiableAt_t (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => u s x) t :=
  (hasDerivAt_fst_of_differentiable (hU.differentiable (by norm_num)) t x).differentiableAt

/-- A `C²` field is differentiable in space. -/
theorem differentiableAt_x (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    DifferentiableAt ℝ (u t) x :=
  (hasDerivAt_snd_of_differentiable (hU.differentiable (by norm_num)) t x).differentiableAt

/-- The velocity of a `C²` field is differentiable in time. -/
theorem differentiableAt_dt_t (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    DifferentiableAt ℝ (fun s => dt u s x) t := by
  rw [dt_eq_dirDeriv hU]
  exact (hasDerivAt_fst_of_differentiable
    ((contDiff_dirDeriv hU _).differentiable one_ne_zero) t x).differentiableAt

/-- The strain of a `C²` field is differentiable in space. -/
theorem differentiableAt_dx_x (hU : ContDiff ℝ 2 (Function.uncurry u)) (t x : ℝ) :
    DifferentiableAt ℝ (dx u t) x := by
  rw [dx_eq_dirDeriv hU]
  exact (hasDerivAt_snd_of_differentiable
    ((contDiff_dirDeriv hU _).differentiable one_ne_zero) t x).differentiableAt

end Partials
end LeanSolid.AntiPlane.Strip.Partials
