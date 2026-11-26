/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Elastostatics/LameCylinder.lean at 7e41dfe (Apache-2.0). -/
module

public import LeanSolid.Elastostatics.Radial.Definitions
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

public section

noncomputable section

namespace LeanSolid.Elastostatics.Radial

variable (lam μ : ℝ)

/-- `σ_r - σ_θ = 2μ (u' - u/r)`. -/
theorem sigR_sub_sigT (du u r : ℝ) :
    sigR lam μ du u r - sigT lam μ du u r = 2 * μ * (du - u / r) := by
  unfold sigR sigT; ring

/-- The derivative of the radial stress along a twice-differentiable displacement:
`σ_r' = (λ + 2μ) u'' + λ (u' r - u)/r²`. -/
theorem hasDerivAt_sigR {u du ddu : ℝ → ℝ} {r : ℝ} (hu : HasDerivAt u (du r) r)
    (hdu : HasDerivAt du (ddu r) r) (hr : r ≠ 0) :
    HasDerivAt (fun s => sigR lam μ (du s) (u s) s)
      ((lam + 2 * μ) * ddu r + lam * ((du r * r - u r) / r ^ 2)) r := by
  unfold sigR
  have h := HasDerivAt.add ((hdu.const_mul (lam + 2 * μ))) (HasDerivAt.div ((hu.const_mul lam)) (hasDerivAt_id' r) hr)
  convert h using 1
  ring

/-- Radial equilibrium residual: `σ_r' + (σ_r - σ_θ)/r = (λ + 2μ)(u'' + u'/r - u/r²)`. -/
theorem equilibrium_eq {u du ddu : ℝ → ℝ} {r : ℝ} (hu : HasDerivAt u (du r) r)
    (hdu : HasDerivAt du (ddu r) r) (hr : r ≠ 0) :
    deriv (fun s => sigR lam μ (du s) (u s) s) r +
        (sigR lam μ (du r) (u r) r - sigT lam μ (du r) (u r) r) / r =
      (lam + 2 * μ) * odeRes (ddu r) (du r) (u r) r := by
  rw [(hasDerivAt_sigR lam μ hu hdu hr).deriv, sigR_sub_sigT, odeRes]
  field_simp
  ring

/-- For `λ + 2μ ≠ 0`, radial equilibrium `σ_r' + (σ_r - σ_θ)/r = 0` is equivalent to the
Euler equation `u'' + u'/r - u/r² = 0`. -/
theorem equilibrium_iff_ode {u du ddu : ℝ → ℝ} {r : ℝ} (hu : HasDerivAt u (du r) r)
    (hdu : HasDerivAt du (ddu r) r) (hr : r ≠ 0) (hlm : lam + 2 * μ ≠ 0) :
    deriv (fun s => sigR lam μ (du s) (u s) s) r +
        (sigR lam μ (du r) (u r) r - sigT lam μ (du r) (u r) r) / r = 0 ↔
      odeRes (ddu r) (du r) (u r) r = 0 := by
  rw [equilibrium_eq lam μ hu hdu hr, mul_eq_zero, or_iff_right hlm]

/-- `(A r + B/r)' = A - B/r²` for `r ≠ 0`. -/
theorem hasDerivAt_gen (A B : ℝ) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (gen A B) (genD A B r) r := by
  have h := HasDerivAt.add ((hasDerivAt_id' r).const_mul A) ((hasDerivAt_inv hr).const_mul B)
  convert h using 1
  · funext s; simp [gen, div_eq_mul_inv]
  · simp only [genD]; ring

/-- `(A - B/r²)' = 2B/r³` for `r ≠ 0`. -/
theorem hasDerivAt_genD (A B : ℝ) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (genD A B) (genDD B r) r := by
  have h := HasDerivAt.sub (hasDerivAt_const r A) ((HasDerivAt.inv (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr)).const_mul B)
  convert h using 1
  · funext s; simp [genD, div_eq_mul_inv]
  · simp only [genDD]
    field_simp
    ring

/-- `u = A r + B/r` solves `u'' + u'/r - u/r² = 0` on `r ≠ 0`. -/
theorem general_solves (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    odeRes (genDD B r) (genD A B r) (gen A B r) r = 0 := by
  unfold odeRes genDD genD gen
  field_simp
  ring

/-- Stresses of the general solution: `σ_r = 2(λ + μ)A - 2μB/r²`. -/
theorem sigR_general (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sigR lam μ (genD A B r) (gen A B r) r = 2 * (lam + μ) * A - 2 * μ * B / r ^ 2 := by
  unfold sigR genD gen; field_simp; ring

/-- Stresses of the general solution: `σ_θ = 2(λ + μ)A + 2μB/r²`. -/
theorem sigT_general (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sigT lam μ (genD A B r) (gen A B r) r = 2 * (lam + μ) * A + 2 * μ * B / r ^ 2 := by
  unfold sigT genD gen; field_simp; ring

/-- `σ_r' = 2B'/r³`. -/
theorem hasDerivAt_lameR (a b pa pb : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (lameR a b pa pb) (2 * lameB a b pa pb / r ^ 3) r := by
  have h := HasDerivAt.sub (hasDerivAt_const r (lameA a b pa pb))
    (((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)).const_mul (lameB a b pa pb))
  convert h using 1
  · funext s; simp [lameR, div_eq_mul_inv]
  · field_simp; ring

/-- **Equilibrium** of Lamé's stresses: `σ_r' + (σ_r - σ_θ)/r = 0` on `r ≠ 0`. -/
theorem lame_equilibrium (a b pa pb : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (lameR a b pa pb) r + (lameR a b pa pb r - lameT a b pa pb r) / r = 0 := by
  rw [(hasDerivAt_lameR a b pa pb hr).deriv]
  unfold lameR lameT
  field_simp
  ring

/-- Inner boundary condition `σ_r(a) = -p_a`. -/
theorem lameR_inner (a b pa pb : ℝ) (ha : a ≠ 0) (hab : b ^ 2 - a ^ 2 ≠ 0) :
    lameR a b pa pb a = -pa := by
  unfold lameR lameA lameB
  field_simp
  ring

/-- Outer boundary condition `σ_r(b) = -p_b`. -/
theorem lameR_outer (a b pa pb : ℝ) (hb : b ≠ 0) (hab : b ^ 2 - a ^ 2 ≠ 0) :
    lameR a b pa pb b = -pb := by
  unfold lameR lameA lameB
  field_simp
  ring

/-- The displacement `u = A r + B/r` with `A = A'/(2(λ + μ))`, `B = B'/(2μ)` produces exactly
Lamé's stresses (for `λ + μ ≠ 0`, `μ ≠ 0`). -/
theorem lame_displacement_stress (a b pa pb : ℝ) (h1 : lam + μ ≠ 0) (h2 : μ ≠ 0) {r : ℝ}
    (hr : r ≠ 0) :
    let A := lameA a b pa pb / (2 * (lam + μ))
    let B := lameB a b pa pb / (2 * μ)
    sigR lam μ (genD A B r) (gen A B r) r = lameR a b pa pb r ∧
      sigT lam μ (genD A B r) (gen A B r) r = lameT a b pa pb r := by
  intro A B
  rw [sigR_general lam μ A B hr, sigT_general lam μ A B hr]
  simp only [A, B, lameR, lameT]
  constructor <;> field_simp

/-- Stresses of the spherical general solution `u = A r + B/r²`, `u' = A - 2B/r³`:
`σ_r = (3λ + 2μ)A - 4μB/r³` and `σ_θ = (3λ + 2μ)A + 2μB/r³`. -/
theorem sphere_general (A B : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sphSigR lam μ (A - 2 * B / r ^ 3) (A * r + B / r ^ 2) r =
        (3 * lam + 2 * μ) * A - 4 * μ * B / r ^ 3 ∧
      sphSigT lam μ (A - 2 * B / r ^ 3) (A * r + B / r ^ 2) r =
        (3 * lam + 2 * μ) * A + 2 * μ * B / r ^ 3 := by
  unfold sphSigR sphSigT
  constructor <;> field_simp <;> ring

/-- `σ_r' = 6B'/r⁴` for the sphere. -/
theorem hasDerivAt_sphR (a b pa pb : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (sphR a b pa pb) (6 * sphB a b pa pb / r ^ 4) r := by
  have h := HasDerivAt.sub (hasDerivAt_const r (sphA a b pa pb))
    (((hasDerivAt_pow 3 r).inv (pow_ne_zero 3 hr)).const_mul (2 * sphB a b pa pb))
  convert h using 1
  · funext s; simp [sphR, div_eq_mul_inv]
  · field_simp; ring

/-- Spherical **equilibrium** `σ_r' + 2(σ_r - σ_θ)/r = 0` on `r ≠ 0`. -/
theorem sphere_equilibrium (a b pa pb : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (sphR a b pa pb) r + 2 * (sphR a b pa pb r - sphT a b pa pb r) / r = 0 := by
  rw [(hasDerivAt_sphR a b pa pb hr).deriv]
  unfold sphR sphT
  field_simp
  ring

/-- Sphere boundary conditions `σ_r(a) = -p_a`, `σ_r(b) = -p_b`. -/
theorem sphere_bc (a b pa pb : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b ^ 3 - a ^ 3 ≠ 0) :
    sphR a b pa pb a = -pa ∧ sphR a b pa pb b = -pb := by
  unfold sphR sphA sphB
  constructor <;> field_simp <;> ring

/-- The displacement `u = A r + B/r²` with `A = A'/(3λ + 2μ)`, `B = B'/(2μ)` produces the
spherical Lamé stresses. -/
theorem sphere_displacement_stress (a b pa pb : ℝ) (h1 : 3 * lam + 2 * μ ≠ 0) (h2 : μ ≠ 0)
    {r : ℝ} (hr : r ≠ 0) :
    let A := sphA a b pa pb / (3 * lam + 2 * μ)
    let B := sphB a b pa pb / (2 * μ)
    sphSigR lam μ (A - 2 * B / r ^ 3) (A * r + B / r ^ 2) r = sphR a b pa pb r ∧
      sphSigT lam μ (A - 2 * B / r ^ 3) (A * r + B / r ^ 2) r = sphT a b pa pb r := by
  intro A B
  rw [(sphere_general lam μ A B hr).1, (sphere_general lam μ A B hr).2]
  simp only [A, B, sphR, sphT]
  constructor
  · field_simp; ring
  · field_simp

end LeanSolid.Elastostatics.Radial
