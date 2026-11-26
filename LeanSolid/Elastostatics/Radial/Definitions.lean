/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Elastostatics/LameCylinder.lean at 7e41dfe (Apache-2.0). -/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

namespace LeanSolid.Elastostatics.Radial

variable (lam μ : ℝ)

/-- Radial stress `σ_r = (λ + 2μ) ε_r + λ ε_θ` for `ε_r = u'`, `ε_θ = u/r`. -/
def sigR (du u r : ℝ) : ℝ := (lam + 2 * μ) * du + lam * u / r

/-- Hoop stress `σ_θ = λ ε_r + (λ + 2μ) ε_θ` for `ε_r = u'`, `ε_θ = u/r`. -/
def sigT (du u r : ℝ) : ℝ := lam * du + (lam + 2 * μ) * u / r

/-- Plane-strain axial stress `σ_z = λ (ε_r + ε_θ)`. -/
def sigZ (du u r : ℝ) : ℝ := lam * (du + u / r)

/-- The Euler-type residual `u'' + u'/r - u/r²` of the radial displacement equation. -/
def odeRes (ddu du u r : ℝ) : ℝ := ddu + du / r - u / r ^ 2

/-- The general radial displacement `u = A r + B/r`. -/
def gen (A B r : ℝ) : ℝ := A * r + B / r

/-- Its derivative `u' = A - B/r²`. -/
def genD (A B r : ℝ) : ℝ := A - B / r ^ 2

/-- Its second derivative `u'' = 2B/r³`. -/
def genDD (B r : ℝ) : ℝ := 2 * B / r ^ 3

/-- `A' = (p_a a² - p_b b²)/(b² - a²)`. -/
def lameA (a b pa pb : ℝ) : ℝ := (pa * a ^ 2 - pb * b ^ 2) / (b ^ 2 - a ^ 2)

/-- `B' = (p_a - p_b) a² b²/(b² - a²)`. -/
def lameB (a b pa pb : ℝ) : ℝ := (pa - pb) * a ^ 2 * b ^ 2 / (b ^ 2 - a ^ 2)

/-- Lamé's radial stress `σ_r = A' - B'/r²`. -/
def lameR (a b pa pb r : ℝ) : ℝ := lameA a b pa pb - lameB a b pa pb / r ^ 2

/-- Lamé's hoop stress `σ_θ = A' + B'/r²`. -/
def lameT (a b pa pb r : ℝ) : ℝ := lameA a b pa pb + lameB a b pa pb / r ^ 2

/-- Spherical radial stress for `u = A r + B/r²`: `σ_r = (λ + 2μ) u' + 2λ u/r`. -/
def sphSigR (du u r : ℝ) : ℝ := (lam + 2 * μ) * du + 2 * lam * u / r

/-- Spherical hoop stress: `σ_θ = λ u' + 2(λ + μ) u/r`. -/
def sphSigT (du u r : ℝ) : ℝ := lam * du + 2 * (lam + μ) * u / r

/-- Lamé constant `A' = (p_a a³ - p_b b³)/(b³ - a³)` for the sphere. -/
def sphA (a b pa pb : ℝ) : ℝ := (pa * a ^ 3 - pb * b ^ 3) / (b ^ 3 - a ^ 3)

/-- Lamé constant `B' = (p_a - p_b) a³ b³/(2(b³ - a³))` for the sphere. -/
def sphB (a b pa pb : ℝ) : ℝ := (pa - pb) * a ^ 3 * b ^ 3 / (2 * (b ^ 3 - a ^ 3))

/-- Sphere radial stress `σ_r = A' - 2B'/r³`. -/
def sphR (a b pa pb r : ℝ) : ℝ := sphA a b pa pb - 2 * sphB a b pa pb / r ^ 3

/-- Sphere hoop stress `σ_θ = A' + B'/r³`. -/
def sphT (a b pa pb r : ℝ) : ℝ := sphA a b pa pb + sphB a b pa pb / r ^ 3

end LeanSolid.Elastostatics.Radial
