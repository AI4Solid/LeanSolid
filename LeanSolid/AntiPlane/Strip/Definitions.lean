/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Elastostatics/SaintVenantPrinciple.lean at 7e41dfe (Apache-2.0). -/
module

public import LeanSolid.AntiPlane.Strip.Partials

@[expose] public section

open Real
open LeanSolid.AntiPlane.Strip.Partials (dt dx)

noncomputable section

namespace LeanSolid.AntiPlane.Strip

/-- **Laplace's equation** `w_xx + w_yy = 0` at the point `(x, y)` (equilibrium of antiplane
shear). -/
def IsHarmonicAt (w : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  dt (dt w) x y + dx (dx w) x y = 0

/-- The **resultant force** `F(x) = μ ∫₀ᵇ w_x(x, y) dy` of the shear traction `τ_xz = μ w_x` on
the cross-section at `x`. -/
def resultant (μ b : ℝ) (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  μ * ∫ y in (0 : ℝ)..b, dt w x y

/-- The separated field `e^{-kx} cos(ky)`. -/
def mode (k x y : ℝ) : ℝ := exp (-k * x) * cos (k * y)

/-- The companion field `e^{-kx} sin(ky)` (the transverse derivative of `mode`, up to `-k`). -/
def modeSin (k x y : ℝ) : ℝ := exp (-k * x) * sin (k * y)

/-- A finite superposition `∑ₙ cₙ e^{-kₙx} cos(kₙy)`. -/
def modeSum (s : Finset ℕ) (c k : ℕ → ℝ) (x y : ℝ) : ℝ := ∑ n ∈ s, c n * mode (k n) x y

/-- The companion superposition `∑ₙ cₙ e^{-kₙx} sin(kₙy)`. -/
def modeSinSum (s : Finset ℕ) (c k : ℕ → ℝ) (x y : ℝ) : ℝ := ∑ n ∈ s, c n * modeSin (k n) x y

/-- The strip wavenumbers `kₙ = nπ/b`. -/
def wavenumber (b : ℝ) (n : ℕ) : ℝ := n * π / b

/-- The **uniform shear** field `w = A x + C` (the separated solution with `k = 0`). -/
def shear (A C x _y : ℝ) : ℝ := A * x + C

/-- The **strain energy per unit length** at the section `x`:
`S(x) = (μ/2) ∫₀ᵇ (w_x² + w_y²) dy`. -/
def sectionEnergy (μ b : ℝ) (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  μ / 2 * ∫ y in (0 : ℝ)..b, (dt w x y ^ 2 + dx w x y ^ 2)

/-- The **strain energy stored beyond the section `x`** in the finite strip `[0, L] × [0, b]`:
`E(x) = ∫ₓᴸ S(s) ds = (μ/2) ∫ₓᴸ ∫₀ᵇ |∇w|²`. -/
def energy (μ b L : ℝ) (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s in x..L, sectionEnergy μ b w s

/-- The **work of the section traction** `W(x) = ∫₀ᵇ τ_xz w dy = μ ∫₀ᵇ w w_x dy`. -/
def sectionWork (μ b : ℝ) (w : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  μ * ∫ y in (0 : ℝ)..b, w x y * dt w x y

end LeanSolid.AntiPlane.Strip
