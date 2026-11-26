module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

public section

namespace LeanSolid.AntiPlane

/-- The displacement from a holomorphic potential is harmonic in the complex plane. -/
theorem realPotential_harmonic {potential : ℂ → ℂ} {z : ℂ}
    (h : AnalyticAt ℂ potential z) : InnerProductSpace.HarmonicAt (fun w => (potential w).re) z :=
  h.harmonicAt_re

/-- A zero real part alone cannot fix the imaginary additive constant. -/
theorem nonzeroPotential_with_zeroRealPart :
    ∃ f : ℂ → ℂ, (∀ z, AnalyticAt ℂ f z) ∧ (∀ z, (f z).re = 0) ∧ f ≠ 0 := by
  refine ⟨fun _ => Complex.I, fun _ => analyticAt_const, fun _ => Complex.I_re, ?_⟩
  intro h
  have hI : Complex.I = 0 := congrFun h 0
  exact Complex.I_ne_zero hI

end LeanSolid.AntiPlane
