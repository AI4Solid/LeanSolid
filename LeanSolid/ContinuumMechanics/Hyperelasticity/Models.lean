module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Theorems
public import LeanSolid.LinearElasticity.Theorems
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

open LeanSolid.Math

variable {n : ℕ}

/-- Saint Venant–Kirchhoff energy, using the Lamé quadratic form on Green–Lagrange strain. -/
def saintVenantKirchhoff (lam mu : ℝ) (E : Tensor n) : ℝ :=
  LinearElasticity.energyDensity lam mu E

theorem saintVenantKirchhoff_secondPiola (lam mu : ℝ) (E : Tensor n) :
    secondPiolaStress (saintVenantKirchhoff lam mu) E = LinearElasticity.stress lam mu E := by
  ext i j
  exact ((LinearElasticity.hasDerivAt_energyDensity lam mu E (Matrix.single i j 1)).deriv).trans
    (contract_single_right _ _ _)

/-- Compressible logarithmic neo-Hookean energy in the invariants of C.
The physical domain has positive J, so I₃(C) = J² > 0. -/
def neoHookeanInvariants (lam mu : ℝ) (q : Vector 3) : ℝ :=
  mu / 2 * (q 0 - 3) - mu / 2 * Real.log (q 2) + lam / 8 * (Real.log (q 2)) ^ 2

def neoHookeanEnergy (lam mu : ℝ) (C : Tensor 3) : ℝ :=
  invariantEnergy (neoHookeanInvariants lam mu) C

private theorem hasEnergyGradient_neoHookean (lam mu : ℝ) (C : Tensor 3)
    (hC : 0 < invariant₃ C) :
    HasEnergyGradient (neoHookeanEnergy lam mu) C
      ((mu / 2) • (1 : Tensor 3) +
        ((-mu / 2 + lam / 4 * Real.log (invariant₃ C)) / invariant₃ C) • C.adjugate.transpose) := by
  intro c H hc hH
  have h1 := hasEnergyGradient_invariant₁ C c H hc hH
  have h3 := hasEnergyGradient_invariant₃ C c H hc hH
  have hlog : HasDerivAt (fun t => Real.log (invariant₃ (c t)))
      ((invariant₃ C)⁻¹ * contract C.adjugate.transpose H) 0 :=
    (Real.hasDerivAt_log hC.ne').comp_of_eq 0 h3 (congrArg invariant₃ hc.symm)
  have hlin := (h1.sub_const 3).const_mul (mu / 2)
  have hloglin := hlog.const_mul (mu / 2)
  have hlogsq := (hlog.pow 2).const_mul (lam / 8)
  have h := (hlin.sub hloglin).add hlogsq
  convert h using 1
  · funext t
    simp [neoHookeanEnergy, invariantEnergy, neoHookeanInvariants, principalInvariants]
  · rw [contract_add_left, contract_smul_left, contract_smul_left, hc]
    norm_num
    ring

/-- Closed-form second Piola stress of the logarithmic neo-Hookean model. -/
theorem neoHookean_secondPiola (lam mu : ℝ) (C : Tensor 3) (hC : 0 < invariant₃ C) :
    secondPiolaFromC (neoHookeanEnergy lam mu) C =
      mu • (1 : Tensor 3) +
        ((-mu + lam / 2 * Real.log (invariant₃ C)) / invariant₃ C) • C.adjugate.transpose := by
  rw [secondPiolaFromC, (hasEnergyGradient_neoHookean lam mu C hC).eq_energyGradient]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem neoHookean_firstPiola (lam mu : ℝ) (F : Tensor 3) (hJ : 0 < jacobian F) :
    firstPiolaStress (fun A => neoHookeanEnergy lam mu (rightCauchyGreen A)) F =
      F * secondPiolaFromC (neoHookeanEnergy lam mu) (rightCauchyGreen F) := by
  let C := rightCauchyGreen F
  have hC : 0 < invariant₃ C := by
    rw [show C = rightCauchyGreen F by rfl, invariant₃_rightCauchyGreen]
    exact pow_pos hJ _
  have hg := hasEnergyGradient_neoHookean lam mu C hC
  have ha : C.adjugate.transpose = C.adjugate := by
    rw [Matrix.adjugate_transpose, rightCauchyGreen_transpose F]
  rw [secondPiolaFromC, hg.eq_energyGradient]
  apply (hasEnergyGradient_rightCauchyGreen hg ?_).eq_energyGradient
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, ha]

end LeanSolid.ContinuumMechanics.Hyperelasticity
