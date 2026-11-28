/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Thermal/Thermoelastic.lean
at 7e41dfe (Apache-2.0). -/
module

public import LeanSolid.LinearElasticity.Corollaries

@[expose] public section

namespace LeanSolid.ContinuumMechanics.Thermoelastic

open LeanSolid.Math

/-- The stress-free strain for isotropic expansion by a temperature increment. -/
noncomputable def thermalStrain (n : ℕ) (α ΔT : ℝ) : Tensor n :=
  (α * ΔT) • (1 : Tensor n)

/-- Apply the elastic law to the strain relative to the thermally expanded state. -/
noncomputable def stress {n : ℕ} (lam μ α ΔT : ℝ) (ε : Tensor n) : Tensor n :=
  LeanSolid.LinearElasticity.stress lam μ (ε - thermalStrain n α ΔT)

/-- Recover total strain by adding thermal strain to elastic compliance. -/
noncomputable def strain {n : ℕ} (lam μ α ΔT : ℝ) (σ : Tensor n) : Tensor n :=
  LeanSolid.LinearElasticity.compliance lam μ σ + thermalStrain n α ΔT

theorem strain_stress {n : ℕ} (lam μ α ΔT : ℝ) (ε : Tensor n)
    (hμ : μ ≠ 0) (hbulk : (n : ℝ) * lam + 2 * μ ≠ 0) :
    strain lam μ α ΔT (stress lam μ α ΔT ε) = ε := by
  rw [strain, stress, LeanSolid.LinearElasticity.compliance_stress _ _ _ hμ hbulk, sub_add_cancel]

theorem stress_strain {n : ℕ} (lam μ α ΔT : ℝ) (σ : Tensor n)
    (hμ : μ ≠ 0) (hbulk : (n : ℝ) * lam + 2 * μ ≠ 0) :
    stress lam μ α ΔT (strain lam μ α ΔT σ) = σ := by
  rw [stress, strain, add_sub_cancel_right, LeanSolid.LinearElasticity.stress_compliance _ _ _ hμ hbulk]

theorem stress_free_expansion (n : ℕ) (lam μ α ΔT : ℝ) :
    stress lam μ α ΔT (thermalStrain n α ΔT) = 0 := by
  simp [stress, LeanSolid.LinearElasticity.stress]

theorem restrained_stress (n : ℕ) (lam μ α ΔT : ℝ) :
    stress lam μ α ΔT (0 : Tensor n) =
      (-((n : ℝ) * lam + 2 * μ) * (α * ΔT)) • (1 : Tensor n) := by
  simp only [stress, thermalStrain, zero_sub, ← neg_smul, LeanSolid.LinearElasticity.stress,
    Matrix.trace_smul, smul_eq_mul, Matrix.trace_one, Fintype.card_fin, smul_smul, ← add_smul]
  congr 1
  ring

end LeanSolid.ContinuumMechanics.Thermoelastic
