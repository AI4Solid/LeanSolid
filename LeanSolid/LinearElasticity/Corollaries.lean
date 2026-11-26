module

public import LeanSolid.LinearElasticity.Theorems
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

public section

namespace LeanSolid.LinearElasticity

/-- The strictly positive Lamé range gives the physical Young–Poisson range. -/
theorem young_poisson_admissible_of_lame (lam mu : ℝ)
    (hm : 0 < mu) (hb : 0 < 3 * lam + 2 * mu) :
    0 < youngFromLame lam mu ∧
      -1 < poissonFromLame lam mu ∧ poissonFromLame lam mu < 1 / 2 := by
  have hd : 0 < lam + mu := by linarith
  have hden : 0 < 2 * (lam + mu) := by positivity
  refine ⟨div_pos (mul_pos hm hb) hd, ?_, ?_⟩
  · apply (lt_div_iff₀ hden).2
    linarith
  · apply (div_lt_iff₀ hden).2
    linarith

open LeanSolid.Math

variable {n : ℕ}

theorem stress_of_trace_zero (lam mu : ℝ) (A : Tensor n) (hA : A.trace = 0) :
    stress lam mu A = (2 * mu) • A := by
  simp [stress, hA]

theorem energyPosDef3_iff_bulk_shear (lam mu : ℝ) :
    EnergyPosDef3 lam mu ↔ 0 < bulkModulus lam mu ∧ 0 < mu := by
  rw [energyPosDef3_iff]
  unfold bulkModulus
  constructor
  · rintro ⟨hm, hb⟩
    exact ⟨by linarith, hm⟩
  · rintro ⟨hb, hm⟩
    exact ⟨hm, by linarith⟩

theorem bulkModulus_fromYoungPoisson (young poisson : ℝ)
    (h₁ : 1 + poisson ≠ 0) (h₂ : 1 - 2 * poisson ≠ 0) :
    bulkModulus (lameFromYoungPoisson young poisson) (shearFromYoungPoisson young poisson) =
      young / (3 * (1 - 2 * poisson)) := by
  unfold bulkModulus lameFromYoungPoisson shearFromYoungPoisson
  set d : ℝ := 1 - 2 * poisson with hd
  field_simp [h₁, h₂]
  rw [hd]
  ring

theorem energyPosDef3_of_young_poisson (young poisson : ℝ)
    (hY : 0 < young) (hlo : -1 < poisson) (hhi : poisson < 1 / 2) :
    EnergyPosDef3 (lameFromYoungPoisson young poisson)
      (shearFromYoungPoisson young poisson) := by
  have h₁ : 0 < 1 + poisson := by linarith
  have h₂ : 0 < 1 - 2 * poisson := by linarith
  rw [energyPosDef3_iff_bulk_shear, bulkModulus_fromYoungPoisson _ _ h₁.ne' h₂.ne']
  exact ⟨div_pos hY (mul_pos (by norm_num : (0 : ℝ) < 3) h₂),
    div_pos hY (mul_pos (by norm_num : (0 : ℝ) < 2) h₁)⟩

/-- This is pointwise recovery of strain, with no domain or boundary conditions. -/
theorem strain_eq_of_stress_eq (lam mu : ℝ) (A B : Tensor n)
    (hmu : mu ≠ 0) (hbulk : (n : ℝ) * lam + 2 * mu ≠ 0)
    (hσ : stress lam mu A = stress lam mu B) : A = B := by
  have htrace := congrArg Matrix.trace hσ
  rw [trace_stress, trace_stress] at htrace
  have hab : A.trace = B.trace := mul_left_cancel₀ hbulk htrace
  unfold stress at hσ
  rw [hab] at hσ
  have hscaled : (2 * mu) • A = (2 * mu) • B := add_left_cancel hσ
  ext i j
  have hij := congrArg (fun T : Tensor n => T i j) hscaled
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hmu) hij

theorem compliance_stress (lam mu : ℝ) (A : Tensor n)
    (hmu : mu ≠ 0) (hbulk : (n : ℝ) * lam + 2 * mu ≠ 0) :
    compliance lam mu (stress lam mu A) = A := by
  let d : ℝ := (n : ℝ) * lam + 2 * mu
  have hd : d ≠ 0 := hbulk
  have hcancel : lam * (d * A.trace) / d = lam * A.trace := by
    rw [show lam * (d * A.trace) = (lam * A.trace) * d by ring]
    exact mul_div_cancel_right₀ _ hd
  unfold compliance
  rw [trace_stress]
  change (1 / (2 * mu)) • (stress lam mu A -
    (lam * (d * A.trace) / d) • (1 : Tensor n)) = A
  rw [hcancel]
  ext i j
  simp [stress, smul_eq_mul]
  field_simp [hmu]

theorem stress_compliance (lam mu : ℝ) (A : Tensor n)
    (hmu : mu ≠ 0) (hbulk : (n : ℝ) * lam + 2 * mu ≠ 0) :
    stress lam mu (compliance lam mu A) = A := by
  let d : ℝ := (n : ℝ) * lam + 2 * mu
  have hd : d ≠ 0 := hbulk
  have htrace : (compliance lam mu A).trace = A.trace / d := by
    simp only [compliance, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one,
      smul_eq_mul, Fintype.card_fin]
    change (1 / (2 * mu)) * (A.trace - (lam * A.trace / d) * (n : ℝ)) = A.trace / d
    field_simp [hmu, hd]
    dsimp [d]
    ring
  unfold stress
  rw [htrace]
  ext i j
  change (lam * (A.trace / d)) * (1 : Tensor n) i j +
    (2 * mu) * ((1 / (2 * mu)) * (A i j -
      (lam * A.trace / d) * (1 : Tensor n) i j)) = A i j
  field_simp [hmu, hd]
  ring

theorem trace_planeBlock (A : Tensor 2) (s : ℝ) : (planeBlock A s).trace = A.trace + s := by
  simp [planeBlock, Matrix.trace, Fin.sum_univ_succ, add_assoc]

/-- The complete three-dimensional stress under the plane-strain ansatz. -/
theorem stress_planeStrain (lam mu : ℝ) (A : Tensor 2) :
    stress lam mu (planeBlock A 0) = planeBlock (stress lam mu A) (lam * A.trace) := by
  ext i j
  rw [show (stress lam mu (planeBlock A 0)) i j =
      ((lam * (planeBlock A 0).trace) • (1 : Tensor 3) +
        (2 * mu) • planeBlock A 0) i j by rfl, trace_planeBlock]
  fin_cases i <;> fin_cases j <;> norm_num [planeBlock, stress, Matrix.one_apply, smul_eq_mul]

/-- Plane stress derived from the three-dimensional law by imposing zero normal stress. -/
theorem stress_planeStress (lam mu : ℝ) (A : Tensor 2) (h : lam + 2 * mu ≠ 0) :
    stress lam mu (planeBlock A (planeStressNormalStrain lam mu A.trace)) =
      planeBlock (stress (planeStressLame lam mu) mu A) 0 := by
  ext i j
  rw [show (stress lam mu (planeBlock A (planeStressNormalStrain lam mu A.trace))) i j =
      ((lam * (planeBlock A (planeStressNormalStrain lam mu A.trace)).trace) •
        (1 : Tensor 3) + (2 * mu) • planeBlock A (planeStressNormalStrain lam mu A.trace))
        i j by rfl, trace_planeBlock]
  fin_cases i <;> fin_cases j <;>
    norm_num [planeBlock, stress, planeStressNormalStrain, planeStressLame,
      Matrix.one_apply, smul_eq_mul] <;> field_simp [h] <;> ring

/-- Isotropic Hooke stress preserves every principal strain direction and gives its
principal stress by the Lamé formula. -/
theorem stress_mulVec_of_strain_mulVec {n : ℕ} (lam mu principal : ℝ)
    (A : Tensor n) (v : Vector n) (h : A.mulVec v = principal • v) :
    (stress lam mu A).mulVec v = (lam * A.trace + 2 * mu * principal) • v := by
  rw [stress, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, h, smul_smul, add_smul]

end LeanSolid.LinearElasticity
