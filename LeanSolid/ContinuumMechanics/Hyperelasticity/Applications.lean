module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Incompressible
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

@[expose] public section

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

open LeanSolid.Math

noncomputable section

/-- The in-plane nominal/cauchy solution with zero transverse traction is obtained
by subtracting the third unconstrained principal Cauchy stress as pressure. -/
theorem biaxial_mooneyRivlin (c₁ c₂ x y z p : ℝ) (hJ : x * y * z = 1) :
    let F : Tensor 3 := Matrix.diagonal ![x, y, z]
    let σ := cauchyFromPiola F (firstPiolaStress
      (constrainedEnergy (fun A => mooneyRivlinEnergy c₁ c₂ (rightCauchyGreen A)) p) F)
    (σ 2 2 = 0 ↔ p = 2 * (c₁ + c₂ * (x ^ 2 + y ^ 2)) * z ^ 2) ∧
      (σ 2 2 = 0 → σ 0 0 = 2 * (c₁ + c₂ * y ^ 2) * (x ^ 2 - z ^ 2) ∧
        σ 1 1 = 2 * (c₁ + c₂ * x ^ 2) * (y ^ 2 - z ^ 2)) := by
  dsimp only
  have hd : jacobian (Matrix.diagonal (![x, y, z] : Vector 3)) = 1 := by
    simpa [jacobian, Matrix.det_diagonal, Fin.prod_univ_succ, mul_assoc] using hJ
  rw [mooneyRivlin_cauchy _ _ _ _ hd]
  have hb : leftCauchyGreen (Matrix.diagonal (![x, y, z] : Vector 3)) =
      Matrix.diagonal ![x ^ 2, y ^ 2, z ^ 2] := by
    rw [leftCauchyGreen, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [pow_two]
  rw [hb]
  simp [Matrix.trace_diagonal, Fin.sum_univ_succ, Matrix.diagonal_mul_diagonal, smul_eq_mul]
  constructor
  · constructor <;> intro h <;> linear_combination (norm := ring) -h
  · intro h
    constructor <;> linear_combination h

/-- Thin spherical membrane pressure from the equibiaxial Mooney–Rivlin stress,
isochoric thickness, and the spherical membrane force balance. -/
theorem mooneyRivlin_balloon_pressure (c₁ c₂ H R stretch : ℝ)
    (hR : R ≠ 0) (hs : stretch ≠ 0) :
    let hoop := 2 * (c₁ + c₂ * stretch ^ 2) * (stretch ^ 2 - 1 / stretch ^ 4)
    let thickness := H / stretch ^ 2
    let radius := R * stretch
    2 * hoop * thickness / radius =
      (4 * H / R) * (1 / stretch - 1 / stretch ^ 7) * (c₁ + c₂ * stretch ^ 2) := by
  dsimp only
  field_simp
  ring

/-- The algebraic Biot condition factors into the coincident-root case and
the cubic governing the strictly compressed branch. -/
theorem biot_compressed_polynomial (stretch : ℝ) (h : stretch < 1) :
    stretch ^ 4 - 2 * stretch + 1 = 0 ↔
      stretch ^ 3 + stretch ^ 2 + stretch - 1 = 0 := by
  rw [show stretch ^ 4 - 2 * stretch + 1 =
    (stretch - 1) * (stretch ^ 3 + stretch ^ 2 + stretch - 1) by ring]
  simp only [mul_eq_zero, sub_eq_zero, h.ne, false_or]

/-- The compressed positive branch of the lecture's polynomial lies in (0.54, 0.55). -/
theorem biot_compressed_root_bounds (stretch : ℝ) (hs : 0 < stretch) (h : stretch < 1)
    (hr : stretch ^ 4 - 2 * stretch + 1 = 0) :
    (54 / 100 : ℝ) < stretch ∧ stretch < (55 / 100 : ℝ) := by
  have hc := (biot_compressed_polynomial stretch h).mp hr
  have hmono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      x ^ 3 + x ^ 2 + x - 1 ≤ y ^ 3 + y ^ 2 + y - 1 := by
    gcongr
  constructor
  · by_contra! hn
    have he := hmono hs.le hn
    rw [hc] at he
    norm_num at he
  · by_contra! hn
    have he := hmono (by norm_num : (0 : ℝ) ≤ 55 / 100) hn
    rw [hc] at he
    norm_num at he

/-- The displayed polynomial has exactly one root in the strictly compressed
positive interval. This result concerns the polynomial itself. -/
theorem biot_existsUnique_compressed_root :
    ∃! x : ℝ, (0 < x ∧ x < 1) ∧ x ^ 4 - 2 * x + 1 = 0 := by
  let f (x : ℝ) := x ^ 3 + x ^ 2 + x - 1
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (f (54 / 100)) (f (55 / 100)) := by
    norm_num [f]
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc
    (by norm_num : (54 / 100 : ℝ) ≤ 55 / 100) hc.continuousOn hzero
  have hx₀ : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hx₁ : x < 1 := lt_of_le_of_lt hx.2 (by norm_num)
  refine ⟨x, ⟨⟨hx₀, hx₁⟩, (biot_compressed_polynomial x hx₁).mpr hfx⟩, ?_⟩
  have hMono : StrictMonoOn f (Set.Ici 0) := by
    intro a ha b _ hab
    have ha' : 0 ≤ a := ha
    have h₂ : a ^ 2 ≤ b ^ 2 := by gcongr
    have h₃ : a ^ 3 ≤ b ^ 3 := by gcongr
    dsimp [f]
    linarith
  intro y hy
  exact hMono.injOn hy.1.1.le hx₀.le
    (((biot_compressed_polynomial y hy.1.2).mp hy.2 : f y = 0).trans hfx.symm)

theorem biot_reported_value_not_root :
    (57 / 100 : ℝ) ^ 4 - 2 * (57 / 100) + 1 ≠ 0 := by
  norm_num

/-- A rational enclosure of width 10⁻⁵ for the strict-compression root. -/
theorem biot_compressed_root_decimal_bounds (stretch : ℝ) (hs : 0 < stretch)
    (hc : stretch < 1) (h : stretch ^ 4 - 2 * stretch + 1 = 0) :
    (54368 / 100000 : ℝ) < stretch ∧ stretch < (54369 / 100000 : ℝ) := by
  have hr := (biot_compressed_polynomial stretch hc).mp h
  have hmono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
      x ^ 3 + x ^ 2 + x - 1 ≤ y ^ 3 + y ^ 2 + y - 1 := by gcongr
  constructor
  · by_contra! hh
    have he := hmono hs.le hh
    rw [hr] at he
    norm_num at he
  · by_contra! hh
    have he := hmono (by norm_num : (0 : ℝ) ≤ 54369 / 100000) hh
    rw [hr] at he
    norm_num at he

end

end LeanSolid.ContinuumMechanics.Hyperelasticity
