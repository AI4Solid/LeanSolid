module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Models
public import LeanSolid.ContinuumMechanics.Hyperelasticity.Incompressible
public import LeanSolid.ContinuumMechanics.GeometryRates
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

@[expose] public section

open LeanSolid.Math Filter
open scoped Matrix Matrix.Norms.Elementwise Topology

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

noncomputable section

variable {n : ℕ}

private theorem differentiable_saintVenantKirchhoff (lam mu : ℝ) :
    Differentiable ℝ (saintVenantKirchhoff lam mu : Tensor n → ℝ) := by
  have hentry (i j : Fin n) : Differentiable ℝ (fun E : Tensor n => E i j) := by
    have hi : Differentiable ℝ (fun E : Tensor n => E i) := differentiable_apply i
    have hj : Differentiable ℝ (fun v : Vector n => v j) := differentiable_apply j
    exact hj.comp hi
  have ht : Differentiable ℝ (fun E : Tensor n => E.trace) :=
    Differentiable.fun_sum fun i _ => hentry i i
  have hc : Differentiable ℝ (fun E : Tensor n => contract E E) :=
    Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ => (hentry i j).mul (hentry i j)
  have ht₂ : Differentiable ℝ (fun E : Tensor n => E.trace ^ (2 : ℕ)) := ht.pow 2
  have hvol : Differentiable ℝ (fun E : Tensor n => lam * E.trace ^ 2 / 2) := by
    rw [show (fun E : Tensor n => lam * E.trace ^ 2 / 2) =
        (fun E : Tensor n => (lam / 2) * E.trace ^ 2) by funext E; ring]
    exact ht₂.const_mul (lam / 2)
  exact hvol.add (hc.const_mul mu)

/-- The first Piola stress obtained from the Saint Venant–Kirchhoff energy. -/
theorem saintVenantKirchhoff_firstPiola (lam mu : ℝ) (F : Tensor n) :
    firstPiolaStress (fun A => saintVenantKirchhoff lam mu (greenStrain A)) F =
      F * LeanSolid.LinearElasticity.stress lam mu (greenStrain F) := by
  have hSym : (secondPiolaStress (saintVenantKirchhoff lam mu) (greenStrain F)).transpose =
      secondPiolaStress (saintVenantKirchhoff lam mu) (greenStrain F) := by
    rw [saintVenantKirchhoff_secondPiola]
    exact LeanSolid.LinearElasticity.stress_transpose lam mu _ (greenStrain_transpose F)
  rw [firstPiolaStress_greenStrain (differentiable_saintVenantKirchhoff lam mu).differentiableAt hSym,
    saintVenantKirchhoff_secondPiola]

private theorem hasTensorDerivAt_lameStress (lam mu : ℝ) {E : ℝ → Tensor n}
    {K : Tensor n} {t : ℝ} (h : HasTensorDerivAt E K t) :
    HasTensorDerivAt (fun s => LeanSolid.LinearElasticity.stress lam mu (E s))
      (LeanSolid.LinearElasticity.stress lam mu K) t := by
  have hTrace : HasDerivAt (fun s => (E s).trace) K.trace t :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h i i
  intro i j
  have hd := ((hTrace.const_mul lam).mul_const ((1 : Tensor n) i j)).add
    ((h i j).const_mul (2 * mu))
  change HasDerivAt (fun s => (lam * (E s).trace) * (1 : Tensor n) i j + 2 * mu * E s i j)
    ((lam * K.trace) * (1 : Tensor n) i j + 2 * mu * K i j) t at hd
  simpa only [LeanSolid.LinearElasticity.stress, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul] using hd

/-- Linearized Green–Lagrange strain at F in direction H. -/
def greenStrainIncrement (F H : Tensor n) : Tensor n :=
  (1 / 2 : ℝ) • (H.transpose * F + F.transpose * H)

/-- The Saint Venant–Kirchhoff material tangent acting on an incremental
deformation gradient. The two terms come from differentiating F and S. -/
def saintVenantKirchhoffTangent (lam mu : ℝ) (F H : Tensor n) : Tensor n :=
  H * LeanSolid.LinearElasticity.stress lam mu (greenStrain F) +
    F * LeanSolid.LinearElasticity.stress lam mu (greenStrainIncrement F H)

theorem hasTensorDerivAt_saintVenantKirchhoff_firstPiola (lam mu : ℝ)
    {F : ℝ → Tensor n} {H : Tensor n} {t : ℝ} (h : HasTensorDerivAt F H t) :
    HasTensorDerivAt
      (fun s => firstPiolaStress (fun A => saintVenantKirchhoff lam mu (greenStrain A)) (F s))
      (saintVenantKirchhoffTangent lam mu (F t) H) t := by
  simp only [saintVenantKirchhoff_firstPiola]
  exact h.mul (hasTensorDerivAt_lameStress lam mu (hasTensorDerivAt_greenStrain h))

theorem saintVenantKirchhoffTangent_reference (lam mu : ℝ) (H : Tensor n) :
    saintVenantKirchhoffTangent lam mu 1 H =
      LeanSolid.LinearElasticity.stress lam mu (LeanSolid.LinearElasticity.strain H) := by
  simp [saintVenantKirchhoffTangent, greenStrainIncrement, greenStrain_one,
    LeanSolid.LinearElasticity.stress, LeanSolid.LinearElasticity.strain, symPart, add_comm]

/-- The second-order work separates into the prestress contribution and
the quadratic Lamé energy of the incremental Green–Lagrange strain. -/
theorem saintVenantKirchhoffTangent_work (lam mu : ℝ) (F H : Tensor n) :
    contract (saintVenantKirchhoffTangent lam mu F H) H =
      contract (H * LeanSolid.LinearElasticity.stress lam mu (greenStrain F)) H +
        2 * LeanSolid.LinearElasticity.energyDensity lam mu (greenStrainIncrement F H) := by
  let K := greenStrainIncrement F H
  let S := LeanSolid.LinearElasticity.stress lam mu K
  have hK : K.transpose = K := by
    simp [K, greenStrainIncrement, Matrix.transpose_mul, add_comm]
  have hS : S.transpose = S := LeanSolid.LinearElasticity.stress_transpose lam mu K hK
  have hw : contract (F * S) H = contract S K := (greenStrain_work F S H hS).symm
  unfold saintVenantKirchhoffTangent
  rw [contract_add_left, show contract (F * S) H = contract S K from hw]
  rw [LeanSolid.LinearElasticity.energyDensity_eq_half_stress_contract]
  change _ + contract S K = _ + 2 * (contract S K / 2)
  ring

/-- A rank-one shear increment at a uniformly dilated state has an explicit
second-order work coefficient, including the hydrostatic prestress. -/
theorem saintVenantKirchhoffTangent_uniformDilation_shear (lam mu s : ℝ) :
    let H : Tensor 3 := Matrix.single 0 1 1
    contract (saintVenantKirchhoffTangent lam mu (s • (1 : Tensor 3)) H) H =
      (3 * lam + 2 * mu) * (s ^ 2 - 1) / 2 + mu * s ^ 2 := by
  dsimp only
  rw [contract_single_right]
  have hE : greenStrain (s • (1 : Tensor 3)) =
      ((s ^ 2 - 1) / 2) • (1 : Tensor 3) := by
    have hC : rightCauchyGreen (s • (1 : Tensor 3)) = (s ^ 2) • (1 : Tensor 3) := by
      rw [rightCauchyGreen, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
        Matrix.mul_smul, one_mul, smul_smul, pow_two]
    have hSub : (s ^ 2) • (1 : Tensor 3) - 1 = (s ^ 2 - 1) • (1 : Tensor 3) := by
      rw [sub_smul, one_smul]
    rw [greenStrain, hC, hSub, smul_smul]
    congr 1
    ring
  simp [saintVenantKirchhoffTangent, hE, greenStrainIncrement, LeanSolid.LinearElasticity.stress,
    Matrix.transpose_smul, Matrix.mul_add,
    Matrix.smul_apply, smul_eq_mul, Matrix.single, Matrix.trace_smul]
  ring

/-- A negative coefficient in the displayed rank-one shear direction rules
out positive work on every nonzero rank-one increment at that state. -/
theorem saintVenantKirchhoff_negativeShear_of_compression (lam mu s : ℝ)
    (h : (3 * lam + 2 * mu) * (s ^ 2 - 1) / 2 + mu * s ^ 2 < 0) :
    contract (saintVenantKirchhoffTangent lam mu (s • (1 : Tensor 3)) (Matrix.single 0 1 1))
      (Matrix.single 0 1 1) < 0 := by
  rw [saintVenantKirchhoffTangent_uniformDilation_shear]
  exact h

/-- Positive Lamé moduli at the reference state do not prevent a negative
rank-one tangent work at the orientation-preserving state F = I/2. -/
theorem saintVenantKirchhoff_compression_example :
    let F : Tensor 3 := (1 / 2 : ℝ) • (1 : Tensor 3)
    let H : Tensor 3 := Matrix.single 0 1 1
    0 < jacobian F ∧ contract (saintVenantKirchhoffTangent 1 1 F H) H < 0 := by
  dsimp only
  constructor
  · norm_num [jacobian]
  · apply saintVenantKirchhoff_negativeShear_of_compression
    norm_num

/-- At an isochoric state with zero Jacobian rate, the cofactor rate
coincides with the inverse-transpose rate. -/
theorem hasTensorDerivAt_cofactor_isochoric {F : ℝ → Tensor 3} {H : Tensor 3} {t : ℝ}
    (hF : HasTensorDerivAt F H t) (hJ : jacobian (F t) = 1)
    (hVol : HasDerivAt (fun s => jacobian (F s)) 0 t) :
    HasTensorDerivAt (fun s => (F s).adjugate.transpose)
      ((-(F t)⁻¹ * H * (F t)⁻¹).transpose) t := by
  have hne : jacobian (F t) ≠ 0 := by rw [hJ]; exact one_ne_zero
  have hInv := (hasTensorDerivAt_inverse hF hne).transpose
  have hNear := hVol.continuousAt.eventually_ne hne
  intro i j
  have hd := hVol.mul (hInv i j)
  change HasDerivAt (fun s => jacobian (F s) * ((F s)⁻¹).transpose i j)
    (0 * ((F t)⁻¹).transpose i j + jacobian (F t) *
      ((-(F t)⁻¹ * H * (F t)⁻¹).transpose) i j) t at hd
  rw [hJ, zero_mul, zero_add, one_mul] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hNear] with s hs
  exact congrArg (fun M : Tensor 3 => M i j) (cofactor_eq_jacobian_smul_invTranspose (F s) hs)

/-- Incremental nominal stress for the incompressible neo-Hookean law.
The pressure path may vary independently. -/
theorem hasTensorDerivAt_neoHookean_firstPiola_isochoric
    (mu : ℝ) {F : ℝ → Tensor 3} {H : Tensor 3} {p : ℝ → ℝ} {pdot t : ℝ}
    (hF : HasTensorDerivAt F H t) (hp : HasDerivAt p pdot t)
    (hJ : jacobian (F t) = 1) (hVol : HasDerivAt (fun s => jacobian (F s)) 0 t) :
    HasTensorDerivAt
      (fun s => firstPiolaStress (constrainedEnergy
        (fun A => incompressibleNeoHookean mu (rightCauchyGreen A)) (p s)) (F s))
      (mu • H - pdot • (F t).adjugate.transpose -
        p t • ((-(F t)⁻¹ * H * (F t)⁻¹).transpose)) t := by
  have hc := hasTensorDerivAt_cofactor_isochoric hF hJ hVol
  intro i j
  have hd := ((hF i j).const_mul mu).sub (hp.mul (hc i j))
  change HasDerivAt (fun s => mu * F s i j - p s * (F s).adjugate.transpose i j)
    (mu * H i j - (pdot * (F t).adjugate.transpose i j +
      p t * ((-(F t)⁻¹ * H * (F t)⁻¹).transpose) i j)) t at hd
  simpa only [incompressibleNeoHookean_firstPiola, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, sub_add_eq_sub_sub] using hd

/-- Push the incremental nominal stress to the current configuration
using the fixed base-state gradient. -/
theorem hasTensorDerivAt_neoHookean_pushedIncrement
    (mu : ℝ) {F : ℝ → Tensor 3} {H : Tensor 3} {p : ℝ → ℝ} {pdot t : ℝ}
    (hF : HasTensorDerivAt F H t) (hp : HasDerivAt p pdot t)
    (hJ : jacobian (F t) = 1) (hVol : HasDerivAt (fun s => jacobian (F s)) 0 t) :
    let L := velocityGradient (F t) H
    HasTensorDerivAt
      (fun s => firstPiolaStress (constrainedEnergy
        (fun A => incompressibleNeoHookean mu (rightCauchyGreen A)) (p s)) (F s) * (F t).transpose)
      (mu • (L * leftCauchyGreen (F t)) - pdot • (1 : Tensor 3) + p t • L.transpose) t := by
  intro L
  have hne : jacobian (F t) ≠ 0 := by rw [hJ]; exact one_ne_zero
  have hCof : (F t).adjugate.transpose * (F t).transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_adjugate, show (F t).det = 1 from hJ,
      one_smul, Matrix.transpose_one]
  have hInv : (F t)⁻¹ᵀ * (F t).transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hne),
      Matrix.transpose_one]
  have hRate : ((-(F t)⁻¹ * H * (F t)⁻¹).transpose) * (F t).transpose = -L.transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_assoc,
      hInv, mul_one, L, velocityGradient]
  have hLF : L * leftCauchyGreen (F t) = H * (F t).transpose := by
    rw [leftCauchyGreen, ← Matrix.mul_assoc, velocityGradient_mul (F t) H hne]
  have hd := (hasTensorDerivAt_neoHookean_firstPiola_isochoric mu hF hp hJ hVol).mul
    (hasTensorDerivAt_const (F t).transpose t)
  simpa only [Matrix.mul_zero, add_zero, Matrix.sub_mul, Matrix.smul_mul, hCof, hRate,
    smul_neg, sub_neg_eq_add, hLF] using hd

end

end LeanSolid.ContinuumMechanics.Hyperelasticity
