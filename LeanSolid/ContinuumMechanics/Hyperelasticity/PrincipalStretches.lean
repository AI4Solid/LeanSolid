module

public import LeanSolid.ContinuumMechanics.Hyperelasticity.Incompressible
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

@[expose] public section

open LeanSolid.Math Filter
open scoped Matrix Topology

namespace LeanSolid.ContinuumMechanics.Hyperelasticity

noncomputable section

/-- Ogden energy on a supplied tuple of principal stretches. Coefficients
include any normalization of the chosen Ogden parameters. -/
def ogdenPrincipalEnergy {m : ℕ} (weight exponent : Fin m → ℝ) (stretch : Vector 3) : ℝ :=
  ∑ k, weight k * ((∑ i, stretch i ^ exponent k) - 3)

/-- Principal stretch derivative of the Ogden energy. -/
def ogdenStretchDerivative {m : ℕ} (weight exponent : Fin m → ℝ)
    (stretch : Vector 3) (i : Fin 3) : ℝ :=
  ∑ k, weight k * (exponent k * stretch i ^ (exponent k - 1))

theorem hasDerivAt_ogdenPrincipalEnergy {m : ℕ} (weight exponent : Fin m → ℝ)
    {stretchPath : ℝ → Vector 3} {rate : Vector 3} {t : ℝ}
    (hPositive : ∀ i, 0 < stretchPath t i) (hRate : ∀ i, HasDerivAt (fun s => stretchPath s i) (rate i) t) :
    HasDerivAt (fun s => ogdenPrincipalEnergy weight exponent (stretchPath s))
      (∑ i, ogdenStretchDerivative weight exponent (stretchPath t) i * rate i) t := by
  have h (k : Fin m) (i : Fin 3) :
      HasDerivAt (fun s => stretchPath s i ^ exponent k)
        ((exponent k * stretchPath t i ^ (exponent k - 1)) * rate i) t := by
    have hd := (Real.hasDerivAt_rpow_const (Or.inl (hPositive i).ne') :
      HasDerivAt (fun x : ℝ => x ^ exponent k)
        (exponent k * stretchPath t i ^ (exponent k - 1)) (stretchPath t i)).comp t (hRate i)
    exact hd
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    ((HasDerivAt.fun_sum (u := Finset.univ) fun i _ => h k i).sub_const 3).const_mul (weight k)
  have he :
      (∑ k, weight k * ∑ i, (exponent k * stretchPath t i ^ (exponent k - 1)) * rate i) =
      ∑ i, ogdenStretchDerivative weight exponent (stretchPath t) i * rate i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [ogdenStretchDerivative, Finset.sum_mul, mul_assoc]
  rw [he] at hd
  exact hd

/-- Under the incompressible principal-stretch stress law, the Cauchy stress
component equals the stretch times its energy derivative minus pressure. -/
def ogdenPrincipalStress {m : ℕ} (weight exponent : Fin m → ℝ) (stretch : Vector 3)
    (p : ℝ) (i : Fin 3) : ℝ :=
  stretch i * ogdenStretchDerivative weight exponent stretch i - p

theorem ogdenPrincipalStress_eq_sum {m : ℕ} (weight exponent : Fin m → ℝ)
    (stretch : Vector 3) (p : ℝ) (i : Fin 3) (h : 0 < stretch i) :
    ogdenPrincipalStress weight exponent stretch p i =
      (∑ k, weight k * exponent k * stretch i ^ exponent k) - p := by
  unfold ogdenPrincipalStress ogdenStretchDerivative
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hp : stretch i * stretch i ^ (exponent k - 1) = stretch i ^ exponent k := by
    calc
      _ = stretch i ^ (1 : ℝ) * stretch i ^ (exponent k - 1) := by rw [Real.rpow_one]
      _ = stretch i ^ (1 + (exponent k - 1)) := (Real.rpow_add h _ _).symm
      _ = _ := by rw [show 1 + (exponent k - 1) = exponent k by ring]
  calc
    _ = (weight k * exponent k) * (stretch i * stretch i ^ (exponent k - 1)) := by ring
    _ = _ := by rw [hp]

/-- For a uniaxial stretch with equal transverse stretches, eliminating
pressure by imposing zero transverse stress gives the axial stress. -/
theorem ogden_uniaxial_stress {m : ℕ} (weight exponent : Fin m → ℝ)
    (axial r p : ℝ) (hAxial : 0 < axial) (hr : 0 < r)
    (hTransverse : ogdenPrincipalStress weight exponent ![axial, r, r] p 1 = 0) :
    ogdenPrincipalStress weight exponent ![axial, r, r] p 0 =
      ∑ k, weight k * exponent k * (axial ^ exponent k - r ^ exponent k) := by
  have hp : p = ∑ k, weight k * exponent k * r ^ exponent k := by
    rw [ogdenPrincipalStress_eq_sum _ _ _ _ _ (show 0 < (![axial, r, r] : Vector 3) 1 from hr)] at hTransverse
    exact (sub_eq_zero.mp hTransverse).symm
  rw [ogdenPrincipalStress_eq_sum _ _ _ _ _ (show 0 < (![axial, r, r] : Vector 3) 0 from hAxial),
    hp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  change weight k * exponent k * axial ^ exponent k - weight k * exponent k * r ^ exponent k =
    weight k * exponent k * (axial ^ exponent k - r ^ exponent k)
  ring

/-- In incompressible uniaxial deformation the transverse stretch is
the inverse square root of the axial stretch. -/
theorem jacobian_uniaxial_isochoric (axial : ℝ) (h : 0 < axial) :
    let lateral := axial ^ (-(1 / 2) : ℝ)
    jacobian (Matrix.diagonal (![axial, lateral, lateral] : Vector 3)) = 1 := by
  intro lateral
  have hl : lateral * lateral = axial⁻¹ := by
    dsimp only [lateral]
    rw [← Real.rpow_add h, show (-(1 / 2) : ℝ) + (-(1 / 2)) = -1 by norm_num,
      Real.rpow_neg_one]
  simp only [jacobian, Matrix.det_diagonal, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  change axial * (lateral * lateral) = 1
  rw [hl, mul_inv_cancel₀ h.ne']

theorem ogden_uniaxial_isochoric_stress {m : ℕ} (weight exponent : Fin m → ℝ)
    (axial p : ℝ) (h : 0 < axial) :
    let lateral := axial ^ (-(1 / 2) : ℝ)
    ogdenPrincipalStress weight exponent ![axial, lateral, lateral] p 1 = 0 →
    ogdenPrincipalStress weight exponent ![axial, lateral, lateral] p 0 =
      ∑ k, weight k * exponent k * (axial ^ exponent k - axial ^ (-(1 / 2) * exponent k)) := by
  intro lateral ht
  have hl : 0 < lateral := Real.rpow_pos_of_pos h _
  rw [ogden_uniaxial_stress weight exponent axial lateral p h hl ht]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Real.rpow_mul h.le]

/-- If a tensor energy agrees with the Ogden law on positive diagonal
gradients, a coordinate stretch variation recovers the diagonal Piola
component from its tensor energy gradient. -/
theorem energyGradient_diagonal_eq_ogdenStretchDerivative {m : ℕ} (weight exponent : Fin m → ℝ)
    (W : Tensor 3 → ℝ) (stretch : Vector 3) (G : Tensor 3)
    (hPositive : ∀ j, 0 < stretch j)
    (hDiagonal : ∀ a : Vector 3, (∀ j, 0 < a j) →
      W (Matrix.diagonal a) = ogdenPrincipalEnergy weight exponent a)
    (hW : HasEnergyGradient W (Matrix.diagonal stretch) G) (i : Fin 3) :
    G i i = ogdenStretchDerivative weight exponent stretch i := by
  let e : Vector 3 := Pi.single i 1
  let s (t : ℝ) : Vector 3 := fun j => stretch j + t * e j
  have hs (j : Fin 3) : HasDerivAt (fun t => s t j) (e j) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).mul_const (e j)).const_add (stretch j)
    simpa only [id_eq, one_mul, s] using h
  have hs₀ : s 0 = stretch := by funext j; simp [s]
  have ht : HasTensorDerivative (fun t => Matrix.diagonal (s t)) (Matrix.diagonal e) := by
    intro j k
    by_cases h : j = k
    · subst k
      simpa only [Matrix.diagonal_apply_eq] using hs j
    · simpa only [Matrix.diagonal_apply_ne _ h] using (hasDerivAt_const 0 (0 : ℝ))
  have hMatrix := hW _ _ (congrArg Matrix.diagonal hs₀) ht
  have hOgden := hasDerivAt_ogdenPrincipalEnergy weight exponent
    (show ∀ j, 0 < s 0 j by rw [hs₀]; exact hPositive) hs
  have hAgree : (fun t => W (Matrix.diagonal (s t))) =ᶠ[𝓝 0]
      fun t => ogdenPrincipalEnergy weight exponent (s t) := by
    have hall : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j, 0 < s t j := by
      apply eventually_all.mpr
      intro j
      exact (hs j).continuousAt.tendsto.eventually (Ioi_mem_nhds (by rw [hs₀]; exact hPositive j))
    exact hall.mono fun _ h => hDiagonal _ h
  have hh := hMatrix.unique (hOgden.congr_of_eventuallyEq hAgree)
  simpa [contract, Matrix.diagonal_apply, Pi.single_apply, e, hs₀, mul_ite] using hh

/-- At a positive diagonal isochoric deformation, a tensor energy with the
Ogden restriction gives the principal Cauchy stress including the pressure. -/
theorem cauchy_diagonal_ogden {m : ℕ} (weight exponent : Fin m → ℝ)
    (W : Tensor 3 → ℝ) (stretch : Vector 3) (G : Tensor 3) (p : ℝ)
    (hPositive : ∀ j, 0 < stretch j)
    (hDiagonal : ∀ a : Vector 3, (∀ j, 0 < a j) →
      W (Matrix.diagonal a) = ogdenPrincipalEnergy weight exponent a)
    (hW : HasEnergyGradient W (Matrix.diagonal stretch) G)
    (hJ : jacobian (Matrix.diagonal stretch) = 1) (i : Fin 3) :
    cauchyFromPiola (Matrix.diagonal stretch)
      (firstPiolaStress (constrainedEnergy W p) (Matrix.diagonal stretch)) i i =
      ogdenPrincipalStress weight exponent stretch p i := by
  have hn : jacobian (Matrix.diagonal stretch) ≠ 0 := by rw [hJ]; exact one_ne_zero
  have hP := (hasEnergyGradient_constrainedEnergy hW p).eq_energyGradient
  change firstPiolaStress (constrainedEnergy W p) (Matrix.diagonal stretch) = _ at hP
  rw [hP, cauchyFromPiola_pressure _ _ _ hn, cauchyFromPiola, hJ, inv_one, one_smul,
    Matrix.diagonal_transpose]
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, ogdenPrincipalStress,
    energyGradient_diagonal_eq_ogdenStretchDerivative weight exponent W stretch G hPositive hDiagonal hW i]
  rw [mul_comm]

end

end LeanSolid.ContinuumMechanics.Hyperelasticity
