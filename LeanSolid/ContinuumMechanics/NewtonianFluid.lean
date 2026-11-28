module

public import LeanSolid.ContinuumMechanics.Rates
public import LeanSolid.ContinuumMechanics.BoundaryFlux
public import LeanSolid.LinearElasticity.Theorems
import LeanSolid.LinearElasticity.Kinematics
import LeanSolid.Math.Calculus.Theorems
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

open scoped Matrix ContDiff

namespace LeanSolid.ContinuumMechanics.NewtonianFluid

open LeanSolid.Math

variable {n : ℕ}

/-- Constitutive stress of an incompressible Newtonian fluid for supplied pressure and rate D. -/
noncomputable def stress (p mu : ℝ) (D : Tensor n) : Tensor n :=
  (-p) • (1 : Tensor n) + (2 * mu) • D

theorem stress_transpose (p mu : ℝ) (L : Tensor n) :
    (stress p mu (rateOfDeformation L)).transpose = stress p mu (rateOfDeformation L) := by
  simp [stress, rateOfDeformation_transpose]

theorem stressPower (p mu : ℝ) (D : Tensor n) (hD : D.trace = 0) :
    contract (stress p mu D) D = 2 * mu * contract D D := by
  rw [stress, contract_add_left, contract_smul_left, contract_smul_left, contract_one_left, hD,
    mul_zero, zero_add]

theorem dissipation_nonneg (p mu : ℝ) (D : Tensor n) (hD : D.trace = 0) (hmu : 0 ≤ mu) :
    0 ≤ contract (stress p mu D) D := by
  rw [stressPower p mu D hD]
  exact mul_nonneg (mul_nonneg (by norm_num) hmu) (contract_self_nonneg D)

/-- Streamwise velocity between plates at y=0 and y=h, with upper wall speed U. -/
noncomputable def couette (h U y : ℝ) : ℝ := (U / h) * y

/-- Pressure-driven velocity between stationary plates. `g` is the signed pressure gradient. -/
noncomputable def poiseuille (h mu g y : ℝ) : ℝ := (g / (2 * mu)) * (y ^ 2 - h * y)

theorem couette_profile (h U mu : ℝ) (hh : h ≠ 0) (y : ℝ) :
    couette h U 0 = 0 ∧ couette h U h = U ∧
      mu * deriv (deriv (couette h U)) y = 0 := by
  have hd : deriv (couette h U) = fun _ => U / h := by
    funext r
    change deriv (fun y => (U / h) * y) r = U / h
    simp
  rw [hd]
  simp [couette, div_mul_cancel₀ _ hh]

theorem poiseuille_profile (h mu g : ℝ) (hmu : mu ≠ 0) (y : ℝ) :
    poiseuille h mu g 0 = 0 ∧ poiseuille h mu g h = 0 ∧
      mu * deriv (deriv (poiseuille h mu g)) y = g := by
  let c := g / (2 * mu)
  have hd : deriv (poiseuille h mu g) = fun r => c * (2 * r - h) := by
    funext r
    have hh := ((hasDerivAt_pow 2 r).sub ((hasDerivAt_id r).const_mul h)).const_mul c
    have he := hh.deriv
    change deriv (fun y => c * (y ^ 2 - h * y)) r = _ at he
    change deriv (fun y => c * (y ^ 2 - h * y)) r = _
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using he
  have hdd : deriv (fun r => c * (2 * r - h)) y = c * 2 := by
    simp
  rw [hd, hdd]
  refine ⟨by simp [poiseuille], by simp [poiseuille, pow_two], ?_⟩
  dsimp [c]
  field_simp

/-- For a divergence-free velocity and constant viscosity, the divergence
of the Newtonian stress is minus the pressure gradient plus μ Δv. -/
theorem tensorDivergence_stress_incompressible (p : Vector n → ℝ) (mu : ℝ)
    (v : Vector n → Vector n) (hp : Differentiable ℝ p)
    (hv : ∀ i, ContDiff ℝ 2 (fun x => v x i))
    (hMass : ∀ x, spatialDivergence v x = 0) (x : Vector n) (i : Fin n) :
    tensorDivergence (fun y => stress (p y) mu (rateOfDeformation (deformationGradient v y))) x i =
      mu * laplacian (fun y => v y i) x - partialDeriv p i x := by
  classical
  let E (y : Vector n) := LeanSolid.LinearElasticity.stress 0 mu (LeanSolid.LinearElasticity.strainField v y)
  have hd (k j : Fin n) : Differentiable ℝ (partialDeriv (fun y => v y k) j) :=
    (contDiff_partial (hv k) (k := 1) (by norm_num) j).differentiable one_ne_zero
  have hE (j : Fin n) :
      (fun y => E y i j) = (fun y => mu *
        (partialDeriv (fun z => v z i) j y + partialDeriv (fun z => v z j) i y)) := by
    funext y
    simp only [E, LeanSolid.LinearElasticity.stress, LeanSolid.LinearElasticity.strainField_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, zero_mul, zero_add]
    ring
  have hsplit (j : Fin n) :
      (fun y => stress (p y) mu (rateOfDeformation (deformationGradient v y)) i j) =
      fun y => (if i = j then -p y else 0) + E y i j := by
    funext y
    change ((-p y) • (1 : Tensor n) + (2 * mu) • LeanSolid.LinearElasticity.strainField v y) i j = _
    simp only [E, LeanSolid.LinearElasticity.stress, zero_mul, zero_smul, zero_add, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  have hterm (j : Fin n) :
      partialDeriv (fun y => stress (p y) mu (rateOfDeformation (deformationGradient v y)) i j) j x =
        (if i = j then -partialDeriv p j x else 0) + partialDeriv (fun y => E y i j) j x := by
    have hdE : Differentiable ℝ (fun y => E y i j) := by
      rw [hE j]
      exact ((hd i j).add (hd j i)).const_mul mu
    rw [hsplit]
    by_cases hij : i = j
    · simp only [ite_eq_left hij]
      have he := congrFun (partial_add hp.neg hdE j) x
      change partialDeriv (fun y => -p y + E y i j) j x =
        partialDeriv (fun y => -p y) j x + partialDeriv (fun y => E y i j) j x at he
      rwa [partial_neg] at he
    · simp only [hij, ite_false, zero_add]
  have hDiv : (fun y => ∑ j, partialDeriv (fun z => v z j) j y) = fun _ => 0 :=
    funext fun y => hMass y
  have he := LeanSolid.LinearElasticity.tensorDivergence_stress_strainField 0 mu v hv x i
  rw [hDiv, partial_const] at he
  simp only [zero_add, mul_zero, add_zero] at he
  change (∑ j, partialDeriv (fun y => stress (p y) mu
    (rateOfDeformation (deformationGradient v y)) i j) j x) = _
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change -partialDeriv p i x + tensorDivergence E x i = _
  rw [show tensorDivergence E x i = _ from he]
  ring

/-- The local stress-divergence form of momentum balance is equivalent to
the incompressible Navier–Stokes component equations. The acceleration is
supplied as local velocity rate plus convective acceleration. -/
theorem momentumBalance_iff_navierStokes (p : Vector n → ℝ) (mu ρ : ℝ)
    (v : Vector n → Vector n) (hp : Differentiable ℝ p)
    (hv : ∀ i, ContDiff ℝ 2 (fun x => v x i))
    (hMass : ∀ x, spatialDivergence v x = 0) (x localRate body : Vector n) :
    (tensorDivergence (fun y => stress (p y) mu (rateOfDeformation (deformationGradient v y))) x +
      body = ρ • (localRate + deformationGradient v x *ᵥ v x)) ↔
    ∀ i, ρ * (localRate i + (deformationGradient v x *ᵥ v x) i) =
      mu * laplacian (fun y => v y i) x - partialDeriv p i x + body i := by
  rw [funext_iff]
  apply forall_congr'
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    tensorDivergence_stress_incompressible p mu v hp hv hMass x i, eq_comm]

/-- Along a fluid trajectory the acceleration is the sum of the local
time derivative and the velocity-gradient convective term. -/
theorem hasDerivAt_materialVelocity {u : ℝ × Vector n → Vector n}
    {path : ℝ → Vector n} {t : ℝ}
    (hu : DifferentiableAt ℝ u (t, path t))
    (hPath : HasDerivAt path (u (t, path t)) t) :
    HasDerivAt (fun s => u (s, path s))
      (fderiv ℝ u (t, path t) (1, 0) +
        deformationGradient (fun y => u (t, y)) (path t) *ᵥ u (t, path t)) t := by
  let L := ContinuousLinearMap.inr ℝ ℝ (Vector n)
  have hSpace : HasFDerivAt (fun y : Vector n => (t, y)) L (path t) := by
    have h := L.hasFDerivAt (x := path t) |>.add_const (t, (0 : Vector n))
    simpa [L] using h
  have hFixed : HasFDerivAt (fun y => u (t, y))
      ((fderiv ℝ u (t, path t)).comp L) (path t) :=
    hu.hasFDerivAt.comp (path t) hSpace
  have hConv : deformationGradient (fun y => u (t, y)) (path t) *ᵥ u (t, path t) =
      fderiv ℝ u (t, path t) (0, u (t, path t)) := by
    rw [deformationGradient_eq_toMatrix hFixed.differentiableAt, hFixed.fderiv,
      ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  rw [hConv]
  have h := hu.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hPath)
  change HasDerivAt (fun s => u (s, path s)) (fderiv ℝ u (t, path t) (1, u (t, path t))) t at h
  have hsplit : ((1 : ℝ), u (t, path t)) = (1, 0) + (0, u (t, path t)) := by simp
  rwa [hsplit, map_add] at h

end LeanSolid.ContinuumMechanics.NewtonianFluid
