module

public import LeanSolid.ContinuumMechanics.Momentum
import LeanSolid.Math.Calculus.Theorems
import LeanSolid.Math.Theorems
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix

@[expose] public section

open LeanSolid.Math MeasureTheory Set
open scoped Matrix ContDiff

namespace LeanSolid.ContinuumMechanics

/-- Flux whose normal component is the power of the Cauchy traction. -/
def stressPowerFlux {n : ℕ} (σ : Vector n → Tensor n) (v : Vector n → Vector n)
    (x : Vector n) : Vector n :=
  (σ x).transpose *ᵥ v x

theorem stressPowerFlux_dot_normal {n : ℕ} (σ : Vector n → Tensor n)
    (v : Vector n → Vector n) (x normal : Vector n) :
    stressPowerFlux σ v x ⬝ᵥ normal = v x ⬝ᵥ (σ x *ᵥ normal) := by
  rw [dotProduct_comm (stressPowerFlux σ v x) normal, stressPowerFlux,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

/-- The divergence of traction power splits into the power of the stress
divergence and the local stress working against the velocity gradient. -/
theorem spatialDivergence_stressPowerFlux {n : ℕ} (σ : Vector n → Tensor n)
    (v : Vector n → Vector n)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hv : ∀ i, Differentiable ℝ (fun x => v x i)) (x : Vector n) :
    spatialDivergence (stressPowerFlux σ v) x =
      v x ⬝ᵥ tensorDivergence σ x + contract (σ x) (deformationGradient v x) := by
  have hsum (j : Fin n) :
      partialDeriv (fun y => stressPowerFlux σ v y j) j x =
        ∑ i, partialDeriv (fun y => σ y i j * v y i) j x := by
    change partialDeriv (fun y => ∑ i, σ y i j * v y i) j x = _
    unfold partialDeriv
    have hd : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        DifferentiableAt ℝ (fun y => σ y i j * v y i) x :=
      fun i _ => ((hσ i j).mul (hv i)) x
    exact (congrArg (fun f : Vector n →L[ℝ] ℝ => f (Pi.single j 1))
      (fderiv_fun_sum hd)).trans (sum_apply _ _ _)
  have hp (i j : Fin n) :
      partialDeriv (fun y => σ y i j * v y i) j x =
        partialDeriv (fun y => σ y i j) j x * v x i +
        σ x i j * partialDeriv (fun y => v y i) j x :=
    congrFun (partial_mul (hσ i j) (hv i) j) x
  change (∑ j, partialDeriv (fun y => stressPowerFlux σ v y j) j x) = _
  simp only [hsum, hp]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, dotProduct, tensorDivergence,
    contract, deformationGradient, Matrix.of_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- For symmetric Cauchy stress, the local stress working depends on the
symmetric velocity gradient. -/
theorem spatialDivergence_stressPowerFlux_of_symmetric {n : ℕ} (σ : Vector n → Tensor n)
    (v : Vector n → Vector n) (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hv : ∀ i, Differentiable ℝ (fun x => v x i)) (x : Vector n)
    (hs : (σ x).transpose = σ x) :
    spatialDivergence (stressPowerFlux σ v) x =
      v x ⬝ᵥ tensorDivergence σ x + contract (σ x) (rateOfDeformation (deformationGradient v x)) := by
  rw [spatialDivergence_stressPowerFlux σ v hσ hv, rateOfDeformation,
    contract_comm (σ x) (symPart (deformationGradient v x)),
    contract_symPart_of_symmetric _ _ hs, contract_comm]

/-- Specific kinetic energy along a path has rate v · a. -/
theorem hasDerivAt_specificKineticEnergy {n : ℕ} {v : ℝ → Vector n} {a : Vector n} {t : ℝ}
    (hv : ∀ i, HasDerivAt (fun s => v s i) (a i) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * (v s ⬝ᵥ v s)) (v t ⬝ᵥ a) t := by
  have h (i : Fin n) :
      HasDerivAt (fun s => v s i * v s i) (2 * (v t i * a i)) t := by
    have hd := (hv i).mul (hv i)
    change HasDerivAt (fun s => v s i * v s i) (a i * v t i + v t i * a i) t at hd
    convert hd using 1
    ring
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)).const_mul (1 / 2 : ℝ)
  rw [← Finset.mul_sum, ← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul] at hd
  exact hd

/-- Contracting linear momentum with velocity gives the local kinetic-energy
balance with kinetic rate v · a and stress power σ : D. Body is a force
per current volume and ρ is the current mass density. -/
theorem local_kineticEnergyBalance {n : ℕ} (σ : Vector n → Tensor n) (v : Vector n → Vector n)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (x body a : Vector n) (ρ : ℝ) (hs : (σ x).transpose = σ x)
    (hMomentum : tensorDivergence σ x + body - ρ • a = 0) :
    ρ * (v x ⬝ᵥ a) =
      spatialDivergence (stressPowerFlux σ v) x + v x ⬝ᵥ body -
        contract (σ x) (rateOfDeformation (deformationGradient v x)) := by
  have h := congrArg (dotProduct (v x)) hMomentum
  simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero] at h
  rw [spatialDivergence_stressPowerFlux_of_symmetric σ v hσ hv x hs]
  linarith

/-- After subtracting the kinetic balance, the first law for total energy
is equivalent to the internal-energy equation. A positive heat-flux
divergence removes heat and a positive heat source adds it. -/
theorem local_totalEnergyBalance_iff_internal
    (ρ kineticRate internalRate tractionPowerDiv bodyPower stressPower heatDiv heatSource : ℝ)
    (hKinetic : ρ * kineticRate = tractionPowerDiv + bodyPower - stressPower) :
    (ρ * (internalRate + kineticRate) = tractionPowerDiv + bodyPower - heatDiv + heatSource) ↔
      ρ * internalRate = stressPower - heatDiv + heatSource := by
  rw [mul_add]
  constructor <;> intro h <;> linarith

/-- The flux of energy supplied to a control volume by surface traction
and heat across its boundary. The heat flux is positive outward. -/
def surfaceEnergyFlux {n : ℕ} (σ : Vector n → Tensor n) (v q : Vector n → Vector n)
    (x : Vector n) : Vector n :=
  stressPowerFlux σ v x - q x

theorem surfaceEnergyFlux_dot_normal {n : ℕ} (σ : Vector n → Tensor n)
    (v q : Vector n → Vector n) (x normal : Vector n) :
    surfaceEnergyFlux σ v q x ⬝ᵥ normal =
      v x ⬝ᵥ (σ x *ᵥ normal) - q x ⬝ᵥ normal := by
  rw [surfaceEnergyFlux, sub_dotProduct, stressPowerFlux_dot_normal]

theorem differentiable_stressPowerFlux_component {n : ℕ}
    (σ : Vector n → Tensor n) (v : Vector n → Vector n)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hv : ∀ i, Differentiable ℝ (fun x => v x i)) (j : Fin n) :
    Differentiable ℝ (fun x => stressPowerFlux σ v x j) := by
  change Differentiable ℝ (fun x => ∑ i, σ x i j * v x i)
  exact Differentiable.fun_sum fun i _ => (hσ i j).mul (hv i)

theorem spatialDivergence_surfaceEnergyFlux {n : ℕ} (σ : Vector n → Tensor n)
    (v q : Vector n → Vector n)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hq : ∀ i, Differentiable ℝ (fun x => q x i)) (x : Vector n) :
    spatialDivergence (surfaceEnergyFlux σ v q) x =
      spatialDivergence (stressPowerFlux σ v) x - spatialDivergence q x := by
  have hd (j : Fin n) := congrFun
    (partial_sub (differentiable_stressPowerFlux_component σ v hσ hv j) (hq j) j) x
  change (∑ j, partialDeriv (fun y => stressPowerFlux σ v y j - q y j) j x) =
    (∑ j, partialDeriv (fun y => stressPowerFlux σ v y j) j x) -
      ∑ j, partialDeriv (fun y => q y j) j x
  simp only [hd, Finset.sum_sub_distrib]

/-- Combining momentum and stress symmetry with the heat-flux sign
convention gives the local first law in total- and internal-energy forms. -/
theorem local_totalEnergyBalance_iff_internal_of_momentum {n : ℕ}
    (σ : Vector n → Tensor n) (v q : Vector n → Vector n)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hq : ∀ i, Differentiable ℝ (fun x => q x i))
    (x body acceleration : Vector n) (ρ edot heatSource : ℝ)
    (hs : (σ x).transpose = σ x)
    (hMomentum : tensorDivergence σ x + body - ρ • acceleration = 0) :
    (ρ * (edot + v x ⬝ᵥ acceleration) =
      spatialDivergence (surfaceEnergyFlux σ v q) x + v x ⬝ᵥ body + heatSource) ↔
    ρ * edot = contract (σ x) (rateOfDeformation (deformationGradient v x)) -
      spatialDivergence q x + heatSource := by
  have hKinetic := local_kineticEnergyBalance σ v hσ hv x body acceleration ρ hs hMomentum
  rw [spatialDivergence_surfaceEnergyFlux σ v q hσ hv hq, mul_add]
  constructor <;> intro h <;> linarith

/-- With mass conservation, the total energy per unit reference volume
has rate equal to reference mass times the sum of the two specific rates. -/
theorem hasDerivAt_materialTotalEnergy {F : ℝ → Tensor 3} {H : Tensor 3}
    {ρ e : ℝ → ℝ} {v : ℝ → Vector 3} {a : Vector 3} {t ρdot edot : ℝ}
    (hF : HasTensorDerivAt F H t) (hρ : HasDerivAt ρ ρdot t)
    (he : HasDerivAt e edot t) (hv : ∀ i, HasDerivAt (fun s => v s i) (a i) t)
    (hJ : jacobian (F t) ≠ 0)
    (hMass : ρdot + ρ t * (velocityGradient (F t) H).trace = 0) :
    HasDerivAt (fun s => (ρ s * jacobian (F s)) * (e s + (1 / 2 : ℝ) * (v s ⬝ᵥ v s)))
      ((ρ t * jacobian (F t)) * (edot + v t ⬝ᵥ a)) t := by
  have h := he.add (hasDerivAt_specificKineticEnergy hv)
  change HasDerivAt (fun s => e s + (1 / 2 : ℝ) * (v s ⬝ᵥ v s)) _ t at h
  exact hasDerivAt_materialMomentum_of_continuity hF hρ h hJ hMass

/-- On a moving deformed box, the local total-energy law gives its integral
form. The material transport derivative is supplied by transport of specific
total energy and mass, and the boundary term is evaluated on reference faces. -/
theorem hasDerivAt_totalEnergy_imageBox {a b : Vector 3} (hab : a ≤ b)
    (χ : ℝ → Vector 3 → Vector 3) (t : ℝ) (energyDensity : ℝ → Vector 3 → ℝ)
    (rate source : Vector 3 → ℝ) (σ : Vector 3 → Tensor 3) (v q : Vector 3 → Vector 3)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ t X i))
    (hInj : InjOn (χ t) (Icc a b))
    (hJ : ∀ X ∈ Icc a b, 0 < jacobian (deformationGradient (χ t) X))
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hq : ∀ i, Differentiable ℝ (fun x => q x i))
    (hFluxInt : IntegrableOn (spatialDivergence (surfaceEnergyFlux σ v q)) (χ t '' Icc a b))
    (hPullback : IntegrableOn (spatialDivergence (piolaFlux (χ t) (surfaceEnergyFlux σ v q))) (Icc a b))
    (hSource : IntegrableOn source (χ t '' Icc a b))
    (hLocal : ∀ x ∈ χ t '' Icc a b, rate x = spatialDivergence (surfaceEnergyFlux σ v q) x + source x)
    (hTransport : HasDerivAt (fun s => ∫ x in χ s '' Icc a b, energyDensity s x)
      (∫ x in χ t '' Icc a b, rate x) t) :
    HasDerivAt (fun s => ∫ x in χ s '' Icc a b, energyDensity s x)
      (boxBoundaryFlux a b (piolaFlux (χ t) (surfaceEnergyFlux σ v q)) +
        ∫ x in χ t '' Icc a b, source x) t := by
  have hMeas : MeasurableSet (χ t '' Icc a b) :=
    (isCompact_Icc.image (continuous_pi fun j => (hχ j).continuous)).isClosed.measurableSet
  have hdiff : Differentiable ℝ (surfaceEnergyFlux σ v q) := differentiable_pi.mpr fun j =>
    (differentiable_stressPowerFlux_component σ v hσ hv j).sub (hq j)
  have he : (∫ x in χ t '' Icc a b, rate x) =
      (∫ x in χ t '' Icc a b, spatialDivergence (surfaceEnergyFlux σ v q) x) +
        (∫ x in χ t '' Icc a b, source x) :=
    (setIntegral_congr_fun hMeas hLocal).trans (integral_add hFluxInt hSource)
  rw [he, integral_spatialDivergence_image_box hab (χ t) _ hχ hdiff hInj hJ hPullback] at hTransport
  exact hTransport

/-- The total-energy law can also be localized from moving deformed-box
balances by comparing the transport and applied-energy derivatives. -/
theorem local_totalEnergyBalance_of_imageBoxRates {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (χ : ℝ → Vector 3 → Vector 3) (t : ℝ) (energyDensity : ℝ → Vector 3 → ℝ)
    (flux : Vector 3 → Vector 3) (rate source : Vector 3 → ℝ)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ t X i))
    (hInj : InjOn (χ t) Ω)
    (hJ : ∀ X ∈ Ω, 0 < jacobian (deformationGradient (χ t) X))
    (hFlux : Differentiable ℝ flux) (hDiv : Continuous (spatialDivergence flux))
    (hRate : Continuous rate) (hSource : Continuous source)
    (hBalance : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω →
      let E (s : ℝ) := ∫ x in χ s '' Icc a b, energyDensity s x
      HasDerivAt E (∫ x in χ t '' Icc a b, rate x) t ∧
      HasDerivAt E (boxBoundaryFlux a b (piolaFlux (χ t) flux) +
        ∫ x in χ t '' Icc a b, source x) t) :
    ∀ x ∈ χ t '' Ω, rate x = spatialDivergence flux x + source x := by
  let J (X : Vector 3) := jacobian (deformationGradient (χ t) X)
  let R (X : Vector 3) := J X * rate (χ t X)
  let D (X : Vector 3) := J X * spatialDivergence flux (χ t X)
  let S (X : Vector 3) := J X * source (χ t X)
  have hχ' : Differentiable ℝ (χ t) :=
    differentiable_pi.mpr fun i => (hχ i).differentiable (by norm_num)
  have hj : Continuous J := by
    apply Continuous.matrix_det
    exact continuous_pi fun i => continuous_pi fun j =>
      (contDiff_partial (hχ i) (k := 1) (by norm_num) j).continuous
  have hR : Continuous R := hj.mul (hRate.comp hχ'.continuous)
  have hD : Continuous D := hj.mul (hDiv.comp hχ'.continuous)
  have hS : Continuous S := hj.mul (hSource.comp hχ'.continuous)
  rintro _ ⟨X, hX, rfl⟩
  have hz : R X - (D X + S X) = 0 := by
    apply eq_zero_of_integral_box_eq_zero hΩ
      (fun Y => R Y - (D Y + S Y)) (hR.sub (hD.add hS)) _ hX
    intro a b hab hsub
    have hp (g : Vector 3 → ℝ) :
        (∫ x in χ t '' Icc a b, g x) = ∫ Y in Icc a b, J Y * g (χ t Y) :=
      integral_image_placement volume measurableSet_Icc (χ t) (fun Y _ => hχ' Y)
        (hInj.mono hsub) (fun Y hY => hJ Y (hsub hY)) g
    have hPull : spatialDivergence (piolaFlux (χ t) flux) = D :=
      funext fun Y => spatialDivergence_piolaFlux (χ t) flux hχ hFlux Y
    have hBoundary : (∫ x in χ t '' Icc a b, spatialDivergence flux x) =
        boxBoundaryFlux a b (piolaFlux (χ t) flux) :=
      integral_spatialDivergence_image_box hab (χ t) flux hχ hFlux (hInj.mono hsub)
        (fun Y hY => hJ Y (hsub hY)) (by rw [hPull]; exact hD.integrableOn_Icc)
    obtain ⟨hTransport, hSupplied⟩ := hBalance a b hab hsub
    have he := hTransport.unique hSupplied
    rw [← hBoundary, hp rate, hp (spatialDivergence flux), hp source] at he
    have hSum : (∫ Y in Icc a b, (D + S) Y) =
        (∫ Y in Icc a b, D Y) + ∫ Y in Icc a b, S Y :=
      integral_add hD.integrableOn_Icc hS.integrableOn_Icc
    have hDiff : (∫ Y in Icc a b, R Y - (D Y + S Y)) =
        (∫ Y in Icc a b, R Y) - ∫ Y in Icc a b, (D + S) Y :=
      integral_sub hR.integrableOn_Icc (hD.add hS).integrableOn_Icc
    rw [hDiff, hSum]
    exact sub_eq_zero.mpr he
  change J X * rate (χ t X) -
    (J X * spatialDivergence flux (χ t X) + J X * source (χ t X)) = 0 at hz
  rw [← mul_add, ← mul_sub] at hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hJ X hX).ne')

end LeanSolid.ContinuumMechanics
