module

public import LeanSolid.Math.Calculus.Theorems
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open LeanSolid.Math
open scoped ContDiff

namespace LeanSolid.ContinuumMechanics.InviscidFlow

/-- The one-dimensional linear acoustic equations imply the wave equation
for both density perturbation and velocity. Coordinate 0 is time. -/
theorem acoustic_wave_equations (r u : Vector 2 → ℝ) (ρ₀ c : ℝ) (hρ : ρ₀ ≠ 0)
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u)
    (hMass : partialDeriv r 0 = fun x => -ρ₀ * partialDeriv u 1 x)
    (hMomentum : partialDeriv u 0 = fun x => -(c ^ 2 / ρ₀) * partialDeriv r 1 x)
    (x : Vector 2) :
    partialDeriv (partialDeriv r 0) 0 x = c ^ 2 * partialDeriv (partialDeriv r 1) 1 x ∧
    partialDeriv (partialDeriv u 0) 0 x = c ^ 2 * partialDeriv (partialDeriv u 1) 1 x := by
  have hdr (j : Fin 2) : Differentiable ℝ (partialDeriv r j) :=
    (contDiff_partial hr (k := 1) (by norm_num) j).differentiable one_ne_zero
  have hdu (j : Fin 2) : Differentiable ℝ (partialDeriv u j) :=
    (contDiff_partial hu (k := 1) (by norm_num) j).differentiable one_ne_zero
  constructor
  · calc
      _ = -ρ₀ * partialDeriv (partialDeriv u 0) 1 x := by
        rw [hMass, partial_const_mul _ (hdu 1), partial_partial_comm hu 0 1]
      _ = _ := by
        rw [hMomentum, partial_const_mul _ (hdr 1)]
        field_simp
  · calc
      _ = -(c ^ 2 / ρ₀) * partialDeriv (partialDeriv r 0) 1 x := by
        rw [hMomentum, partial_const_mul _ (hdr 1), partial_partial_comm hr 0 1]
      _ = _ := by
        rw [hMass, partial_const_mul _ (hdu 1)]
        field_simp

/-- Steady one-dimensional mass and isentropic momentum balance give the
area–velocity relation before dividing by area or velocity. -/
theorem nozzle_area_velocity (A ρ u c Adot ρdot udot : ℝ) (hρ : ρ ≠ 0)
    (hMass : (Adot * ρ + A * ρdot) * u + A * ρ * udot = 0)
    (hMomentum : ρ * u * udot + c ^ 2 * ρdot = 0) :
    c ^ 2 * u * Adot = (u ^ 2 - c ^ 2) * A * udot := by
  apply mul_left_cancel₀ hρ
  linear_combination c ^ 2 * hMass - A * u * hMomentum

/-- The normalized area relation contains the factor Mach squared minus one. -/
theorem nozzle_area_ratio (A u c Adot udot : ℝ) (hA : A ≠ 0) (hu : u ≠ 0) (hc : c ≠ 0)
    (h : c ^ 2 * u * Adot = (u ^ 2 - c ^ 2) * A * udot) :
    Adot / A = ((u / c) ^ 2 - 1) * (udot / u) := by
  field_simp
  linear_combination h

/-- At a sonic point with nonzero speed, the quasi-one-dimensional law
requires stationary cross-sectional area. -/
theorem nozzle_area_stationary_of_sonic (A u c Adot udot : ℝ) (hu : u ≠ 0)
    (hSonic : u ^ 2 = c ^ 2) (h : c ^ 2 * u * Adot = (u ^ 2 - c ^ 2) * A * udot) :
    Adot = 0 := by
  rw [← hSonic, sub_self, zero_mul, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (pow_ne_zero _ hu) hu)

/-- The area–Mach relation from differentiable area, density and speed
profiles satisfying constant mass flux and barotropic momentum balance. -/
theorem nozzle_area_ratio_of_steady_profiles
    {A ρ u : ℝ → ℝ} {x c Adot ρdot udot : ℝ}
    (hA : HasDerivAt A Adot x) (hρ : HasDerivAt ρ ρdot x) (hu : HasDerivAt u udot x)
    (hArea : A x ≠ 0) (hDensity : ρ x ≠ 0) (hSpeed : u x ≠ 0) (hSound : c ≠ 0)
    (hMass : HasDerivAt (fun y => A y * ρ y * u y) 0 x)
    (hMomentum : ρ x * u x * udot + c ^ 2 * ρdot = 0) :
    Adot / A x = ((u x / c) ^ 2 - 1) * (udot / u x) := by
  have hd := (hA.mul hρ).mul hu
  change HasDerivAt (fun y => A y * ρ y * u y)
    ((Adot * ρ x + A x * ρdot) * u x + A x * ρ x * udot) x at hd
  exact nozzle_area_ratio _ _ _ _ _ hArea hSpeed hSound
    (nozzle_area_velocity _ _ _ _ _ _ _ hDensity (hd.unique hMass) hMomentum)

/-- In any spatial dimension, the linearized barotropic equations give a
scalar density wave. Coordinate zero is time and successor indices are spatial. -/
theorem acoustic_densityWave {n : ℕ} (r : Vector (n + 1) → ℝ)
    (u : Fin n → Vector (n + 1) → ℝ) (ρ₀ c : ℝ) (hρ : ρ₀ ≠ 0)
    (hr : ContDiff ℝ 2 r) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hMass : partialDeriv r 0 = fun x => -ρ₀ * ∑ j, partialDeriv (u j) j.succ x)
    (hMomentum : ∀ j, partialDeriv (u j) 0 = fun x => -(c ^ 2 / ρ₀) * partialDeriv r j.succ x)
    (x : Vector (n + 1)) :
    partialDeriv (partialDeriv r 0) 0 x =
      c ^ 2 * ∑ j : Fin n, partialDeriv (partialDeriv r j.succ) j.succ x := by
  have hdu (j : Fin n) : Differentiable ℝ (partialDeriv (u j) j.succ) :=
    (contDiff_partial (hu j) (k := 1) (by norm_num) j.succ).differentiable one_ne_zero
  have hdr (j : Fin n) : Differentiable ℝ (partialDeriv r j.succ) :=
    (contDiff_partial hr (k := 1) (by norm_num) j.succ).differentiable one_ne_zero
  have hSum :
      partialDeriv (fun y => ∑ j : Fin n, partialDeriv (u j) j.succ y) 0 x =
        ∑ j : Fin n, partialDeriv (partialDeriv (u j) j.succ) 0 x := by
    unfold partialDeriv
    have hf : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        DifferentiableAt ℝ (partialDeriv (u j) j.succ) x := fun j _ => hdu j x
    exact (congrArg (fun f : Vector (n + 1) →L[ℝ] ℝ => f (Pi.single 0 1))
      (fderiv_fun_sum hf)).trans (sum_apply _ _ _)
  have hTerm (j : Fin n) :
      partialDeriv (partialDeriv (u j) j.succ) 0 x =
        -(c ^ 2 / ρ₀) * partialDeriv (partialDeriv r j.succ) j.succ x := by
    rw [partial_partial_comm (hu j) j.succ 0, hMomentum j, partial_const_mul _ (hdr j)]
  have hD : Differentiable ℝ (fun y => ∑ j : Fin n, partialDeriv (u j) j.succ y) :=
    Differentiable.fun_sum fun j _ => hdu j
  rw [hMass, partial_const_mul _ hD]
  change -ρ₀ * partialDeriv (fun y => ∑ j : Fin n, partialDeriv (u j) j.succ y) 0 x = _
  simp only [hSum, hTerm, ← Finset.mul_sum]
  field_simp

/-- The multidimensional acoustic velocity satisfies the grad–div wave
system. For a potential flow this is the componentwise wave operator. -/
theorem acoustic_velocity_gradDiv {n : ℕ} (r : Vector (n + 1) → ℝ)
    (u : Fin n → Vector (n + 1) → ℝ) (ρ₀ c : ℝ) (hρ : ρ₀ ≠ 0)
    (hr : ContDiff ℝ 2 r) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hMass : partialDeriv r 0 = fun x => -ρ₀ * ∑ j, partialDeriv (u j) j.succ x)
    (hMomentum : ∀ j, partialDeriv (u j) 0 = fun x => -(c ^ 2 / ρ₀) * partialDeriv r j.succ x)
    (x : Vector (n + 1)) (i : Fin n) :
    partialDeriv (partialDeriv (u i) 0) 0 x =
      c ^ 2 * partialDeriv (fun y => ∑ j, partialDeriv (u j) j.succ y) i.succ x := by
  have hdr : Differentiable ℝ (partialDeriv r i.succ) :=
    (contDiff_partial hr (k := 1) (by norm_num) i.succ).differentiable one_ne_zero
  have hD : Differentiable ℝ (fun y => ∑ j, partialDeriv (u j) j.succ y) :=
    Differentiable.fun_sum fun j _ =>
      (contDiff_partial (hu j) (k := 1) (by norm_num) j.succ).differentiable one_ne_zero
  calc
    _ = -(c ^ 2 / ρ₀) * partialDeriv (partialDeriv r 0) i.succ x := by
      rw [hMomentum i, partial_const_mul _ hdr, partial_partial_comm hr i.succ 0]
    _ = _ := by
      rw [hMass, partial_const_mul _ hD]
      field_simp

/-- For irrotational acoustic velocities, the spatial grad–div operator is
the componentwise spatial Laplacian. -/
theorem acoustic_gradDiv_eq_laplacian_of_irrotational {n : ℕ}
    (u : Fin n → Vector (n + 1) → ℝ) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hCurl : ∀ i j, partialDeriv (u i) j.succ = partialDeriv (u j) i.succ)
    (x : Vector (n + 1)) (i : Fin n) :
    partialDeriv (fun y => ∑ j, partialDeriv (u j) j.succ y) i.succ x =
      ∑ j : Fin n, partialDeriv (partialDeriv (u i) j.succ) j.succ x := by
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      DifferentiableAt ℝ (partialDeriv (u j) j.succ) x := fun j _ =>
    ((contDiff_partial (hu j) (k := 1) (by norm_num) j.succ).differentiable one_ne_zero) x
  have hSum :
      partialDeriv (fun y => ∑ j, partialDeriv (u j) j.succ y) i.succ x =
        ∑ j : Fin n, partialDeriv (partialDeriv (u j) j.succ) i.succ x := by
    unfold partialDeriv
    exact (congrArg (fun f : Vector (n + 1) →L[ℝ] ℝ => f (Pi.single i.succ 1))
      (fderiv_fun_sum hf)).trans (sum_apply _ _ _)
  rw [hSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partial_partial_comm (hu j) j.succ i.succ, hCurl j i]

/-- An accelerating subsonic stream requires contraction; an accelerating
supersonic stream requires expansion in the steady area law. -/
theorem nozzle_area_sign_of_acceleration (A u c Adot udot : ℝ)
    (hA : 0 < A) (hu : 0 < u) (hc : 0 < c) (hAcc : 0 < udot)
    (h : c ^ 2 * u * Adot = (u ^ 2 - c ^ 2) * A * udot) :
    (u < c → Adot < 0) ∧ (c < u → 0 < Adot) := by
  have hCoeff : 0 < c ^ 2 * u := mul_pos (pow_pos hc _) hu
  constructor
  · intro hs
    have hsign : u ^ 2 - c ^ 2 < 0 := by nlinarith [mul_pos (sub_pos.mpr hs) (add_pos hc hu)]
    have hneg : c ^ 2 * u * Adot < 0 :=
      h ▸ (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hsign hA) hAcc)
    by_contra! hn
    exact (not_lt_of_ge (mul_nonneg hCoeff.le hn)) hneg
  · intro hs
    have hsign : 0 < u ^ 2 - c ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hs) (add_pos hu hc)]
    have hpos : 0 < c ^ 2 * u * Adot :=
      h ▸ (mul_pos (mul_pos hsign hA) hAcc)
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hCoeff.le hn)) hpos

/-- Quadratic energy density of a one-dimensional acoustic perturbation. -/
noncomputable def acousticEnergy (ρ₀ c r u : ℝ) : ℝ :=
  (c ^ 2 / (2 * ρ₀)) * (r * r) + (ρ₀ / 2) * (u * u)

/-- Linear acoustics conserves its quadratic energy with flux p′u,
where the barotropic pressure perturbation is p′ = c²r. -/
theorem acoustic_localEnergyBalance (r u : Vector 2 → ℝ) (ρ₀ c : ℝ) (hρ : ρ₀ ≠ 0)
    (hr : Differentiable ℝ r) (hu : Differentiable ℝ u)
    (hMass : partialDeriv r 0 = fun x => -ρ₀ * partialDeriv u 1 x)
    (hMomentum : partialDeriv u 0 = fun x => -(c ^ 2 / ρ₀) * partialDeriv r 1 x)
    (x : Vector 2) :
    partialDeriv (fun y => acousticEnergy ρ₀ c (r y) (u y)) 0 x +
      partialDeriv (fun y => c ^ 2 * (r y * u y)) 1 x = 0 := by
  unfold acousticEnergy
  have hr₂ : Differentiable ℝ (fun y => r y * r y) := hr.mul hr
  have hu₂ : Differentiable ℝ (fun y => u y * u y) := hu.mul hu
  have hru : Differentiable ℝ (fun y => r y * u y) := hr.mul hu
  have hR : Differentiable ℝ (fun y => c ^ 2 / (2 * ρ₀) * (r y * r y)) := hr₂.const_mul _
  have hU : Differentiable ℝ (fun y => ρ₀ / 2 * (u y * u y)) := hu₂.const_mul _
  simp only [partial_add hR hU, partial_const_mul _ hr₂, partial_const_mul _ hu₂,
    partial_const_mul _ hru, partial_mul hr hr, partial_mul hu hu, partial_mul hr hu,
    hMass, hMomentum]
  field_simp
  ring

end LeanSolid.ContinuumMechanics.InviscidFlow
