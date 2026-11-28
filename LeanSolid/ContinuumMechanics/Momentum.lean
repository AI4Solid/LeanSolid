module

public import LeanSolid.ContinuumMechanics.PiolaFlux
public import LeanSolid.ContinuumMechanics.Balance
import LeanSolid.Math.Calculus.Theorems
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

open LeanSolid.Math MeasureTheory Set
open scoped Matrix ContDiff

namespace LeanSolid.ContinuumMechanics

theorem firstPiola_row_eq_piolaFlux (χ : Vector 3 → Vector 3) (σ : Vector 3 → Tensor 3)
    (i : Fin 3) :
    (fun X => firstPiola (deformationGradient χ X) (σ (χ X)) i) =
      piolaFlux χ (fun x => σ x i) := by
  funext X j
  simp only [firstPiola, piolaFlux, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The material stress divergence is the Piola transform of the spatial
stress divergence. This identity applies row by row and needs no inverse. -/
theorem tensorDivergence_firstPiola_placement (χ : Vector 3 → Vector 3)
    (σ : Vector 3 → Tensor 3) (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i))
    (hσ : ∀ i, Differentiable ℝ (fun x => σ x i)) (X : Vector 3) :
    tensorDivergence (fun Y => firstPiola (deformationGradient χ Y) (σ (χ Y))) X =
      jacobian (deformationGradient χ X) • tensorDivergence σ (χ X) := by
  funext i
  have he := spatialDivergence_piolaFlux χ (fun x => σ x i) hχ (hσ i) X
  rw [← firstPiola_row_eq_piolaFlux χ σ i] at he
  exact he

/-- The same momentum residual, expressed in material and spatial variables.
The spatial rates are force and inertia per unit current volume. -/
theorem material_momentumResidual_eq (χ : Vector 3 → Vector 3)
    (σ : Vector 3 → Tensor 3) (body inertia : Vector 3 → Vector 3)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i))
    (hσ : ∀ i, Differentiable ℝ (fun x => σ x i)) (X : Vector 3) :
    let J := jacobian (deformationGradient χ X)
    tensorDivergence (fun Y => firstPiola (deformationGradient χ Y) (σ (χ Y))) X +
        J • body (χ X) - J • inertia (χ X) =
      J • (tensorDivergence σ (χ X) + body (χ X) - inertia (χ X)) := by
  dsimp only
  rw [tensorDivergence_firstPiola_placement χ σ hχ hσ, smul_sub, smul_add]

theorem material_momentumBalance_iff_spatial (χ : Vector 3 → Vector 3)
    (σ : Vector 3 → Tensor 3) (body inertia : Vector 3 → Vector 3)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i))
    (hσ : ∀ i, Differentiable ℝ (fun x => σ x i)) (X : Vector 3)
    (hJ : jacobian (deformationGradient χ X) ≠ 0) :
    (tensorDivergence (fun Y => firstPiola (deformationGradient χ Y) (σ (χ Y))) X +
      jacobian (deformationGradient χ X) • body (χ X) -
      jacobian (deformationGradient χ X) • inertia (χ X) = 0) ↔
    tensorDivergence σ (χ X) + body (χ X) - inertia (χ X) = 0 := by
  rw [material_momentumResidual_eq χ σ body inertia hχ hσ X, smul_eq_zero]
  exact or_iff_right hJ

/-- A continuous scalar residual with zero integral on every Cartesian box
contained in an open region vanishes at each point of that region. -/
theorem eq_zero_of_integral_box_eq_zero {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (f : Vector 3 → ℝ) (hf : Continuous f)
    (hInt : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → (∫ y in Icc a b, f y) = 0)
    {x : Vector 3} (hx : x ∈ Ω) : f x = 0 := by
  have not_pos (g : Vector 3 → ℝ) (hg : Continuous g)
      (hzero : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → (∫ y in Icc a b, g y) = 0) :
      ¬ 0 < g x := by
    intro hp
    let c := g x / 2
    have hc : 0 < c := by dsimp [c]; positivity
    have hOpen : IsOpen (Ω ∩ g ⁻¹' Ioi c) := hΩ.inter (isOpen_Ioi.preimage hg)
    have hmem : x ∈ Ω ∩ g ⁻¹' Ioi c := ⟨hx, by change c < g x; dsimp [c]; linarith⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOpen x hmem
    let a (i : Fin 3) := x i - r / 2
    let b (i : Fin 3) := x i + r / 2
    have hab : a ≤ b := fun i => by dsimp [a, b]; linarith
    have hbox : Icc a b ⊆ Ω ∩ g ⁻¹' Ioi c := by
      intro y hy
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ r / 2)).mpr
        fun i => ?_) (by linarith)
      change |y i - x i| ≤ r / 2
      exact abs_le.mpr ⟨by have h := hy.1 i; dsimp [a] at h; linarith,
        by have h := hy.2 i; dsimp [b] at h; linarith⟩
    have hvol : 0 < volume.real (Icc a b) := by
      rw [measureReal_def, Real.volume_Icc_pi_toReal hab]
      apply Finset.prod_pos
      intro i _
      dsimp [a, b]
      linarith
    have hi : (∫ _ in Icc a b, c) ≤ ∫ y in Icc a b, g y :=
      setIntegral_mono_on (continuous_const.integrableOn_Icc) (hg.integrableOn_Icc)
        measurableSet_Icc fun y hy => (show c < g y from (hbox hy).2).le
    rw [hzero a b hab (fun y hy => (hbox hy).1), integral_const, measureReal_def,
      Measure.restrict_apply_univ, ← measureReal_def, smul_eq_mul] at hi
    exact (not_lt_of_ge hi) (mul_pos hvol hc)
  apply le_antisymm (le_of_not_gt (not_pos f hf hInt))
  have hneg := not_pos (fun y => -f y) hf.neg (fun a b hab hsub => by
    rw [integral_neg, hInt a b hab hsub, neg_zero])
  linarith

/-- Componentwise stress flux plus the net bulk force equals the inertial
force on every box if and only if the spatial momentum equation holds. -/
theorem spatial_momentumBalance_iff_boxForceBalance {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (σ : Vector 3 → Tensor 3) (body inertia : Vector 3 → Vector 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hDiv : ∀ i, Continuous (fun x => tensorDivergence σ x i))
    (hBody : Continuous body) (hInertia : Continuous inertia) :
    (∀ x ∈ Ω, tensorDivergence σ x + body x - inertia x = 0) ↔
    ∀ (a b : Vector 3), a ≤ b → Icc a b ⊆ Ω → ∀ i,
      boxBoundaryFlux a b (fun x => σ x i) +
        (∫ x in Icc a b, body x i) = ∫ x in Icc a b, inertia x i := by
  have hbody (i : Fin 3) : Continuous (fun x => body x i) := (continuous_apply i).comp hBody
  have hinertia (i : Fin 3) : Continuous (fun x => inertia x i) := (continuous_apply i).comp hInertia
  have hResidual (a b : Vector 3) (hab : a ≤ b) (i : Fin 3) :
      (∫ x in Icc a b, tensorDivergence σ x i + body x i - inertia x i) =
        boxBoundaryFlux a b (fun x => σ x i) +
          (∫ x in Icc a b, body x i) - (∫ x in Icc a b, inertia x i) := by
    have hflux : (∫ x in Icc a b, tensorDivergence σ x i) =
        boxBoundaryFlux a b (fun x => σ x i) :=
      integral_spatialDivergence_box hab (fun x => σ x i) (hσ i) (hDiv i).integrableOn_Icc
    calc
      _ = (∫ x in Icc a b, tensorDivergence σ x i + body x i) -
          (∫ x in Icc a b, inertia x i) :=
        integral_sub ((hDiv i).add (hbody i)).integrableOn_Icc (hinertia i).integrableOn_Icc
      _ = _ := by
        have he : (∫ x in Icc a b, tensorDivergence σ x i + body x i) =
            (∫ x in Icc a b, tensorDivergence σ x i) + (∫ x in Icc a b, body x i) :=
          integral_add (hDiv i).integrableOn_Icc (hbody i).integrableOn_Icc
        rw [he, hflux]
  constructor
  · intro h a b hab hsub i
    apply sub_eq_zero.mp
    rw [← hResidual a b hab i]
    have he : (∫ x in Icc a b, tensorDivergence σ x i + body x i - inertia x i) =
        ∫ _ in Icc a b, (0 : ℝ) :=
      setIntegral_congr_fun measurableSet_Icc fun x hx => congrFun (h x (hsub hx)) i
    rw [he, integral_zero]
  · intro h x hx
    funext i
    exact eq_zero_of_integral_box_eq_zero hΩ
      (fun y => tensorDivergence σ y i + body y i - inertia y i)
      (((hDiv i).add (hbody i)).sub (hinertia i)) (fun a b hab hsub => by
        rw [hResidual a b hab i, h a b hab hsub i, sub_self]) hx

/-- Along a material path, conservation of mass cancels the density and
volume rates in the derivative of momentum per unit reference volume. -/
theorem hasDerivAt_materialMomentum_of_massBalance {ρ J v : ℝ → ℝ} {t ρdot Jdot a : ℝ}
    (hρ : HasDerivAt ρ ρdot t) (hJ : HasDerivAt J Jdot t) (hv : HasDerivAt v a t)
    (hMass : ρdot * J t + ρ t * Jdot = 0) :
    HasDerivAt (fun s => (ρ s * J s) * v s) ((ρ t * J t) * a) t := by
  have h := (hρ.mul hJ).mul hv
  change HasDerivAt (fun s => (ρ s * J s) * v s)
    ((ρdot * J t + ρ t * Jdot) * v t + (ρ t * J t) * a) t at h
  simpa only [hMass, zero_mul, zero_add] using h

/-- On a material path, the local continuity equation reduces the momentum
rate to reference mass density times acceleration. -/
theorem hasDerivAt_materialMomentum_of_continuity {F : ℝ → Tensor 3} {H : Tensor 3}
    {ρ v : ℝ → ℝ} {t ρdot a : ℝ} (hF : HasTensorDerivAt F H t)
    (hρ : HasDerivAt ρ ρdot t) (hv : HasDerivAt v a t) (hJ : jacobian (F t) ≠ 0)
    (hMass : ρdot + ρ t * (velocityGradient (F t) H).trace = 0) :
    HasDerivAt (fun s => (ρ s * jacobian (F s)) * v s)
      ((ρ t * jacobian (F t)) * a) t := by
  have h := (localMassBalance_iff hF hρ hJ).mpr hMass
  have hm := h.mul hv
  change HasDerivAt (fun s => (ρ s * jacobian (F s)) * v s)
    (0 * v t + (ρ t * jacobian (F t)) * a) t at hm
  simpa only [zero_mul, zero_add] using hm

/-- Reynolds transport of a component of momentum. The reference derivative
can be obtained by dominated differentiation on the fixed material region.
Local continuity turns it into the integral of density times acceleration. -/
theorem hasDerivAt_movingRegion_momentum {Ω : Set (Vector 3)} (hΩ : MeasurableSet Ω)
    (χ : ℝ → Vector 3 → Vector 3) (ρ v : ℝ → Vector 3 → ℝ)
    (t : ℝ) (Fdot : Vector 3 → Tensor 3) (ρdot vdot momentumRate : Vector 3 → ℝ)
    (acceleration : Vector 3 → ℝ)
    (hχ : ∀ X ∈ Ω, DifferentiableAt ℝ (χ t) X) (hInj : InjOn (χ t) Ω)
    (hJ : ∀ X ∈ Ω, 0 < jacobian (deformationGradient (χ t) X))
    (hF : ∀ X ∈ Ω, HasTensorDerivAt (fun s => deformationGradient (χ s) X) (Fdot X) t)
    (hρ : ∀ X ∈ Ω, HasDerivAt (fun s => ρ s (χ s X)) (ρdot X) t)
    (hv : ∀ X ∈ Ω, HasDerivAt (fun s => v s (χ s X)) (vdot X) t)
    (hAcc : ∀ X ∈ Ω, vdot X = acceleration (χ t X))
    (hMass : ∀ X ∈ Ω, ρdot X + ρ t (χ t X) *
      (velocityGradient (deformationGradient (χ t) X) (Fdot X)).trace = 0)
    (hRate : ∀ X ∈ Ω, HasDerivAt (fun s => ρ s (χ s X) * v s (χ s X)) (momentumRate X) t)
    (hReference : HasDerivAt (fun s => ∫ x in χ s '' Ω, ρ s x * v s x)
      (∫ X in Ω, transportIntegrand (deformationGradient (χ t) X) (Fdot X)
        (ρ t (χ t X) * v t (χ t X)) (momentumRate X)) t) :
    HasDerivAt (fun s => ∫ x in χ s '' Ω, ρ s x * v s x)
      (∫ x in χ t '' Ω, ρ t x * acceleration x) t := by
  rw [integral_image_placement volume hΩ (χ t) hχ hInj hJ]
  convert hReference using 1
  apply setIntegral_congr_fun hΩ
  intro X hX
  have hw := hasDerivAt_referenceVolumeWeight (hF X hX) (hRate X hX) (hJ X hX).ne'
  have hm := hasDerivAt_materialMomentum_of_continuity
    (hF X hX) (hρ X hX) (hv X hX) (hJ X hX).ne' (hMass X hX)
  have he : (fun s => jacobian (deformationGradient (χ s) X) *
      (ρ s (χ s X) * v s (χ s X))) =
      (fun s => (ρ s (χ s X) * jacobian (deformationGradient (χ s) X)) * v s (χ s X)) := by
    funext s
    ring
  rw [he] at hw
  have h := hm.unique hw
  dsimp only
  rw [← h, hAcc X hX]
  ring

/-- If moving-control-volume momentum rates are given both by the applied
forces and by mass times acceleration, the local spatial equation follows.
The family of motions is parametrized by the current configuration at t. -/
theorem spatial_momentumBalance_of_movingBoxRates {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (χ : ℝ → Vector 3 → Vector 3) (ρ : ℝ → Vector 3 → ℝ)
    (v : ℝ → Vector 3 → Vector 3) (t : ℝ)
    (σ : Vector 3 → Tensor 3) (body acceleration : Vector 3 → Vector 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hDiv : ∀ i, Continuous (fun x => tensorDivergence σ x i))
    (hBody : Continuous body) (hρ : Continuous (ρ t)) (hAcceleration : Continuous acceleration)
    (hRate : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → ∀ i,
      HasDerivAt (fun s => ∫ x in χ s '' Icc a b, ρ s x * v s x i)
        (∫ x in Icc a b, ρ t x * acceleration x i) t)
    (hBalance : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → ∀ i,
      HasDerivAt (fun s => ∫ x in χ s '' Icc a b, ρ s x * v s x i)
        (boxBoundaryFlux a b (fun x => σ x i) + ∫ x in Icc a b, body x i) t) :
    ∀ x ∈ Ω, tensorDivergence σ x + body x - ρ t x • acceleration x = 0 := by
  let inertia (x : Vector 3) := ρ t x • acceleration x
  apply (spatial_momentumBalance_iff_boxForceBalance hΩ σ body inertia hσ hDiv hBody
    (hρ.smul hAcceleration)).mpr
  intro a b hab hsub i
  exact (hBalance a b hab hsub i).unique (hRate a b hab hsub i)

/-- Local torque density contributed by the skew part of Cauchy stress. -/
def stressTorqueDensity (σ : Tensor 3) : Vector 3 :=
  ![σ 2 1 - σ 1 2, σ 0 2 - σ 2 0, σ 1 0 - σ 0 1]

/-- The local angular balance without a body couple is equivalent to
Cauchy stress symmetry. -/
theorem stressTorqueDensity_eq_zero_iff (σ : Tensor 3) :
    stressTorqueDensity σ = 0 ↔ σ.transpose = σ := by
  constructor
  · intro h
    have h₀ : σ 2 1 = σ 1 2 := sub_eq_zero.mp (congrFun h 0)
    have h₁ : σ 0 2 = σ 2 0 := sub_eq_zero.mp (congrFun h 1)
    have h₂ : σ 1 0 = σ 0 1 := sub_eq_zero.mp (congrFun h 2)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, h₀, h₁, h₂]
  · intro h
    have hs (i j : Fin 3) : σ j i = σ i j :=
      congrArg (fun A : Tensor 3 => A i j) h
    funext i
    fin_cases i <;> simp [stressTorqueDensity, hs 1 2, hs 2 0, hs 0 1]

/-- The j-th column is the moment of the traction on the j-th coordinate face
about the spatial origin. -/
def angularStressFlux (σ : Vector 3 → Tensor 3) (x : Vector 3) : Tensor 3 :=
  Matrix.of fun i j => (x ⨯₃ (fun k => σ x k j)) i

theorem angularStressFlux_differentiable (σ : Vector 3 → Tensor 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j)) (i j : Fin 3) :
    Differentiable ℝ (fun x => angularStressFlux σ x i j) := by
  have h (k l : Fin 3) : Differentiable ℝ (fun x : Vector 3 => x k * σ x l j) :=
    (differentiable_apply k).mul (hσ l j)
  fin_cases i
  · exact (h 1 2).sub (h 2 1)
  · exact (h 2 0).sub (h 0 2)
  · exact (h 0 1).sub (h 1 0)

/-- Divergence of the moment flux consists of the moment of the stress
divergence and the torque from the skew part of stress. -/
theorem tensorDivergence_angularStressFlux (σ : Vector 3 → Tensor 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j)) (x : Vector 3) :
    tensorDivergence (angularStressFlux σ) x =
      x ⨯₃ tensorDivergence σ x + stressTorqueDensity (σ x) := by
  have h (k l j : Fin 3) : Differentiable ℝ (fun y : Vector 3 => y k * σ y l j) :=
    (differentiable_apply k).mul (hσ l j)
  have hprod (k l j : Fin 3) :
      partialDeriv (fun y => y k * σ y l j) j x =
        (Pi.single j (1 : ℝ) : Vector 3) k * σ x l j +
        x k * partialDeriv (fun y => σ y l j) j x := by
    have hh := congrFun (partial_mul (differentiable_apply k) (hσ l j) j) x
    change partialDeriv (fun y => y k * σ y l j) j x =
      partialDeriv (fun y => y k) j x * σ x l j + x k * partialDeriv (fun y => σ y l j) j x at hh
    rw [partial_coord] at hh
    exact hh
  have hdiff (k l p q j : Fin 3) :
      partialDeriv (fun y => y k * σ y l j - y p * σ y q j) j x =
        ((Pi.single j (1 : ℝ) : Vector 3) k * σ x l j +
          x k * partialDeriv (fun y => σ y l j) j x) -
        ((Pi.single j (1 : ℝ) : Vector 3) p * σ x q j +
          x p * partialDeriv (fun y => σ y q j) j x) := by
    rw [partial_sub (h k l j) (h p q j)]
    exact congrArg₂ Sub.sub (hprod k l j) (hprod p q j)
  funext i
  fin_cases i <;>
    simp [tensorDivergence, angularStressFlux, cross_apply, Fin.sum_univ_succ, hdiff,
      stressTorqueDensity] <;> ring

/-- Contracting the moment flux with a face normal gives the moment of the
Cauchy traction on that face. -/
theorem angularStressFlux_mulVec (σ : Vector 3 → Tensor 3) (x n : Vector 3) :
    angularStressFlux σ x *ᵥ n = x ⨯₃ (σ x *ᵥ n) := by
  funext i
  fin_cases i <;> simp [angularStressFlux, cross_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] <;> ring

private theorem continuous_position_cross (v : Vector 3 → Vector 3) (hv : Continuous v) :
    Continuous (fun x => x ⨯₃ v x) := by
  have h (i j : Fin 3) : Continuous (fun x : Vector 3 => x i * v x j) :=
    (continuous_apply i).mul ((continuous_apply j).comp hv)
  apply continuous_pi
  intro i
  fin_cases i
  · exact (h 1 2).sub (h 2 1)
  · exact (h 2 0).sub (h 0 2)
  · exact (h 0 1).sub (h 1 0)

private theorem continuous_angularStressDivergence (σ : Vector 3 → Tensor 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hDiv : ∀ i, Continuous (fun x => tensorDivergence σ x i)) (i : Fin 3) :
    Continuous (fun x => tensorDivergence (angularStressFlux σ) x i) := by
  have hCross := continuous_position_cross _ (continuous_pi hDiv)
  have hTorque (j : Fin 3) : Continuous (fun x => stressTorqueDensity (σ x) j) := by
    fin_cases j
    · exact (hσ 2 1).continuous.sub (hσ 1 2).continuous
    · exact (hσ 0 2).continuous.sub (hσ 2 0).continuous
    · exact (hσ 1 0).continuous.sub (hσ 0 1).continuous
  simp only [tensorDivergence_angularStressFlux σ hσ]
  exact ((continuous_apply i).comp hCross).add (hTorque i)

private theorem angularResidual_eq_stressTorque (σ : Vector 3 → Tensor 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (x b a : Vector 3) (hLinear : tensorDivergence σ x + b - a = 0) :
    tensorDivergence (angularStressFlux σ) x + x ⨯₃ b - x ⨯₃ a =
      stressTorqueDensity (σ x) := by
  have h := congrArg (crossProduct x) hLinear
  simp only [map_sub, map_add, map_zero] at h
  rw [tensorDivergence_angularStressFlux σ hσ, add_right_comm, add_sub_right_comm, h, zero_add]

/-- Under the local linear momentum equation and in the absence of body
couples, the box integral angular balance is equivalent to Cauchy stress
symmetry throughout the open region. -/
theorem cauchyStress_symmetric_iff_boxAngularBalance {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (σ : Vector 3 → Tensor 3) (body inertia : Vector 3 → Vector 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hDiv : ∀ i, Continuous (fun x => tensorDivergence σ x i))
    (hbody : Continuous body) (hinertia : Continuous inertia)
    (hLinear : ∀ x ∈ Ω, tensorDivergence σ x + body x - inertia x = 0) :
    (∀ x ∈ Ω, (σ x).transpose = σ x) ↔
    ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → ∀ i,
      boxBoundaryFlux a b (fun x => angularStressFlux σ x i) +
        (∫ x in Icc a b, (x ⨯₃ body x) i) =
        ∫ x in Icc a b, (x ⨯₃ inertia x) i := by
  rw [← spatial_momentumBalance_iff_boxForceBalance hΩ (angularStressFlux σ)
    (fun x => x ⨯₃ body x) (fun x => x ⨯₃ inertia x)
    (angularStressFlux_differentiable σ hσ) (continuous_angularStressDivergence σ hσ hDiv)
    (continuous_position_cross body hbody) (continuous_position_cross inertia hinertia)]
  have hEq (x : Vector 3) (hx : x ∈ Ω) :
      tensorDivergence (angularStressFlux σ) x + x ⨯₃ body x - x ⨯₃ inertia x =
        stressTorqueDensity (σ x) :=
    angularResidual_eq_stressTorque σ hσ x _ _ (hLinear x hx)
  constructor
  · intro hs x hx
    rw [hEq x hx]
    exact (stressTorqueDensity_eq_zero_iff _).mpr (hs x hx)
  · intro ha x hx
    exact (stressTorqueDensity_eq_zero_iff _).mp ((hEq x hx).symm.trans (ha x hx))

/-- A material particle's specific angular momentum has rate x × a.
The term v × v vanishes. -/
theorem hasDerivAt_materialSpecificAngularMomentum {x v : ℝ → Vector 3}
    {a : Vector 3} {t : ℝ}
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v t i) t)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (a i) t) (i : Fin 3) :
    HasDerivAt (fun s => (x s ⨯₃ v s) i) ((x t ⨯₃ a) i) t := by
  have h (j k : Fin 3) :
      HasDerivAt (fun s => x s j * v s k - x s k * v s j)
        (x t j * a k - x t k * a j) t := by
    have hd := ((hx j).mul (hv k)).sub ((hx k).mul (hv j))
    change HasDerivAt (fun s => x s j * v s k - x s k * v s j)
      ((v t j * v t k + x t j * a k) - (v t k * v t j + x t k * a j)) t at hd
    convert hd using 1
    ring
  fin_cases i
  · exact h 1 2
  · exact h 2 0
  · exact h 0 1

/-- With conserved reference mass, the weighted angular momentum rate is
reference mass times the moment of the acceleration. -/
theorem hasDerivAt_materialAngularMomentum_of_continuity {F : ℝ → Tensor 3} {H : Tensor 3}
    {ρ : ℝ → ℝ} {x v : ℝ → Vector 3} {a : Vector 3} {t ρdot : ℝ}
    (hF : HasTensorDerivAt F H t) (hρ : HasDerivAt ρ ρdot t)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v t i) t)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (a i) t)
    (hJ : jacobian (F t) ≠ 0)
    (hMass : ρdot + ρ t * (velocityGradient (F t) H).trace = 0) (i : Fin 3) :
    HasDerivAt (fun s => (ρ s * jacobian (F s)) * (x s ⨯₃ v s) i)
      ((ρ t * jacobian (F t)) * (x t ⨯₃ a) i) t :=
  hasDerivAt_materialMomentum_of_continuity hF hρ
    (hasDerivAt_materialSpecificAngularMomentum hx hv i) hJ hMass

/-- Moving-box angular momentum balance implies Cauchy stress symmetry.
The material rate is supplied by transport of the angular momentum density. -/
theorem cauchyStress_symmetric_of_movingBoxAngularRates {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (χ : ℝ → Vector 3 → Vector 3) (ρ : ℝ → Vector 3 → ℝ)
    (v : ℝ → Vector 3 → Vector 3) (t : ℝ)
    (σ : Vector 3 → Tensor 3) (body acceleration : Vector 3 → Vector 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hDiv : ∀ i, Continuous (fun x => tensorDivergence σ x i))
    (hBody : Continuous body) (hρ : Continuous (ρ t)) (hAcceleration : Continuous acceleration)
    (hLinear : ∀ x ∈ Ω, tensorDivergence σ x + body x - ρ t x • acceleration x = 0)
    (hRate : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → ∀ i,
      HasDerivAt (fun s => ∫ x in χ s '' Icc a b, ρ s x * (x ⨯₃ v s x) i)
        (∫ x in Icc a b, ρ t x * (x ⨯₃ acceleration x) i) t)
    (hBalance : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → ∀ i,
      HasDerivAt (fun s => ∫ x in χ s '' Icc a b, ρ s x * (x ⨯₃ v s x) i)
        (boxBoundaryFlux a b (fun x => angularStressFlux σ x i) +
          ∫ x in Icc a b, (x ⨯₃ body x) i) t) :
    ∀ x ∈ Ω, (σ x).transpose = σ x := by
  let inertia (x : Vector 3) := ρ t x • acceleration x
  apply (cauchyStress_symmetric_iff_boxAngularBalance hΩ σ body inertia
    hσ hDiv hBody (hρ.smul hAcceleration) hLinear).mpr
  intro a b hab hsub i
  have he : (fun x => (x ⨯₃ inertia x) i) = fun x => ρ t x * (x ⨯₃ acceleration x) i := by
    funext x
    change ((crossProduct x) (ρ t x • acceleration x)) i = _
    rw [map_smul]
    rfl
  simp only [he]
  exact (hBalance a b hab hsub i).unique (hRate a b hab hsub i)

/-- Linear momentum balance on the image of an open reference set is
equivalent to force balances on all deformed boxes contained in it. Boundary
tractions are integrated through the rowwise Piola flux on the reference faces. -/
theorem spatial_momentumBalance_iff_imageBoxForceBalance {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (χ : Vector 3 → Vector 3) (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i))
    (hInj : InjOn χ Ω) (hJ : ∀ X ∈ Ω, 0 < jacobian (deformationGradient χ X))
    (σ : Vector 3 → Tensor 3) (body inertia : Vector 3 → Vector 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hDiv : ∀ i, Continuous (fun x => tensorDivergence σ x i))
    (hBody : Continuous body) (hInertia : Continuous inertia) :
    (∀ x ∈ χ '' Ω, tensorDivergence σ x + body x - inertia x = 0) ↔
    ∀ (a b : Vector 3), a ≤ b → Icc a b ⊆ Ω → ∀ i,
      boxBoundaryFlux a b (piolaFlux χ (fun x => σ x i)) +
        (∫ x in χ '' Icc a b, body x i) = ∫ x in χ '' Icc a b, inertia x i := by
  let P (X : Vector 3) := firstPiola (deformationGradient χ X) (σ (χ X))
  let J (X : Vector 3) := jacobian (deformationGradient χ X)
  have hχ' : Differentiable ℝ χ := differentiable_pi.mpr fun i =>
    (hχ i).differentiable (by norm_num)
  have hJc : Continuous J := by
    apply Continuous.matrix_det
    exact continuous_pi fun i => continuous_pi fun j =>
      (contDiff_partial (hχ i) (k := 1) (by norm_num) j).continuous
  have hσ' (i : Fin 3) : Differentiable ℝ (fun x => σ x i) := differentiable_pi.mpr (hσ i)
  have hrow (i : Fin 3) : (fun X => P X i) = piolaFlux χ (fun x => σ x i) :=
    firstPiola_row_eq_piolaFlux χ σ i
  have hP (i j : Fin 3) : Differentiable ℝ (fun X => P X i j) := by
    have he : (fun X => P X i j) = fun X => piolaFlux χ (fun x => σ x i) X j :=
      congrArg (fun w : Vector 3 → Vector 3 => fun X => w X j) (hrow i)
    rw [he]
    exact differentiable_piolaFlux_component χ _ hχ (hσ' i) j
  have hDP (i : Fin 3) : Continuous (fun X => tensorDivergence P X i) := by
    have he : (fun X => tensorDivergence P X i) = fun X => J X * tensorDivergence σ (χ X) i :=
      funext fun X => congrFun (tensorDivergence_firstPiola_placement χ σ hχ hσ' X) i
    rw [he]
    exact hJc.mul ((hDiv i).comp hχ'.continuous)
  let B (X : Vector 3) := J X • body (χ X)
  let I (X : Vector 3) := J X • inertia (χ X)
  have hRef := spatial_momentumBalance_iff_boxForceBalance hΩ P B I hP hDP
    (hJc.smul (hBody.comp hχ'.continuous)) (hJc.smul (hInertia.comp hχ'.continuous))
  have heq (X : Vector 3) (hX : X ∈ Ω) :
      (tensorDivergence P X + B X - I X = 0) ↔
      tensorDivergence σ (χ X) + body (χ X) - inertia (χ X) = 0 :=
    material_momentumBalance_iff_spatial χ σ body inertia hχ hσ' X (hJ X hX).ne'
  have hbox (a b : Vector 3) (hsub : Icc a b ⊆ Ω) (g : Vector 3 → Vector 3) (i : Fin 3) :
      (∫ x in χ '' Icc a b, g x i) = ∫ X in Icc a b, (J X • g (χ X)) i :=
    integral_image_placement volume measurableSet_Icc χ (fun X _ => hχ' X)
      (hInj.mono hsub) (fun X hX => hJ X (hsub hX)) _
  constructor
  · intro h a b hab hsub i
    have hh := hRef.mp (fun X hX => (heq X hX).mpr (h (χ X) ⟨X, hX, rfl⟩)) a b hab hsub i
    rw [hbox a b hsub body i, hbox a b hsub inertia i]
    rwa [hrow i] at hh
  · intro h x hx
    obtain ⟨X, hX, rfl⟩ := hx
    apply (heq X hX).mp
    apply hRef.mpr _ X hX
    intro a b hab hsub i
    rw [hrow i]
    have hh := h a b hab hsub i
    rwa [hbox a b hsub body i, hbox a b hsub inertia i] at hh

/-- Under linear momentum balance, integral angular balance on every
deformed box is equivalent to Cauchy stress symmetry on the current region. -/
theorem cauchyStress_symmetric_iff_imageBoxAngularBalance {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (χ : Vector 3 → Vector 3) (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i))
    (hInj : InjOn χ Ω) (hJ : ∀ X ∈ Ω, 0 < jacobian (deformationGradient χ X))
    (σ : Vector 3 → Tensor 3) (body inertia : Vector 3 → Vector 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hDiv : ∀ i, Continuous (fun x => tensorDivergence σ x i))
    (hBody : Continuous body) (hInertia : Continuous inertia)
    (hLinear : ∀ x ∈ χ '' Ω, tensorDivergence σ x + body x - inertia x = 0) :
    (∀ x ∈ χ '' Ω, (σ x).transpose = σ x) ↔
    ∀ (a b : Vector 3), a ≤ b → Icc a b ⊆ Ω → ∀ i,
      boxBoundaryFlux a b (piolaFlux χ (fun x => angularStressFlux σ x i)) +
        (∫ x in χ '' Icc a b, (x ⨯₃ body x) i) = ∫ x in χ '' Icc a b, (x ⨯₃ inertia x) i := by
  rw [← spatial_momentumBalance_iff_imageBoxForceBalance hΩ χ hχ hInj hJ (angularStressFlux σ)
    (fun x => x ⨯₃ body x) (fun x => x ⨯₃ inertia x) (angularStressFlux_differentiable σ hσ)
    (continuous_angularStressDivergence σ hσ hDiv)
    (continuous_position_cross body hBody) (continuous_position_cross inertia hInertia)]
  have heq (x : Vector 3) (hx : x ∈ χ '' Ω) :
      tensorDivergence (angularStressFlux σ) x + x ⨯₃ body x - x ⨯₃ inertia x =
        stressTorqueDensity (σ x) :=
    angularResidual_eq_stressTorque σ hσ x _ _ (hLinear x hx)
  constructor
  · intro h x hx
    rw [heq x hx]
    exact (stressTorqueDensity_eq_zero_iff _).mpr (h x hx)
  · intro h x hx
    exact (stressTorqueDensity_eq_zero_iff _).mp ((heq x hx).symm.trans (h x hx))

/-- Pulling back the spatial torque flux agrees with forming the moment
of each nominal traction at the current position. -/
theorem firstPiola_angularStressFlux (F : Tensor 3) (σ : Vector 3 → Tensor 3)
    (x : Vector 3) :
    firstPiola F (angularStressFlux σ x) =
      angularStressFlux (fun _ => firstPiola F (σ x)) x := by
  ext i j
  fin_cases i <;> simp [firstPiola, angularStressFlux, cross_apply, Matrix.mul_apply,
    Fin.sum_univ_succ] <;> ring

/-- The reference angular momentum equation is equivalent to symmetry of the
Kirchhoff stress P Fᵀ when linear momentum balance holds. -/
theorem material_angularMomentumBalance_iff {χ : Vector 3 → Vector 3}
    (σ : Vector 3 → Tensor 3) (body inertia : Vector 3 → Vector 3)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i))
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j)) (X : Vector 3)
    (hJ : jacobian (deformationGradient χ X) ≠ 0)
    (hLinear : tensorDivergence σ (χ X) + body (χ X) - inertia (χ X) = 0) :
    (tensorDivergence (fun Y => firstPiola (deformationGradient χ Y) (angularStressFlux σ (χ Y))) X +
        jacobian (deformationGradient χ X) • (χ X ⨯₃ body (χ X)) -
        jacobian (deformationGradient χ X) • (χ X ⨯₃ inertia (χ X)) = 0) ↔
    IsMomentBalanced (deformationGradient χ X) (firstPiola (deformationGradient χ X) (σ (χ X))) := by
  have hDiff (i : Fin 3) : Differentiable ℝ (fun x => angularStressFlux σ x i) :=
    differentiable_pi.mpr (angularStressFlux_differentiable σ hσ i)
  rw [material_momentumBalance_iff_spatial χ (angularStressFlux σ)
      (fun x => x ⨯₃ body x) (fun x => x ⨯₃ inertia x) hχ hDiff X hJ]
  rw [angularResidual_eq_stressTorque σ hσ _ _ _ hLinear, stressTorqueDensity_eq_zero_iff,
    momentBalanced_firstPiola_iff _ _ hJ]

/-- Comparing material transport rates with applied force and torque gives
both local momentum equations on a region covered by moving deformed boxes. -/
theorem local_balances_of_movingImageBoxRates {Ω : Set (Vector 3)} (hΩ : IsOpen Ω)
    (χ : ℝ → Vector 3 → Vector 3) (t : ℝ)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ t X i))
    (hInj : InjOn (χ t) Ω) (hJ : ∀ X ∈ Ω, 0 < jacobian (deformationGradient (χ t) X))
    (ρ : ℝ → Vector 3 → ℝ) (v : ℝ → Vector 3 → Vector 3)
    (σ : Vector 3 → Tensor 3) (body acceleration : Vector 3 → Vector 3)
    (hσ : ∀ i j, Differentiable ℝ (fun x => σ x i j))
    (hDiv : ∀ i, Continuous (fun x => tensorDivergence σ x i))
    (hBody : Continuous body) (hρ : Continuous (ρ t)) (hAcceleration : Continuous acceleration)
    (hLinearRates : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → ∀ i,
      let p (s : ℝ) := ∫ x in χ s '' Icc a b, ρ s x * v s x i
      HasDerivAt p (∫ x in χ t '' Icc a b, ρ t x * acceleration x i) t ∧
      HasDerivAt p (boxBoundaryFlux a b (piolaFlux (χ t) (fun x => σ x i)) +
        ∫ x in χ t '' Icc a b, body x i) t)
    (hAngularRates : ∀ a b : Vector 3, a ≤ b → Icc a b ⊆ Ω → ∀ i,
      let p (s : ℝ) := ∫ x in χ s '' Icc a b, ρ s x * (x ⨯₃ v s x) i
      HasDerivAt p (∫ x in χ t '' Icc a b, ρ t x * (x ⨯₃ acceleration x) i) t ∧
      HasDerivAt p (boxBoundaryFlux a b (piolaFlux (χ t) (fun x => angularStressFlux σ x i)) +
        ∫ x in χ t '' Icc a b, (x ⨯₃ body x) i) t) :
    (∀ x ∈ χ t '' Ω, tensorDivergence σ x + body x - ρ t x • acceleration x = 0) ∧
    (∀ x ∈ χ t '' Ω, (σ x).transpose = σ x) := by
  let inertia (x : Vector 3) := ρ t x • acceleration x
  have hI : Continuous inertia := hρ.smul hAcceleration
  have hLin : ∀ x ∈ χ t '' Ω, tensorDivergence σ x + body x - inertia x = 0 := by
    apply (spatial_momentumBalance_iff_imageBoxForceBalance hΩ (χ t) hχ hInj hJ
      σ body inertia hσ hDiv hBody hI).mpr
    intro a b hab hsub i
    obtain ⟨hRate, hBalance⟩ := hLinearRates a b hab hsub i
    exact hBalance.unique hRate
  refine ⟨hLin, ?_⟩
  apply (cauchyStress_symmetric_iff_imageBoxAngularBalance hΩ (χ t) hχ hInj hJ
    σ body inertia hσ hDiv hBody hI hLin).mpr
  intro a b hab hsub i
  have he : (fun x => (x ⨯₃ inertia x) i) = fun x => ρ t x * (x ⨯₃ acceleration x) i := by
    funext x
    change ((crossProduct x) (ρ t x • acceleration x)) i = _
    rw [map_smul]
    rfl
  simp only [he]
  obtain ⟨hRate, hBalance⟩ := hAngularRates a b hab hsub i
  exact hBalance.unique hRate

end LeanSolid.ContinuumMechanics
