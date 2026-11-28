module

public import LeanSolid.ContinuumMechanics.Transport
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import LeanSolid.Math.Calculus.Theorems
import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

open MeasureTheory Set LeanSolid.Math

namespace LeanSolid.ContinuumMechanics

noncomputable section

variable {n : ℕ}

/-- Cartesian divergence of a spatial vector field. -/
def spatialDivergence (v : Vector n → Vector n) (x : Vector n) : ℝ :=
  (deformationGradient v x).trace

/-- Scalar flux carried by the spatial velocity. -/
def advectiveFlux (g : Vector n → ℝ) (v : Vector n → Vector n) (x : Vector n) : Vector n :=
  g x • v x

theorem spatialDivergence_advectiveFlux (g : Vector n → ℝ) (v : Vector n → Vector n)
    (hg : Differentiable ℝ g) (hv : ∀ i, Differentiable ℝ (fun x => v x i)) (x : Vector n) :
    spatialDivergence (advectiveFlux g v) x =
      (∑ i, partialDeriv g i x * v x i) + g x * spatialDivergence v x := by
  have h (i : Fin n) :
      partialDeriv (fun y => g y * v y i) i x =
        partialDeriv g i x * v x i + g x * partialDeriv (fun y => v y i) i x :=
    congrFun (partial_mul hg (hv i) i) x
  simp only [spatialDivergence, deformationGradient, Matrix.trace, Matrix.diag_apply,
    Matrix.of_apply, advectiveFlux, Pi.smul_apply, smul_eq_mul, h, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- Net outward flux over a Cartesian box, given by integrals on opposite faces. -/
def boxBoundaryFlux (a b : Vector (n + 1)) (w : Vector (n + 1) → Vector (n + 1)) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), w (i.insertNth (b i) y) i) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), w (i.insertNth (a i) y) i)

theorem integral_spatialDivergence_box {a b : Vector (n + 1)} (hab : a ≤ b)
    (w : Vector (n + 1) → Vector (n + 1))
    (hw : ∀ i, Differentiable ℝ (fun x => w x i))
    (hInt : IntegrableOn (spatialDivergence w) (Icc a b)) :
    (∫ x in Icc a b, spatialDivergence w x) = boxBoundaryFlux a b w := by
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (fun i x => w x i) (fun i x => fderiv ℝ (fun y => w y i) x)
    ∅ Set.countable_empty (fun i => (hw i).continuous.continuousOn)
    (fun x _ i => (hw i x).hasFDerivAt) hInt
  exact h

/-- Boundary form of scalar Reynolds transport at a time when the spatial region
is a Cartesian box. The supplied volume-rate theorem can come from reference transport. -/
theorem hasDerivAt_reynolds_boxFlux {a b : Vector 3} (hab : a ≤ b)
    {I : ℝ → ℝ} {t : ℝ} (g gTime : Vector 3 → ℝ) (v : Vector 3 → Vector 3)
    (hg : Differentiable ℝ g) (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hTime : IntegrableOn gTime (Icc a b))
    (hDiv : IntegrableOn (spatialDivergence (advectiveFlux g v)) (Icc a b))
    (hVolume : HasDerivAt I (∫ x in Icc a b, gTime x +
      (∑ i, partialDeriv g i x * v x i) + g x * spatialDivergence v x) t) :
    HasDerivAt I ((∫ x in Icc a b, gTime x) + boxBoundaryFlux a b (advectiveFlux g v)) t := by
  have hw (i : Fin 3) : Differentiable ℝ (fun x => advectiveFlux g v x i) :=
    hg.mul (hv i)
  have he : (fun x => gTime x + (∑ i, partialDeriv g i x * v x i) +
      g x * spatialDivergence v x) =
      fun x => gTime x + spatialDivergence (advectiveFlux g v) x := by
    funext x
    rw [spatialDivergence_advectiveFlux g v hg hv, add_assoc]
  rw [he, integral_add hTime hDiv, integral_spatialDivergence_box hab _ hw hDiv] at hVolume
  exact hVolume

/-- Convert reference-coordinate transport to the Eulerian boundary formula at a
time when the current image is a Cartesian box. The derivative premise is the output
of `hasDerivAt_integral_movingRegion`; the rate premises identify its material data. -/
theorem hasDerivAt_movingRegion_boxFlux {Ω : Set (Vector 3)} (hΩ : MeasurableSet Ω)
    {a b : Vector 3} (hab : a ≤ b) (χ : ℝ → Vector 3 → Vector 3) (φ : ℝ → Vector 3 → ℝ)
    (t : ℝ) (Fdot : Vector 3 → Tensor 3) (φdot : Vector 3 → ℝ)
    (gTime : Vector 3 → ℝ) (v : Vector 3 → Vector 3)
    (hχ : ∀ X ∈ Ω, DifferentiableAt ℝ (χ t) X) (hInj : InjOn (χ t) Ω)
    (hJ : ∀ X ∈ Ω, 0 < jacobian (deformationGradient (χ t) X))
    (hBox : χ t '' Ω = Icc a b)
    (hg : Differentiable ℝ (φ t)) (hv : ∀ i, Differentiable ℝ (fun x => v x i))
    (hTime : IntegrableOn gTime (Icc a b))
    (hDiv : IntegrableOn (spatialDivergence (advectiveFlux (φ t) v)) (Icc a b))
    (hVelocity : ∀ X ∈ Ω, velocityGradient (deformationGradient (χ t) X) (Fdot X) =
      deformationGradient v (χ t X))
    (hScalarRate : ∀ X ∈ Ω, φdot X = gTime (χ t X) +
      ∑ i, partialDeriv (φ t) i (χ t X) * v (χ t X) i)
    (hReference : HasDerivAt (fun τ => ∫ x in χ τ '' Ω, φ τ x)
      (∫ X in Ω, transportIntegrand (deformationGradient (χ t) X) (Fdot X)
        (φ t (χ t X)) (φdot X)) t) :
    HasDerivAt (fun τ => ∫ x in χ τ '' Ω, φ τ x)
      ((∫ x in Icc a b, gTime x) + boxBoundaryFlux a b (advectiveFlux (φ t) v)) t := by
  apply hasDerivAt_reynolds_boxFlux hab (φ t) gTime v hg hv hTime hDiv
  rw [← hBox, integral_image_placement volume hΩ (χ t) hχ hInj hJ]
  have he :
      (∫ X in Ω, jacobian (deformationGradient (χ t) X) *
        (gTime (χ t X) + (∑ i, partialDeriv (φ t) i (χ t X) * v (χ t X) i) +
          φ t (χ t X) * spatialDivergence v (χ t X))) =
      ∫ X in Ω, transportIntegrand (deformationGradient (χ t) X) (Fdot X)
        (φ t (χ t X)) (φdot X) := by
    apply setIntegral_congr_fun hΩ
    intro X hX
    simp only [transportIntegrand, hVelocity X hX, hScalarRate X hX, spatialDivergence]
  rw [he]
  exact hReference

end

end LeanSolid.ContinuumMechanics
