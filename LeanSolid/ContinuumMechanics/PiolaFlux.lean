module

public import LeanSolid.ContinuumMechanics.Piola
public import LeanSolid.ContinuumMechanics.BoundaryFlux
import LeanSolid.Math.Calculus.Theorems
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open LeanSolid.Math
open MeasureTheory Set
open scoped Matrix ContDiff

namespace LeanSolid.ContinuumMechanics

/-- Refer to a spatial vector flux using the contravariant Piola transform. -/
noncomputable def piolaFlux (χ v : Vector 3 → Vector 3) (X : Vector 3) : Vector 3 :=
  (deformationGradient χ X).adjugate *ᵥ v (χ X)

private theorem differentiable_adjugate_deformationGradient
    (χ : Vector 3 → Vector 3) (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i))
    (i j : Fin 3) : Differentiable ℝ (fun X => (deformationGradient χ X).adjugate i j) := by
  have hF (i j : Fin 3) : Differentiable ℝ (fun X => deformationGradient χ X i j) :=
    (contDiff_partial (hχ i) (k := 1) (by norm_num) j).differentiable one_ne_zero
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_three] <;> fun_prop

/-- The contravariant Piola transformation commutes with divergence, with the
volume Jacobian as weight. This cofactor formulation needs no nonsingularity. -/
theorem spatialDivergence_piolaFlux (χ v : Vector 3 → Vector 3)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i)) (hv : Differentiable ℝ v) (X : Vector 3) :
    spatialDivergence (piolaFlux χ v) X =
      jacobian (deformationGradient χ X) * spatialDivergence v (χ X) := by
  let F := deformationGradient χ
  let B := deformationGradient v (χ X)
  let w := v ∘ χ
  have hχ' : Differentiable ℝ χ := fun Y => differentiableAt_pi.mpr fun i =>
    (hχ i).differentiable (by norm_num) Y
  have hw (i : Fin 3) : Differentiable ℝ (fun Y => w Y i) :=
    (differentiable_pi.mp (hv.comp hχ')) i
  have hAdj : ∀ i j, Differentiable ℝ (fun Y => (F Y).adjugate i j) :=
    differentiable_adjugate_deformationGradient χ hχ
  have hPiola (i : Fin 3) :
      (∑ j, partialDeriv (fun Y => (F Y).adjugate j i) j X) = 0 := by
    exact congrFun (tensorDivergence_cofactor_deformationGradient χ hχ X) i
  have hGrad (i j : Fin 3) : partialDeriv (fun Y => w Y i) j X = (B * F X) i j :=
    congrArg (fun A : Tensor 3 => A i j) (deformationGradient_comp (hχ' X) (hv (χ X)))
  have hProd (j i : Fin 3) :
      partialDeriv (fun Y => (F Y).adjugate j i * w Y i) j X =
        partialDeriv (fun Y => (F Y).adjugate j i) j X * w X i +
          (F X).adjugate j i * (B * F X) i j := by
    rw [partial_mul (hAdj j i) (hw i)]
    exact congrArg (fun t => partialDeriv (fun Y => (F Y).adjugate j i) j X * w X i +
      (F X).adjugate j i * t) (hGrad i j)
  have hSum (j : Fin 3) :
      partialDeriv (fun Y => piolaFlux χ v Y j) j X =
        ∑ i, partialDeriv (fun Y => (F Y).adjugate j i * w Y i) j X := by
    change partialDeriv (fun Y => ∑ i, (F Y).adjugate j i * w Y i) j X = _
    unfold partialDeriv
    have hd : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        DifferentiableAt ℝ (fun Y => (F Y).adjugate j i * w Y i) X :=
      fun i _ => ((hAdj j i).mul (hw i)) X
    exact (congrArg (fun f : Vector 3 →L[ℝ] ℝ => f (Pi.single j 1))
      (fderiv_fun_sum hd)).trans (sum_apply _ _ _)
  change (∑ j, partialDeriv (fun Y => piolaFlux χ v Y j) j X) =
    jacobian (F X) * B.trace
  simp only [hSum, hProd]
  rw [Finset.sum_comm]
  have hCancel (i : Fin 3) :
      (∑ j, (partialDeriv (fun Y => (F Y).adjugate j i) j X * w X i +
        (F X).adjugate j i * (B * F X) i j)) =
        ∑ j, (F X).adjugate j i * (B * F X) i j := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hPiola, zero_mul, zero_add]
  rw [Finset.sum_congr rfl (fun i _ => hCancel i)]
  have hTrace : (∑ i, ∑ j, (F X).adjugate j i * (B * F X) i j) =
      ((B * F X) * (F X).adjugate).trace := by
    change (∑ i, ∑ j, (F X).adjugate j i * (B * F X) i j) =
      ∑ i, ∑ j, (B * F X) i j * (F X).adjugate j i
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hTrace, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, mul_one,
    Matrix.trace_smul]
  rfl

theorem differentiable_piolaFlux_component (χ v : Vector 3 → Vector 3)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i)) (hv : Differentiable ℝ v) (j : Fin 3) :
    Differentiable ℝ (fun X => piolaFlux χ v X j) := by
  have hχ' : Differentiable ℝ χ := fun X => differentiableAt_pi.mpr fun i =>
    (hχ i).differentiable (by norm_num) X
  have hw (i : Fin 3) : Differentiable ℝ (fun X => v (χ X) i) :=
    (differentiable_pi.mp (hv.comp hχ')) i
  change Differentiable ℝ (fun X => ∑ i, (deformationGradient χ X).adjugate j i * v (χ X) i)
  exact Differentiable.fun_sum fun i _ =>
    (differentiable_adjugate_deformationGradient χ hχ j i).mul (hw i)

/-- Divergence theorem on the smooth, positively oriented image of a box.
The boundary term is evaluated on the six reference faces using the Piola flux. -/
theorem integral_spatialDivergence_image_box {a b : Vector 3} (hab : a ≤ b)
    (χ v : Vector 3 → Vector 3)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ X i)) (hv : Differentiable ℝ v)
    (hInj : InjOn χ (Icc a b))
    (hJ : ∀ X ∈ Icc a b, 0 < jacobian (deformationGradient χ X))
    (hInt : IntegrableOn (spatialDivergence (piolaFlux χ v)) (Icc a b)) :
    (∫ x in χ '' Icc a b, spatialDivergence v x) = boxBoundaryFlux a b (piolaFlux χ v) := by
  have hχ' : Differentiable ℝ χ := fun X => differentiableAt_pi.mpr fun i =>
    (hχ i).differentiable (by norm_num) X
  calc
    _ = ∫ X in Icc a b, jacobian (deformationGradient χ X) *
          spatialDivergence v (χ X) :=
      integral_image_placement volume measurableSet_Icc χ (fun X _ => hχ' X) hInj hJ _
    _ = ∫ X in Icc a b, spatialDivergence (piolaFlux χ v) X :=
      setIntegral_congr_fun measurableSet_Icc fun X _ =>
        (spatialDivergence_piolaFlux χ v hχ hv X).symm
    _ = _ := integral_spatialDivergence_box hab _ (differentiable_piolaFlux_component χ v hχ hv) hInt

/-- Boundary form of Reynolds transport for a moving image of a reference box.
The boundary term uses the six reference faces and their transformed area
vectors through the Piola flux. The material volume derivative is supplied by
the moving-region transport theorem. -/
theorem hasDerivAt_movingRegion_imageBoxFlux {a b : Vector 3} (hab : a ≤ b)
    (χ : ℝ → Vector 3 → Vector 3) (φ : ℝ → Vector 3 → ℝ) (t : ℝ)
    (Fdot : Vector 3 → Tensor 3) (φdot gTime : Vector 3 → ℝ) (v : Vector 3 → Vector 3)
    (hχ : ∀ i, ContDiff ℝ 2 (fun X => χ t X i)) (hInj : InjOn (χ t) (Icc a b))
    (hJ : ∀ X ∈ Icc a b, 0 < jacobian (deformationGradient (χ t) X))
    (hg : Differentiable ℝ (φ t)) (hv : Differentiable ℝ v)
    (hTime : IntegrableOn gTime (χ t '' Icc a b))
    (hDiv : IntegrableOn (spatialDivergence (advectiveFlux (φ t) v)) (χ t '' Icc a b))
    (hPullback : IntegrableOn (spatialDivergence (piolaFlux (χ t) (advectiveFlux (φ t) v)))
      (Icc a b))
    (hVelocity : ∀ X ∈ Icc a b, velocityGradient (deformationGradient (χ t) X) (Fdot X) =
      deformationGradient v (χ t X))
    (hScalarRate : ∀ X ∈ Icc a b, φdot X = gTime (χ t X) +
      ∑ i, partialDeriv (φ t) i (χ t X) * v (χ t X) i)
    (hReference : HasDerivAt (fun τ => ∫ x in χ τ '' Icc a b, φ τ x)
      (∫ X in Icc a b, transportIntegrand (deformationGradient (χ t) X) (Fdot X)
        (φ t (χ t X)) (φdot X)) t) :
    HasDerivAt (fun τ => ∫ x in χ τ '' Icc a b, φ τ x)
      ((∫ x in χ t '' Icc a b, gTime x) +
        boxBoundaryFlux a b (piolaFlux (χ t) (advectiveFlux (φ t) v))) t := by
  have hχ' : Differentiable ℝ (χ t) := fun X => differentiableAt_pi.mpr fun i =>
    (hχ i).differentiable (by norm_num) X
  have hv' := differentiable_pi.mp hv
  have hw : Differentiable ℝ (advectiveFlux (φ t) v) :=
    differentiable_pi.mpr fun i => hg.mul (hv' i)
  rw [← integral_spatialDivergence_image_box hab (χ t) _ hχ hw hInj hJ hPullback,
    ← integral_add hTime hDiv,
    integral_image_placement volume measurableSet_Icc (χ t) (fun X _ => hχ' X) hInj hJ]
  convert hReference using 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro X hX
  dsimp only
  rw [spatialDivergence_advectiveFlux (φ t) v hg hv' (χ t X)]
  simp only [transportIntegrand, hVelocity X hX, hScalarRate X hX, spatialDivergence, add_assoc]

end LeanSolid.ContinuumMechanics
