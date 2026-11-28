module

public import LeanSolid.ContinuumMechanics.Area
public import LeanSolid.ContinuumMechanics.Rates
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

public section

open scoped Topology Matrix

namespace LeanSolid.ContinuumMechanics

open LeanSolid.Math

/-- The inverse deformation gradient is differentiable at each nonsingular state of a
differentiable three-dimensional path, with rate −F⁻¹ Ḟ F⁻¹. -/
theorem hasTensorDerivAt_inverse {F : ℝ → Tensor 3} {H : Tensor 3} {t : ℝ}
    (h : HasTensorDerivAt F H t) (hJ : jacobian (F t) ≠ 0) :
    HasTensorDerivAt (fun s => (F s)⁻¹) (-(F t)⁻¹ * H * (F t)⁻¹) t := by
  have hd := hasDerivAt_invariant₃ h
  have hd' : DifferentiableAt ℝ (fun s => (F s).det) t := hd.differentiableAt
  have hr : DifferentiableAt ℝ (fun s => ((F s).det)⁻¹) t := hd'.inv hJ
  have hEntry (i j : Fin 3) : DifferentiableAt ℝ (fun s => F s i j) t := (h i j).differentiableAt
  have hAdj (i j : Fin 3) : DifferentiableAt ℝ (fun s => (F s).adjugate i j) t := by
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_three] <;> fun_prop
  let K := tensorRate (fun s => (F s)⁻¹) t
  have hK : HasTensorDerivAt (fun s => (F s)⁻¹) K t := by
    intro i j
    have hh : DifferentiableAt ℝ (fun s => (F s)⁻¹ i j) t := by
      have he : (fun s => (F s)⁻¹ i j) =
          (fun s => ((F s).det)⁻¹) * (fun s => (F s).adjugate i j) := by
        funext s
        simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, Pi.mul_apply]
      rw [he]
      exact hr.mul (hAdj i j)
    exact hh.hasDerivAt
  have hn : ∀ᶠ s in 𝓝 t, (F s).det ≠ 0 :=
    hd'.continuousAt.eventually_ne hJ
  have hzero : HasTensorDerivAt (fun s => F s * (F s)⁻¹) 0 t := by
    intro i j
    apply (hasTensorDerivAt_const (1 : Tensor 3) t i j).congr_of_eventuallyEq
    filter_upwards [hn] with s hs
    rw [Matrix.mul_nonsing_inv (F s) (isUnit_iff_ne_zero.mpr hs)]
  have hz := (h.mul hK).unique hzero
  have hz' : F t * K = -(H * (F t)⁻¹) := eq_neg_of_add_eq_zero_right hz
  have hInv : IsUnit (F t).det := isUnit_iff_ne_zero.mpr hJ
  have hk : K = -(F t)⁻¹ * H * (F t)⁻¹ := by
    calc
      K = (F t)⁻¹ * (F t * K) := (Matrix.nonsing_inv_mul_cancel_left _ _ hInv).symm
      _ = _ := by rw [hz', Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc]
  rwa [← hk]

/-- Rate of an oriented spatial area vector pulled forward from two fixed reference tangents. -/
theorem hasDerivAt_areaVector {F : ℝ → Tensor 3} {H : Tensor 3} {t : ℝ}
    (h : HasTensorDerivAt F H t) (hJ : jacobian (F t) ≠ 0) (a b : Vector 3) (i : Fin 3) :
    let L := velocityGradient (F t) H
    let q := (F t *ᵥ a) ⨯₃ (F t *ᵥ b)
    HasDerivAt (fun s => ((F s *ᵥ a) ⨯₃ (F s *ᵥ b)) i)
      ((L.trace • q - L.transpose *ᵥ q) i) t := by
  dsimp only
  let N := a ⨯₃ b
  let L := velocityGradient (F t) H
  let M := (F t)⁻¹
  let z := M.transpose *ᵥ N
  have hi := (hasTensorDerivAt_inverse h hJ).transpose
  have hcoeff : (-(F t)⁻¹ * H * (F t)⁻¹).transpose = -(L.transpose * M.transpose) := by
    simp only [L, M, velocityGradient, Matrix.transpose_mul, Matrix.transpose_neg,
      Matrix.mul_neg, Matrix.mul_assoc]
  rw [hcoeff] at hi
  have hz : HasDerivAt (fun s => ((F s)⁻¹).transpose.mulVec N i)
      (-(L.transpose *ᵥ z) i) t := by
    have he : ((-(L.transpose * M.transpose)) *ᵥ N) i = -(L.transpose *ᵥ z) i := by
      rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
      rfl
    rw [← he]
    have hh := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hi i j).mul_const (N j)
    simpa only [Matrix.mulVec, dotProduct] using hh
  have hd := (hasDerivAt_jacobian_of_spatialRate h hJ).mul hz
  have hn : ∀ᶠ s in 𝓝 t, jacobian (F s) ≠ 0 :=
    (hasDerivAt_jacobian_of_spatialRate h hJ).continuousAt.eventually_ne hJ
  have hd' : HasDerivAt (fun s => ((F s *ᵥ a) ⨯₃ (F s *ᵥ b)) i)
      (jacobian (F t) * L.trace * z i + jacobian (F t) * (-(L.transpose *ᵥ z) i)) t := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [hn] with s hs
    exact congrFun (areaVector_transform_inverse (F s) a b hs) i
  rw [areaVector_transform_inverse (F t) a b hJ]
  convert hd' using 1
  change (L.trace • (jacobian (F t) • z) - L.transpose *ᵥ (jacobian (F t) • z)) i = _
  simp only [Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Rate of the inner product of two material line elements carried by the same
deformation. Taking both directions equal gives the squared stretch rate. -/
theorem hasDerivAt_lineElementInner {F : ℝ → Tensor 3} {H : Tensor 3} {t : ℝ}
    (h : HasTensorDerivAt F H t) (a b : Vector 3) :
    HasDerivAt (fun s => (F s *ᵥ a) ⬝ᵥ (F s *ᵥ b))
      ((H *ᵥ a) ⬝ᵥ (F t *ᵥ b) + (F t *ᵥ a) ⬝ᵥ (H *ᵥ b)) t := by
  have hline (u : Vector 3) (i : Fin 3) :
      HasDerivAt (fun s => (F s *ᵥ u) i) ((H *ᵥ u) i) t := by
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (h i j).mul_const (u j)
    simpa only [Matrix.mulVec, dotProduct] using hd
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hline a i).mul (hline b i)
  change HasDerivAt (fun s => ∑ i, (F s *ᵥ a) i * (F s *ᵥ b) i) _ t at hd
  simpa only [dotProduct, Finset.sum_add_distrib] using hd

/-- Euclidean length of the image of a reference line element. -/
noncomputable def lineElementLength (F : Tensor 3) (a : Vector 3) : ℝ :=
  Real.sqrt ((F *ᵥ a) ⬝ᵥ (F *ᵥ a))

/-- The rate of the length is the projection of the line-element rate onto its
current unit direction. -/
theorem hasDerivAt_lineElementLength {F : ℝ → Tensor 3} {H : Tensor 3} {t : ℝ}
    (h : HasTensorDerivAt F H t) (a : Vector 3)
    (ha : lineElementLength (F t) a ≠ 0) :
    HasDerivAt (fun s => lineElementLength (F s) a)
      (((H *ᵥ a) ⬝ᵥ (F t *ᵥ a)) / lineElementLength (F t) a) t := by
  have hsq : (F t *ᵥ a) ⬝ᵥ (F t *ᵥ a) ≠ 0 := by
    intro hz
    apply ha
    simp [lineElementLength, hz]
  have hd := (hasDerivAt_lineElementInner h a a).sqrt hsq
  rw [dotProduct_comm (F t *ᵥ a) (H *ᵥ a)] at hd
  change HasDerivAt (fun s => lineElementLength (F s) a)
    ((_ + _) / (2 * lineElementLength (F t) a)) t at hd
  convert hd using 1
  field_simp
  ring

/-- Cosine of the angle between two carried line elements. -/
noncomputable def lineElementCosine (F : Tensor 3) (a b : Vector 3) : ℝ :=
  ((F *ᵥ a) ⬝ᵥ (F *ᵥ b)) / (lineElementLength F a * lineElementLength F b)

/-- Rate of the cosine from the inner product and the two length rates. -/
theorem hasDerivAt_lineElementCosine {F : ℝ → Tensor 3} {H : Tensor 3} {t : ℝ}
    (h : HasTensorDerivAt F H t) (a b : Vector 3)
    (ha : lineElementLength (F t) a ≠ 0) (hb : lineElementLength (F t) b ≠ 0) :
    let A := lineElementLength (F t) a
    let B := lineElementLength (F t) b
    let A' := ((H *ᵥ a) ⬝ᵥ (F t *ᵥ a)) / A
    let B' := ((H *ᵥ b) ⬝ᵥ (F t *ᵥ b)) / B
    let N := (F t *ᵥ a) ⬝ᵥ (F t *ᵥ b)
    let N' := (H *ᵥ a) ⬝ᵥ (F t *ᵥ b) + (F t *ᵥ a) ⬝ᵥ (H *ᵥ b)
    HasDerivAt (fun s => lineElementCosine (F s) a b)
      ((N' * (A * B) - N * (A' * B + A * B')) / (A * B) ^ 2) t := by
  exact (hasDerivAt_lineElementInner h a b).div
    ((hasDerivAt_lineElementLength h a ha).mul (hasDerivAt_lineElementLength h b hb))
    (mul_ne_zero ha hb)

/-- For noncollinear line elements the angle rate is the negative cosine rate
divided by the sine of the current angle. -/
theorem hasDerivAt_lineElementAngle {F : ℝ → Tensor 3} {t c' : ℝ}
    (a b : Vector 3) (hc : HasDerivAt (fun s => lineElementCosine (F s) a b) c' t)
    (hlo : -1 < lineElementCosine (F t) a b) (hhi : lineElementCosine (F t) a b < 1) :
    HasDerivAt (fun s => Real.arccos (lineElementCosine (F s) a b))
      (-(1 / Real.sqrt (1 - lineElementCosine (F t) a b ^ 2)) * c') t :=
  by
    have hd := (Real.hasDerivAt_arccos (ne_of_gt hlo) (ne_of_lt hhi)).comp t hc
    exact hd

end LeanSolid.ContinuumMechanics
