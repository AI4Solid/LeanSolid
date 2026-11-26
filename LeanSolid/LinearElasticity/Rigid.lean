/- Adapted from raphos-com/lean-mechanics, ContinuumMechanics/Kinematics/Rigid.lean at 7e41dfe (Apache-2.0). Rephrased skewness directly in the inner product. -/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Infinitesimal rigid displacements

A displacement field `u` whose gradient is skew everywhere on a connected open set is an
**infinitesimal rigid displacement** `u(x) = a + W x` with `W` skew ([Gurtin1981], §12, Thm. 1;
[Ciarlet1988], Thm. 6.3-4). Equivalently: zero infinitesimal strain `ε = sym ∇u = 0` forces
`u` to be rigid.

The proof is the classical one. With `D = ∇∇u(x)` and `T(a, b, c) = (D a b) · c`:
`T` is symmetric in `(a, b)` (symmetry of second derivatives) and antisymmetric in `(b, c)`
(differentiate the skewness of `∇u`); a trilinear form with both properties vanishes. Hence
`∇∇u = 0`, so `∇u` is constant on the connected set, and `u - W x` is constant.

## Main results

* `eq_zero_of_symmetric_of_skew`: the algebraic lemma.
* `eq_rigid_of_skew_fderiv`: skew gradient on a connected open set ⇒ infinitesimal rigid
  displacement.

## References

* [Gurtin1981] M. E. Gurtin, *An Introduction to Continuum Mechanics*, §12.
* [Ciarlet1988] P. G. Ciarlet, *Mathematical Elasticity*, Vol. I, §6.3.
-/

open Set Filter Topology
open scoped InnerProductSpace

public section

namespace LeanSolid.LinearElasticity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E]  in
/-- A trilinear form symmetric in its first two arguments and antisymmetric in its last two
vanishes. -/
theorem eq_zero_of_symmetric_of_skew (T : E → E → E → ℝ) (hs : ∀ a b c, T a b c = T b a c)
    (ha : ∀ a b c, T a b c = -T a c b) (a b c : E) : T a b c = 0 := by
  have : T a b c = -T a b c := by
    calc T a b c = -T a c b := ha a b c
      _ = -T c a b := by rw [hs]
      _ = T c b a := by rw [ha c a b, neg_neg]
      _ = T b c a := by rw [hs]
      _ = -T b a c := ha b c a
      _ = -T a b c := by rw [hs]
  linarith

/-- **Infinitesimal rigid displacements.** If `u` is `C²` on a connected open set `Ω` and `∇u` is
skew at every point of `Ω`, then `u(x) = a + W x` on `Ω` for a constant vector `a` and a constant
skew tensor `W`. [Gurtin1981], §12, Thm. 1. -/
theorem eq_rigid_of_skew_fderiv {Ω : Set E} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    {u : E → E} (hu : ContDiffOn ℝ 2 u Ω)
    (hskw : ∀ x ∈ Ω, ∀ b c : E, ⟪fderiv ℝ u x b, c⟫_ℝ + ⟪fderiv ℝ u x c, b⟫_ℝ = 0) :
    ∃ (a : E) (W : E →L[ℝ] E), (∀ b c : E, ⟪W b, c⟫_ℝ + ⟪W c, b⟫_ℝ = 0) ∧
      ∀ x ∈ Ω, u x = a + W x := by
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, 0, (by simp), fun x hx => absurd hx (Set.notMem_empty x)⟩
  -- `∇u` is `C¹` on `Ω`
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hdu : ∀ x ∈ Ω, DifferentiableAt ℝ u x := fun x hx =>
    (hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
  have hddu : ∀ x ∈ Ω, DifferentiableAt ℝ (fderiv ℝ u) x := fun x hx =>
    (hDu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
  -- step 1: the second derivative vanishes on `Ω`
  have hD2 : ∀ x ∈ Ω, fderiv ℝ (fderiv ℝ u) x = 0 := by
    intro x hx
    set D := fderiv ℝ (fderiv ℝ u) x
    have hsymm : ∀ a b, D a b = D b a :=
      (hu.contDiffAt (hΩ.mem_nhds hx)).isSymmSndFDerivAt (by simp)
    -- antisymmetry in the last two arguments, by differentiating skewness
    have hanti : ∀ a b c, ⟪D a b, c⟫_ℝ = -⟪D a c, b⟫_ℝ := by
      intro a b c
      let ℓ : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ c).comp (ContinuousLinearMap.apply ℝ E b) +
        (innerSL ℝ b).comp (ContinuousLinearMap.apply ℝ E c)
      have hzero : (fun y => ℓ (fderiv ℝ u y)) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hΩ.mem_nhds hx] with y hy
        simpa [ℓ, real_inner_comm c, real_inner_comm b] using hskw y hy b c
      have h1 : HasFDerivAt (fun y => ℓ (fderiv ℝ u y)) (ℓ.comp D) x :=
        ℓ.hasFDerivAt.comp x (hddu x hx).hasFDerivAt
      have h2 : HasFDerivAt (fun y => ℓ (fderiv ℝ u y)) (0 : E →L[ℝ] ℝ) x :=
        (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hzero
      have := congrArg (fun L : E →L[ℝ] ℝ => L a) (h1.unique h2)
      simp only [ℓ, ContinuousLinearMap.comp_apply, add_apply,
        ContinuousLinearMap.apply_apply, innerSL_apply_apply, zero_apply]
        at this
      have e1 := real_inner_comm (D a b) c
      have e2 := real_inner_comm (D a c) b
      linarith
    have hT := eq_zero_of_symmetric_of_skew (fun a b c => ⟪D a b, c⟫_ℝ)
      (fun a b c => by simp only [hsymm a b]) hanti
    ext a b
    refine ext_inner_right ℝ fun c => ?_
    simpa using hT a b c
  -- step 2: `∇u` is constant
  set W := fderiv ℝ u x₀
  have hW : ∀ x ∈ Ω, fderiv ℝ u x = W := fun x hx =>
    hΩ.is_const_of_fderiv_eq_zero hc (fun y hy => (hddu y hy).differentiableWithinAt)
      (fun y hy => hD2 y hy) hx hx₀
  -- step 3: `u - W` is constant
  have hv : ∀ x ∈ Ω, u x - W x = u x₀ - W x₀ := fun x hx =>
    hΩ.is_const_of_fderiv_eq_zero hc
      (fun y hy => ((hdu y hy).sub W.differentiableAt).differentiableWithinAt)
      (fun y hy => by
        simp only [Pi.zero_apply]
        rw [fderiv_sub (hdu y hy) W.differentiableAt, ContinuousLinearMap.fderiv, hW y hy,
          sub_self]) hx hx₀
  refine ⟨u x₀ - W x₀, W, hskw x₀ hx₀, fun x hx => ?_⟩
  rw [← hv x hx]
  abel

/-- Vanishing normal strain in every direction implies an infinitesimal rigid displacement. -/
theorem eq_rigid_of_zero_directional_strain {Ω : Set E} (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) {u : E → E} (hu : ContDiffOn ℝ 2 u Ω)
    (hε : ∀ x ∈ Ω, ∀ b : E, ⟪fderiv ℝ u x b, b⟫_ℝ = 0) :
    ∃ (a : E) (W : E →L[ℝ] E), (∀ b c : E, ⟪W b, c⟫_ℝ + ⟪W c, b⟫_ℝ = 0) ∧
      ∀ x ∈ Ω, u x = a + W x := by
  apply eq_rigid_of_skew_fderiv hΩ hc hu
  intro x hx b c
  have h := hε x hx (b + c)
  simp only [map_add, inner_add_left, inner_add_right, hε x hx b, hε x hx c, zero_add,
    add_zero] at h
  simpa only [add_comm] using h

end LeanSolid.LinearElasticity
