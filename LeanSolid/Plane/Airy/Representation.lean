module

public import LeanSolid.Plane.Airy.Theorems
import LeanSolid.Math.Calculus.PoincareStar
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

public section

open LeanSolid.Math Set
open scoped ContDiff

namespace LeanSolid.Plane.Airy

private theorem vector_two_expand (u : Vector 2) :
    u = u 0 • Pi.single 0 1 + u 1 • Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp [Pi.single]

private theorem exists_cartesian_primitive {s : Set (Vector 2)} {c : Vector 2}
    (hs : StarConvex ℝ c s) (ho : IsOpen s) {P Q : Vector 2 → ℝ}
    (hP : DifferentiableOn ℝ P s) (hQ : DifferentiableOn ℝ Q s)
    (hclosed : ∀ x ∈ s, partialDeriv P 1 x = partialDeriv Q 0 x) :
    ∃ F : Vector 2 → ℝ, DifferentiableOn ℝ F s ∧
      (∀ {k : WithTop ℕ∞}, k ≠ ω → ContDiffOn ℝ k P s → ContDiffOn ℝ k Q s →
        ContDiffOn ℝ (k + 1) F s) ∧
      ∀ x ∈ s, partialDeriv F 0 x = P x ∧ partialDeriv F 1 x = Q x := by
  let e (i : Fin 2) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i
  let form (x : Vector 2) := P x • e 0 + Q x • e 1
  have hd (x : Vector 2) (hx : x ∈ s) :
      HasFDerivAt form
        ((fderiv ℝ P x).smulRight (e 0) + (fderiv ℝ Q x).smulRight (e 1)) x :=
    ((((hP x hx).differentiableAt (ho.mem_nhds hx)).hasFDerivAt.smul_const (e 0))).add
      (((hQ x hx).differentiableAt (ho.mem_nhds hx)).hasFDerivAt.smul_const (e 1))
  obtain ⟨F, hF⟩ := hs.exists_forall_hasFDerivAt_of_fderiv_symmetric ho
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx u v => by
      rw [(hd x hx).fderiv]
      simp only [add_apply, ContinuousLinearMap.smulRight_apply,
        smul_apply, smul_eq_mul]
      change fderiv ℝ P x u * v 0 + fderiv ℝ Q x u * v 1 =
        fderiv ℝ P x v * u 0 + fderiv ℝ Q x v * u 1
      conv_lhs =>
        arg 1
        arg 1
        rw [vector_two_expand u]
      conv_lhs =>
        arg 2
        arg 1
        rw [vector_two_expand u]
      conv_rhs =>
        arg 1
        arg 1
        rw [vector_two_expand v]
      conv_rhs =>
        arg 2
        arg 1
        rw [vector_two_expand v]
      simp only [map_add, map_smul, smul_eq_mul]
      have hh := hclosed x hx
      unfold partialDeriv at hh
      rw [hh]
      ring)
  have hFd : DifferentiableOn ℝ F s := fun x hx => (hF x hx).differentiableAt.differentiableWithinAt
  refine ⟨F, hFd, ?_, ?_⟩
  · intro k hk hPk hQk
    apply (contDiffOn_succ_iff_fderiv_of_isOpen ho).mpr
    refine ⟨hFd, fun h => (hk h).elim, ?_⟩
    have hform : ContDiffOn ℝ k form s := by
      unfold form
      fun_prop
    exact hform.congr fun x hx => (hF x hx).fderiv
  · intro x hx
    unfold partialDeriv
    rw [(hF x hx).fderiv]
    simp [form, e, Pi.single]

/-- Every differentiable symmetric Cartesian stress in homogeneous equilibrium on an open
star-shaped planar domain has a single-valued Airy stress function on that domain. -/
theorem exists_airy_of_equilibrium_with_regularity {s : Set (Vector 2)} {c : Vector 2}
    (hs : StarConvex ℝ c s) (ho : IsOpen s)
    {sxx syy sxy : Vector 2 → ℝ}
    (hxx : DifferentiableOn ℝ sxx s) (hyy : DifferentiableOn ℝ syy s)
    (hxy : DifferentiableOn ℝ sxy s)
    (hx : ∀ x ∈ s, partialDeriv sxx 0 x + partialDeriv sxy 1 x = 0)
    (hy : ∀ x ∈ s, partialDeriv sxy 0 x + partialDeriv syy 1 x = 0) :
    ∃ φ : Vector 2 → ℝ, DifferentiableOn ℝ φ s ∧
      (ContDiffOn ℝ 2 sxx s → ContDiffOn ℝ 2 syy s → ContDiffOn ℝ 2 sxy s →
        ContDiffOn ℝ 4 φ s) ∧ ∀ x ∈ s,
      normalStressX φ x = sxx x ∧ normalStressY φ x = syy x ∧ shearStress φ x = sxy x := by
  have hneg (i : Fin 2) (x : Vector 2) :
      partialDeriv (-sxy) i x = -partialDeriv sxy i x := by
    simp [partialDeriv, fderiv_neg]
  obtain ⟨P, hP, hPr, hDP⟩ := exists_cartesian_primitive hs ho hyy hxy.neg
    (fun x hx' => by rw [hneg]; linarith [hy x hx'])
  obtain ⟨Q, hQ, hQr, hDQ⟩ := exists_cartesian_primitive hs ho hxy.neg hxx
    (fun x hx' => by rw [hneg]; linarith [hx x hx'])
  obtain ⟨φ, hφ, hφr, hDφ⟩ := exists_cartesian_primitive hs ho hP hQ
    (fun x hx' => (hDP x hx').2.trans (hDQ x hx').1.symm)
  refine ⟨φ, hφ, ?_, fun x hx' => ?_⟩
  · intro h2xx h2yy h2xy
    exact hφr (k := 3) (by simp) (hPr (k := 2) (by simp) h2yy h2xy.neg)
      (hQr (k := 2) (by simp) h2xy.neg h2xx)
  · have eP : partialDeriv φ 0 =ᶠ[nhds x] P := by
      filter_upwards [ho.mem_nhds hx'] with y hy' using (hDφ y hy').1
    have eQ : partialDeriv φ 1 =ᶠ[nhds x] Q := by
      filter_upwards [ho.mem_nhds hx'] with y hy' using (hDφ y hy').2
    have hP' (i : Fin 2) : partialDeriv (partialDeriv φ 0) i x = partialDeriv P i x :=
      congrArg (fun A : Vector 2 →L[ℝ] ℝ => A (Pi.single i 1)) eP.fderiv_eq
    have hQ' (i : Fin 2) : partialDeriv (partialDeriv φ 1) i x = partialDeriv Q i x :=
      congrArg (fun A : Vector 2 →L[ℝ] ℝ => A (Pi.single i 1)) eQ.fderiv_eq
    exact ⟨(hQ' 1).trans (hDQ x hx').2, (hP' 0).trans (hDP x hx').1,
      by simp [shearStress, hP', (hDP x hx').2]⟩

private theorem exists_global_germ {s : Set (Vector 2)} (ho : IsOpen s)
    {f : Vector 2 → ℝ} (hf : ContDiffOn ℝ 4 f s)
    {x : Vector 2} (hx : x ∈ s) :
    ∃ g : Vector 2 → ℝ, ContDiff ℝ 4 g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp ho x hx
  let χ : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hχ : tsupport (χ : Vector 2 → ℝ) ⊆ s := by
    rw [χ.tsupport_eq]
    intro y hy
    exact hsub (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hy)
      (half_lt_self hr)))
  refine ⟨fun y => χ y * f y, contDiff_iff_contDiffAt.mpr fun y => ?_, ?_⟩
  · by_cases hy : y ∈ s
    · exact χ.contDiffAt.mul ((hf y hy).contDiffAt (ho.mem_nhds hy))
    · have hz : y ∉ tsupport (χ : Vector 2 → ℝ) := fun h => hy (hχ h)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_closure : IsClosed (tsupport (χ : Vector 2 → ℝ))).isOpen_compl.mem_nhds hz]
        with z hz'
      rw [image_eq_zero_of_notMem_tsupport hz', zero_mul]
  · filter_upwards [Metric.ball_mem_nhds x χ.rIn_pos] with y hy
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]

private theorem partial_germ {f g : Vector 2 → ℝ} {x : Vector 2}
    (h : f =ᶠ[nhds x] g) (i : Fin 2) :
    partialDeriv f i =ᶠ[nhds x] partialDeriv g i :=
  (h.fderiv (𝕜 := ℝ)).mono fun _ hy => congrArg (fun A : Vector 2 →L[ℝ] ℝ =>
    A (Pi.single i 1)) hy

/-- Compatibility and the biharmonic residual agree locally on an open domain. -/
theorem compatibility_eq_biharmonic_on {s : Set (Vector 2)} (ho : IsOpen s)
    {φ : Vector 2 → ℝ} (hφ : ContDiffOn ℝ 4 φ s) (a b : ℝ) {x : Vector 2} (hx : x ∈ s) :
    compatibility (strainXX a b φ) (strainYY a b φ) (strainXY a b φ) x =
      a * biharmonic φ x := by
  obtain ⟨g, hg, h⟩ := exists_global_germ ho hφ hx
  have hs₁ : strainXX a b g =ᶠ[nhds x] strainXX a b φ := by
    filter_upwards [partial_germ (partial_germ h 1) 1, partial_germ (partial_germ h 0) 0]
      with y h₁ h₂
    simp only [strainXX, normalStressX, normalStressY, h₁, h₂]
  have hs₂ : strainYY a b g =ᶠ[nhds x] strainYY a b φ := by
    filter_upwards [partial_germ (partial_germ h 1) 1, partial_germ (partial_germ h 0) 0]
      with y h₁ h₂
    simp only [strainYY, normalStressX, normalStressY, h₁, h₂]
  have hs₃ : strainXY a b g =ᶠ[nhds x] strainXY a b φ := by
    filter_upwards [partial_germ (partial_germ h 0) 1] with y h₁
    simp only [strainXY, shearStress, h₁]
  have hb : biharmonic g x = biharmonic φ x := by
    unfold biharmonic
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (partial_germ (partial_germ (partial_germ (partial_germ h i) i) j) j).self_of_nhds
  have hmain := compatibility_eq_biharmonic a b hg x
  rw [hb] at hmain
  unfold compatibility at hmain ⊢
  rwa [(partial_germ (partial_germ hs₁ 1) 1).self_of_nhds,
    (partial_germ (partial_germ hs₂ 0) 0).self_of_nhds,
    (partial_germ (partial_germ hs₃ 0) 1).self_of_nhds] at hmain

/-- Every equilibrated stress whose isotropic compliance strains are compatible has a
biharmonic Airy representation on an open star-shaped domain. -/
theorem exists_biharmonic_airy {s : Set (Vector 2)} {c : Vector 2}
    (hs : StarConvex ℝ c s) (ho : IsOpen s) {sxx syy sxy : Vector 2 → ℝ}
    (hxx : ContDiffOn ℝ 2 sxx s) (hyy : ContDiffOn ℝ 2 syy s)
    (hxy : ContDiffOn ℝ 2 sxy s)
    (hx : ∀ x ∈ s, partialDeriv sxx 0 x + partialDeriv sxy 1 x = 0)
    (hy : ∀ x ∈ s, partialDeriv sxy 0 x + partialDeriv syy 1 x = 0)
    {a : ℝ} (ha : a ≠ 0) (b : ℝ)
    (hcompat : ∀ x ∈ s, compatibility (fun y => a * sxx y - b * syy y)
      (fun y => a * syy y - b * sxx y) (fun y => (a + b) * sxy y) x = 0) :
    ∃ φ : Vector 2 → ℝ, ContDiffOn ℝ 4 φ s ∧ ∀ x ∈ s,
      normalStressX φ x = sxx x ∧ normalStressY φ x = syy x ∧
      shearStress φ x = sxy x ∧ biharmonic φ x = 0 := by
  obtain ⟨φ, _, hreg, hstress⟩ := exists_airy_of_equilibrium_with_regularity hs ho
    (hxx.differentiableOn (by norm_num)) (hyy.differentiableOn (by norm_num))
    (hxy.differentiableOn (by norm_num)) hx hy
  have hφ := hreg hxx hyy hxy
  refine ⟨φ, hφ, fun x hx' => ⟨(hstress x hx').1, (hstress x hx').2.1,
    (hstress x hx').2.2, ?_⟩⟩
  have h₁ : strainXX a b φ =ᶠ[nhds x] fun y => a * sxx y - b * syy y := by
    filter_upwards [ho.mem_nhds hx'] with y h
    simp only [strainXX, (hstress y h).1, (hstress y h).2.1]
  have h₂ : strainYY a b φ =ᶠ[nhds x] fun y => a * syy y - b * sxx y := by
    filter_upwards [ho.mem_nhds hx'] with y h
    simp only [strainYY, (hstress y h).1, (hstress y h).2.1]
  have h₃ : strainXY a b φ =ᶠ[nhds x] fun y => (a + b) * sxy y := by
    filter_upwards [ho.mem_nhds hx'] with y h
    simp only [strainXY, (hstress y h).2.2]
  have hc := compatibility_eq_biharmonic_on ho hφ a b hx'
  unfold compatibility at hc
  rw [(partial_germ (partial_germ h₁ 1) 1).self_of_nhds,
    (partial_germ (partial_germ h₂ 0) 0).self_of_nhds,
    (partial_germ (partial_germ h₃ 0) 1).self_of_nhds] at hc
  exact (mul_eq_zero.mp (hc.symm.trans (hcompat x hx'))).resolve_left ha

/-- On an open domain, a C⁴ biharmonic Airy potential produces an equilibrated stress
whose isotropic compliance strains are compatible. -/
theorem biharmonic_airy_equilibrium_on {s : Set (Vector 2)} (ho : IsOpen s)
    {φ : Vector 2 → ℝ} (hφ : ContDiffOn ℝ 4 φ s)
    (hb : ∀ x ∈ s, biharmonic φ x = 0) (a b : ℝ) :
    ∀ x ∈ s,
      partialDeriv (normalStressX φ) 0 x + partialDeriv (shearStress φ) 1 x = 0 ∧
      partialDeriv (shearStress φ) 0 x + partialDeriv (normalStressY φ) 1 x = 0 ∧
      compatibility (strainXX a b φ) (strainYY a b φ) (strainXY a b φ) x = 0 := by
  intro x hx
  obtain ⟨g, hg, h⟩ := exists_global_germ ho hφ hx
  have hxx : normalStressX g =ᶠ[nhds x] normalStressX φ :=
    partial_germ (partial_germ h 1) 1
  have hyy : normalStressY g =ᶠ[nhds x] normalStressY φ :=
    partial_germ (partial_germ h 0) 0
  have hxy : shearStress g =ᶠ[nhds x] shearStress φ :=
    (partial_germ (partial_germ h 0) 1).mono fun _ he => congrArg Neg.neg he
  refine ⟨?_, ?_, by rw [compatibility_eq_biharmonic_on ho hφ a b hx, hb x hx, mul_zero]⟩
  · rw [← (partial_germ hxx 0).self_of_nhds, ← (partial_germ hxy 1).self_of_nhds]
    exact equilibrium_x (hg.of_le (by norm_num)) x
  · rw [← (partial_germ hxy 0).self_of_nhds, ← (partial_germ hyy 1).self_of_nhds]
    exact equilibrium_y (hg.of_le (by norm_num)) x

end LeanSolid.Plane.Airy
