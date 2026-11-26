import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace LeanSolid.OpenAI372

open MeasureTheory

/-- Integrate the four real density pairings in the complexified energy. -/
theorem integral_complex_energy {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h k : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hk : Integrable k μ) :
    (∫ x, (f x : ℂ) + g x + Complex.I * ((h x : ℂ) - k x) ∂μ) =
      ((∫ x, f x ∂μ : ℝ) : ℂ) + ((∫ x, g x ∂μ : ℝ) : ℂ) +
        Complex.I * (((∫ x, h x ∂μ : ℝ) : ℂ) - ((∫ x, k x ∂μ : ℝ) : ℂ)) := by
  have hf' : Integrable (fun x => (f x : ℂ)) μ := hf.ofReal
  have hg' : Integrable (fun x => (g x : ℂ)) μ := hg.ofReal
  have hh' : Integrable (fun x => (h x : ℂ)) μ := hh.ofReal
  have hk' : Integrable (fun x => (k x : ℂ)) μ := hk.ofReal
  have hfg := (integral_add hf' hg').trans <|
    congrArg₂ (fun a b : ℂ => a + b)
      (integral_complex_ofReal (μ := μ) (f := f))
      (integral_complex_ofReal (μ := μ) (f := g))
  have hhk := (integral_sub hh' hk').trans <|
    congrArg₂ (fun a b : ℂ => a - b)
      (integral_complex_ofReal (μ := μ) (f := h))
      (integral_complex_ofReal (μ := μ) (f := k))
  have him := (integral_const_mul (μ := μ) Complex.I
    (fun x => (h x : ℂ) - k x)).trans (congrArg (fun a : ℂ => Complex.I * a) hhk)
  have hleft := integral_add (hf'.add hg') ((hh'.sub hk').const_mul Complex.I)
  simp only [Pi.add_apply, Pi.sub_apply] at hleft
  have hright := congrArg₂ (fun a b : ℂ => a + b) hfg him
  exact hleft.trans hright

end LeanSolid.OpenAI372
