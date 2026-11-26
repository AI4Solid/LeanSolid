module

public import LeanSolid.Elastostatics.Theorems
import Mathlib.Tactic.Abel

public section

namespace LeanSolid.Elastostatics.BoundaryResponse

/-!
The variational Dirichlet-to-Neumann pairing follows OpenAI, *Global Uniqueness
for the Smooth Isotropic Elasticity Inverse Problem* (2026), §2, and the
companion Variational.lean at revision 3344da59991ed94f9ba711217b29c1d760badfa6.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A prescribed boundary class and homogeneous virtual work against zero-trace fields. -/
@[expose] def Solves (N : Submodule ℝ V) (a : V →L[ℝ] V →L[ℝ] ℝ) (g u : V) : Prop :=
  u - g ∈ N ∧ ∀ w : N, a u w = 0

/-- Coercivity on the zero-trace space suffices for the prescribed-boundary problem. -/
theorem existsUnique_solution (N : Submodule ℝ V) [CompleteSpace N]
    (a : V →L[ℝ] V →L[ℝ] ℝ)
    (hc : IsCoercive (a.bilinearComp N.subtypeL N.subtypeL)) (g : V) : ∃! u, Solves N a g u := by
  let b := a.bilinearComp N.subtypeL N.subtypeL
  let f := -(a g).comp N.subtypeL
  obtain ⟨w, hw, hu⟩ := existsUnique_weakSolution b f hc
  have hw' (v : N) : a (w : V) v = -a g v := hw v
  refine ⟨g + (w : V), ⟨?_, ?_⟩, ?_⟩
  · rw [add_sub_cancel_left]
    exact w.property
  · intro v
    rw [map_add, add_apply, hw', add_neg_cancel]
  · intro u h
    let z : N := ⟨u - g, h.1⟩
    have hz : g + (z : V) = u := by change g + (u - g) = u; abel
    have hz' : z = w := hu z fun v => by
      change a (z : V) v = -a g v
      have e := h.2 v
      rw [← hz, map_add, add_apply] at e
      exact eq_neg_of_add_eq_zero_right e
    rw [← hz, hz']

/-- Pairing with a solution is independent of the test lift. -/
theorem work_eq_of_same_trace {N : Submodule ℝ V} {a : V →L[ℝ] V →L[ℝ] ℝ}
    {g u v w : V} (hu : Solves N a g u) (h : v - w ∈ N) :
    a u v = a u w := by
  have he := hu.2 ⟨v - w, h⟩
  change a u (v - w) = 0 at he
  rw [map_sub, sub_eq_zero] at he
  exact he

/-- The difference of the boundary responses equals the difference of the two
virtual-work forms on the two physical solutions (Alessandrini identity). -/
theorem alessandrini {N : Submodule ℝ V} {a b : V →L[ℝ] V →L[ℝ] ℝ}
    (hb : ∀ x y, b x y = b y x) {f g u v w : V}
    (hu : Solves N a f u) (hv : Solves N b g v) (hw : Solves N b f w) :
    a u g - b w g = a u v - b u v := by
  have h₁ : a u v = a u g := work_eq_of_same_trace hu hv.1
  have h₂ : b v w = b v f := work_eq_of_same_trace hv hw.1
  have h₃ : b v u = b v f := work_eq_of_same_trace hv hu.1
  have h₄ : b w v = b w g := work_eq_of_same_trace hw hv.1
  rw [h₁, hb u v, h₃, ← h₂, hb v w, h₄]

/-- Boundary data as a quotient by the zero-trace subspace. -/
abbrev Trace (N : Submodule ℝ V) := Quot (fun g h : V => g - h ∈ N)

/-- The variational response descends to the boundary quotient whenever each
prescribed boundary value has a unique weak solution. -/
noncomputable def dnOfExists (N : Submodule ℝ V) (a : V →L[ℝ] V →L[ℝ] ℝ)
    (wellPosed : ∀ f, ∃! u, Solves N a f u) : Trace N → Trace N → ℝ := by
  let solve (g : V) := (wellPosed g).exists.choose
  have hsolve (g : V) : Solves N a g (solve g) :=
    (wellPosed g).exists.choose_spec
  let work (g : V) : Trace N → ℝ := Quot.lift (fun h => a (solve g) h)
    (fun _ _ h => work_eq_of_same_trace (hsolve g) h)
  refine Quot.lift work ?_
  intro g h hgh
  have he : solve g = solve h := by
    apply (wellPosed h).unique ?_ (hsolve h)
    refine ⟨?_, (hsolve g).2⟩
    convert N.add_mem (hsolve g).1 hgh using 1
    abel
  funext q
  induction q using Quot.inductionOn with
  | _ q => exact congrArg (fun u => a u q) he

/-- Evaluate the response using a weak solution and a representative of the test trace. -/
theorem dnOfExists_apply {N : Submodule ℝ V} {a : V →L[ℝ] V →L[ℝ] ℝ}
    (wellPosed : ∀ f, ∃! u, Solves N a f u) {f u : V} (hu : Solves N a f u) (g : V) :
    dnOfExists N a wellPosed (Quot.mk _ f) (Quot.mk _ g) = a u g := by
  change a ((wellPosed f).exists.choose) g = a u g
  exact congrArg (fun w => a w g)
    ((wellPosed f).unique (wellPosed f).exists.choose_spec hu)

/-- The response obtained from a coercive weak problem. -/
noncomputable def dn (N : Submodule ℝ V) [CompleteSpace N]
    (a : V →L[ℝ] V →L[ℝ] ℝ)
    (hc : IsCoercive (a.bilinearComp N.subtypeL N.subtypeL)) : Trace N → Trace N → ℝ :=
  dnOfExists N a (existsUnique_solution N a hc)

/-- Evaluation of DN on representatives using any physical solution. -/
theorem dn_apply {N : Submodule ℝ V} [CompleteSpace N]
    {a : V →L[ℝ] V →L[ℝ] ℝ} (hc : IsCoercive (a.bilinearComp N.subtypeL N.subtypeL))
    {f u : V} (hu : Solves N a f u) (g : V) :
    dn N a hc (Quot.mk _ f) (Quot.mk _ g) = a u g :=
  dnOfExists_apply (existsUnique_solution N a hc) hu g

/-- Equality of DN responses gives the virtual-work identity for two physical fields. -/
theorem alessandrini_of_dn_eq {N : Submodule ℝ V} [CompleteSpace N]
    {a b : V →L[ℝ] V →L[ℝ] ℝ}
    (ha : IsCoercive (a.bilinearComp N.subtypeL N.subtypeL))
    (hb : IsCoercive (b.bilinearComp N.subtypeL N.subtypeL))
    (hs : ∀ x y, b x y = b y x) (hDN : dn N a ha = dn N b hb)
    {f g u v : V} (hu : Solves N a f u) (hv : Solves N b g v) :
    a u v = b u v := by
  obtain ⟨w, hw⟩ := (existsUnique_solution N b hb f).exists
  have he := congrFun (congrFun hDN (Quot.mk _ f)) (Quot.mk _ g)
  rw [dn_apply ha hu, dn_apply hb hw] at he
  exact sub_eq_zero.mp ((alessandrini hs hu hv hw).symm.trans (sub_eq_zero.mpr he))

end LeanSolid.Elastostatics.BoundaryResponse
