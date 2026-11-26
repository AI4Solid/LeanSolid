module

public import LeanSolid.Elastostatics.BoundaryResponse

public section

namespace LeanSolid.Elastostatics.BoundaryResponse

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace ℝ V] [InnerProductSpace ℝ W]
  {N : Submodule ℝ V} {M : Submodule ℝ W}

/-- A linear equivalence preserving zero trace induces an equivalence on boundary data.
This is the transport needed for the quotient in OpenAI (2026), §2, companion Basic.lean. -/
def traceEquiv (e : V ≃ₗ[ℝ] W) (he : ∀ x, e x ∈ M ↔ x ∈ N) : Trace N ≃ Trace M where
  toFun := Quot.map e fun x y h => by
    rw [← map_sub]
    exact (he _).mpr h
  invFun := Quot.map e.symm fun x y h => by
    rw [← map_sub]
    apply (he _).mp
    simpa using h
  left_inv q := by
    induction q using Quot.inductionOn with
    | _ x =>
      change Quot.mk _ (e.symm (e x)) = Quot.mk _ x
      rw [LinearEquiv.symm_apply_apply]
  right_inv q := by
    induction q using Quot.inductionOn with
    | _ x =>
      change Quot.mk _ (e (e.symm x)) = Quot.mk _ x
      rw [LinearEquiv.apply_symm_apply]

theorem traceEquiv_mk (e : V ≃ₗ[ℝ] W) (he : ∀ x, e x ∈ M ↔ x ∈ N) (x : V) :
    traceEquiv e he (Quot.mk _ x) = Quot.mk _ (e x) := by
  unfold traceEquiv
  rfl

/-- The physical weak solution predicate is invariant under a change of graph coordinates
that preserves both the zero-trace space and the energy form. -/
theorem solves_iff_transport (e : V ≃ₗ[ℝ] W) (he : ∀ x, e x ∈ M ↔ x ∈ N)
    {a : V →L[ℝ] V →L[ℝ] ℝ} {b : W →L[ℝ] W →L[ℝ] ℝ}
    (hab : ∀ u v, b (e u) (e v) = a u v) (f u : V) :
    Solves M b (e f) (e u) ↔ Solves N a f u := by
  constructor
  · intro h
    refine ⟨(he _).mp (by rw [map_sub]; exact h.1), fun w => ?_⟩
    rw [← hab]
    exact h.2 ⟨e w, (he _).mpr w.property⟩
  · intro h
    refine ⟨by rw [← map_sub]; exact (he _).mpr h.1, fun w => ?_⟩
    let z : N := ⟨e.symm w, (he _).mp (by simp [w.property])⟩
    have hz : e (z : V) = (w : W) := e.apply_symm_apply w
    rw [← hz, hab]
    exact h.2 z

/-- Conjugating the graph representation transports the full DN pairing. -/
theorem dn_transport [CompleteSpace N] [CompleteSpace M]
    (e : V ≃ₗ[ℝ] W) (he : ∀ x, e x ∈ M ↔ x ∈ N)
    {a : V →L[ℝ] V →L[ℝ] ℝ} {b : W →L[ℝ] W →L[ℝ] ℝ}
    (hab : ∀ u v, b (e u) (e v) = a u v)
    (ha : IsCoercive (a.bilinearComp N.subtypeL N.subtypeL))
    (hb : IsCoercive (b.bilinearComp M.subtypeL M.subtypeL))
    (f g : Trace N) : dn M b hb (traceEquiv e he f) (traceEquiv e he g) = dn N a ha f g := by
  induction f using Quot.inductionOn with
  | _ f =>
    induction g using Quot.inductionOn with
    | _ g =>
      obtain ⟨u, hu⟩ := (existsUnique_solution N a ha f).exists
      have hv := (solves_iff_transport e he hab f u).mpr hu
      rw [traceEquiv_mk, traceEquiv_mk, dn_apply hb hv, dn_apply ha hu, hab]

end LeanSolid.Elastostatics.BoundaryResponse
