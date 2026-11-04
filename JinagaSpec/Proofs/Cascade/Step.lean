import JinagaSpec.Proofs.Cascade.Tree

/-!
# Cascade: correct steps compose, and a pipeline's output depends only on its input

`run_correct`: a correct step, run over any sequence of input events, keeps its
output equivalent to its denotation of the input. `andThen_correct`: two correct
steps in sequence form a correct step for the composed denotation. Together they
say a whole pipeline is correct for the composition of its steps' denotations.

`order_independent` is the consequence that issue jinaga/jinaga-cascade-core#29
broke: two sequences of input events that reach the same input tree produce the
same output, in whatever order the rows arrived.
-/
namespace JinagaSpec.Cascade

noncomputable section

variable {S S₁ S₂ : Step} {F F₁ F₂ : Tree → Tree}

/-- **`run_correct`.** Run over input events from `T` to `T'`, a correct step's
events take `F T` to a tree equivalent to `F T'`. -/
theorem run_correct (hS : Correct S F) (hF : Denotation F) :
    ∀ (es : List Event) (T T' : Tree), T.WF → T.applyAll es = some T' →
      ∃ U, (F T).applyAll (run S T es) = some U ∧ U.Equiv (F T') := by
  intro es
  induction es with
  | nil => intro T T' _ h; cases h; exact ⟨F T, rfl, Tree.Equiv.refl _⟩
  | cons e es ih =>
    intro T T' hT h
    simp only [Tree.applyAll, Option.bind_eq_some_iff] at h
    obtain ⟨T1, h1, h2⟩ := h
    have hT1 := apply_wf hT h1
    obtain ⟨V, hV, hVe⟩ := hS T e T1 hT h1
    obtain ⟨W, hW, hWe⟩ := ih T1 T' hT1 h2
    have hVwf := applyAll_wf (hF.wf T hT) hV
    obtain ⟨W', hW', hW'e⟩ := applyAll_equiv (hF.wf T1 hT1) hVwf hVe.symm hW
    refine ⟨W', ?_, hW'e.symm.trans hWe⟩
    simp only [run, h1, applyAll_append, hV, Option.bind_some, hW']

/-- **`andThen_correct`.** Correct steps compose. -/
theorem andThen_correct (h₁ : Correct S₁ F₁) (hF₁ : Denotation F₁)
    (h₂ : Correct S₂ F₂) (hF₂ : Denotation F₂) :
    Correct (S₁.andThen S₂ F₁) (F₂ ∘ F₁) := by
  intro T e T' hT he
  obtain ⟨U, hU, hUe⟩ := h₁ T e T' hT he
  have hU' := applyAll_wf (hF₁.wf T hT) hU
  obtain ⟨W, hW, hWe⟩ := run_correct h₂ hF₂ _ _ _ (hF₁.wf T hT) hU
  exact ⟨W, hW, hWe.trans (hF₂.equiv _ _ hU' (hF₁.wf T' (apply_wf hT he)) hUe)⟩

theorem Denotation.comp (hF₁ : Denotation F₁) (hF₂ : Denotation F₂) : Denotation (F₂ ∘ F₁) :=
  ⟨fun T hT => hF₂.wf _ (hF₁.wf T hT),
   fun T U hT hU h => hF₂.equiv _ _ (hF₁.wf T hT) (hF₁.wf U hU) (hF₁.equiv T U hT hU h)⟩

/-- **`order_independent`.** Two sequences of input events that reach
equivalent input trees produce equivalent outputs. -/
theorem order_independent (hS : Correct S F) (hF : Denotation F) {T T₁ T₂ : Tree}
    {es₁ es₂ : List Event} (hT : T.WF)
    (h₁ : T.applyAll es₁ = some T₁) (h₂ : T.applyAll es₂ = some T₂) (h : T₁.Equiv T₂) :
    ∃ U₁ U₂, (F T).applyAll (run S T es₁) = some U₁ ∧ (F T).applyAll (run S T es₂) = some U₂ ∧
      U₁.Equiv U₂ := by
  obtain ⟨U₁, hU₁, hU₁e⟩ := run_correct hS hF es₁ T T₁ hT h₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := run_correct hS hF es₂ T T₂ hT h₂
  exact ⟨U₁, U₂, hU₁, hU₂, hU₁e.trans
    ((hF.equiv _ _ (applyAll_wf hT h₁) (applyAll_wf hT h₂) h).trans hU₂e.symm)⟩

end

end JinagaSpec.Cascade
