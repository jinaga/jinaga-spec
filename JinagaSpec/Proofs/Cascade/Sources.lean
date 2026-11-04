import JinagaSpec.Cascade.Sources
import JinagaSpec.Proofs.Cascade.Step

/-!
# Cascade: named sources

`lift_correct`: when each source's step is correct, running each on its own tree
is correct for the sources. `Join.after_correct` and `Join.andThen_correct`: a
correct join composes with the pipelines before it and the steps after it.
`Join.order_independent`: two sequences of source events that reach equivalent
sources produce equivalent output, however the sources' events interleave.
-/
namespace JinagaSpec.Cascade

/-! ## Applying source events -/

theorem Forest.set_self (F : Forest) (s : Source) (T : Tree) : (F.set s T) s = T := by
  simp [Forest.set]

theorem Forest.set_other (F : Forest) {s s' : Source} (h : s' ≠ s) (T : Tree) : (F.set s T) s' = F s' := by
  simp [Forest.set, h]

theorem Forest.set_set (F : Forest) (s : Source) (T U : Tree) : (F.set s T).set s U = F.set s U := by
  funext s'; by_cases h : s' = s <;> simp [Forest.set, h]

theorem Forest.apply_eq {F F' : Forest} {e : SEvent} (h : F.apply e = some F') :
    ∃ T', (F e.1).apply e.2 = some T' ∧ F' = F.set e.1 T' := by
  simp only [Forest.apply, Option.map_eq_some_iff] at h
  obtain ⟨T', h1, rfl⟩ := h
  exact ⟨T', h1, rfl⟩

theorem Forest.set_wf {F : Forest} (hF : F.WF) {s : Source} {T : Tree} (hT : T.WF) : (F.set s T).WF := by
  intro s'; by_cases h : s' = s
  · subst h; rw [Forest.set_self]; exact hT
  · rw [Forest.set_other F h]; exact hF s'

theorem Forest.apply_wf {F F' : Forest} {e : SEvent} (hF : F.WF) (h : F.apply e = some F') : F'.WF := by
  obtain ⟨T', h1, rfl⟩ := Forest.apply_eq h
  exact Forest.set_wf hF (Cascade.apply_wf (hF e.1) h1)

/-- Events in one source change only that source. -/
theorem Forest.applyAll_tag (s : Source) :
    ∀ (es : List Event) (H : Forest),
      H.applyAll (es.map (s, ·)) = ((H s).applyAll es).map (H.set s) := by
  intro es
  induction es with
  | nil => intro H; simp only [List.map_nil, Forest.applyAll, Tree.applyAll, Option.map_some]
           congr 1; funext s'; by_cases h : s' = s <;> simp [Forest.set, h]
  | cons e es ih =>
    intro H
    simp only [List.map_cons, Forest.applyAll, Tree.applyAll, Forest.apply]
    cases h : (H s).apply e with
    | none => rfl
    | some T1 =>
      simp only [Option.map_some, Option.bind_some]
      rw [ih, Forest.set_self]
      congr 1; funext U; exact Forest.set_set H s T1 U

/-! ## Each source's own pipeline -/

theorem liftD_wf {D : Source → Tree → Tree} (hD : ∀ s, Denotation (D s)) {F : Forest} (hF : F.WF) :
    (liftD D F).WF :=
  fun s => (hD s).wf _ (hF s)

theorem liftD_equiv {D : Source → Tree → Tree} (hD : ∀ s, Denotation (D s)) {F H : Forest}
    (hF : F.WF) (hH : H.WF) (h : F.Equiv H) : (liftD D F).Equiv (liftD D H) :=
  fun s => (hD s).equiv _ _ (hF s) (hH s) (h s)

/-- **`lift_correct`.** Each source's correct step, on its own tree, takes the
sources' outputs to their outputs after the event. -/
theorem lift_correct {P : Source → Step} {D : Source → Tree → Tree} (hP : ∀ s, Correct (P s) (D s)) :
    ∀ (F : Forest) e F', F.WF → F.apply e = some F' →
      ∃ H, (liftD D F).applyAll (Step.lift P F e) = some H ∧ H.Equiv (liftD D F') := by
  intro F e F' hF he
  obtain ⟨T', h1, rfl⟩ := Forest.apply_eq he
  obtain ⟨U, hU, hUe⟩ := hP e.1 (F e.1) e.2 T' (hF e.1) h1
  refine ⟨(liftD D F).set e.1 U, ?_, fun s => ?_⟩
  · simp only [Step.lift]
    rw [Forest.applyAll_tag]
    show ((D e.1 (F e.1)).applyAll _).map _ = _
    rw [hU]; rfl
  · by_cases h : s = e.1
    · subst h; simp only [Forest.set_self, liftD]; exact hUe
    · simp only [liftD, Forest.set_other _ h]; exact Tree.Equiv.refl _

/-! ## Joins -/

variable {J : Join} {G : Forest → Tree}

/-- **`Join.run_correct`.** -/
theorem Join.run_correct (hJ : JCorrect J G) (hG : JDenotation G) :
    ∀ (es : List SEvent) (F F' : Forest), F.WF → F.applyAll es = some F' →
      ∃ U, (G F).applyAll (J.run F es) = some U ∧ U.Equiv (G F') := by
  intro es
  induction es with
  | nil => intro F F' _ h; cases h; exact ⟨G F, rfl, Tree.Equiv.refl _⟩
  | cons e es ih =>
    intro F F' hF h
    simp only [Forest.applyAll, Option.bind_eq_some_iff] at h
    obtain ⟨F1, h1, h2⟩ := h
    have hF1 := Forest.apply_wf hF h1
    obtain ⟨V, hV, hVe⟩ := hJ F e F1 hF h1
    obtain ⟨W, hW, hWe⟩ := ih F1 F' hF1 h2
    have hVwf := applyAll_wf (hG.wf F hF) hV
    obtain ⟨W', hW', hW'e⟩ := applyAll_equiv (hG.wf F1 hF1) hVwf hVe.symm hW
    refine ⟨W', ?_, hW'e.symm.trans hWe⟩
    simp only [Join.run, h1, applyAll_append, hV, Option.bind_some, hW']

theorem Forest.applyAll_wf {F F' : Forest} {es : List SEvent} (hF : F.WF) (h : F.applyAll es = some F') :
    F'.WF := by
  induction es generalizing F with
  | nil => cases h; exact hF
  | cons e es ih =>
    simp only [Forest.applyAll, Option.bind_eq_some_iff] at h
    obtain ⟨F1, h1, h2⟩ := h
    exact ih (Forest.apply_wf hF h1) h2

theorem JDenotation.after {D : Source → Tree → Tree} (hD : ∀ s, Denotation (D s)) (hG : JDenotation G) :
    JDenotation (G ∘ liftD D) :=
  ⟨fun _ hF => hG.wf _ (liftD_wf hD hF),
   fun _ _ hF hH h => hG.equiv _ _ (liftD_wf hD hF) (liftD_wf hD hH) (liftD_equiv hD hF hH h)⟩

/-- **`Join.after_correct`.** Each source's pipeline, then a correct join. -/
theorem Join.after_correct {P : Source → Step} {D : Source → Tree → Tree}
    (hP : ∀ s, Correct (P s) (D s)) (hD : ∀ s, Denotation (D s)) (hJ : JCorrect J G)
    (hG : JDenotation G) : JCorrect (J.after P D) (G ∘ liftD D) := by
  intro F e F' hF he
  obtain ⟨H, hH, hHe⟩ := lift_correct hP F e F' hF he
  obtain ⟨U, hU, hUe⟩ := Join.run_correct hJ hG _ _ _ (liftD_wf hD hF) hH
  have hHwf := Forest.applyAll_wf (liftD_wf hD hF) hH
  exact ⟨U, hU, hUe.trans (hG.equiv _ _ hHwf (liftD_wf hD (Forest.apply_wf hF he)) hHe)⟩

/-- **`Join.andThen_correct`.** A correct join, then a correct step. -/
theorem Join.andThen_correct {S : Step} {Fs : Tree → Tree} (hJ : JCorrect J G) (hG : JDenotation G)
    (hS : Correct S Fs) (hFs : Denotation Fs) : JCorrect (J.andThen S G) (Fs ∘ G) := by
  intro F e F' hF he
  obtain ⟨U, hU, hUe⟩ := hJ F e F' hF he
  have hU' := applyAll_wf (hG.wf F hF) hU
  obtain ⟨W, hW, hWe⟩ := Cascade.run_correct hS hFs _ _ _ (hG.wf F hF) hU
  exact ⟨W, hW, hWe.trans (hFs.equiv _ _ hU' (hG.wf F' (Forest.apply_wf hF he)) hUe)⟩

theorem JDenotation.andThen {Fs : Tree → Tree} (hG : JDenotation G) (hFs : Denotation Fs) :
    JDenotation (Fs ∘ G) :=
  ⟨fun F hF => hFs.wf _ (hG.wf F hF),
   fun F H hF hH h => hFs.equiv _ _ (hG.wf F hF) (hG.wf H hH) (hG.equiv F H hF hH h)⟩

/-- **`Join.order_independent`.** Two sequences of source events that reach
equivalent sources produce equivalent outputs, however the sources' events
interleave. -/
theorem Join.order_independent (hJ : JCorrect J G) (hG : JDenotation G) {F F₁ F₂ : Forest}
    {es₁ es₂ : List SEvent} (hF : F.WF)
    (h₁ : F.applyAll es₁ = some F₁) (h₂ : F.applyAll es₂ = some F₂) (h : F₁.Equiv F₂) :
    ∃ U₁ U₂, (G F).applyAll (J.run F es₁) = some U₁ ∧ (G F).applyAll (J.run F es₂) = some U₂ ∧
      U₁.Equiv U₂ := by
  obtain ⟨U₁, hU₁, hU₁e⟩ := Join.run_correct hJ hG es₁ F F₁ hF h₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := Join.run_correct hJ hG es₂ F F₂ hF h₂
  exact ⟨U₁, U₂, hU₁, hU₂, hU₁e.trans
    ((hG.equiv _ _ (Forest.applyAll_wf hF h₁) (Forest.applyAll_wf hF h₂) h).trans hU₂e.symm)⟩

end JinagaSpec.Cascade
