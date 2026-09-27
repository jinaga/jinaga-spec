import JinagaSpec.Proofs.SplitPaths

/-!
# The tail's givens are closed

The tail's givens are derived from what the tail uses: the labels in scope at the
pivot that its matches and projection name. This file shows the derivation is
closed: every label a path condition of the tail names is either one of its
givens or declared earlier in the tail, and so is every label its projection
names. Together with locality, that is why the tail can run from its givens
alone.

The hypotheses are those of `WellFormed`.
-/
namespace JinagaSpec

/-! ## Scope is monotone in what is used -/

mutual
  /-- Shrinking the scope keeps a list of matches scoped, provided every label
  the matches use from the old scope is in the new one. -/
  theorem scopedMatches_shrink :
      ∀ (ms : List Match) (A B : List Name), ScopedMatches A ms →
        (∀ x ∈ usedInMatches ms, x ∈ A → x ∈ B) → ScopedMatches B ms
    | [], _, _, _, _ => by simp [ScopedMatches]
    | .mk u cs :: rest, A, B, h, hu => by
      simp only [ScopedMatches] at h ⊢
      refine ⟨scopedConditions_shrink cs u.name A B h.1 ?_,
        scopedMatches_shrink rest (u.name :: A) (u.name :: B) h.2 ?_⟩
      · intro x hx hxA
        exact hu x (by simp [usedInMatches, hx]) hxA
      · intro x hx hxA
        rcases List.mem_cons.mp hxA with rfl | hxA'
        · simp
        · exact List.mem_cons_of_mem _ (hu x (by simp [usedInMatches, hx]) hxA')

  theorem scopedConditions_shrink :
      ∀ (cs : List Condition) (n : Name) (A B : List Name), ScopedConditions (n :: A) A cs →
        (∀ x ∈ usedInConditions cs, x ∈ A → x ∈ B) → ScopedConditions (n :: B) B cs
    | [], _, _, _, _, _ => by simp [ScopedConditions]
    | c :: cs, n, A, B, h, hu => by
      simp only [ScopedConditions] at h ⊢
      exact ⟨scopedCondition_shrink c n A B h.1 (fun x hx hxA => hu x (by simp [usedInConditions, hx]) hxA),
        scopedConditions_shrink cs n A B h.2 (fun x hx hxA => hu x (by simp [usedInConditions, hx]) hxA)⟩

  theorem scopedCondition_shrink :
      ∀ (c : Condition) (n : Name) (A B : List Name), ScopedCondition (n :: A) A c →
        (∀ x ∈ usedInCondition c, x ∈ A → x ∈ B) → ScopedCondition (n :: B) B c
    | .path p, n, A, B, h, hu => by
      simp only [ScopedCondition] at h ⊢
      exact hu p.labelRight (by simp [usedInCondition]) h
    | .existential e ms, n, A, B, h, hu => by
      simp only [ScopedCondition] at h ⊢
      refine scopedMatches_shrink ms (n :: A) (n :: B) h ?_
      intro x hx hxA
      rcases List.mem_cons.mp hxA with rfl | hxA'
      · simp
      · exact List.mem_cons_of_mem _ (hu x (by simpa [usedInCondition] using hx) hxA')
end

/-! ## Helpers on lists of matches and conditions -/

theorem scopedMatches_append {A : List Name} {ms1 ms2 : List Match} :
    ScopedMatches A (ms1 ++ ms2) ↔
      ScopedMatches A ms1 ∧ ScopedMatches (scopeAfter A ms1) ms2 := by
  induction ms1 generalizing A with
  | nil => simp [ScopedMatches, scopeAfter]
  | cons m ms ih =>
    obtain ⟨u, cs⟩ := m
    simp only [List.cons_append, ScopedMatches, ih, scopeAfter, Match.unknown_mk]
    grind

theorem wellNamedMatches_append {A : List Name} {ms1 ms2 : List Match} :
    WellNamedMatches A (ms1 ++ ms2) ↔
      WellNamedMatches A ms1 ∧ WellNamedMatches (scopeAfter A ms1) ms2 := by
  induction ms1 generalizing A with
  | nil => simp [WellNamedMatches, scopeAfter]
  | cons m ms ih =>
    obtain ⟨u, cs⟩ := m
    simp only [List.cons_append, WellNamedMatches, ih, scopeAfter, Match.unknown_mk]
    grind

/-- No unknown of a well-named list of matches is in the scope. -/
theorem wellNamed_names_notin {ms : List Match} :
    ∀ {A : List Name}, WellNamedMatches A ms → ∀ x ∈ ms.map (·.unknown.name), x ∉ A := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    obtain ⟨u, cs⟩ := m
    intro A h x hx
    simp only [WellNamedMatches] at h
    simp only [List.map_cons, List.mem_cons, Match.unknown_mk] at hx
    rcases hx with rfl | hx
    · exact h.1
    · intro hxA
      exact ih h.2.2.2 x hx (List.mem_cons_of_mem _ hxA)

/-- Every unknown of a well-named list of matches is ordinary. -/
theorem wellNamed_ordinary {ms : List Match} :
    ∀ {A : List Name}, WellNamedMatches A ms → ∀ m ∈ ms, isReserved m.unknown.name = false := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    obtain ⟨u, cs⟩ := m
    intro A h m' hm'
    simp only [WellNamedMatches] at h
    rcases List.mem_cons.mp hm' with rfl | hm'
    · exact h.2.1
    · exact ih h.2.2.2 m' hm'

/-! ## Every label a scoped, well-named list of matches uses is ordinary

A used label is either something already in scope (ordinary, by hypothesis) or
something the matches themselves declare (ordinary, by well-namedness) —
recursively, through existential conditions at any depth. -/

mutual
  theorem usedInMatches_ordinary :
      ∀ (ms : List Match) (A : List Name), ScopedMatches A ms → WellNamedMatches A ms →
        (∀ x ∈ A, isReserved x = false) → ∀ x ∈ usedInMatches ms, isReserved x = false
    | [], _, _, _, _, _, hx => by simp [usedInMatches] at hx
    | .mk u cs :: rest, A, hsc, hwn, hordA, x, hx => by
      obtain ⟨hcs, hrest⟩ : ScopedConditions (u.name :: A) A cs ∧ ScopedMatches (u.name :: A) rest := hsc
      obtain ⟨hun, hordU, hwncs, hwnrest⟩ :
          u.name ∉ A ∧ isReserved u.name = false ∧ WellNamedConditions (u.name :: A) cs ∧
            WellNamedMatches (u.name :: A) rest := hwn
      have hordAu : ∀ y ∈ u.name :: A, isReserved y = false := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hordU
        · exact hordA y hy
      simp only [usedInMatches, List.mem_append] at hx
      rcases hx with hx | hx
      · exact usedInConditions_ordinary cs (u.name :: A) A hcs hwncs hordAu hordA x hx
      · exact usedInMatches_ordinary rest (u.name :: A) hrest hwnrest hordAu x hx

  theorem usedInConditions_ordinary :
      ∀ (cs : List Condition) (inner outer : List Name), ScopedConditions inner outer cs →
        WellNamedConditions inner cs → (∀ x ∈ inner, isReserved x = false) →
        (∀ x ∈ outer, isReserved x = false) → ∀ x ∈ usedInConditions cs, isReserved x = false
    | [], _, _, _, _, _, _, _, hx => by simp [usedInConditions] at hx
    | c :: cs, inner, outer, hsc, hwn, hordI, hordO, x, hx => by
      obtain ⟨hc0, hcs⟩ : ScopedCondition inner outer c ∧ ScopedConditions inner outer cs := hsc
      obtain ⟨hwnc, hwncs⟩ : WellNamedCondition inner c ∧ WellNamedConditions inner cs := hwn
      simp only [usedInConditions, List.mem_append] at hx
      rcases hx with hx | hx
      · exact usedInCondition_ordinary c inner outer hc0 hwnc hordI hordO x hx
      · exact usedInConditions_ordinary cs inner outer hcs hwncs hordI hordO x hx

  theorem usedInCondition_ordinary :
      ∀ (c : Condition) (inner outer : List Name), ScopedCondition inner outer c →
        WellNamedCondition inner c → (∀ x ∈ inner, isReserved x = false) →
        (∀ x ∈ outer, isReserved x = false) → ∀ x ∈ usedInCondition c, isReserved x = false
    | .path pc, _, outer, hsc, _, _, hordO, x, hx => by
      simp only [usedInCondition, List.mem_singleton] at hx
      subst hx
      exact hordO _ hsc
    | .existential _ ms, inner, _, hsc, hwn, hordI, _, x, hx =>
      usedInMatches_ordinary ms inner hsc hwn hordI x hx
end

/-! ## Facts about a specification split at a pivot -/

section Pivot

variable {s : Specification} {before after : List Match} {pivot : Match}

/-- No label in scope at the pivot is reserved, so none is a split label. -/
theorem scopeAt_ordinary (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after) :
    ∀ x ∈ scopeAt s before, isReserved x = false := by
  intro x hx
  unfold scopeAt at hx
  rw [mem_scopeAfter] at hx
  have h := hwf.wellNamed
  rw [hs, wellNamedMatches_append] at h
  rcases hx with hx | hx
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    exact wellNamed_ordinary h.1 m hm
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact hwf.givensOrdinary g hg

/-- Every projected label is in scope at the pivot, or is bound by the pivot
or a later match: what the split's own derivation of the tail's givens
(`tailGivenAt`) needs from well-formedness, whatever produced the tail. -/
theorem pivot_scoped (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after) :
    ∀ x ∈ s.projection.labels,
      x ∈ scopeAt s before ∨ x ∈ (pivot :: after).map (·.unknown.name) := by
  intro x hx
  rcases hwf.projected x hx with h | h
  · exact Or.inl (by unfold scopeAt; rw [mem_scopeAfter]; exact Or.inr h)
  · rw [hs] at h
    simp only [List.map_append, List.mem_append] at h
    rcases h with h | h
    · exact Or.inl (by unfold scopeAt; rw [mem_scopeAfter]; exact Or.inl h)
    · exact Or.inr h

end Pivot

end JinagaSpec
