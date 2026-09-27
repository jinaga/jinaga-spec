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

theorem scopedConditions_append {i o : List Name} {a b : List Condition} :
    ScopedConditions i o (a ++ b) ↔ ScopedConditions i o a ∧ ScopedConditions i o b := by
  induction a with
  | nil => simp [ScopedConditions]
  | cons c cs ih =>
    simp only [List.cons_append, ScopedConditions, ih]
    grind

theorem scopedConditions_map_path {i o : List Name} {ps : List PathCondition} :
    ScopedConditions i o (ps.map .path) ↔ ∀ p ∈ ps, p.labelRight ∈ o := by
  induction ps with
  | nil => simp [ScopedConditions]
  | cons p ps ih =>
    simp only [List.map_cons, ScopedConditions, ScopedCondition, ih, List.mem_cons]
    grind

theorem usedInConditions_append {a b : List Condition} :
    usedInConditions (a ++ b) = usedInConditions a ++ usedInConditions b := by
  induction a with
  | nil => simp [usedInConditions]
  | cons c cs ih => simp [usedInConditions, ih]

theorem usedInConditions_map_path {ps : List PathCondition} :
    usedInConditions (ps.map .path) = ps.map (·.labelRight) := by
  induction ps with
  | nil => simp [usedInConditions]
  | cons p ps ih => simp [usedInConditions, usedInCondition, ih]

theorem scopedConditions_pathsOf {i o : List Name} :
    ∀ {cs : List Condition}, ScopedConditions i o cs →
      ∀ c ∈ pathsOf cs, c.labelRight ∈ o := by
  intro cs
  induction cs with
  | nil => simp [pathsOf]
  | cons c cs ih =>
    intro h p hp
    simp only [ScopedConditions] at h
    cases c with
    | path q =>
      simp only [pathsOf, List.filterMap_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact h.1
      · exact ih h.2 p (by simpa [pathsOf] using hp)
    | existential e ms =>
      simp only [pathsOf, List.filterMap_cons] at hp
      exact ih h.2 p (by simpa [pathsOf] using hp)


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

/-- The existential conditions of a scoped list of conditions are scoped. -/
theorem scopedConditions_existentialsOf {inner outer : List Name} :
    ∀ {cs : List Condition}, ScopedConditions inner outer cs →
      ScopedConditions inner outer (existentialsOf cs) := by
  intro cs
  induction cs with
  | nil => simp [existentialsOf]
  | cons c cs ih =>
    intro h
    simp only [ScopedConditions] at h
    cases c with
    | path q => simpa [existentialsOf] using ih h.2
    | existential e ms =>
      have e : existentialsOf (.existential e ms :: cs) =
          .existential e ms :: existentialsOf cs := by simp [existentialsOf]
      rw [e]
      exact ⟨h.1, ih h.2⟩

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

/-- What well-formedness says about the pieces of the original specification
that the tail keeps. -/
theorem pivot_scoped (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after) :
    (∀ c ∈ pathsOf pivot.conditions, c.labelRight ∈ scopeAt s before) ∧
    ScopedConditions (pivot.unknown.name :: scopeAt s before) (scopeAt s before)
      (existentialsOf pivot.conditions) ∧
    ScopedMatches (pivot.unknown.name :: scopeAt s before) after ∧
    (∀ x ∈ s.projection.labels,
      x ∈ scopeAt s before ∨ x ∈ (pivot :: after).map (·.unknown.name)) := by
  have h1 := hwf.inScope
  rw [hs, scopedMatches_append] at h1
  obtain ⟨-, h2⟩ := h1
  obtain ⟨u, cs⟩ := pivot
  simp only [ScopedMatches] at h2
  refine ⟨?_, scopedConditions_existentialsOf h2.1, h2.2, ?_⟩
  · exact scopedConditions_pathsOf h2.1
  · intro x hx
    rcases hwf.projected x hx with h | h
    · exact Or.inl (by unfold scopeAt; rw [mem_scopeAfter]; exact Or.inr h)
    · rw [hs] at h
      simp only [List.map_append, List.mem_append] at h
      rcases h with h | h
      · exact Or.inl (by unfold scopeAt; rw [mem_scopeAfter]; exact Or.inl h)
      · exact Or.inr h

/-- The pivot's unknown and the labels its path conditions join are ordinary. -/
theorem pivot_labels_ordinary (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after) :
    ∀ x ∈ pivot.unknown.name :: (pathsOf pivot.conditions).map (·.labelRight),
      isReserved x = false := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · have h := hwf.wellNamed
    rw [hs, wellNamedMatches_append] at h
    exact wellNamed_ordinary h.2 pivot (by simp)
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact scopeAt_ordinary hwf hs _ ((pivot_scoped hwf hs).1 c hc)

/-- No path condition of the pivot joins the pivot to itself: the label it
joins is in scope, and the pivot's unknown is not. -/
theorem pivot_paths_ne (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after) :
    ∀ c ∈ pathsOf pivot.conditions, c.labelRight ≠ pivot.unknown.name := by
  intro c hc heq
  have hin := (pivot_scoped hwf hs).1 c hc
  have hun := hwf.wellNamed
  rw [hs] at hun
  have hun2 := (wellNamedMatches_append.mp hun).2
  exact wellNamed_names_notin hun2 pivot.unknown.name (by simp) (heq ▸ hin)

/-- The derivation of the tail's givens is closed, for any split matches and
tail paths whose labels the pivot joined or the split matches bind. -/
theorem tail_scoped_aux (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after)
    (sm : List Match) (tps : List PathCondition)
    (hpaths : ∀ c ∈ tps, c.labelRight ∈ (pathsOf pivot.conditions).map (·.labelRight) ∨
        c.labelRight ∈ sm.map (·.unknown.name)) :
    ScopedMatches ((tailGivenAt s (before ++ sm) (tailMatchesAt pivot tps after)).map (·.name))
        (tailMatchesAt pivot tps after) ∧
      ∀ x ∈ s.projection.labels,
        x ∈ (tailGivenAt s (before ++ sm) (tailMatchesAt pivot tps after)).map (·.name) ∨
        x ∈ (tailMatchesAt pivot tps after).map (·.unknown.name) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := pivot_scoped hwf hs
  have hused : usedInMatches (tailMatchesAt pivot tps after) =
      tps.map (·.labelRight) ++ (usedInConditions (existentialsOf pivot.conditions) ++
        usedInMatches after) := by
    obtain ⟨u, cs⟩ := pivot
    simp [tailMatchesAt, usedInMatches, usedInConditions_append, usedInConditions_map_path]
  have hnames : ∀ x, x ∈ (tailGivenAt s (before ++ sm) (tailMatchesAt pivot tps after)).map (·.name) ↔
      x ∈ (s.given ++ (before ++ sm).map (·.unknown)).map (·.name) ∧
        x ∈ usedInMatches (tailMatchesAt pivot tps after) ++ s.projection.labels := by
    intro x
    simp only [tailGivenAt, List.mem_map, List.mem_filter, List.contains_iff_mem]
    constructor
    · rintro ⟨l, ⟨hl, hu⟩, rfl⟩
      exact ⟨⟨l, hl, rfl⟩, hu⟩
    · rintro ⟨⟨l, hl, rfl⟩, hu⟩
      exact ⟨l, ⟨hl, hu⟩, rfl⟩
  -- a scope label the tail uses, or the projection names, is a given
  have hscope : ∀ x ∈ scopeAt s before,
      x ∈ usedInMatches (tailMatchesAt pivot tps after) ++ s.projection.labels →
      x ∈ (tailGivenAt s (before ++ sm) (tailMatchesAt pivot tps after)).map (·.name) := by
    intro x hx hu
    rw [hnames]
    refine ⟨?_, hu⟩
    unfold scopeAt at hx
    rw [mem_scopeAfter] at hx
    simp only [List.map_append, List.mem_append, List.map_map]
    rcases hx with h | h
    · exact Or.inr (Or.inl (by simpa [Function.comp_def] using h))
    · exact Or.inl (by simpa using h)
  have hN : ∀ x ∈ sm.map (·.unknown.name),
      x ∈ usedInMatches (tailMatchesAt pivot tps after) ++ s.projection.labels →
      x ∈ (tailGivenAt s (before ++ sm) (tailMatchesAt pivot tps after)).map (·.name) := by
    intro x hx hu
    rw [hnames]
    refine ⟨?_, hu⟩
    simp only [List.map_append, List.mem_append, List.map_map]
    exact Or.inr (Or.inr (by simpa [Function.comp_def] using hx))
  have key : ∀ G, ScopedMatches G (tailMatchesAt pivot tps after) ↔
      ScopedConditions (pivot.unknown.name :: G) G
        (tps.map .path ++ existentialsOf pivot.conditions) ∧
      ScopedMatches (pivot.unknown.name :: G) after := fun G => Iff.rfl
  refine ⟨?_, ?_⟩
  · rw [key]
    refine ⟨scopedConditions_append.mpr ⟨scopedConditions_map_path.mpr ?_, ?_⟩, ?_⟩
    · intro t ht
      have hut : t.labelRight ∈ usedInMatches (tailMatchesAt pivot tps after) ++
          s.projection.labels := by
        rw [hused]
        simp only [List.mem_append]
        exact Or.inl (Or.inl (List.mem_map.mpr ⟨t, ht, rfl⟩))
      rcases hpaths t ht with h | h
      · obtain ⟨c, hc, hcl⟩ := List.mem_map.mp h
        exact hscope _ (hcl ▸ hp1 c hc) hut
      · exact hN _ h hut
    · refine scopedConditions_shrink _ _ _ _ hp2 ?_
      intro x hx hxA
      refine hscope x hxA ?_
      rw [hused]
      simp only [List.mem_append]
      exact Or.inl (Or.inr (Or.inl hx))
    · refine scopedMatches_shrink after _ _ hp3 ?_
      intro x hx hxA
      rcases List.mem_cons.mp hxA with rfl | hxA'
      · simp
      · refine List.mem_cons_of_mem _ (hscope x hxA' ?_)
        rw [hused]
        simp only [List.mem_append]
        exact Or.inl (Or.inr (Or.inr hx))
  · intro x hx
    rcases hp4 x hx with h | h
    · exact Or.inl (hscope x h (List.mem_append_right _ hx))
    · exact Or.inr (by simpa [tailMatchesAt] using h)

/-- The derivation of the tail's givens is closed. Every path condition of the
tail joins a label that is one of its givens or is declared earlier in it, and
so does every label its projection names. -/
theorem tail_scoped (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after) :
    let split := splitPaths 0 (pathsOf pivot.conditions)
    let tail := tailMatchesAt pivot split.2 after
    let given := (tailGivenAt s (before ++ split.1) tail).map (·.name)
    ScopedMatches given tail ∧
    ∀ x ∈ s.projection.labels, x ∈ given ∨ x ∈ tail.map (·.unknown.name) := by
  intro split tail given
  have hn := splitPaths_names 0 (pathsOf pivot.conditions)
  exact tail_scoped_aux hwf hs split.1 split.2 hn.2

end Pivot

end JinagaSpec
