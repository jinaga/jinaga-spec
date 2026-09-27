import JinagaSpec.Proofs.Locality
import JinagaSpec.Proofs.Derivation

/-!
# The split preserves the specification's meaning

`split_correct`: for a well-formed specification, evaluating the head on the
graph and then the tail, once per head tuple and seeded only with the tail's
givens, yields exactly the results of the whole specification.

The argument is one step at the pivot (`pivot_step`), then the matches before
it, which both sides share.
-/
namespace JinagaSpec

/-- Two environments that agree on a scope give the same projected results for
a list of matches scoped in it, provided the projection names only labels that
are in scope or declared by the matches. -/
theorem exists_projection_iff {g : Graph} {after : List Match} {S L : List Name}
    (hsc : ScopedMatches S after) {env env2 : Env} (h : Agree S env env2)
    (hL : ∀ x ∈ L, x ∈ S ++ after.map (·.unknown.name)) (r : List (Option FactId)) :
    (∃ e3 ∈ evalMatches g env after, L.map e3 = r) ↔
    (∃ e4 ∈ evalMatches g env2 after, L.map e4 = r) := by
  constructor
  · rintro ⟨e3, he3, rfl⟩
    obtain ⟨e4, he4, hagree⟩ := evalMatches_agree g after S env env2 hsc h e3 he3
    exact ⟨e4, he4, (Agree.map (hagree.mono hL)).symm⟩
  · rintro ⟨e4, he4, rfl⟩
    obtain ⟨e3, he3, hagree⟩ := evalMatches_agree g after S env2 env hsc h.symm e4 he4
    exact ⟨e3, he3, (Agree.map (hagree.mono hL)).symm⟩

section Pivot

variable {g : Graph} {s : Specification} {before after : List Match} {pivot : Match}
  {sm : List Match} {tps : List PathCondition}

/-- Solving the pivot and everything after it from `e` is the same as solving
the split labels from `e`, then the tail from the tail's givens alone. -/
theorem pivot_step (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after)
    (hsp : splitPaths (declaredLabels s) (pathsOf pivot.conditions) = (sm, tps))
    (e : Env) (r : List (Option FactId)) :
    (∃ e2 ∈ evalMatches g e (pivot :: after), s.projection.labels.map e2 = r) ↔
    (∃ e' ∈ evalMatches g e sm,
      ∃ e3 ∈ evalMatches g
          (e'.restrictTo ((tailGivenAt s sm (tailMatchesAt pivot tps after)).map (·.name)))
          (tailMatchesAt pivot tps after),
        s.projection.labels.map e3 = r) := by
  -- What well-formedness says at the pivot.
  obtain ⟨hpaths, hex, hafter, hproj⟩ := pivot_scoped hwf hs
  have hT := tail_scoped hwf hs
  simp only [hsp] at hT
  obtain ⟨hTscoped, hTproj⟩ := hT
  have hdecl := pivot_labels_declared hwf hs
  have hscopeDecl := scopeAt_declared hwf hs
  have hne := pivot_paths_ne hwf hs
  have hnames := splitPaths_names (declaredLabels s) (pathsOf pivot.conditions)
  simp only [hsp] at hnames
  obtain ⟨hfresh, -⟩ := hnames
  generalize htg : (tailGivenAt s sm (tailMatchesAt pivot tps after)).map (·.name) = tgn at *
  obtain ⟨u, cs⟩ := pivot
  have hTdef : tailMatchesAt (.mk u cs) tps after =
      .mk u (tps.map .path ++ existentialsOf cs) :: after := by
    simp [tailMatchesAt]
  rw [hTdef] at hTscoped hTproj ⊢
  simp only [Match.unknown_mk, Match.conditions_mk] at hpaths hex hafter hproj hdecl hTproj hne hsp
  obtain ⟨hTconds, hTafter⟩ := hTscoped
  -- One candidate fact for the pivot at a time.
  have hf : ∀ f : Fact,
      (allHold g (e.bind u.name f.id) u.name cs = true ∧
        ∃ e2 ∈ evalMatches g (e.bind u.name f.id) after, s.projection.labels.map e2 = r) ↔
      (∃ e' ∈ evalMatches g e sm,
        allHold g ((e'.restrictTo tgn).bind u.name f.id) u.name (tps.map .path ++ existentialsOf cs) = true ∧
        ∃ e3 ∈ evalMatches g ((e'.restrictTo tgn).bind u.name f.id) after,
          s.projection.labels.map e3 = r) := by
    intro f
    -- The head's solutions leave every label in the pivot's scope alone.
    have hframe : ∀ e' ∈ evalMatches g e sm,
        Agree (u.name :: scopeAt s before) (e'.bind u.name f.id) (e.bind u.name f.id) := by
      intro e' he'
      have h1 : Agree (scopeAt s before) e' e := by
        intro x hx
        apply evalMatches_frame he' x
        intro hmem
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hmem
        exact hfresh m hm (hscopeDecl _ hx)
      exact h1.bind u.name f.id
    -- The tail sees only its givens.
    have hrestr : ∀ e' : Env, Agree (u.name :: tgn) ((e'.restrictTo tgn).bind u.name f.id)
        (e'.bind u.name f.id) := fun (e' : Env) => (Env.restrictTo_agree tgn e').bind u.name f.id
    have hcondT : ∀ e' : Env, allHold g ((e'.restrictTo tgn).bind u.name f.id) u.name
          (tps.map .path ++ existentialsOf cs) =
        allHold g (e'.bind u.name f.id) u.name (tps.map .path ++ existentialsOf cs) :=
      fun (e' : Env) => allHold_agree g _ u.name tgn _ _ hTconds (hrestr e')
    have hexs : ∀ e' ∈ evalMatches g e sm,
        allHold g (e'.bind u.name f.id) u.name (existentialsOf cs) =
        allHold g (e.bind u.name f.id) u.name (existentialsOf cs) :=
      fun e' he' => allHold_agree g _ u.name (scopeAt s before) _ _ hex (hframe e' he')
    -- The projected results are the same from either environment.
    have hLC : ∀ x ∈ s.projection.labels, x ∈ (u.name :: tgn) ++ after.map (·.unknown.name) := by
      intro x hx
      have := hTproj x hx
      simp at this ⊢
      grind
    have hLF : ∀ x ∈ s.projection.labels,
        x ∈ (u.name :: scopeAt s before) ++ after.map (·.unknown.name) := by
      intro x hx
      have := hproj x hx
      simp at this ⊢
      grind
    have hprojC : ∀ e' : Env, (∃ e3 ∈ evalMatches g ((e'.restrictTo tgn).bind u.name f.id) after,
          s.projection.labels.map e3 = r) ↔
        ∃ e3 ∈ evalMatches g (e'.bind u.name f.id) after, s.projection.labels.map e3 = r :=
      fun (e' : Env) => exists_projection_iff hTafter (hrestr e') hLC r
    have hprojF : ∀ e' ∈ evalMatches g e sm,
        (∃ e3 ∈ evalMatches g (e'.bind u.name f.id) after, s.projection.labels.map e3 = r) ↔
        ∃ e4 ∈ evalMatches g (e.bind u.name f.id) after, s.projection.labels.map e4 = r :=
      fun e' he' => exists_projection_iff hafter (hframe e' he') hLF r
    -- The pivot's path conditions.
    have hG := splitPaths_correct g u.name f.id (pathsOf cs) (declaredLabels s) e hne hdecl
    simp only [hsp] at hG
    have hsplitCs : allHold g (e.bind u.name f.id) u.name cs =
        (allHold g (e.bind u.name f.id) u.name ((pathsOf cs).map .path) &&
          allHold g (e.bind u.name f.id) u.name (existentialsOf cs)) :=
      allHold_pathsOf_existentialsOf
    constructor
    · rintro ⟨hc, hY⟩
      rw [hsplitCs] at hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨e', he', hp⟩ := hG.mpr hc.1
      refine ⟨e', he', ?_, (hprojC e').mpr ((hprojF e' he').mpr hY)⟩
      rw [hcondT, allHold_append, hexs e' he']
      simp [hp, hc.2]
    · rintro ⟨e', he', hc, hY⟩
      rw [hcondT, allHold_append, hexs e' he'] at hc
      simp only [Bool.and_eq_true] at hc
      refine ⟨?_, (hprojF e' he').mp ((hprojC e').mp hY)⟩
      rw [hsplitCs]
      simp only [Bool.and_eq_true]
      exact ⟨hG.mp ⟨e', he', hc.1⟩, hc.2⟩
  constructor
  · rintro ⟨e2, he2, hr⟩
    obtain ⟨f, hfg, hft, hc, he2'⟩ := mem_evalMatches_cons.mp he2
    obtain ⟨e', he', hh, e3, he3, hr3⟩ := (hf f).mp ⟨hc, e2, he2', hr⟩
    exact ⟨e', he', e3, mem_evalMatches_cons.mpr ⟨f, hfg, hft, hh, he3⟩, hr3⟩
  · rintro ⟨e', he', e3, he3, hr⟩
    obtain ⟨f, hfg, hft, hh, he3'⟩ := mem_evalMatches_cons.mp he3
    obtain ⟨hc, e2, he2, hr2⟩ := (hf f).mpr ⟨e', he', hh, e3, he3', hr⟩
    exact ⟨e2, mem_evalMatches_cons.mpr ⟨f, hfg, hft, hc, he2⟩, hr2⟩

end Pivot

/-- The two halves of `span` make up the list. -/
private theorem span_loop_append (p : Match → Bool) :
    ∀ (l acc : List Match), (List.span.loop p l acc).1 ++ (List.span.loop p l acc).2 = acc.reverse ++ l := by
  intro l
  induction l with
  | nil => intro acc; simp [List.span.loop]
  | cons a as ih =>
    intro acc
    simp only [List.span.loop]
    cases p a <;> simp [ih]

/-- A split preserves the meaning of a well-formed specification. -/
theorem split_correct (s : Specification) (hwf : WellFormed s) (g : Graph) (env : Env)
    (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluate g env ↔ r ∈ s.evaluate g env := by
  unfold splitBeforeFirstSuccessor
  generalize hspan : s.matchList.span matchIsDeterministic = sp
  obtain ⟨before, rest⟩ := sp
  cases rest with
  | nil =>
    -- Every match is deterministic: the whole specification is the head.
    simp [Split.evaluate]
  | cons pivot after =>
    have hs : s.matchList = before ++ pivot :: after := by
      have h := span_loop_append matchIsDeterministic s.matchList []
      unfold List.span at hspan
      rw [hspan] at h
      simpa using h.symm
    have hlhs : r ∈ s.evaluate g env ↔
        ∃ e2 ∈ evalMatches g env (before ++ pivot :: after), s.projection.labels.map e2 = r := by
      unfold Specification.evaluate
      rw [hs, List.mem_map]
    unfold splitAt
    rcases hsp : splitPaths (declaredLabels s) (pathsOf pivot.conditions) with ⟨sm, tps⟩
    simp only [hsp]
    by_cases hempty : (before ++ sm).isEmpty = true
    · -- Nothing for the graph to run: the tail is the whole specification.
      simp [hempty, Split.evaluate]
    · rw [hlhs]
      simp only [hempty, Bool.false_eq_true, ite_false, Split.evaluate, Specification.evaluate]
      rw [List.mem_flatMap]
      simp only [List.mem_map, mem_evalMatches_append]
      constructor
      · rintro ⟨tuple, ⟨e, he, he'⟩, e3, he3, hr⟩
        obtain ⟨e2, he2, hr2⟩ := (pivot_step hwf hs hsp e r).mpr ⟨tuple, he', e3, he3, hr⟩
        exact ⟨e2, ⟨e, he, he2⟩, hr2⟩
      · rintro ⟨e2, ⟨e, he, he2⟩, hr⟩
        obtain ⟨tuple, ht, e3, he3, hr3⟩ := (pivot_step hwf hs hsp e r).mp ⟨e2, he2, hr⟩
        exact ⟨tuple, ⟨e, he, ht⟩, e3, he3, hr3⟩

end JinagaSpec
