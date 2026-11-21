import JinagaSpec.Feeds
import JinagaSpec.Proofs.Fresh
import JinagaSpec.Proofs.Basic

/-!
# Feeds

`buildFeeds_shape`: every feed has `FeedShape`, and, when the specification
declares each label once, declares each of its own labels once.
-/
namespace JinagaSpec

/-! ## Shape -/

mutual
  theorem stripped_paths : ∀ (ms : List Match), ∀ m ∈ stripped ms, ∀ c ∈ m.conditions, c.isPath = true
    | [], _, h, _, _ => by simp [stripped] at h
    | .mk u cs :: rest, m, h, c, hc => by
      simp only [stripped, List.mem_cons, List.mem_append] at h
      rcases h with rfl | h | h
      · simpa using (List.mem_filter.mp hc).2
      · exact strippedPositives_paths _ m h c hc
      · exact stripped_paths _ m h c hc

  theorem strippedPositives_paths : ∀ (cs : List Condition), ∀ m ∈ strippedPositives cs, ∀ c ∈ m.conditions, c.isPath = true
    | [], _, h, _, _ => by simp [strippedPositives] at h
    | .existential true ms :: cs, m, h, c, hc => by
      simp only [strippedPositives, List.mem_append] at h
      rcases h with h | h
      · exact stripped_paths _ m h c hc
      · exact strippedPositives_paths _ m h c hc
    | .existential false _ :: cs, m, h, c, hc => by
      simp only [strippedPositives] at h; exact strippedPositives_paths _ m h c hc
    | .path _ :: cs, m, h, c, hc => by
      simp only [strippedPositives] at h; exact strippedPositives_paths _ m h c hc
end

theorem FeedShape.append {a b : List Match} (ha : FeedShape a) (hb : FeedShape b) : FeedShape (a ++ b) :=
  fun m hm => (List.mem_append.mp hm).elim (ha m) (hb m)

theorem FeedShape.cons {m : Match} {ms : List Match} (hm : FeedShape [m]) (hms : FeedShape ms) : FeedShape (m :: ms) :=
  FeedShape.append (a := [m]) hm hms

theorem FeedShape.of_cons {m : Match} {ms : List Match} (h : FeedShape (m :: ms)) : FeedShape [m] ∧ FeedShape ms :=
  ⟨fun x hx => h x (by simp_all), fun x hx => h x (by simp [hx])⟩

/-- A match with only path conditions has the shape. -/
theorem FeedShape.paths {u : Label} (cs : List Condition) : FeedShape [.mk u (cs.filter (·.isPath))] := by
  intro m hm c hc; simp at hm; subst hm; exact Or.inl (List.mem_filter.mp hc).2

theorem attach_shape {l : Name} {ms' : List Match} (hms : ∀ m ∈ ms', ∀ c ∈ m.conditions, c.isPath = true) :
    ∀ {ms : List Match}, FeedShape ms → FeedShape (attach l (.existential false ms') ms)
  | [], _ => by simp [attach, FeedShape]
  | .mk u cs :: rest, h => by
    obtain ⟨hu, hr⟩ := h.of_cons
    simp only [attach]
    split
    · exact FeedShape.cons hu (attach_shape hms hr)
    · split
      · refine FeedShape.cons ?_ hr
        intro m hm c hc
        simp at hm; subst hm
        rcases List.mem_append.mp hc with hc | hc
        · exact hu (.mk u cs) (by simp) c hc
        · simp at hc; subst hc; exact Or.inr ⟨ms', rfl, hms⟩
      · exact h

theorem unattach_shape {base : Nat} {feed : Specification} (h : FeedShape feed.matchList) :
    FeedShape (unattach base feed).matchList := by
  refine FeedShape.append (fun m hm => h m (List.mem_of_mem_take hm)) ?_
  intro m hm
  obtain ⟨⟨u, cs⟩, -, rfl⟩ := List.mem_map.mp hm
  exact FeedShape.paths cs _ (List.mem_singleton_self _)

theorem run_shape (givens : List Label) (feed : Specification) (parity base : Nat) (w : List Work)
    (h : FeedShape feed.matchList) : ∀ f ∈ run givens feed parity base w, FeedShape f.matchList := by
  fun_induction run givens feed parity base w
  all_goals intro f hf
  case case1 | case2 => simp at hf; subst hf; exact h
  case case3 | case4 | case6 | case7 | case8 => rename_i ih; exact ih h f hf
  case case5 => rename_i ih; exact ih (FeedShape.append h (FeedShape.paths _)) f hf
  case case9 =>
    rename_i excluding restoring main
    simp (config := { zetaDelta := true }) only [List.mem_append] at hf
    rcases hf with hf | hf
    · split at hf
      · exact excluding h f hf
      · exact restoring (unattach_shape h) f hf
    · exact main (attach_shape (stripped_paths _) h) f hf

/-! ## Each label once -/

/-- Every label the work still declares. -/
def workDeclared (w : List Work) : List Name := w.flatMap fun
  | .matches ms => declaredMatches ms
  | .conditions _ cs => declaredConditions cs
  | .stop _ => []

theorem afterStop_suffix (p : Nat) : ∀ w, workDeclared (afterStop p w) <:+ workDeclared w
  | [] => by simp [afterStop]
  | .stop q :: w => by
    simp only [afterStop]
    split
    · simp [workDeclared]
    · exact (afterStop_suffix p w).trans (by simp [workDeclared])
  | .matches _ :: w | .conditions _ _ :: w =>
    (afterStop_suffix p w).trans (List.suffix_append _ _)

theorem attach_names {l : Name} {c : Condition} : ∀ {ms : List Match}, names (attach l c ms) = names ms
  | [] => rfl
  | .mk u cs :: rest => by
    simp only [attach]
    have ih := attach_names (l := l) (c := c) (ms := rest)
    simp only [names] at ih
    split
    · simp [names, ih]
    · split <;> simp [names]

theorem run_nodup (givens : List Label) (feed : Specification) (parity base : Nat) (w : List Work)
    (h : (names feed.matchList ++ workDeclared w).Nodup) :
    ∀ f ∈ run givens feed parity base w, (names f.matchList).Nodup := by
  fun_induction run givens feed parity base w
  all_goals intro f hf
  case case1 | case2 => simp at hf; subst hf; exact h.sublist (List.sublist_append_left _ _)
  case case3 | case4 | case6 | case7 =>
    rename_i ih; exact ih (by simpa [workDeclared, declaredConditions, declaredMatches] using h) f hf
  case case5 =>
    rename_i ih
    exact ih (by simpa [workDeclared, declaredMatches, withMatch, names, List.append_assoc] using h) f hf
  case case8 =>
    rename_i ih
    exact ih (by simpa [workDeclared, declaredConditions, List.append_assoc] using h) f hf
  case case9 =>
    rename_i excluding restoring main
    simp only [workDeclared, List.flatMap_cons, declaredConditions, List.append_assoc] at h
    simp (config := { zetaDelta := true }) only [List.mem_append] at hf
    rcases hf with hf | hf
    · split at hf
      · exact excluding (by simpa (config := { zetaDelta := true }) [workDeclared, List.append_assoc] using h) f hf
      · refine restoring (h.sublist ?_) f hf
        simp only [unattach, names, List.map_append, List.map_map, List.map_take, List.map_drop]
        have : (fun x : Match => x.unknown.name) ∘ Match.paths = (·.unknown.name) := by
          funext m; cases m; rfl
        rw [this, List.take_append_drop, workDeclared, List.flatMap_cons]
        exact (List.Sublist.append_left (List.Sublist.append_left
          (afterStop_suffix _ (.conditions _ _ :: _)).sublist _) _)
    · refine main (h.sublist ?_) f hf
      simp only [withCondition, attach_names, workDeclared]
      exact List.Sublist.append_left (List.sublist_append_right _ _) _

/-- Every feed has `FeedShape`. When the specification declares each label once, so does each feed. -/
theorem buildFeeds_shape (s : Specification) :
    ∀ f ∈ buildFeeds s, FeedShape f.matchList ∧ (DistinctLabels s → (names f.matchList).Nodup) :=
  fun f hf => ⟨run_shape _ _ 0 0 _ (by simp [FeedShape]) f (List.mem_filter.mp hf).1,
    fun hd => run_nodup _ _ 0 0 _ (by simpa [names, workDeclared, DistinctLabels] using hd) f (List.mem_filter.mp hf).1⟩

/-! ## A new tuple binds a new fact -/

variable {g : Graph} {B : List Fact}

/-- Every label the environment binds names a fact outside the batch. -/
def Settled (B : List Fact) (env : Env) : Prop := ∀ n id, env n = some id → Outside B id

theorem Settled.bind {env : Env} (h : Settled B env) {n : Name} {id : FactId} (hid : Outside B id) :
    Settled B (env.bind n id) := by
  intro x i hx
  by_cases hxn : x = n
  · simp [Env.bind, hxn] at hx; exact hx ▸ hid
  · exact h x i (by simpa [Env.bind, hxn] using hx)

theorem allHold_paths_fresh (hf : Fresh g B) {env : Env} (henv : Settled B env) {u : Name} :
    ∀ {cs : List Condition}, (∀ c ∈ cs, c.isPath = true) → allHold (g ++ B) env u cs = allHold g env u cs
  | [], _ => rfl
  | .path pc :: cs, h => by
    simp only [allHold, holds, pathHolds_fresh hf pc (henv u) (henv pc.labelRight),
      allHold_paths_fresh hf henv fun c hc => h c (List.mem_cons_of_mem _ hc)]
  | .existential .. :: _, h => by simp [Condition.isPath] at h

/-- Matches with only path conditions keep every solution when a fresh batch
arrives. -/
theorem evalMatches_paths_mono (hf : Fresh g B) :
    ∀ {ms : List Match} {env σ : Env}, (∀ m ∈ ms, ∀ c ∈ m.conditions, c.isPath = true) → Settled B env →
      σ ∈ evalMatches g env ms → σ ∈ evalMatches (g ++ B) env ms
  | [], _, _, _, _, h => h
  | .mk u cs :: rest, env, σ, hp, henv, h => by
    obtain ⟨f, hfg, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    have hout : Outside B f.id := fun b hb => hf.idNew f hfg b hb
    have henv' := henv.bind (n := u.name) hout
    refine mem_evalMatches_cons.mpr ⟨f, List.mem_append_left _ hfg, ht, ?_, ?_⟩
    · rw [allHold_paths_fresh hf henv' (cs := cs) fun c hc => hp _ (List.mem_cons_self ..) c hc]; exact hc
    · exact evalMatches_paths_mono hf (fun m hm => hp m (List.mem_cons_of_mem _ hm)) henv' hr

theorem allHold_feed (hf : Fresh g B) {env : Env} (henv : Settled B env) {u : Name} :
    ∀ {cs : List Condition}, (∀ c ∈ cs, c.isPath = true ∨
        ∃ ms', c = .existential false ms' ∧ ∀ m' ∈ ms', ∀ c' ∈ m'.conditions, c'.isPath = true) →
      allHold (g ++ B) env u cs = true → allHold g env u cs = true
  | [], _, _ => rfl
  | c :: cs, hs, h => by
    simp only [allHold, Bool.and_eq_true] at h ⊢
    refine ⟨?_, allHold_feed hf henv (fun c hc => hs c (List.mem_cons_of_mem _ hc)) h.2⟩
    rcases hs c (List.mem_cons_self ..) with hc | ⟨ms', rfl, hms'⟩
    · have := allHold_paths_fresh hf henv (u := u) (cs := [c]) (by simpa using hc)
      simp only [allHold, Bool.and_true] at this
      exact this ▸ h.1
    · have h1 := h.1
      simp only [holds] at h1 ⊢
      cases h2 : evalMatches g env ms' with
      | nil => rfl
      | cons σ _ =>
        have := evalMatches_paths_mono hf hms' henv (h2 ▸ List.mem_cons_self ..)
        cases h3 : evalMatches (g ++ B) env ms' with
        | nil => rw [h3] at this; simp at this
        | cons => rw [h3] at h1; simp at h1

/-- A solution of a feed after a fresh batch arrives, all of whose labels bind
facts that were there before, was a solution before. -/
theorem evalMatches_feed_antitone (hf : Fresh g B) :
    ∀ {ms : List Match} {env e : Env}, FeedShape ms → (names ms).Nodup → Settled B env →
      e ∈ evalMatches (g ++ B) env ms → Settled B e → e ∈ evalMatches g env ms
  | [], _, _, _, _, _, h, _ => h
  | .mk u cs :: rest, env, e, hs, hnd, henv, h, he => by
    obtain ⟨f, hfg, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    have hnd' : u.name ∉ names rest ∧ (names rest).Nodup := by simpa [names] using hnd
    have heu : e u.name = some f.id := by
      rw [evalMatches_frame hr u.name hnd'.1]; simp [Env.bind]
    have hout : Outside B f.id := he _ _ heu
    have henv' := henv.bind (n := u.name) hout
    have hfg' : f ∈ g := (List.mem_append.mp hfg).resolve_right fun hb => hout f hb rfl
    obtain ⟨hs1, hs2⟩ := hs.of_cons
    exact mem_evalMatches_cons.mpr ⟨f, hfg', ht,
      allHold_feed hf henv' (hs1 _ (List.mem_singleton_self _)) hc,
      evalMatches_feed_antitone hf hs2 hnd'.2 henv' hr he⟩

/-- A tuple a feed finds after a fresh batch arrives, none of whose facts is in
the batch, is a tuple the feed found before. This is what lets a replicator
page a feed by a bookmark: a tuple that is new to a feed binds a new fact. -/
theorem feed_antitone (hf : Fresh g B) {f : Specification} (hs : FeedShape f.matchList)
    (hnd : (names f.matchList).Nodup) {env : Env} (henv : Settled B env) {t : List FactId}
    (ht : t ∈ f.tuples (g ++ B) env) (hout : ∀ id ∈ t, Outside B id) : t ∈ f.tuples g env := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  refine List.mem_map.mpr ⟨e, evalMatches_feed_antitone hf hs hnd henv he ?_, rfl⟩
  intro n id hn
  by_cases hm : n ∈ names f.matchList
  · exact hout id (List.mem_filterMap.mpr ⟨n, hm, hn⟩)
  · exact henv n id (by rw [← evalMatches_frame he n hm]; exact hn)

end JinagaSpec
