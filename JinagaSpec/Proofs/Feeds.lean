import JinagaSpec.Feeds
import JinagaSpec.Proofs.Fresh
import JinagaSpec.Proofs.Reorder

/-!
# Feeds

* `buildFeeds_feedShape`: a feed has path conditions, and negative conditions
  over matches with only path conditions.
* `feed_antitone`: so a tuple that is new to a feed binds a new fact, which is
  what paging by bookmark needs (`Proofs/Cursor.lean`).
-/
namespace JinagaSpec

/-- Every condition of the matches is a path condition. -/
def PathsOnly (ms : List Match) : Prop := ∀ m ∈ ms, ∀ c ∈ m.conditions, c.isPath = true

theorem pathsOnly_paths (ms : List Match) : PathsOnly (ms.map Match.paths) := by
  intro m hm c hc
  obtain ⟨⟨u, cs⟩, -, rfl⟩ := List.mem_map.mp hm
  exact (List.mem_filter.mp hc).2

theorem PathsOnly.append {a b : List Match} (ha : PathsOnly a) (hb : PathsOnly b) : PathsOnly (a ++ b) :=
  fun m hm => (List.mem_append.mp hm).elim (ha m) (hb m)

/-- Every condition is a path condition, or a negative condition over matches
with only path conditions: the one level of negative condition that paging by
bookmark allows. -/
def FeedConditions (cs : List Condition) : Prop :=
  ∀ c ∈ cs, c.isPath = true ∨ ∃ ns, c = .existential false ns ∧ PathsOnly ns

def FeedShape (ms : List Match) : Prop := ∀ m ∈ ms, FeedConditions m.conditions

theorem FeedShape.append {a b : List Match} (ha : FeedShape a) (hb : FeedShape b) : FeedShape (a ++ b) :=
  fun m hm => (List.mem_append.mp hm).elim (ha m) (hb m)

theorem PathsOnly.shape {a : List Match} (h : PathsOnly a) : FeedShape a :=
  fun m hm c hc => Or.inl (h m hm c hc)

theorem attach_shape {l : Name} {ns : List Match} (hns : PathsOnly ns) :
    ∀ {ms : List Match}, FeedShape ms → FeedShape (attach l (.existential false ns) ms)
  | [], _ => by simp [attach, FeedShape]
  | .mk u cs :: rest, h => by
    have hu : FeedConditions cs := h _ (List.mem_cons_self ..)
    have hr : FeedShape rest := fun m hm => h m (List.mem_cons_of_mem _ hm)
    simp only [attach]
    split
    · exact FeedShape.append (a := [_]) (fun m hm => by simp at hm; subst hm; exact hu) (attach_shape hns hr)
    · split
      · refine FeedShape.append (a := [_]) (fun m hm => ?_) hr
        simp at hm; subst hm
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hu c hc
        · simp at hc; subst hc; exact Or.inr ⟨ns, rfl, hns⟩
      · exact h

mutual
  theorem levelFeeds_shape (k : List Match → List (List Match))
      (hk : ∀ Q, FeedShape Q → ∀ F ∈ k Q, FeedShape F) :
      ∀ (P ms : List Match), FeedShape P → ∀ F ∈ levelFeeds k P ms, FeedShape F
    | P, [], hP, F, hF => by rw [levelFeeds] at hF; exact hk P hP F hF
    | P, m :: rest, hP, F, hF => by
      rw [levelFeeds] at hF
      exact negFeeds_shape _ (fun Q hQ F hF => levelFeeds_shape k hk Q rest hQ F hF) _ _
        (hP.append (pathsOnly_paths _).shape) F hF
  termination_by _ ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (m :: rest)) (by simp; omega) fun p hp => sizeOf_unitNegatives p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

  theorem negFeeds_shape (k : List Match → List (List Match))
      (hk : ∀ Q, FeedShape Q → ∀ F ∈ k Q, FeedShape F) :
      ∀ (Q : List Match) (negs : List (Name × List Match)), FeedShape Q → ∀ F ∈ negFeeds k Q negs, FeedShape F
    | Q, [], hQ, F, hF => by rw [negFeeds] at hF; exact hk Q hQ F hF
    | Q, (h, ns) :: rest, hQ, F, hF => by
      rw [negFeeds] at hF
      have hlevel : FeedShape (Q ++ level ns) := hQ.append (pathsOnly_paths _).shape
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hlevel
      rcases List.mem_append.mp hF with hF | hF
      · exact negFeeds_shape k hk _ rest (attach_shape (pathsOnly_paths _) hQ) F hF
      · obtain ⟨⟨ns', hns'⟩, -, hF⟩ := List.mem_flatMap.mp hF
        exact levelFeeds_shape _ (fun Q' hQ' F hF => negFeeds_shape k hk Q' rest hQ' F hF) _ ns' hlevel F hF
  termination_by _ negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (simp only [Prod.lex_def]; have := maxSize_cons (h, ns) rest; omega)
      | (apply Prod.Lex.left
         exact Nat.lt_of_lt_of_le (sizeOf_cancellers _ hns') (le_maxSize (p := (h, ns)) (List.mem_cons_self ..)))
end

/-- Every feed has one level of negative condition, over matches with only path
conditions. -/
theorem buildFeeds_feedShape (s : Specification) : ∀ f ∈ buildFeeds s, FeedShape f.matchList := by
  intro f hf
  obtain ⟨hf, -⟩ := List.mem_filter.mp hf
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hf
  exact levelFeeds_shape _ (fun Q hQ F hF => by simp at hF; exact hF ▸ hQ) [] s.matchList
    (by simp [FeedShape]) F hF

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
    ∀ {ms : List Match} {env σ : Env}, PathsOnly ms → Settled B env →
      σ ∈ evalMatches g env ms → σ ∈ evalMatches (g ++ B) env ms
  | [], _, _, _, _, h => h
  | .mk u cs :: rest, env, σ, hp, henv, h => by
    obtain ⟨f, hfg, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    have henv' := henv.bind (n := u.name) fun b hb => hf.idNew f hfg b hb
    refine mem_evalMatches_cons.mpr ⟨f, List.mem_append_left _ hfg, ht, ?_, ?_⟩
    · rw [allHold_paths_fresh hf henv' (cs := cs) fun c hc => hp _ (List.mem_cons_self ..) c hc]; exact hc
    · exact evalMatches_paths_mono hf (fun m hm => hp m (List.mem_cons_of_mem _ hm)) henv' hr

/-- A feed's conditions, true after a fresh batch arrives at an environment that
binds no fact of the batch, were true before: a path condition reads the same,
and a negative condition over path conditions only loses solutions going back. -/
theorem allHold_feed (hf : Fresh g B) {env : Env} (henv : Settled B env) {u : Name} :
    ∀ {cs : List Condition}, FeedConditions cs → allHold (g ++ B) env u cs = true → allHold g env u cs = true
  | [], _, _ => rfl
  | c :: cs, hs, h => by
    simp only [allHold, Bool.and_eq_true] at h ⊢
    refine ⟨?_, allHold_feed hf henv (fun c hc => hs c (List.mem_cons_of_mem _ hc)) h.2⟩
    rcases hs c (List.mem_cons_self ..) with hc | ⟨ns, rfl, hns⟩
    · have := allHold_paths_fresh hf henv (u := u) (cs := [c]) (by simpa using hc)
      simp only [allHold, Bool.and_true] at this
      exact this ▸ h.1
    · have h1 := h.1
      simp only [holds] at h1 ⊢
      cases h2 : evalMatches g env ns with
      | nil => rfl
      | cons σ _ =>
        have := evalMatches_paths_mono hf hns henv (h2 ▸ List.mem_cons_self ..)
        cases h3 : evalMatches (g ++ B) env ns with
        | nil => rw [h3] at this; simp at this
        | cons => rw [h3] at h1; simp at h1

/-- A solution after a fresh batch arrives, of a feed's matches, that binds no
fact of the batch, was a solution before. -/
theorem evalMatches_paths_antitone (hf : Fresh g B) :
    ∀ {ms : List Match} {env e : Env}, FeedShape ms → (names ms).Nodup → Settled B env →
      e ∈ evalMatches (g ++ B) env ms → Settled B e → e ∈ evalMatches g env ms
  | [], _, _, _, _, _, h, _ => h
  | .mk u cs :: rest, env, e, hp, hnd, henv, h, he => by
    obtain ⟨f, hfg, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    have hnd' : u.name ∉ names rest ∧ (names rest).Nodup := by simpa [names] using hnd
    have hout : Outside B f.id := he _ _ (by rw [evalMatches_frame hr u.name hnd'.1]; simp [Env.bind])
    have henv' := henv.bind (n := u.name) hout
    have hfg' : f ∈ g := (List.mem_append.mp hfg).resolve_right fun hb => hout f hb rfl
    exact mem_evalMatches_cons.mpr ⟨f, hfg', ht, allHold_feed hf henv' (hp _ (List.mem_cons_self ..)) hc,
      evalMatches_paths_antitone hf (fun m hm => hp m (List.mem_cons_of_mem _ hm)) hnd'.2 henv' hr he⟩

/-- A tuple a feed finds after a fresh batch arrives, none of whose facts is in
the batch, is a tuple the feed found before. This is what lets a replicator
page a feed by a bookmark: a tuple that is new to a feed binds a new fact. -/
theorem feed_antitone (hf : Fresh g B) {f : Specification} (hp : FeedShape f.matchList)
    (hnd : (names f.matchList).Nodup) {env : Env} (henv : Settled B env) {t : List FactId}
    (ht : t ∈ f.tuples (g ++ B) env) (hout : ∀ id ∈ t, Outside B id) : t ∈ f.tuples g env := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  refine List.mem_map.mpr ⟨e, evalMatches_paths_antitone hf hp hnd henv he ?_, rfl⟩
  intro n id hn
  by_cases hm : n ∈ names f.matchList
  · exact hout id (List.mem_filterMap.mpr ⟨n, hm, hn⟩)
  · exact henv n id (by rw [← evalMatches_frame he n hm]; exact hn)

end JinagaSpec
