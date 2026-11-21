import JinagaSpec.Feeds
import JinagaSpec.Proofs.Fresh
import JinagaSpec.Proofs.Reorder

/-!
# Feeds

* `buildFeeds_paths`: a feed has only path conditions.
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

theorem levelFeeds_pathsOnly : ∀ (pre ms : List Match), PathsOnly pre → ∀ F ∈ levelFeeds pre ms, PathsOnly F := by
  intro pre ms
  induction pre, ms using levelFeeds.induct with
  | case1 pre ms here ih =>
    intro h F hF
    rw [levelFeeds] at hF
    rcases List.mem_cons.mp hF with rfl | hF
    · exact h.append (pathsOnly_paths _)
    · simp only [List.mem_flatMap] at hF
      obtain ⟨⟨m, hm⟩, -, ⟨ns, hns⟩, -, hF⟩ := hF
      exact ih m hm ns hns (h.append (pathsOnly_paths _)) F hF

/-- A feed has only path conditions. -/
theorem buildFeeds_paths (s : Specification) : ∀ f ∈ buildFeeds s, PathsOnly f.matchList := by
  intro f hf
  obtain ⟨hf, -⟩ := List.mem_filter.mp hf
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hf
  exact levelFeeds_pathsOnly [] s.matchList (by simp [PathsOnly]) F hF

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

/-- A solution after a fresh batch arrives, of matches with only path
conditions, that binds no fact of the batch, was a solution before. -/
theorem evalMatches_paths_antitone (hf : Fresh g B) :
    ∀ {ms : List Match} {env e : Env}, PathsOnly ms → (names ms).Nodup → Settled B env →
      e ∈ evalMatches (g ++ B) env ms → Settled B e → e ∈ evalMatches g env ms
  | [], _, _, _, _, _, h, _ => h
  | .mk u cs :: rest, env, e, hp, hnd, henv, h, he => by
    obtain ⟨f, hfg, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    have hnd' : u.name ∉ names rest ∧ (names rest).Nodup := by simpa [names] using hnd
    have hout : Outside B f.id := he _ _ (by rw [evalMatches_frame hr u.name hnd'.1]; simp [Env.bind])
    have henv' := henv.bind (n := u.name) hout
    have hfg' : f ∈ g := (List.mem_append.mp hfg).resolve_right fun hb => hout f hb rfl
    refine mem_evalMatches_cons.mpr ⟨f, hfg', ht, ?_,
      evalMatches_paths_antitone hf (fun m hm => hp m (List.mem_cons_of_mem _ hm)) hnd'.2 henv' hr he⟩
    rw [← allHold_paths_fresh hf henv' (cs := cs) fun c hc => hp _ (List.mem_cons_self ..) c hc]; exact hc

/-- A tuple a feed finds after a fresh batch arrives, none of whose facts is in
the batch, is a tuple the feed found before. This is what lets a replicator
page a feed by a bookmark: a tuple that is new to a feed binds a new fact. -/
theorem feed_antitone (hf : Fresh g B) {f : Specification} (hp : PathsOnly f.matchList)
    (hnd : (names f.matchList).Nodup) {env : Env} (henv : Settled B env) {t : List FactId}
    (ht : t ∈ f.tuples (g ++ B) env) (hout : ∀ id ∈ t, Outside B id) : t ∈ f.tuples g env := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  refine List.mem_map.mpr ⟨e, evalMatches_paths_antitone hf hp hnd henv he ?_, rfl⟩
  intro n id hn
  by_cases hm : n ∈ names f.matchList
  · exact hout id (List.mem_filterMap.mpr ⟨n, hm, hn⟩)
  · exact henv n id (by rw [← evalMatches_frame he n hm]; exact hn)

end JinagaSpec
