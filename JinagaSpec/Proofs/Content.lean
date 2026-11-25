import JinagaSpec.Content
import JinagaSpec.Proofs.Basic
import JinagaSpec.Proofs.Children
import JinagaSpec.Proofs.Exact
import JinagaSpec.Proofs.WellFormedCheck

/-!
# The content store's security invariants

SEC-1 to SEC-5 of the content-storage requirements, for every policy
(`Content.lean`). Each is stated for the replicator's state after any history
of saves and uploads (`Replicator.run`), where it needs one; SEC-1, SEC-4 and
SEC-5 hold of `read` on every state.

* `read_authorized` (SEC-1): a read returns an object only to an authenticated
  user whom the distribution rules let run the proof, and whose proof yields
  the content fact.
* `stored_authorized` (SEC-3): every stored object was uploaded, those bytes
  exactly, for its key, by a user the authorization rules let create the
  content fact at the moment the upload was accepted, and the bytes matched
  the fact's content hash then.
* `read_integrity` (SEC-2): a read returns only bytes whose hash is the content
  fact's content hash.
* `read_isolated` (SEC-4): a read keyed by `F` depends on the object stored
  under `F` alone, so never on bytes stored under another key, whatever their
  content hash.
* `read_noninterference` and `write_noninterference` (SEC-5): to a reader the
  rules do not admit, or a writer they refuse, the answer does not depend on
  which objects are stored.

`yields_iff_reads` says what `Proof.yields` means: some result a replica
reads (`Specification.Reads`, child specifications included) names the fact
at some depth (`Result.Names`), which is what RR-4 and CR-1 ask. The step on
the way is `yields_iff`: a solution of the matches, then of a child
specification's matches from it, and so on down, names the fact
(`Projection.Names`), which `Projection.names_iff_reads` proves is the same.

`read` does not compute `Proof.yields`: it runs `Proof.confirms`, which binds
the content fact as a result and looks for a solution, starting at the fact
(RR-4). `confirms_eq_yields` proves the two agree on every proof whose
specification's descendants are well formed, and `Proof.bound_iff` that
`Proof.bound`, which `read` checks first, decides exactly that and the given
count (`Proof.Bound`). So SEC-1 and `read_admitted`, stated against
`Proof.yields`, say that the check is right. `read_badRequest` is RR-1: a read
is 400 exactly when the proof is not bound.

SEC-1 to SEC-5 only say when the replicator may serve or store. The success
path is `read_admitted` and `write_accepted`: an admitted reader is served, or
told nothing is stored, and an authorized, matching upload is stored.

`CheckContent.lean` tests each statement as written against mutants of the
handlers, one per way of breaking it.
-/
namespace JinagaSpec

theorem Replicator.write_store (P : Policy) (r : Replicator) (u : Option User) (k : FactId) (o : Bytes) :
    (r.write P u k o).1.store = r.store := by
  unfold write; repeat' split
  all_goals rfl

/-- The fact store only grows. -/
theorem Replicator.store_grows (P : Policy) (evs : List Event) (r : Replicator) :
    ∃ g, (evs.foldl (step P) r).store = r.store ++ g := by
  induction evs generalizing r with
  | nil => exact ⟨[], by simp⟩
  | cons e evs ih =>
    obtain ⟨g, hg⟩ := ih (r.step P e)
    simp only [List.foldl, hg]
    cases e with
    | save B => by_cases h : r.store.accepts B <;> simp [step, h] <;> exact ⟨_, rfl⟩
    | write u k o => exact ⟨g, by simp [step, write_store]⟩

/-- An object in the state after an event was there before, or that event is
the accepted upload of exactly those bytes for that key. -/
theorem Replicator.mem_step {P : Policy} {r : Replicator} {e : Event}
    (h : (k, o) ∈ (r.step P e).objects) :
    (k, o) ∈ r.objects ∨ ∃ u f, e = .write (some u) k o ∧ r.store.factOf k = some f ∧
      P.mayCreate u r.store f = true ∧ P.contentHash f = some (P.hash o) := by
  cases e with
  | save B => simp only [step] at h; split at h <;> exact .inl h
  | write user key o' =>
    rcases user with _ | u
    · exact .inl h
    simp only [step, write] at h
    repeat' split at h <;> try exact .inl h
    rcases List.mem_cons.1 h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact .inr ⟨u, _, rfl, by assumption, by simp_all, by simp_all⟩
    · exact .inl h

/-- An object stored after a history of events, from any state, was there
already, or was accepted at some point in the history. -/
theorem Replicator.mem_foldl {P : Policy} {r : Replicator} {evs : List Event}
    (h : (k, o) ∈ (evs.foldl (step P) r).objects) :
    (k, o) ∈ r.objects ∨ ∃ pre post u f, evs = pre ++ .write (some u) k o :: post ∧
      (pre.foldl (step P) r).store.factOf k = some f ∧
      P.mayCreate u (pre.foldl (step P) r).store f = true ∧ P.contentHash f = some (P.hash o) := by
  induction evs generalizing r with
  | nil => exact .inl h
  | cons e evs ih =>
    rcases ih h with h | ⟨pre, post, u, f, rfl, hw⟩
    · rcases mem_step h with h | ⟨u, f, rfl, hw⟩
      · exact .inl h
      · exact .inr ⟨[], evs, u, f, rfl, hw⟩
    · exact .inr ⟨e :: pre, post, u, f, rfl, hw⟩

/-- SEC-3. -/
theorem stored_authorized {P : Policy} {evs : List Event} (h : (k, o) ∈ (Replicator.run P evs).objects) :
    ∃ pre post u f, evs = pre ++ .write (some u) k o :: post ∧
      (Replicator.run P pre).store.factOf k = some f ∧
      P.mayCreate u (Replicator.run P pre).store f = true ∧ P.contentHash f = some (P.hash o) := by
  simpa [Replicator.run, Replicator.empty] using Replicator.mem_foldl h

/-! ## Confirming a proof by binding the result (RR-4) -/

/-- Pinning `l`'s match keeps exactly the solutions that bind `l` to the
pinned fact, when `l` is bound once and the pin is not an unknown. -/
theorem evalMatches_pinUnknown {G : Graph} {l : Name} {key : FactId} :
    ∀ {ms : List Match} {env σ : Env}, env pinLabel = some key → pinLabel ∉ names ms → l ∈ names ms →
      (names ms).Nodup →
      (σ ∈ evalMatches G env (pinUnknown l ms) ↔ σ ∈ evalMatches G env ms ∧ σ l = some key)
  | [], _, _, _, _, hl, _ => by simp [names] at hl
  | .mk u cs :: rest, env, σ, hk, hp, hl, hnd => by
    simp only [names, List.map_cons, List.mem_cons, List.nodup_cons, not_or, Match.unknown_mk] at hp hl hnd
    have hk' : ∀ x, (env.bind u.name x) pinLabel = some key := fun x => by
      simp only [Env.bind, hp.1, ↓reduceIte, hk]
    simp only [pinUnknown, List.map_cons, Match.unknown_mk, Match.conditions_mk]
    by_cases hu : u.name = l
    · subst hu
      have hrest : rest.map (fun m => if m.unknown.name == u.name then
          Match.mk m.unknown (pinCondition :: m.conditions) else m) = rest :=
        (List.map_congr_left fun m hm => by
          simp [show m.unknown.name ≠ u.name from fun h => hnd.1 (h ▸ List.mem_map_of_mem hm)]).trans
          (List.map_id _)
      simp only [beq_self_eq_true, ite_true, hrest, mem_evalMatches_cons, allHold, Bool.and_eq_true]
      have hpin : ∀ x, holds G (env.bind u.name x) u.name pinCondition = decide (x = key) := fun x => by
        simp only [holds, PathCondition.holds, pinCondition, hk' x]; simp [Env.bind, Graph.walk]
      simp only [hpin, decide_eq_true_eq]
      constructor
      · rintro ⟨x, hx, ht, ⟨rfl, hc⟩, hr⟩
        exact ⟨⟨x, hx, ht, hc, hr⟩, by rw [evalMatches_frame hr _ hnd.1]; simp [Env.bind]⟩
      · rintro ⟨⟨x, hx, ht, hc, hr⟩, hσ⟩
        rw [evalMatches_frame hr _ hnd.1] at hσ
        exact ⟨x, hx, ht, ⟨by simpa [Env.bind] using hσ, hc⟩, hr⟩
    · have hl' : l ∈ names rest := hl.resolve_left (Ne.symm hu)
      simp only [show (u.name == l) = false from by simpa using hu, Bool.false_eq_true, ite_false,
        mem_evalMatches_cons]
      constructor
      · rintro ⟨x, hx, ht, hc, hr⟩
        obtain ⟨hr, hσ⟩ := (evalMatches_pinUnknown (hk' x.id) hp.2 hl' hnd.2).1 hr
        exact ⟨⟨x, hx, ht, hc, hr⟩, hσ⟩
      · rintro ⟨⟨x, hx, ht, hc, hr⟩, hσ⟩
        exact ⟨x, hx, ht, hc, (evalMatches_pinUnknown (hk' x.id) hp.2 hl' hnd.2).2 ⟨hr, hσ⟩⟩

theorem not_isEmpty_iff {α : Type} {xs : List α} : (!xs.isEmpty) = true ↔ ∃ x, x ∈ xs := by
  cases xs <;> simp

/-- `bindsResult` finds a solution that binds the label to the fact. -/
theorem Specification.bindsResult_iff {d : Specification} (hwf : WellFormed d) (g : Graph) (env : Env)
    (key : FactId) (l : Name) :
    d.bindsResult g env key l = true ↔ ∃ σ ∈ evalMatches g env d.matchList, σ l = some key := by
  unfold Specification.bindsResult
  split
  · rename_i m hm
    obtain rfl : m.unknown.name = l := by simpa using List.find?_some hm
    have hl : m.unknown.name ∈ names d.matchList := List.mem_map_of_mem (List.mem_of_find?_eq_some hm)
    have hp : m.unknown.name ≠ pinLabel := hwf.not_pin (.inr hl)
    have hpin σ' := evalMatches_pinUnknown (G := g) (σ := σ') (env := env.bind pinLabel key) (key := key)
      (by simp [Env.bind]) (fun h => hwf.not_pin (.inr h) rfl) hl hwf.wellNamed.nodup
    rw [not_isEmpty_iff]
    simp only [reorderOrSelf_correct]
    simp only [Specification.evaluate, Specification.pinResult, List.mem_map]
    constructor
    · rintro ⟨_, σ', hσ', -⟩
      obtain ⟨hσ', hk⟩ := (hpin σ').1 hσ'
      obtain ⟨σ, hσ, hag⟩ := evalMatches_agreeOff _ (AgreeOff.pin env key) hwf.pin_unused hσ'
      exact ⟨σ, hσ, hag _ hp ▸ hk⟩
    · rintro ⟨σ, hσ, hk⟩
      obtain ⟨σ', hσ', hag⟩ := evalMatches_agreeOff _ (AgreeOff.pin env key).symm hwf.pin_unused hσ
      exact ⟨_, σ', (hpin σ').2 ⟨hσ', hag _ hp ▸ hk⟩, rfl⟩
  · rename_i hm
    have hl : l ∉ d.matchList.map (·.unknown.name) := fun h => by
      obtain ⟨m, hm', rfl⟩ := List.mem_map.1 h
      exact List.find?_eq_none.1 hm m hm' (by simp)
    rw [Bool.and_eq_true, not_isEmpty_iff, beq_iff_eq]
    exact ⟨fun ⟨hk, σ, hσ⟩ => ⟨σ, hσ, evalMatches_frame hσ l hl ▸ hk⟩,
      fun ⟨σ, hσ, hk⟩ => ⟨evalMatches_frame hσ l hl ▸ hk, σ, hσ⟩⟩

/-- **`confirms_eq_yields`.** The replicator's check is `Proof.yields`, for every
proof whose specification's descendants are well formed, which `Proof.bound`
checks. -/
theorem confirms_eq_yields {p : Proof} (hwf : ∀ d ∈ p.spec.descendants, WellFormed d) (g : Graph)
    (key : FactId) : p.confirms g key = p.yields g key := by
  rw [Bool.eq_iff_iff]
  simp only [Proof.confirms, Proof.yields, List.any_eq_true]
  refine exists_congr fun d => and_congr_right fun hd => ?_
  simp only [Specification.read, Bool.and_eq_true, List.any_eq_true, Specification.bindsResult_iff (hwf d hd)]
  split <;> simp [Specification.evaluate, *]
  exact ⟨fun ⟨l, hl, σ, hσ, hk⟩ => ⟨_, ⟨σ, hσ, rfl⟩, List.mem_map.2 ⟨l, hl, hk⟩⟩,
    fun ⟨_, ⟨σ, hσ, e⟩, hk⟩ => let ⟨l, hl, hk⟩ := List.mem_map.1 (e ▸ hk); ⟨l, hl, σ, hσ, hk⟩⟩

/-! ## The proof is checked at RR-1 -/

/-- What `Proof.bound` checks (RR-1): a fact for every given, and every
descendant of the specification well formed, which `confirms_eq_yields`
assumes. -/
def Proof.Bound (p : Proof) : Prop :=
  p.givens.length = p.spec.given.length ∧ ∀ d ∈ p.spec.descendants, WellFormed d

/-- **`Proof.bound_iff`.** `Proof.bound` decides `Proof.Bound`. -/
theorem Proof.bound_iff (p : Proof) : p.bound = true ↔ p.Bound := by
  simp [Proof.bound, Proof.Bound, isWellFormedDeep_iff]

/-- With a bound proof, `read` asks what `Policy.admits` asks: its check is
`Proof.yields` (`confirms_eq_yields`). -/
theorem Replicator.read_bound {P : Policy} {r : Replicator} (hb : p.bound = true) :
    r.read P (some u) key p = if !P.admits r.store u key p then .forbidden else
      match r.objects.lookup key with
      | none => .notUploaded
      | some o => .ok o := by
  simp only [read, hb, Policy.admits, confirms_eq_yields ((p.bound_iff.1 hb).2)]; rfl

/-- **RR-1.** An authenticated read is refused with 400 exactly when the proof
is not bound: a given without a fact, or a descendant that is not well
formed. -/
theorem read_badRequest {P : Policy} {r : Replicator} :
    r.read P (some u) key p = .badRequest ↔ ¬ p.Bound := by
  rw [← p.bound_iff]
  cases hb : p.bound
  · simp [Replicator.read, hb]
  · rw [Replicator.read_bound hb]; split <;> (try split) <;> simp

/-- A read that returns an object returns the one stored under its key, to a
user the rules admit. -/
theorem Replicator.read_ok {P : Policy} {r : Replicator} (h : r.read P user key p = .ok o) :
    ∃ u, user = some u ∧ P.admits r.store u key p = true ∧ r.objects.lookup key = some o := by
  cases user with
  | none => simp [read] at h
  | some u =>
    cases hb : p.bound
    · simp [read, hb] at h
    · rw [read_bound hb] at h
      split at h
      · cases h
      · split at h <;> simp_all

/-- SEC-1. -/
theorem read_authorized {P : Policy} {r : Replicator} (h : r.read P user key p = .ok o) :
    ∃ u, user = some u ∧ P.distributes u p.spec p.givens r.store = true ∧ p.yields r.store key = true := by
  obtain ⟨u, rfl, h, _⟩ := Replicator.read_ok h
  exact ⟨u, rfl, by simpa [Policy.admits] using h⟩

/-- SEC-2. -/
theorem read_integrity {P : Policy} {evs : List Event}
    (h : (Replicator.run P evs).read P user key p = .ok o) :
    ∃ f, (Replicator.run P evs).store.factOf key = some f ∧ P.contentHash f = some (P.hash o) := by
  obtain ⟨_, _, _, hl⟩ := Replicator.read_ok h
  have hmem : (key, o) ∈ (Replicator.run P evs).objects := by
    obtain ⟨_, _, he, _⟩ := List.lookup_eq_some_iff.1 hl; rw [he]; simp
  obtain ⟨pre, post, _, f, rfl, hf, _, hh⟩ := stored_authorized hmem
  obtain ⟨g, hg⟩ := Replicator.store_grows P (.write _ key o :: post) (Replicator.run P pre)
  simp only [Replicator.run, List.foldl_append] at hg ⊢
  exact ⟨f, hg ▸ Graph.factOf_append hf g, hh⟩

/-- SEC-4. -/
theorem read_isolated {P : Policy} {r r' : Replicator} (hs : r.store = r'.store)
    (ho : r.objects.lookup key = r'.objects.lookup key) :
    r.read P user key p = r'.read P user key p := by
  simp only [Replicator.read, hs, ho]

/-- SEC-5. -/
theorem read_noninterference {P : Policy} {r : Replicator}
    (hu : ∀ u, user = some u → P.admits r.store u key p = false) (objects : List (FactId × Bytes)) :
    r.read P user key p = { r with objects }.read P user key p := by
  cases user with
  | none => rfl
  | some u =>
    cases hb : p.bound
    · simp [Replicator.read, hb]
    · simp [Replicator.read_bound hb, hu u rfl]

/-- SEC-5, for uploads: to a writer the authorization rules refuse, the
answer does not depend on which objects are stored. -/
theorem write_noninterference {P : Policy} {r : Replicator}
    (hu : ∀ u f, user = some u → r.store.factOf key = some f → P.mayCreate u r.store f = false)
    (objects : List (FactId × Bytes)) :
    (r.write P user key o).2 = ({ r with objects }.write P user key o).2 := by
  cases user with
  | none => rfl
  | some u =>
    cases hf : r.store.factOf key with
    | none => simp [Replicator.write, hf]
    | some f => simp [Replicator.write, hf, hu u f rfl hf]

/-- An admitted reader with a bound proof gets the object stored under the
key, or 404 `not_uploaded` if there is none (RR-7). With SEC-1, this fixes
every answer `read` gives an authenticated user. -/
theorem read_admitted {P : Policy} {r : Replicator} (hb : p.bound = true)
    (ha : P.admits r.store u key p = true) :
    r.read P (some u) key p = match r.objects.lookup key with
      | none => .notUploaded
      | some o => .ok o := by
  simp only [Replicator.read_bound hb, ha]; cases r.objects.lookup key <;> rfl

/-- An authorized writer's upload of matching bytes within the constraints is
stored, unless the key already holds an object (RW-8). -/
theorem write_accepted {P : Policy} {r : Replicator} (hf : r.store.factOf key = some f)
    (hm : P.mayCreate u r.store f = true) (hh : P.contentHash f = some (P.hash o))
    (hfit : P.fits f o = true) :
    r.write P (some u) key o = match r.objects.lookup key with
      | some _ => (r, .alreadyStored)
      | none => ({ r with objects := (key, o) :: r.objects }, .stored) := by
  simp [Replicator.write, hf, hm, hh, hfit]; cases r.objects.lookup key <;> rfl

/-- RW-6: an authorized writer's upload to a content-bearing fact that breaks
the constraints is refused with 413, whether or not the bytes match the content
hash. The constraints are checked before the hash, because an oversized stream
is aborted before all of it, and so its hash, is known. -/
theorem write_tooLarge {P : Policy} {r : Replicator} (hf : r.store.factOf key = some f)
    (hm : P.mayCreate u r.store f = true) (hh : P.contentHash f = some h)
    (hfit : P.fits f o = false) :
    r.write P (some u) key o = (r, .tooLarge) := by
  simp [Replicator.write, hf, hm, hh, hfit]

/-- Running the matches `ms` from `env`, the projection `p` names `key`: some
solution projects it, or names it through a child specification, read from
that solution: the nested reading of a specification's results, at every
depth. -/
def Projection.Names (g : Graph) (key : FactId) : Projection → List Match → Env → Prop
  | p, ms, env => ∃ σ ∈ evalMatches g env ms,
      some key ∈ p.labels.map σ ∨ ∃ c, ∃ _ : c ∈ p.children, c.2.Names g key c.1 σ
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children ‹_›

/-- The nested reading is the flat one: some path to a child specification, at
any depth, has a solution of the matches on the way that projects `key`. -/
theorem Projection.names_iff_paths (g : Graph) (key : FactId) (p : Projection) (ms : List Match) (env : Env) :
    p.Names g key ms env ↔ ∃ x ∈ p.paths, ∃ σ ∈ evalMatches g env (ms ++ x.1), some key ∈ x.2.labels.map σ := by
  rw [Projection.Names]
  constructor
  · rintro ⟨σ, hσ, h | ⟨c, hc, hn⟩⟩
    · exact ⟨([], p), mem_paths.2 (.inl rfl), σ, by simpa using hσ, h⟩
    · obtain ⟨y, hy, τ, hτ, hk⟩ := (names_iff_paths g key c.2 c.1 σ).1 hn
      exact ⟨(c.1 ++ y.1, y.2), mem_paths.2 (.inr ⟨c, hc, y, hy, rfl⟩), τ, mem_evalMatches_append.2 ⟨σ, hσ, hτ⟩, hk⟩
  · rintro ⟨x, hx, τ, hτ, hk⟩
    rcases mem_paths.1 hx with rfl | ⟨c, hc, y, hy, rfl⟩
    · exact ⟨τ, by simpa using hτ, .inl hk⟩
    · obtain ⟨σ, hσ, hτ⟩ := mem_evalMatches_append.1 hτ
      exact ⟨σ, hσ, .inr ⟨c, hc, (names_iff_paths g key c.2 c.1 σ).2 ⟨y, hy, τ, hτ, hk⟩⟩⟩
termination_by sizeOf p
decreasing_by all_goals exact Projection.sizeOf_children hc

/-- A proof yields a fact exactly when the replica holds its givens and its
specification names the fact at some depth (RR-4, CR-1). -/
theorem yields_iff (p : Proof) (g : Graph) (key : FactId) :
    p.yields g key = true ↔ p.spec.given.all (g.has (p.spec.bindGivens p.givens)) = true ∧
      p.spec.projection.Names g key p.spec.matchList (p.spec.bindGivens p.givens) := by
  rw [Projection.names_iff_paths]
  simp [Proof.yields, Specification.descendants, Specification.read, Specification.evaluate]
  constructor
  · rintro ⟨a, b, hab, _, ⟨hg, σ, hσ, rfl⟩, hk⟩
    exact ⟨hg, a, b, hab, σ, hσ, by simpa using hk⟩
  · rintro ⟨hg, a, b, hab, σ, hσ, l, hl, hk⟩
    exact ⟨a, b, hab, _, ⟨hg, σ, hσ, rfl⟩, List.mem_map.2 ⟨l, hl, hk⟩⟩

/-! ## Yields, against the nested reading `Reads` -/

/-- The result names `key` at some depth: its row holds it, or a result of one
of its child specifications names it. -/
def Result.Names (key : FactId) : Result → Prop
  | .mk row cs => some key ∈ row ∨ ∃ rs, ∃ _ : rs ∈ cs, ∃ r, ∃ _ : r ∈ rs, r.Names key
termination_by r => sizeOf r
decreasing_by
  have h1 := List.sizeOf_lt_of_mem ‹rs ∈ cs›
  have h2 := List.sizeOf_lt_of_mem ‹r ∈ rs›
  simp only [Result.mk.sizeOf_spec]; omega

/-- A solution that names `key` reads a result naming it. -/
theorem Projection.names_resultsAt (g : Graph) (key : FactId) : ∀ (p : Projection) (σ : Env),
    (some key ∈ p.labels.map σ ∨ ∃ c, ∃ _ : c ∈ p.children, c.2.Names g key c.1 σ) →
      (p.resultsAt g σ).Names key
  | p, σ, h => by
    rw [Projection.resultsAt, Result.Names]
    rcases h with h | ⟨c, hc, hn⟩
    · exact .inl h
    · rw [Projection.Names] at hn
      obtain ⟨τ, hτ, hn⟩ := hn
      exact .inr ⟨_, List.mem_map_of_mem (List.mem_attach _ ⟨c, hc⟩), _, List.mem_map_of_mem hτ,
        names_resultsAt g key c.2 τ hn⟩
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children hc

/-- A result read from a solution names `key` only if the solution does. -/
theorem Projection.names_of_readsAt (g : Graph) (key : FactId) : ∀ (p : Projection) (σ : Env) (r : Result),
    p.ReadsAt g σ r → r.Names key →
      some key ∈ p.labels.map σ ∨ ∃ c, ∃ _ : c ∈ p.children, c.2.Names g key c.1 σ
  | p, σ, .mk row cs, hr, hn => by
    rw [readsAt_index] at hr; obtain ⟨rfl, hlen, hch⟩ := hr
    rw [Result.Names] at hn
    rcases hn with h | ⟨rs, hrs, r, hr, hn⟩
    · exact .inl h
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrs
      have hi' : i < p.children.length := hlen ▸ hi
      obtain ⟨τ, hτ, hra⟩ := (hch i hi' hi).1 r hr
      exact .inr ⟨_, List.getElem_mem hi', by
        rw [Projection.Names]; exact ⟨τ, hτ, names_of_readsAt g key _ τ r hra hn⟩⟩
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children (List.getElem_mem hi')

/-- The nested reading of `Names` is `Reads`: some result read names `key`. -/
theorem Projection.names_iff_reads (g : Graph) (key : FactId) (p : Projection) (ms : List Match) (env : Env) :
    p.Names g key ms env ↔ ∃ r, p.Reads g ms env r ∧ r.Names key := by
  rw [Projection.Names]
  exact ⟨fun ⟨σ, hσ, h⟩ => ⟨_, ⟨σ, hσ, readsAt_resultsAt g p σ⟩, names_resultsAt g key p σ h⟩,
    fun ⟨r, ⟨σ, hσ, hr⟩, hn⟩ => ⟨σ, hσ, names_of_readsAt g key p σ r hr hn⟩⟩

/-- **A proof yields a fact exactly when some result a replica reads names it**,
at any depth of child specifications (RR-4, CR-1). -/
theorem yields_iff_reads (p : Proof) (g : Graph) (key : FactId) :
    p.yields g key = true ↔ ∃ r, p.spec.Reads g (p.spec.bindGivens p.givens) r ∧ r.Names key := by
  rw [yields_iff, Projection.names_iff_reads]
  exact ⟨fun ⟨hg, r, hr, hn⟩ => ⟨r, ⟨hg, hr⟩, hn⟩, fun ⟨r, ⟨hg, hr⟩, hn⟩ => ⟨hg, r, hr, hn⟩⟩


end JinagaSpec
