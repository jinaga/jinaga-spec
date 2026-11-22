import JinagaSpec.Content
import JinagaSpec.Proofs.Basic
import JinagaSpec.Proofs.Children

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

`yields_iff` says what `Proof.yields` means: a solution of the matches,
then of a child specification's matches from it, and so on down, names the
fact (`Projection.Names`), which is what RR-4 and CR-1 ask.

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
    | save f => exact ⟨f :: g, by simp [step]⟩
    | write u k o => exact ⟨g, by simp [step, write_store]⟩

/-- An object in the state after an event was there before, or that event is
the accepted upload of exactly those bytes for that key. -/
theorem Replicator.mem_step {P : Policy} {r : Replicator} {e : Event}
    (h : (k, o) ∈ (r.step P e).objects) :
    (k, o) ∈ r.objects ∨ ∃ u f, e = .write (some u) k o ∧ r.store.factOf k = some f ∧
      P.mayCreate u r.store f = true ∧ P.contentHash f = some (P.hash o) := by
  cases e with
  | save f => exact .inl h
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

/-- A read that returns an object returns the one stored under its key, to a
user the rules admit. -/
theorem Replicator.read_ok {P : Policy} {r : Replicator} (h : r.read P user key p = .ok o) :
    ∃ u, user = some u ∧ P.admits r.store u key p = true ∧ r.objects.lookup key = some o := by
  unfold read at h
  repeat' split at h
  all_goals simp_all

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
  | some u => simp [Replicator.read, hu u rfl]

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
  simp only [Replicator.read, hb, ha]; cases r.objects.lookup key <;> rfl

/-- An authorized writer's upload of matching bytes within the constraints is
stored, unless the key already holds an object (RW-8). -/
theorem write_accepted {P : Policy} {r : Replicator} (hf : r.store.factOf key = some f)
    (hm : P.mayCreate u r.store f = true) (hh : P.contentHash f = some (P.hash o))
    (hfit : P.fits f o = true) :
    r.write P (some u) key o = match r.objects.lookup key with
      | some _ => (r, .alreadyStored)
      | none => ({ r with objects := (key, o) :: r.objects }, .stored) := by
  simp [Replicator.write, hf, hm, hh, hfit]; cases r.objects.lookup key <;> rfl

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
end JinagaSpec
