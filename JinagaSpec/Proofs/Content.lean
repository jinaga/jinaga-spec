import JinagaSpec.Content

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
* `read_noninterference` (SEC-5): to a user the rules do not admit, the answer
  does not depend on which objects are stored.

`CheckContent.lean` tests each statement as written against mutants of the
handlers, one per way of breaking it.
-/
namespace JinagaSpec

theorem Graph.factOf_append {g : Graph} (h : g.factOf k = some f) (g' : Graph) :
    (g ++ g').factOf k = some f := by
  simp [Graph.factOf, List.find?_append] at h ⊢; simp [h]

theorem List.mem_of_lookup_eq_some {l : List (FactId × Bytes)} (h : l.lookup k = some o) :
    (k, o) ∈ l := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.lookup] at h
    split at h <;> simp_all [Prod.ext_iff]

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
    cases hf : r.store.factOf key with
    | none => simp only [hf] at h; exact .inl h
    | some f =>
      cases hc : P.contentHash f with
      | none => simp only [hf, hc] at h; exact .inl h
      | some hsh =>
        simp only [hf, hc] at h
        split at h; · exact .inl h
        split at h; · exact .inl h
        split at h; · exact .inl h
        split at h; · exact .inl h
        rcases List.mem_cons.1 h with h | h
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact .inr ⟨u, f, rfl, hf, by simp_all, by simp_all⟩
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
  obtain ⟨pre, post, _, f, rfl, hf, _, hh⟩ := stored_authorized (List.mem_of_lookup_eq_some hl)
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

end JinagaSpec
