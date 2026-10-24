import JinagaSpec.Proofs.Candidates
import JinagaSpec.Proofs.Reorder
import JinagaSpec.Proofs.Maintain

/-!
# The algorithm: complete candidates, and an exact stream

`candidates` (`Reorder.lean`) builds each inverse (`Candidates.lean`), reorders
it to start at each fact of a batch, and reads it on the graph that holds the
whole batch. Layer 3 says the inverses find every change (`inverses_complete`);
layer 4 says reordering keeps what each one finds (`reorderOrSelf_correct`). So
the candidates cover every change, and with `maintain_correct`, a stream that
re-checks them holds exactly the specification's results.

A replica saves a batch, then notifies each saved fact, reading on the graph
that holds them all (jinaga/jinaga-spec#11). That is `notify_correct`. It needs
no order within the batch: each fact need only be new to the graph before the
batch (`Fresh`), and may name any other fact of the batch.
-/
namespace JinagaSpec

variable {g : Graph} {B : List Fact}

/-- **`candidates_complete`.** For a well-formed specification and a fresh
batch, the candidates include every result the batch adds or removes. -/
theorem candidates_complete (s : Specification) (hwf : WellFormed s) (hf : Fresh g B) (env : Env) :
    Covers s env g B (candidates s env g B) := by
  intro r
  by_cases hgiv : ∃ f ∈ B, s.given.any (env ·.name == some f.id) = true
  · -- A fact of the batch is one of the givens: every result old and new is a candidate.
    obtain ⟨f, hfB, hg⟩ := hgiv
    have hall : ∀ r, r ∈ s.evaluate g env ++ s.evaluate (g ++ B) env → r ∈ candidates s env g B :=
      fun r h => List.mem_flatMap.mpr ⟨f, hfB, by simpa [factCandidates, hg] using h⟩
    by_cases h1 : r ∈ s.evaluate g env
    · exact Or.inr (hall r (List.mem_append_left _ h1))
    by_cases h2 : r ∈ s.evaluate (g ++ B) env
    · exact Or.inr (hall r (List.mem_append_right _ h2))
    exact Or.inl (iff_of_false h1 h2)
  simp only [not_exists, not_and] at hgiv
  rcases inverses_complete s hwf hf env hgiv r with h | ⟨f, hfB, ι, hι, hr⟩
  · exact Or.inl h
  · refine Or.inr (List.mem_flatMap.mpr ⟨f, hfB, ?_⟩)
    simp only [factCandidates, hgiv f hfB, Bool.false_eq_true, ite_false]
    exact List.mem_flatMap.mpr ⟨reorderOrSelf ι, List.mem_map.mpr ⟨ι, hι, rfl⟩,
      (reorderOrSelf_correct ι _ r).mpr hr⟩

/-- **Notifying each fact of a batch.** Start from a held set that equals the
result on `g`. Save a fresh batch `B`, then, for each of its facts, re-check
that fact's candidates, read on `g ++ B`: the held set is then exactly the
result on `g ++ B`. -/
theorem notify_correct (s : Specification) (hwf : WellFormed s) (hf : Fresh g B) (env : Env)
    (held : List Row) (hheld : ∀ r, r ∈ held ↔ r ∈ s.evaluate g env) (r : Row) :
    r ∈ B.foldl (fun held f => recheck s env (g ++ B) (factCandidates s env g (g ++ B) f) held) held ↔
      r ∈ s.evaluate (g ++ B) env := by
  rw [← List.foldl_map (g := fun held c => recheck s env (g ++ B) c held), recheck_each,
    ← List.flatMap_def]
  exact recheck_correct hheld (candidates_complete s hwf hf env) r

/-- **A stream is its specification's result.** Start from a read of the
result, and after each batch arrives re-check the candidates: the stream then
holds exactly the specification's results on the replica's graph, provided each
batch is fresh when it arrives. -/
theorem stream_correct (s : Specification) (hwf : WellFormed s) (env : Env) :
    ∀ (bs : List (List Fact)) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ s.evaluate g env) →
      (∀ pre B post, bs = pre ++ B :: post → Fresh (g ++ pre.flatten) B) →
      ∀ r, r ∈ (bs.foldl (maintainStep s env (candidates s env)) (g, held)).2 ↔
        r ∈ s.evaluate (g ++ bs.flatten) env :=
  fun bs g held hheld hfresh =>
    maintain_correct s env (candidates s env) bs g held hheld
      fun pre B post h => candidates_complete s hwf (hfresh pre B post h) env

end JinagaSpec
