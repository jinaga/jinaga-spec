import JinagaSpec.Proofs.Candidates
import JinagaSpec.Proofs.Reorder
import JinagaSpec.Proofs.Maintain

/-!
# The algorithm: complete candidates, and an exact stream

`candidates` (`Reorder.lean`) builds each inverse (`Candidates.lean`), reorders
it to start at the new fact, and reads it on the new graph. Layer 3 says the
inverses find every change (`inverses_complete`); layer 4 says reordering
keeps what each one finds (`reorderOrSelf_correct`). So the candidates cover
every change, and with `maintain_correct`, a stream that re-checks them holds
exactly the specification's results.
-/
namespace JinagaSpec

variable {g : Graph} {f : Fact}

/-- **`candidates_complete`.** For a well-formed specification and a fresh fact,
the candidates include every result the fact adds or removes. -/
theorem candidates_complete (s : Specification) (hwf : WellFormed s) (hf : Fresh g f) (env : Env) :
    Covers s env g f (candidates s env g f) := by
  intro r
  unfold candidates
  split
  · -- `f` is one of the givens: every result old and new is a candidate.
    by_cases h1 : r ∈ s.evaluate g env <;> by_cases h2 : r ∈ s.evaluate (g ++ [f]) env <;> simp_all
  rename_i hgiv
  rcases inverses_complete s hwf hf env hgiv r with h | ⟨ι, hι, hr⟩
  · exact Or.inl h
  · exact Or.inr (List.mem_flatMap.mpr ⟨reorderOrSelf ι, List.mem_map.mpr ⟨ι, hι, rfl⟩,
      (reorderOrSelf_correct ι _ r).mpr hr⟩)

/-- **A stream is its specification's result.** Start from a read of the
result, and after each fact arrives re-check the candidates: the stream then
holds exactly the specification's results on the replica's graph, provided
each fact is fresh when it arrives. -/
theorem stream_correct (s : Specification) (hwf : WellFormed s) (env : Env) :
    ∀ (fs : List Fact) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ s.evaluate g env) →
      (∀ pre f post, fs = pre ++ f :: post → Fresh (g ++ pre) f) →
      ∀ r, r ∈ (fs.foldl (maintainStep s env (candidates s env)) (g, held)).2 ↔ r ∈ s.evaluate (g ++ fs) env :=
  fun fs g held hheld hfresh =>
    maintain_correct s env (candidates s env) fs g held hheld
      fun pre f post h => candidates_complete s hwf (hfresh pre f post h) env

end JinagaSpec
