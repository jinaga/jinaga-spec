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

/-- No fact of `g` has the id of a fact of a fresh batch. -/
theorem factOf_eq_none_of_fresh (hf : Fresh g B) {b : Fact} (hb : b ∈ B) : g.factOf b.id = none :=
  List.find?_eq_none.mpr fun x hx => by simpa using hf.idNew x hx b hb

/-- A label bound outside the batch is stored after it exactly when it was before. -/
theorem has_append_outside {env : Env} {l : Label} (h : ∀ b ∈ B, env l.name ≠ some b.id) :
    (g ++ B).has env l = g.has env l := by
  unfold Graph.has
  split
  · rename_i id hid
    rw [factOf_append_outside fun b hb heq => h b hb (hid.trans (congrArg some heq))]
  · rfl

/-- A given that arrives in a fresh batch was not stored, so nothing was read
before it. -/
theorem read_given_arrives {s : Specification} (hf : Fresh g B) {env : Env} {f : Fact} (hfB : f ∈ B)
    (hg : s.given.any (env ·.name == some f.id) = true) : s.read g env = [] := by
  obtain ⟨l, hl, he⟩ := List.any_eq_true.mp hg
  simp only [Specification.read, ite_eq_right_iff, List.all_eq_true]
  exact fun h => absurd (h l hl) (by simp [Graph.has, beq_iff_eq.mp he, factOf_eq_none_of_fresh hf hfB])

/-- When no given arrives, each is stored after the batch exactly when it was before. -/
theorem givens_stored_append {s : Specification} {env : Env}
    (hgiv : ∀ f ∈ B, ¬ (s.given.any (env ·.name == some f.id)) = true) :
    s.given.all ((g ++ B).has env) = s.given.all (g.has env) := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact forall₂_congr fun l hl => by
    rw [has_append_outside fun b hb heq => hgiv b hb (List.any_eq_true.mpr ⟨l, hl, by simp [heq]⟩)]

/-- **`candidates_complete`.** For a well-formed specification and a fresh
batch, the candidates include every result the batch adds or removes, as a
replica reads them. -/
theorem candidates_complete (s : Specification) (hwf : WellFormed s) (hf : Fresh g B) (env : Env) :
    Covers (s.read · env) g B (candidates s env g B) := by
  intro r
  by_cases hgiv : ∃ f ∈ B, s.given.any (env ·.name == some f.id) = true
  · -- A given arrives in the batch: every result read now is a candidate.
    obtain ⟨f, hfB, hg⟩ := hgiv
    by_cases h2 : r ∈ s.read (g ++ B) env
    · exact Or.inr (List.mem_flatMap.mpr ⟨f, hfB, by simpa [factCandidates, hg] using h2⟩)
    · exact Or.inl (by simp [read_given_arrives hf hfB hg, h2])
  simp only [not_exists, not_and] at hgiv
  have hhas := givens_stored_append (g := g) hgiv
  by_cases hpres : s.given.all (g.has env) = true
  · have hfound : ∀ f ∈ B, ∀ ι ∈ inverses s, r ∈ ι.evaluate (g ++ B) (pinEnv s env f) →
        r ∈ candidates s env g B := fun f hfB ι hι hr => by
      refine List.mem_flatMap.mpr ⟨f, hfB, ?_⟩
      simp only [factCandidates, hgiv f hfB, Bool.false_eq_true, ite_false]
      exact List.mem_flatMap.mpr ⟨reorderOrSelf ι, List.mem_map.mpr ⟨ι, hι, rfl⟩,
        (reorderOrSelf_correct ι _ r).mpr hr⟩
    have h := inverses_complete s hwf hf env hgiv r
    simp only [Specification.read, hhas, hpres, ite_true]
    by_cases h1 : r ∈ s.evaluate g env <;> by_cases h2 : r ∈ s.evaluate (g ++ B) env
    · exact Or.inl (iff_of_true h1 h2)
    · obtain ⟨f, hfB, ι, hι, hr⟩ := h.2 h1 h2
      exact Or.inr (hfound f hfB ι (List.mem_append_right _ hι) hr)
    · obtain ⟨f, hfB, ι, hι, hr⟩ := h.1 h1 h2
      exact Or.inr (hfound f hfB ι (List.mem_append_left _ hι) hr)
    · exact Or.inl (iff_of_false h1 h2)
  · exact Or.inl (by simp [Specification.read, hhas, hpres])

/-- **Notifying each fact of a batch.** Start from a held set that equals the
result on `g`. Save a fresh batch `B`, then, for each of its facts, re-check
that fact's candidates, read on `g ++ B`: the held set is then exactly the
result on `g ++ B`. -/
theorem notify_correct (s : Specification) (hwf : WellFormed s) (hf : Fresh g B) (env : Env)
    (held : List Row) (hheld : ∀ r, r ∈ held ↔ r ∈ s.read g env) (r : Row) :
    r ∈ B.foldl (fun held f => recheck (s.read · env) (g ++ B) (factCandidates s env (g ++ B) f) held) held ↔
      r ∈ s.read (g ++ B) env := by
  rw [← List.foldl_map (g := fun held c => recheck (s.read · env) (g ++ B) c held), recheck_each,
    ← List.flatMap_def]
  exact recheck_correct hheld (candidates_complete s hwf hf env) r

/-- **A stream is its specification's result.** Start from a read of the
result, and after each batch arrives re-check the candidates: the stream then
holds exactly the specification's results on the replica's graph, provided each
batch is fresh when it arrives. -/
theorem stream_correct (s : Specification) (hwf : WellFormed s) (env : Env) :
    ∀ (bs : List (List Fact)) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ s.read g env) →
      (∀ pre B post, bs = pre ++ B :: post → Fresh (g ++ pre.flatten) B) →
      ∀ r, r ∈ (bs.foldl (maintainStep (s.read · env) (candidates s env)) (g, held)).2 ↔
        r ∈ s.read (g ++ bs.flatten) env :=
  fun bs g held hheld hfresh =>
    maintain_correct (s.read · env) (candidates s env) bs g held hheld
      fun pre B post h => candidates_complete s hwf (hfresh pre B post h) env

end JinagaSpec
