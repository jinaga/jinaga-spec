import JinagaSpec.Proofs.Locality

/-!
# Two environments agreeing on a scope give the same projected results

Used by the split's own correctness proof (`Proofs/Hoist.lean`) to swap the
environment a tail runs from for one that only agrees with it on the scope
the tail's matches are scoped in.
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

end JinagaSpec
