import JinagaSpec.Maintain
import JinagaSpec.Proofs.Basic

/-!
# A re-checked result is the result, whatever order facts arrive in

`maintain_correct`: a held set re-checked on covering candidates after every
insertion equals `evaluate` on the graph so far. It needs nothing about the
specification or the facts: re-checking decides a candidate by reading the
specification, and a result that is not a candidate did not change.

`evaluate_congr`: two graphs holding the same facts give the same results, as
sets. A fact's id must name one fact, which content addressing gives; without
it, the two graphs could resolve an id to different facts. `evaluate_perm` is
the case where the two graphs are the same facts in a different order.
-/
namespace JinagaSpec

theorem recheck_correct {s : Specification} {env : Env} {g : Graph} {f : Fact}
    {candidates held : List Row}
    (hheld : ∀ r, r ∈ held ↔ r ∈ s.evaluate g env) (hcov : Covers s env g f candidates) (r : Row) :
    r ∈ recheck s env (g ++ [f]) candidates held ↔ r ∈ s.evaluate (g ++ [f]) env := by
  rcases hcov r with h | h <;> by_cases r ∈ candidates <;> simp_all [recheck]

/-- After any sequence of insertions, starting from a held set that equals the
result, the held set equals the result, provided each step's candidates cover
that step's change. -/
theorem maintain_correct (s : Specification) (env : Env) (candidates : Graph → Fact → List Row) :
    ∀ (fs : List Fact) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ s.evaluate g env) →
      (∀ pre f post, fs = pre ++ f :: post → Covers s env (g ++ pre) f (candidates (g ++ pre) f)) →
      ∀ r, r ∈ (fs.foldl (maintainStep s env candidates) (g, held)).2 ↔ r ∈ s.evaluate (g ++ fs) env
  | [], g, held, hheld, _ => by simpa using hheld
  | f :: fs, g, held, hheld, hcov => by
    have h := maintain_correct s env candidates fs (g ++ [f]) _
      (recheck_correct hheld (by simpa using hcov [] f fs rfl))
      (fun pre f' post h => by simpa using hcov (f :: pre) f' post (by simp [h]))
    simpa [maintainStep] using h

/-! ## Arrival order -/

theorem walk_congr {g g' : Graph} (hfactOf : g.factOf = g'.factOf) (start : FactId)
    (roles : List Role) : g.walk start roles = g'.walk start roles := by
  induction roles generalizing start with
  | nil => rfl
  | cons role roles ih => simp only [Graph.walk, Graph.step, hfactOf, ih]

mutual
  theorem evalMatches_congr {g g' : Graph} (hmem : ∀ x, x ∈ g ↔ x ∈ g')
      (hfactOf : g.factOf = g'.factOf) : ∀ (ms : List Match) (env e : Env),
      e ∈ evalMatches g env ms ↔ e ∈ evalMatches g' env ms
    | [], _, _ => by simp [evalMatches]
    | .mk u cs :: rest, env, e => by
      simp only [mem_evalMatches_cons, hmem, allHold_congr hmem hfactOf cs,
        evalMatches_congr hmem hfactOf rest]

  theorem allHold_congr {g g' : Graph} (hmem : ∀ x, x ∈ g ↔ x ∈ g')
      (hfactOf : g.factOf = g'.factOf) : ∀ (cs : List Condition) (env : Env) (u : Name),
      allHold g env u cs = allHold g' env u cs
    | [], _, _ => rfl
    | c :: cs, env, u => by
      simp only [allHold, holds_congr hmem hfactOf c, allHold_congr hmem hfactOf cs]

  theorem holds_congr {g g' : Graph} (hmem : ∀ x, x ∈ g ↔ x ∈ g')
      (hfactOf : g.factOf = g'.factOf) : ∀ (c : Condition) (env : Env) (u : Name),
      holds g env u c = holds g' env u c
    | .path c, env, u => by
      simp only [holds, PathCondition.holds, walk_congr hfactOf]
    | .existential e ms, env, u => by
      have : (evalMatches g env ms).isEmpty = (evalMatches g' env ms).isEmpty := by
        rw [Bool.eq_iff_iff]
        simp only [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem,
          evalMatches_congr hmem hfactOf ms env]
      simp only [holds, this]
end

/-- An id names at most one fact of the graph. -/
def Graph.IdsUnique (g : Graph) : Prop := ∀ a ∈ g, ∀ b ∈ g, a.id = b.id → a = b

/-- Two graphs holding the same facts, in any order and with any repetition,
give the same results. -/
theorem evaluate_congr {g g' : Graph} (hmem : ∀ x, x ∈ g ↔ x ∈ g') (huniq : g.IdsUnique)
    (s : Specification) (env : Env) (r : Row) :
    r ∈ s.evaluate g env ↔ r ∈ s.evaluate g' env := by
  have hfactOf : g.factOf = g'.factOf := by
    funext id
    simp only [Graph.factOf]
    cases h : g.find? (·.id == id) with
    | none =>
      exact (List.find?_eq_none.mpr fun x hx => List.find?_eq_none.mp h x ((hmem x).mpr hx)).symm
    | some a =>
      have ha := List.mem_of_find?_eq_some h
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
        (List.find?_isSome.mpr ⟨a, (hmem a).mp ha, List.find?_some h⟩)
      rw [hb, huniq b ((hmem b).mpr (List.mem_of_find?_eq_some hb)) a ha
        (by have := List.find?_some hb; have := List.find?_some h; simp_all)]
  simp only [Specification.evaluate, List.mem_map, evalMatches_congr hmem hfactOf]

/-- Two replicas holding the same facts agree, whatever order the facts arrived in. -/
theorem evaluate_perm {g g' : Graph} (hperm : g.Perm g') (huniq : g.IdsUnique)
    (s : Specification) (env : Env) (r : Row) :
    r ∈ s.evaluate g env ↔ r ∈ s.evaluate g' env :=
  evaluate_congr (fun _ => hperm.mem_iff) huniq s env r

end JinagaSpec
