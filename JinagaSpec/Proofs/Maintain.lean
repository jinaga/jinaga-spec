import JinagaSpec.Maintain
import JinagaSpec.Proofs.Basic

/-!
# A re-checked result is the result, whatever order facts arrive in

`maintain_correct`: a held set re-checked on covering candidates after every
batch equals the result on the graph so far. It needs nothing about the
result or the facts: re-checking decides a candidate by reading the result,
and a result that is not a candidate did not change.

`recheck_each`: re-checking several lists of candidates in turn, on one graph,
is re-checking all of them at once. A replica that notifies each fact of a
batch separately, in any order, re-checks the batch.

`evaluate_congr`: two graphs holding the same facts give the same results, as
sets. A fact's id must name one fact, which content addressing gives; without
it, the two graphs could resolve an id to different facts. `evaluate_perm` is
the case where the two graphs are the same facts in a different order.
-/
namespace JinagaSpec

theorem mem_recheck {result : Graph → List Row} {g : Graph} {candidates held : List Row} {r : Row} :
    r ∈ recheck result g candidates held ↔
      (r ∈ held ∧ r ∉ candidates) ∨ (r ∈ candidates ∧ r ∈ result g) := by
  simp [recheck]

theorem recheck_correct {result : Graph → List Row} {g : Graph} {B : List Fact}
    {candidates held : List Row}
    (hheld : ∀ r, r ∈ held ↔ r ∈ result g) (hcov : Covers result g B candidates) (r : Row) :
    r ∈ recheck result (g ++ B) candidates held ↔ r ∈ result (g ++ B) := by
  rcases hcov r with h | h <;> by_cases r ∈ candidates <;> simp_all [mem_recheck]

/-- Re-checking each list of candidates in turn, on one graph, holds what one
re-check of all of them holds. -/
theorem recheck_each (result : Graph → List Row) (g : Graph) :
    ∀ (cs : List (List Row)) (held : List Row) (r : Row),
      r ∈ cs.foldl (fun held c => recheck result g c held) held ↔ r ∈ recheck result g cs.flatten held
  | [], held, r => by simp [recheck]
  | c :: cs, held, r => by
    rw [List.foldl_cons, recheck_each result g cs]
    simp only [mem_recheck, List.flatten_cons, List.mem_append]
    grind

/-- After any sequence of batches, starting from a held set that equals the
result, the held set equals the result, provided each step's update takes a
held set that equals the result before the batch to one that equals it after. -/
theorem advance_correct (result : Graph → List Row) (update : Graph → List Fact → List Row → List Row) :
    ∀ (bs : List (List Fact)) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ result g) →
      (∀ pre B post, bs = pre ++ B :: post → ∀ held, (∀ r, r ∈ held ↔ r ∈ result (g ++ pre.flatten)) →
        ∀ r, r ∈ update (g ++ pre.flatten) B held ↔ r ∈ result (g ++ pre.flatten ++ B)) →
      ∀ r, r ∈ (bs.foldl (advance update) (g, held)).2 ↔ r ∈ result (g ++ bs.flatten)
  | [], g, held, hheld, _ => by simpa using hheld
  | B :: bs, g, held, hheld, hstep => by
    have h := advance_correct result update bs (g ++ B) _
      (by simpa using hstep [] B bs rfl held (by simpa using hheld))
      (fun pre B' post h held' hheld' => by
        simpa using hstep (B :: pre) B' post (by simp [h]) held' (by simpa using hheld'))
    simpa [advance] using h

/-- After any sequence of batches, starting from a held set that equals the
result, the held set equals the result, provided each step's candidates cover
that step's change. -/
theorem maintain_correct (result : Graph → List Row) (candidates : Graph → List Fact → List Row) :
    ∀ (bs : List (List Fact)) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ result g) →
      (∀ pre B post, bs = pre ++ B :: post →
        Covers result (g ++ pre.flatten) B (candidates (g ++ pre.flatten) B)) →
      ∀ r, r ∈ (bs.foldl (maintainStep result candidates) (g, held)).2 ↔ r ∈ result (g ++ bs.flatten) :=
  fun bs g held hheld hcov => advance_correct result _ bs g held hheld
    fun pre B post h _ hheld => recheck_correct hheld (hcov pre B post h)

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
