import JinagaSpec.Proofs.Basic

/-!
# Locality

Evaluating matches depends only on the labels they use. Two environments that
agree on the labels a list of matches uses from outside give solutions that
agree on those labels and on the labels the matches declare.

This is why the tail may be run from the few facts it is given, rather than
from the whole environment of the head.
-/
namespace JinagaSpec

mutual
  theorem evalMatches_agree (g : Graph) :
      ∀ (ms : List Match) (S : List Name) (env env2 : Env),
        ScopedMatches S ms → Agree S env env2 →
        ∀ e ∈ evalMatches g env ms,
          ∃ e2 ∈ evalMatches g env2 ms, Agree (S ++ ms.map (·.unknown.name)) e e2
    | [], S, env, env2, _, hag, e, he => by
      have : e = env := by simpa [evalMatches] using he
      subst this
      exact ⟨env2, by simp [evalMatches], by simpa using hag⟩
    | .mk u cs :: rest, S, env, env2, hsc, hag, e, he => by
      obtain ⟨f, hf, ht, hc, hrest⟩ := mem_evalMatches_cons.mp he
      have hsc' : ScopedConditions (u.name :: S) S cs ∧ ScopedMatches (u.name :: S) rest := hsc
      have hag' := hag.bind u.name f.id
      have hc2 : allHold g (env2.bind u.name f.id) u.name cs = true := by
        rw [← allHold_agree g cs u.name S _ _ hsc'.1 (hag.bind u.name f.id)]
        exact hc
      obtain ⟨e2, he2, hae⟩ :=
        evalMatches_agree g rest (u.name :: S) _ _ hsc'.2 hag' e hrest
      refine ⟨e2, mem_evalMatches_cons.mpr ⟨f, hf, ht, hc2, he2⟩, ?_⟩
      refine hae.mono ?_
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.map_cons, Match.unknown_mk] at hx ⊢
      rcases hx with hx | hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx

  theorem allHold_agree (g : Graph) :
      ∀ (cs : List Condition) (u : Name) (outer : List Name) (env env2 : Env),
        ScopedConditions (u :: outer) outer cs → Agree (u :: outer) env env2 →
        allHold g env u cs = allHold g env2 u cs
    | [], u, outer, env, env2, _, _ => by simp [allHold]
    | c :: cs, u, outer, env, env2, hsc, hag => by
      have hsc' : ScopedCondition (u :: outer) outer c ∧ ScopedConditions (u :: outer) outer cs := hsc
      simp only [allHold]
      rw [holds_agree g c u outer env env2 hsc'.1 hag,
        allHold_agree g cs u outer env env2 hsc'.2 hag]

  theorem holds_agree (g : Graph) :
      ∀ (c : Condition) (u : Name) (outer : List Name) (env env2 : Env),
        ScopedCondition (u :: outer) outer c → Agree (u :: outer) env env2 →
        holds g env u c = holds g env2 u c
    | .path c, u, outer, env, env2, hsc, hag => by
      have hr : c.labelRight ∈ outer := hsc
      have h1 : env u = env2 u := hag u (by simp)
      have h2 : env c.labelRight = env2 c.labelRight := hag _ (List.mem_cons_of_mem _ hr)
      simp only [holds, PathCondition.holds, h1, h2]
    | .existential e ms, u, outer, env, env2, hsc, hag => by
      have hsc' : ScopedMatches (u :: outer) ms := hsc
      have key : (evalMatches g env ms).isEmpty = (evalMatches g env2 ms).isEmpty := by
        cases h1 : (evalMatches g env ms) with
        | nil =>
          cases h2 : (evalMatches g env2 ms) with
          | nil => rfl
          | cons e2 l2 =>
            obtain ⟨e1, he1, _⟩ := evalMatches_agree g ms (u :: outer) env2 env hsc' hag.symm e2
              (by rw [h2]; simp)
            rw [h1] at he1
            simp at he1
        | cons e1 l1 =>
          obtain ⟨e2, he2, _⟩ := evalMatches_agree g ms (u :: outer) env env2 hsc' hag e1
            (by rw [h1]; simp)
          cases h2 : (evalMatches g env2 ms) with
          | nil => rw [h2] at he2; simp at he2
          | cons => rfl
      simp only [holds, key]
end

end JinagaSpec
