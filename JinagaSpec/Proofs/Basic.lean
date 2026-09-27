import Std.Data.String.ToNat
import JinagaSpec.Proofs.Scoped

/-!
# Basic facts about evaluation and the split's helpers
-/
namespace JinagaSpec

/-- One match: some fact of the unknown's type satisfies the match's
conditions, and the rest of the matches have a solution from there. -/
theorem mem_evalMatches_cons {g : Graph} {env : Env} {u : Label} {cs : List Condition}
    {rest : List Match} {e2 : Env} :
    e2 ∈ evalMatches g env (.mk u cs :: rest) ↔
      ∃ f ∈ g, f.type = u.type ∧ allHold g (env.bind u.name f.id) u.name cs = true ∧
        e2 ∈ evalMatches g (env.bind u.name f.id) rest := by
  simp only [evalMatches, List.mem_flatMap, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨f, ⟨hf, ht⟩, h⟩
    by_cases hc : allHold g (env.bind u.name f.id) u.name cs = true
    · simp only [hc, ite_true] at h
      exact ⟨f, hf, ht, hc, h⟩
    · simp [hc] at h
  · rintro ⟨f, hf, ht, hc, h⟩
    exact ⟨f, ⟨hf, ht⟩, by simp only [hc, ite_true]; exact h⟩

theorem mem_evalMatches_append {g : Graph} {env : Env} {ms1 ms2 : List Match} {e2 : Env} :
    e2 ∈ evalMatches g env (ms1 ++ ms2) ↔
      ∃ e ∈ evalMatches g env ms1, e2 ∈ evalMatches g e ms2 := by
  induction ms1 generalizing env with
  | nil => simp [evalMatches]
  | cons m ms ih =>
    obtain ⟨u, cs⟩ := m
    rw [List.cons_append]
    simp only [mem_evalMatches_cons, ih]
    constructor
    · rintro ⟨f, hf, ht, hc, e, he, h⟩
      exact ⟨e, ⟨f, hf, ht, hc, he⟩, h⟩
    · rintro ⟨e, ⟨f, hf, ht, hc, he⟩, h⟩
      exact ⟨f, hf, ht, hc, e, he, h⟩

theorem allHold_append {g : Graph} {env : Env} {u : Name} {a b : List Condition} :
    allHold g env u (a ++ b) = (allHold g env u a && allHold g env u b) := by
  induction a with
  | nil => simp [allHold]
  | cons c cs ih => simp [allHold, ih, Bool.and_assoc]

/-- A match's conditions hold if and only if its path conditions and its
existential conditions each do. -/
theorem allHold_pathsOf_existentialsOf {g : Graph} {env : Env} {u : Name} {cs : List Condition} :
    allHold g env u cs =
      (allHold g env u ((pathsOf cs).map .path) && allHold g env u (existentialsOf cs)) := by
  induction cs with
  | nil => simp [allHold, pathsOf, existentialsOf]
  | cons c cs ih =>
    cases c with
    | path p =>
      simp [pathsOf, existentialsOf, allHold, ih, Bool.and_assoc] at *
    | existential e ms =>
      have h1 : pathsOf (.existential e ms :: cs) = pathsOf cs := by simp [pathsOf]
      have h2 : existentialsOf (.existential e ms :: cs) =
          .existential e ms :: existentialsOf cs := by simp [existentialsOf]
      rw [h1, h2]
      simp only [allHold]
      rw [ih]
      cases holds g env u (.existential e ms) <;>
        cases allHold g env u ((pathsOf cs).map .path) <;>
        cases allHold g env u (existentialsOf cs) <;> rfl

/-- Only the labels a match list declares change. -/
theorem evalMatches_frame {g : Graph} {ms : List Match} :
    ∀ {env e' : Env}, e' ∈ evalMatches g env ms →
      ∀ x, x ∉ ms.map (·.unknown.name) → e' x = env x := by
  induction ms with
  | nil =>
    intro env e' h x _
    simp [evalMatches] at h
    subst h
    rfl
  | cons m ms ih =>
    obtain ⟨u, cs⟩ := m
    intro env e' h x hx
    obtain ⟨f, _, _, _, h'⟩ := mem_evalMatches_cons.mp h
    have hxu : x ≠ u.name := fun heq => hx (by simp [heq])
    have hxms : x ∉ ms.map (·.unknown.name) := fun hmem => hx (by simp [hmem])
    rw [ih h' x hxms]
    simp [Env.bind, hxu]

/-! ## Fresh labels -/

private theorem sName_injective {m n : Nat} (h : s!"s{m}" = s!"s{n}") : m = n := by
  simp only [toString] at h
  exact Nat.repr_injective ((String.append_right_inj "s").mp h)

/-- If `s1` ... `s(n-1)` are taken, and fewer than `n + fuel` names are, then the
search does not return a taken name. When the fuel runs out, the name is
returned unchecked: it is free because a taken `sn` would make `n` distinct
taken names. -/
private theorem freshFrom_not_mem (taken : List Name) :
    ∀ (fuel n : Nat), 1 ≤ n → (∀ j, 1 ≤ j → j < n → s!"s{j}" ∈ taken) →
      taken.length ≤ fuel + (n - 1) → freshFrom taken fuel n ∉ taken := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn hprev hlen hmem
    simp only [freshFrom] at hmem
    have hall : ∀ x ∈ (List.range' 1 n).map (fun j => s!"s{j}"), x ∈ taken := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range'_1] at hj
      by_cases hjn : j = n
      · subst hjn; exact hmem
      · exact hprev j (by omega) (by omega)
    have hnodup : ((List.range' 1 n).map (fun j => s!"s{j}")).Nodup := by
      have h0 : (List.range' 1 n).Nodup := List.nodup_range'
      exact List.Pairwise.map (fun j => s!"s{j}") (fun a b hab h => hab (sName_injective h)) h0
    have := hnodup.length_le_of_subset hall
    simp at this
    omega
  | succ fuel ih =>
    intro n hn hprev hlen
    simp only [freshFrom]
    by_cases hc : taken.contains s!"s{n}" = true
    · simp only [hc, ite_true]
      apply ih (n + 1) (by omega)
      · intro j hj1 hjn
        by_cases hjeq : j = n
        · subst hjeq; exact List.contains_iff_mem.mp hc
        · exact hprev j hj1 (by omega)
      · omega
    · simp only [hc]
      simpa using hc

/-- The candidate for a split label is not one the specification declares. -/
theorem freshLabel_not_mem (taken : List Name) : freshLabel taken ∉ taken := by
  unfold freshLabel
  apply freshFrom_not_mem taken taken.length 1 (by omega)
  · intro j h1 h2; omega
  · omega

end JinagaSpec
