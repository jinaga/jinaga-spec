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

/-! ## Split labels -/

theorem splitLabel_injective {i j : Nat} (h : splitLabel i = splitLabel j) : i = j := by
  simp only [splitLabel, toString] at h
  exact Nat.repr_injective ((String.append_right_inj "__s").mp h)

/-- A split label is reserved, so it is not a label the specification declares. -/
theorem isReserved_splitLabel (i : Nat) : isReserved (splitLabel i) = true := by
  simp only [isReserved, splitLabel, toString]
  simp

/-! ## Small shared facts

Used by more than one proof file, so stated once here instead of once per
file. -/

/-- The two halves of `span` make up the list. -/
theorem span_loop_append (p : Match → Bool) :
    ∀ (l acc : List Match), (List.span.loop p l acc).1 ++ (List.span.loop p l acc).2 = acc.reverse ++ l := by
  intro l
  induction l with
  | nil => intro acc; simp [List.span.loop]
  | cons a as ih =>
    intro acc
    simp only [List.span.loop]
    cases p a <;> simp [ih]

/-- The labels a list of matches binds. -/
def names (ms : List Match) : List Name := ms.map (·.unknown.name)

theorem Graph.mem_of_factOf_eq_some {g : Graph} {id : FactId} {fact : Fact}
    (h : g.factOf id = some fact) : fact ∈ g := by
  unfold Graph.factOf at h
  exact List.mem_of_find?_eq_some h

mutual
  theorem Condition.eq_of_beq : ∀ {a b : Condition}, Condition.beq a b = true → a = b
    | .path _, .path _, h => by simp [Condition.beq] at h; rw [h]
    | .existential _ _, .existential _ _, h => by
      simp only [Condition.beq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, Match.eq_of_beqList h.2]
    | .path _, .existential _ _, h | .existential _ _, .path _, h => by simp [Condition.beq] at h

  theorem Match.eq_of_beqList : ∀ {a b : List Match}, Match.beqList a b = true → a = b
    | [], [], _ => rfl
    | .mk _ _ :: _, .mk _ _ :: _, h => by
      simp only [Match.beqList, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, Condition.eq_of_beqList h.1.2, Match.eq_of_beqList h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp [Match.beqList] at h

  theorem Condition.eq_of_beqList : ∀ {a b : List Condition}, Condition.beqList a b = true → a = b
    | [], [], _ => rfl
    | _ :: _, _ :: _, h => by
      simp only [Condition.beqList, Bool.and_eq_true] at h
      rw [Condition.eq_of_beq h.1, Condition.eq_of_beqList h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp [Condition.beqList] at h
end

/-- `==` on conditions is equality. -/
theorem Condition.eq_of_beq' {a b : Condition} (h : (a == b) = true) : a = b := Condition.eq_of_beq h

/-- `exists ms` holds exactly when `ms` has a solution. -/
theorem holds_exists {G : Graph} {env : Env} {u : Name} {ms : List Match} :
    holds G env u (.existential true ms) = true ↔ ∃ σ, σ ∈ evalMatches G env ms := by
  simp only [holds]
  cases h : evalMatches G env ms <;> simp

/-- Functions that agree on a list's members give the same `flatMap`. -/
theorem flatMap_congr {l : List α} {g h : α → List β} (he : ∀ x ∈ l, g x = h x) :
    l.flatMap g = l.flatMap h := by
  simp only [List.flatMap_def]
  congr 1
  exact List.map_congr_left he

end JinagaSpec
