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

/-- Functions that agree on a list's members give the same `flatMap`. -/
theorem flatMap_congr {l : List α} {g h : α → List β} (he : ∀ x ∈ l, g x = h x) :
    l.flatMap g = l.flatMap h := by
  simp only [List.flatMap_def]
  congr 1
  exact List.map_congr_left he

end JinagaSpec
