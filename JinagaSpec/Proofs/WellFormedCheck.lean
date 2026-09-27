import JinagaSpec.WellFormed
import JinagaSpec.Proofs.Main

/-!
# The check decides `WellFormed`

`isWellFormed` returns `true` exactly when `WellFormed` holds. So it is safe to
run at a boundary in place of the theorem's hypothesis, and it rejects nothing
the theorem covers.
-/
namespace JinagaSpec

mutual
  theorem isWellFormedMatches_iff :
      ∀ (scope : List Name) (ms : List Match),
        isWellFormedMatches scope ms = true ↔ ScopedMatches scope ms ∧ WellNamedMatches scope ms
    | _, [] => by simp [isWellFormedMatches, ScopedMatches, WellNamedMatches]
    | scope, .mk u cs :: rest => by
      simp only [isWellFormedMatches, ScopedMatches, WellNamedMatches, Bool.and_eq_true,
        Bool.not_eq_true']
      rw [isWellFormedConditions_iff, isWellFormedMatches_iff]
      have h : scope.contains u.name = false ↔ u.name ∉ scope := by
        simp [Bool.eq_false_iff]
      rw [h]
      grind

  theorem isWellFormedConditions_iff :
      ∀ (inner outer : List Name) (cs : List Condition),
        isWellFormedConditions inner outer cs = true ↔
          ScopedConditions inner outer cs ∧ WellNamedConditions inner cs
    | _, _, [] => by simp [isWellFormedConditions, ScopedConditions, WellNamedConditions]
    | inner, outer, c :: cs => by
      simp only [isWellFormedConditions, ScopedConditions, WellNamedConditions, Bool.and_eq_true]
      rw [isWellFormedCondition_iff, isWellFormedConditions_iff]
      grind

  theorem isWellFormedCondition_iff :
      ∀ (inner outer : List Name) (c : Condition),
        isWellFormedCondition inner outer c = true ↔
          ScopedCondition inner outer c ∧ WellNamedCondition inner c
    | _, outer, .path c => by simp [isWellFormedCondition, ScopedCondition, WellNamedCondition]
    | inner, _, .existential _ ms => by
      simp only [isWellFormedCondition, ScopedCondition, WellNamedCondition]
      exact isWellFormedMatches_iff inner ms
end

/-- The check decides `WellFormed`. -/
theorem isWellFormed_iff (s : Specification) : isWellFormed s = true ↔ WellFormed s := by
  simp only [isWellFormed, Bool.and_eq_true, isWellFormedMatches_iff, List.all_eq_true,
    List.contains_iff_mem, Bool.not_eq_true', Bool.or_eq_true]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨fun g hg => h1 g.name (List.mem_map_of_mem hg), h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨fun x hx => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      exact h1 g hg, h2, h3⟩, h4⟩

/-- A specification that passes the check is split correctly. -/
theorem split_correct_of_check (s : Specification) (hcheck : isWellFormed s = true)
    (g : Graph) (env : Env) (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluate g env ↔ r ∈ s.evaluate g env :=
  split_correct s ((isWellFormed_iff s).mp hcheck) g env r

end JinagaSpec
