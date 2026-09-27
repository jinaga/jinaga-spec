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
  theorem isScopedMatches_iff :
      ∀ (scope : List Name) (ms : List Match), isScopedMatches scope ms = true ↔ ScopedMatches scope ms
    | _, [] => by simp [isScopedMatches, ScopedMatches]
    | scope, .mk u cs :: rest => by
      simp only [isScopedMatches, ScopedMatches, Bool.and_eq_true]
      rw [isScopedConditions_iff, isScopedMatches_iff]

  theorem isScopedConditions_iff :
      ∀ (inner outer : List Name) (cs : List Condition),
        isScopedConditions inner outer cs = true ↔ ScopedConditions inner outer cs
    | _, _, [] => by simp [isScopedConditions, ScopedConditions]
    | inner, outer, c :: cs => by
      simp only [isScopedConditions, ScopedConditions, Bool.and_eq_true]
      rw [isScopedCondition_iff, isScopedConditions_iff]

  theorem isScopedCondition_iff :
      ∀ (inner outer : List Name) (c : Condition),
        isScopedCondition inner outer c = true ↔ ScopedCondition inner outer c
    | _, outer, .path c => by simp [isScopedCondition, ScopedCondition]
    | inner, _, .existential _ ms => by
      simp only [isScopedCondition, ScopedCondition]
      exact isScopedMatches_iff inner ms
end

mutual
  theorem isUnshadowedMatches_iff :
      ∀ (scope : List Name) (ms : List Match),
        isUnshadowedMatches scope ms = true ↔ UnshadowedMatches scope ms
    | _, [] => by simp [isUnshadowedMatches, UnshadowedMatches]
    | scope, .mk u cs :: rest => by
      simp only [isUnshadowedMatches, UnshadowedMatches, Bool.and_eq_true, Bool.not_eq_true']
      rw [isUnshadowedConditions_iff, isUnshadowedMatches_iff]
      have h : scope.contains u.name = false ↔ u.name ∉ scope := by
        simp [Bool.eq_false_iff]
      rw [h, and_assoc]

  theorem isUnshadowedConditions_iff :
      ∀ (inner : List Name) (cs : List Condition),
        isUnshadowedConditions inner cs = true ↔ UnshadowedConditions inner cs
    | _, [] => by simp [isUnshadowedConditions, UnshadowedConditions]
    | inner, c :: cs => by
      simp only [isUnshadowedConditions, UnshadowedConditions, Bool.and_eq_true]
      rw [isUnshadowedCondition_iff, isUnshadowedConditions_iff]

  theorem isUnshadowedCondition_iff :
      ∀ (inner : List Name) (c : Condition),
        isUnshadowedCondition inner c = true ↔ UnshadowedCondition inner c
    | _, .path _ => by simp [isUnshadowedCondition, UnshadowedCondition]
    | inner, .existential _ ms => by
      simp only [isUnshadowedCondition, UnshadowedCondition]
      exact isUnshadowedMatches_iff inner ms
end

theorem isProjected_iff (s : Specification) :
    isProjected s = true ↔
      ∀ x ∈ s.projection.labels, x ∈ s.given.map (·.name) ∨ x ∈ s.matchList.map (·.unknown.name) := by
  simp [isProjected, List.all_eq_true]

/-- The check decides `WellFormed`. -/
theorem isWellFormed_iff (s : Specification) : isWellFormed s = true ↔ WellFormed s := by
  simp only [isWellFormed, isScoped, isUnshadowed, Bool.and_eq_true, isScopedMatches_iff,
    isUnshadowedMatches_iff, isProjected_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

/-- A specification that passes the check is split correctly. -/
theorem split_correct_of_check (s : Specification) (hcheck : isWellFormed s = true)
    (g : Graph) (env : Env) (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluate g env ↔ r ∈ s.evaluate g env :=
  split_correct s ((isWellFormed_iff s).mp hcheck) g env r

end JinagaSpec
