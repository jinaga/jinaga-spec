import JinagaSpec.Proofs.Feeds

/-!
# Renaming ids

A specification compares fact ids only for equality, so renaming the ids of a
graph by an injective map renames its solutions and a feed's tuples, and
changes nothing else (`tuples_rename`).
-/
namespace JinagaSpec

variable (ρ : FactId → FactId)

def Fact.rename (f : Fact) : Fact := ⟨ρ f.id, f.type, f.predecessors.map fun p => (p.1, ρ p.2)⟩

def Graph.rename (g : Graph) : Graph := g.map (Fact.rename ρ)

def Env.rename (env : Env) : Env := fun n => (env n).map ρ

theorem bind_rename (env : Env) (n : Name) (id : FactId) :
    (env.bind n id).rename ρ = (env.rename ρ).bind n (ρ id) := by
  funext x; simp only [Env.rename, Env.bind]; split <;> rfl

variable {ρ}

theorem beq_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (a b : FactId) : (ρ a == ρ b) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; exact ⟨hρ a b, congrArg ρ⟩

theorem factOf_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (g : Graph) (id : FactId) :
    (g.rename ρ).factOf (ρ id) = (g.factOf id).map (Fact.rename ρ) := by
  simp only [Graph.factOf, Graph.rename, List.find?_map]
  congr 2; funext f; exact beq_rename hρ f.id id

theorem step_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (g : Graph) (role : Role) (id : FactId) :
    (g.rename ρ).step role (ρ id) = (g.step role id).map ρ := by
  unfold Graph.step
  rw [factOf_rename hρ]
  cases g.factOf id with
  | none => rfl
  | some fact =>
    simp only [Option.map_some, Fact.rename, List.filter_map, List.map_map]
    refine congrArg _ (List.filter_congr fun p _ => ?_)
    simp only [Function.comp, factOf_rename hρ]
    cases g.factOf p.2 <;> rfl

theorem walk_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (g : Graph) : ∀ (roles : List Role) (start : FactId),
    (g.rename ρ).walk (ρ start) roles = (g.walk start roles).map ρ
  | [], _ => rfl
  | role :: roles, start => by
    simp only [Graph.walk, step_rename hρ, List.flatMap_map, List.map_flatMap]
    exact flatMap_congr fun p _ => walk_rename hρ g roles p

theorem pathHolds_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (g : Graph) (env : Env) (u : Name) (c : PathCondition) :
    c.holds (g.rename ρ) (env.rename ρ) u = c.holds g env u := by
  unfold PathCondition.holds Env.rename
  cases env u <;> cases env c.labelRight
  all_goals try rfl
  simp only [Option.map_some, walk_rename hρ, List.any_map]
  congr 1; funext a
  rw [Function.comp_apply, Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨b, hb, h⟩ => hρ _ _ h ▸ hb, fun h => ⟨a, h, rfl⟩⟩

mutual
  theorem evalMatches_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (g : Graph) : ∀ (ms : List Match) (env : Env),
      evalMatches (g.rename ρ) (env.rename ρ) ms = (evalMatches g env ms).map (Env.rename ρ)
    | [], _ => rfl
    | .mk u cs :: rest, env => by
      simp only [evalMatches]
      rw [Graph.rename, List.filter_map, List.flatMap_map, List.map_flatMap]
      refine flatMap_congr fun f _ => ?_
      show (if allHold (g.rename ρ) ((env.rename ρ).bind u.name (ρ f.id)) u.name cs = true then _ else _) = _
      rw [← bind_rename, allHold_rename hρ g cs, show List.map (Fact.rename ρ) g = g.rename ρ from rfl,
        show (Fact.rename ρ f).id = ρ f.id from rfl, ← bind_rename, evalMatches_rename hρ g rest]
      split <;> rfl

  theorem allHold_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (g : Graph) : ∀ (cs : List Condition) (env : Env) (u : Name),
      allHold (g.rename ρ) (env.rename ρ) u cs = allHold g env u cs
    | [], _, _ => rfl
    | c :: cs, env, u => by simp only [allHold, holds_rename hρ g c, allHold_rename hρ g cs]

  theorem holds_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (g : Graph) : ∀ (c : Condition) (env : Env) (u : Name),
      holds (g.rename ρ) (env.rename ρ) u c = holds g env u c
    | .path c, env, u => pathHolds_rename hρ g env u c
    | .existential e ms, env, u => by simp only [holds, evalMatches_rename hρ g ms, List.isEmpty_map]
end

/-- Renaming a graph's ids renames a feed's tuples. -/
theorem tuples_rename (hρ : ∀ a b, ρ a = ρ b → a = b) (f : Specification) (g : Graph) (env : Env) :
    f.tuples (g.rename ρ) (env.rename ρ) = (f.tuples g env).map (List.map ρ) := by
  simp only [Specification.tuples, evalMatches_rename hρ, List.map_map]
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, List.map_filterMap]; rfl

end JinagaSpec
