import JinagaSpec.Proofs.Basic

/-!
# Layer 1: a fresh batch changes nothing behind it

When a batch `B` arrives in `g`, the only thing that can change is what
involves the facts of `B`. A walk follows predecessors, and nothing in `g`
names a fact of `B` as a predecessor, so a walk that starts at any other fact
takes the same steps in `g ++ B` as in `g`. A path condition compares two
walks, so a path condition whose two ends are not in `B` means the same in both
graphs.

This is the only place freshness is used. It needs nothing about the
predecessors of the facts of `B`: they may name each other, in any order.
-/
namespace JinagaSpec

/-- The batch `B` is new to `g`: no fact of `g` has the id of a fact of `B`, and
none points to one. -/
structure Fresh (g : Graph) (B : List Fact) : Prop where
  idNew : ∀ x ∈ g, ∀ b ∈ B, x.id ≠ b.id
  unreferenced : ∀ x ∈ g, ∀ p ∈ x.predecessors, ∀ b ∈ B, p.2 ≠ b.id

/-- The id of no fact of `B`. -/
def Outside (B : List Fact) (id : FactId) : Prop := ∀ b ∈ B, id ≠ b.id

variable {g : Graph} {B : List Fact}

theorem factOf_append_outside {id : FactId} (h : Outside B id) : (g ++ B).factOf id = g.factOf id := by
  unfold Graph.factOf
  rw [List.find?_append]
  cases g.find? (·.id == id) with
  | some => rfl
  | none => simpa using fun b hb heq => h b hb heq.symm

/-- A step from a fact of `g` lands on a predecessor that fact names. -/
theorem step_outside (hf : Fresh g B) {role : Role} {id p : FactId} (h : p ∈ g.step role id) : Outside B p := by
  unfold Graph.step at h
  split at h
  · simp at h
  · rename_i x hx
    simp only [List.mem_filter, List.mem_map] at h
    obtain ⟨⟨q, hq, rfl⟩, -⟩ := h
    exact hf.unreferenced x (Graph.mem_of_factOf_eq_some hx) q hq.1

theorem step_fresh (hf : Fresh g B) (role : Role) {id : FactId} (h : Outside B id) :
    (g ++ B).step role id = g.step role id := by
  unfold Graph.step
  rw [factOf_append_outside h]
  split
  · rfl
  · rename_i x hx
    refine List.filter_congr fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [factOf_append_outside (hf.unreferenced x (Graph.mem_of_factOf_eq_some hx) q (List.mem_filter.mp hq).1)]

theorem walk_fresh (hf : Fresh g B) :
    ∀ (roles : List Role) {start : FactId}, Outside B start → (g ++ B).walk start roles = g.walk start roles
  | [], _, _ => rfl
  | role :: roles, start, h => by
    simp only [Graph.walk, step_fresh hf role h]
    exact flatMap_congr fun p hp => walk_fresh hf roles (step_outside hf hp)

/-- A path condition whose two ends are not in `B` means the same in both graphs. -/
theorem pathHolds_fresh (hf : Fresh g B) {env : Env} {u : Name} (c : PathCondition)
    (hu : ∀ id, env u = some id → Outside B id) (hr : ∀ id, env c.labelRight = some id → Outside B id) :
    c.holds (g ++ B) env u = c.holds g env u := by
  unfold PathCondition.holds
  split
  · rename_i a b ha hb
    rw [walk_fresh hf _ (hu a ha), walk_fresh hf _ (hr b hb)]
  · rfl

end JinagaSpec
