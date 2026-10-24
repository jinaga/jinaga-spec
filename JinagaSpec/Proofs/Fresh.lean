import JinagaSpec.Proofs.Basic

/-!
# Layer 1: a fresh fact changes nothing behind it

When `f` arrives in `g`, the only thing that can change is what involves `f`
itself. A walk follows predecessors, and nothing in `g` names `f` as a
predecessor, so a walk that starts at any other fact takes the same steps in
`g ++ [f]` as in `g`. A path condition compares two walks, so a path condition
whose two ends are not `f` means the same in both graphs.

This is the only place freshness is used. It needs nothing about `f`'s own
predecessors.
-/
namespace JinagaSpec

/-- `f` is new to `g`: no fact of `g` has its id, and none points to it. -/
structure Fresh (g : Graph) (f : Fact) : Prop where
  idNew : ∀ x ∈ g, x.id ≠ f.id
  unreferenced : ∀ x ∈ g, ∀ p ∈ x.predecessors, p.2 ≠ f.id

variable {g : Graph} {f : Fact}

theorem factOf_append_ne {id : FactId} (h : id ≠ f.id) : (g ++ [f]).factOf id = g.factOf id := by
  unfold Graph.factOf
  rw [List.find?_append]
  cases g.find? (·.id == id) <;> simp [Ne.symm h]

/-- A step from a fact of `g` lands on a predecessor that fact names. -/
theorem step_ne (hf : Fresh g f) {role : Role} {id p : FactId} (h : p ∈ g.step role id) : p ≠ f.id := by
  unfold Graph.step at h
  split at h
  · simp at h
  · rename_i x hx
    simp only [List.mem_filter, List.mem_map] at h
    obtain ⟨⟨q, hq, rfl⟩, -⟩ := h
    exact hf.unreferenced x (Graph.mem_of_factOf_eq_some hx) q hq.1

theorem step_fresh (hf : Fresh g f) (role : Role) {id : FactId} (h : id ≠ f.id) :
    (g ++ [f]).step role id = g.step role id := by
  unfold Graph.step
  rw [factOf_append_ne h]
  split
  · rfl
  · rename_i x hx
    refine List.filter_congr fun p hp => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [factOf_append_ne (hf.unreferenced x (Graph.mem_of_factOf_eq_some hx) q (List.mem_filter.mp hq).1)]

theorem walk_fresh (hf : Fresh g f) :
    ∀ (roles : List Role) {start : FactId}, start ≠ f.id → (g ++ [f]).walk start roles = g.walk start roles
  | [], _, _ => rfl
  | role :: roles, start, h => by
    simp only [Graph.walk, step_fresh hf role h]
    exact flatMap_congr fun p hp => walk_fresh hf roles (step_ne hf hp)

/-- A path condition whose two ends are not `f` means the same in both graphs. -/
theorem pathHolds_fresh (hf : Fresh g f) {env : Env} {u : Name} (c : PathCondition)
    (hu : env u ≠ some f.id) (hr : env c.labelRight ≠ some f.id) :
    c.holds (g ++ [f]) env u = c.holds g env u := by
  unfold PathCondition.holds
  split
  · rename_i a b ha hb
    rw [walk_fresh hf _ (fun h => hu (by rw [ha, h])), walk_fresh hf _ (fun h => hr (by rw [hb, h]))]
  · rfl

end JinagaSpec
