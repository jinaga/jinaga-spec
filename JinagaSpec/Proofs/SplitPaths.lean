import JinagaSpec.Proofs.Basic

/-!
# Walking to a fact of a known type

Two small facts about `Graph.walk`, used by the split's own correctness proof
(`Proofs/Hoist.lean`): a step, and a walk of at least one step, land on a fact
of the last role's predecessor type.
-/
namespace JinagaSpec

theorem step_mem_type {g : Graph} {role : Role} {r p : FactId}
    (h : p ∈ g.step role r) :
    ∃ f ∈ g, f.id = p ∧ f.type = role.predecessorType := by
  unfold Graph.step at h
  split at h
  · simp at h
  · simp only [List.mem_filter, List.mem_map] at h
    obtain ⟨_, hp⟩ := h
    revert hp
    cases hf : g.factOf p with
    | none => simp
    | some f =>
      intro hp
      simp only [beq_iff_eq] at hp
      unfold Graph.factOf at hf
      have h1 := List.find?_some hf
      have h2 := List.mem_of_find?_eq_some hf
      simp only [beq_iff_eq] at h1
      exact ⟨f, h2, h1, hp⟩

theorem walk_mem_type {g : Graph} {last : Role} :
    ∀ (R : List Role) (r a : FactId), a ∈ g.walk r R → R.getLast? = some last →
      ∃ f ∈ g, f.id = a ∧ f.type = last.predecessorType := by
  intro R
  induction R with
  | nil => intro r a _ h; simp at h
  | cons role rest ih =>
    intro r a ha hlast
    simp only [Graph.walk, List.mem_flatMap] at ha
    obtain ⟨p, hp, hap⟩ := ha
    cases rest with
    | nil =>
      simp only [Graph.walk, List.mem_singleton] at hap
      subst hap
      have : role = last := by simpa using hlast
      subst this
      exact step_mem_type hp
    | cons r2 rest2 =>
      apply ih p a hap
      simpa [List.getLast?_cons_cons] using hlast

end JinagaSpec
