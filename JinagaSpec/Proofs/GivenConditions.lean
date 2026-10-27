import JinagaSpec.GivenConditions
import JinagaSpec.Proofs.Stream
import JinagaSpec.Proofs.Derivation
import JinagaSpec.Proofs.Main
import JinagaSpec.Proofs.Hoist

/-!
# Conditions on a given, reduced

`read_reduceGivenConditions`: reducing a specification's conditions on its
givens to a match of their own does not change what a replica reads, provided
the reduced specification is well-formed and its new label is one the
specification does not name. Every theorem about the stream then applies to the
reduction (`stream_correct_given`).
-/
namespace JinagaSpec

theorem allHold_eq_all {g : Graph} {env : Env} {u : Name} :
    ∀ cs : List Condition, allHold g env u cs = cs.all (holds g env u)
  | [] => rfl
  | c :: cs => by simp [allHold, allHold_eq_all cs]

/-- The conditions on the givens hold, as conditions of any match. -/
theorem allHold_conditions (c : ConditionedSpecification) (g : Graph) (env : Env) (u : Name) :
    allHold g env u c.conditions = c.conditionsHold g env := by
  simp [allHold_eq_all, ConditionedSpecification.conditions, ConditionedSpecification.conditionsHold,
    List.all_flatMap, List.all_map, Function.comp_def, holds]

/-- Conditions scoped with `x` in scope, that never name `x`, are scoped
without it, as the conditions of any match. -/
theorem scopedConditions_drop {x u : Name} {G : List Name} :
    ∀ cs : List Condition, ScopedConditions (x :: G) G cs → x ∉ usedInConditions cs →
      ScopedConditions (u :: G) G cs
  | [], _, _ => trivial
  | c :: cs, h, hx => by
    obtain ⟨h1, h2⟩ : ScopedCondition (x :: G) G c ∧ ScopedConditions (x :: G) G cs := h
    simp only [usedInConditions, List.mem_append, not_or] at hx
    refine ⟨?_, scopedConditions_drop cs h2 hx.2⟩
    cases c with
    | path p => exact h1
    | existential e ms =>
      refine scopedMatches_mono ms G (u :: G) (fun _ h => List.mem_cons_of_mem _ h)
        (scopedMatches_shrink ms (x :: G) G h1 fun y hy hyx => ?_)
      rcases List.mem_cons.mp hyx with rfl | h
      · exact absurd hy hx.1
      · exact h

/-- **Reducing conditions on a given keeps what a replica reads.** -/
theorem read_reduceGivenConditions (c : ConditionedSpecification) (x : Name)
    (hwf : WellFormed (reduceGivenConditions x c))
    (hx : x ∉ usedInConditions c.conditions ++ usedInMatches c.matchList ++ c.projection.labels)
    (g : Graph) (env : Env) (r : Row) :
    r ∈ (reduceGivenConditions x c).read g env ↔ r ∈ c.read g env := by
  simp only [List.mem_append, not_or] at hx
  obtain ⟨⟨hxc, hxm⟩, hxp⟩ := hx
  cases hfind : c.given.find? (!·.2.isEmpty) with
  | none =>
    -- No given has a condition.
    have hc : c.conditionsHold g env = true := by
      simp only [ConditionedSpecification.conditionsHold, List.all_eq_true]
      rintro ⟨l, gcs⟩ hp
      simp [show gcs = [] by simpa using List.find?_eq_none.mp hfind (l, gcs) hp]
    simp [reduceGivenConditions, hfind, ConditionedSpecification.read, hc]
  | some p =>
    obtain ⟨g0, gcs⟩ := p
    simp only [reduceGivenConditions, hfind] at hwf ⊢
    have hmem := List.mem_of_find?_eq_some hfind
    have hg0 : g0 ∈ c.given.map (·.1) := List.mem_map.mpr ⟨_, hmem, rfl⟩
    let G := c.given.map (·.1.name)
    obtain ⟨-, hsc, hwn, hproj⟩ := hwf
    simp only [ConditionedSpecification.spec, List.map_map, Function.comp_def] at hsc hwn hproj
    obtain ⟨hsc0, hms⟩ := hsc
    obtain ⟨-, hconds⟩ := hsc0
    have hxG : x ∉ G := hwn.1
    have hg0G : g0.name ∈ G := List.mem_map.mpr ⟨_, hmem, rfl⟩
    have hxg0 : g0.name ≠ x := fun h => hxG (h ▸ hg0G)
    have hmsG : ScopedMatches G c.matchList :=
      scopedMatches_shrink _ (x :: G) G hms fun y hy hyx =>
        (List.mem_cons.mp hyx).resolve_left fun h => hxm (h ▸ hy)
    have hcondsG : ScopedConditions (g0.name :: G) G c.conditions := scopedConditions_drop _ hconds hxc
    have hL : ∀ y ∈ c.projection.labels, y ∈ G ++ c.matchList.map (·.unknown.name) := by
      intro y hy
      rcases hproj y hy with h | h
      · exact List.mem_append_left _ h
      · rcases List.mem_cons.mp h with rfl | h
        · exact absurd hy hxp
        · exact List.mem_append_right _ h
    have hagree : ∀ v, Agree (g0.name :: G) (env.bind x v) env := fun v y hy => by
      have : y ∈ G := (List.mem_cons.mp hy).elim (· ▸ hg0G) id
      simp [Env.bind, show y ≠ x from fun h => hxG (h ▸ this)]
    -- The conditions read the same with `x` bound.
    have hguard : ∀ v, allHold g (env.bind x v) x c.conditions = c.conditionsHold g env := fun v =>
      calc allHold g (env.bind x v) x c.conditions
          = allHold g (env.bind x v) g0.name c.conditions := by rw [allHold_conditions, allHold_conditions]
        _ = allHold g env g0.name c.conditions := allHold_agree g _ g0.name G _ env hcondsG (hagree v)
        _ = c.conditionsHold g env := allHold_conditions ..
    have hrows : ∀ v r, (∃ e ∈ evalMatches g (env.bind x v) c.matchList, c.projection.labels.map e = r) ↔
        (∃ e ∈ evalMatches g env c.matchList, c.projection.labels.map e = r) := fun v =>
      exists_projection_iff hmsG ((hagree v).mono fun _ => List.mem_cons_of_mem _) hL
    simp only [Specification.read, ConditionedSpecification.read, ConditionedSpecification.spec]
    rcases (Bool.eq_false_or_eq_true ((c.given.map (·.1)).all (g.has env))).symm with hP | hP
    · simp [hP]
    -- The first given is stored, so the new match has its one solution.
    have hhas : g.has env g0 = true := List.all_eq_true.mp hP g0 hg0
    obtain ⟨id0, hid0⟩ : ∃ id0, env g0.name = some id0 := by
      cases h : env g0.name <;> simp_all [Graph.has]
    obtain ⟨f, hf, hft⟩ : ∃ f, g.factOf id0 = some f ∧ f.type = g0.type := by
      simp only [Graph.has, hid0] at hhas
      cases h : g.factOf id0 <;> simp_all
    have hfid : f.id = id0 := by simpa using List.find?_some hf
    simp only [hP, ite_true, Specification.evaluate, List.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨f', -, -, hall, hrest⟩ := mem_evalMatches_cons.mp he
      simp only [allHold, Bool.and_eq_true, hguard] at hall
      simpa [hall.2] using (hrows _ _).mp ⟨e, hrest, rfl⟩
    · intro h
      rcases (Bool.eq_false_or_eq_true (c.conditionsHold g env)).symm with hc | hc
      · simp [hc] at h
      simp only [hc, ite_true, List.mem_map] at h
      obtain ⟨e, he, hr⟩ := (hrows f.id r).mpr h
      refine ⟨e, mem_evalMatches_cons.mpr ⟨f, Graph.mem_of_factOf_eq_some hf, hft, ?_, he⟩, hr⟩
      simp [allHold, hguard, hc, holds, PathCondition.holds, Env.bind, hxg0, hid0, hfid, Graph.walk]

/-- **The candidates of the reduction cover a conditioned specification.** -/
theorem candidates_complete_given (c : ConditionedSpecification) (x : Name)
    (hwf : WellFormed (reduceGivenConditions x c))
    (hx : x ∉ usedInConditions c.conditions ++ usedInMatches c.matchList ++ c.projection.labels)
    {g : Graph} {B : List Fact} (hf : Fresh g B) (env : Env) :
    Covers (c.read · env) g B (candidates (reduceGivenConditions x c) env g B) := fun r => by
  simpa only [read_reduceGivenConditions c x hwf hx] using candidates_complete _ hwf hf env r

/-- **A stream of a conditioned specification is its result.** Re-checking
the candidates of the reduction, after each fresh batch, holds exactly what a
replica reads. -/
theorem stream_correct_given (c : ConditionedSpecification) (x : Name)
    (hwf : WellFormed (reduceGivenConditions x c))
    (hx : x ∉ usedInConditions c.conditions ++ usedInMatches c.matchList ++ c.projection.labels)
    (env : Env) :
    ∀ (bs : List (List Fact)) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ c.read g env) →
      (∀ pre B post, bs = pre ++ B :: post → Fresh (g ++ pre.flatten) B) →
      ∀ r, r ∈ (bs.foldl (maintainStep (c.read · env) (candidates (reduceGivenConditions x c) env)) (g, held)).2 ↔
        r ∈ c.read (g ++ bs.flatten) env :=
  fun bs g held hheld hfresh =>
    maintain_correct (c.read · env) _ bs g held hheld
      fun pre B post h => candidates_complete_given c x hwf hx (hfresh pre B post h) env

end JinagaSpec
