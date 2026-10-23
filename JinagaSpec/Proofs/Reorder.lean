import JinagaSpec.Reorder
import JinagaSpec.Proofs.Locality

/-!
# Layer 4: a reordered inverse means what the inverse means

**A list of matches is a conjunction.** Read in order, a list of matches binds
each unknown to a fact of its type and keeps the binding when its conditions
hold. When each unknown is bound once and every condition names only labels
already bound, that is the same as asking, of the finished binding, that every
unknown has a fact of its type and every condition holds (`evalMatches_iff`).
That description does not mention order, so two such lists with the same
unknowns and the same conditions have the same solutions, whichever match each
condition is written on (`arranges_correct`). A path condition may also be
written on its other end, reversed, because it says that two walks meet.

**Flattening.** An `exists` condition's matches can be read as ordinary
matches right after the match that held it: a solution of the condition's
matches is exactly what `exists` asks for. The specification projects only its
own top-level labels, so the extra bindings change no result
(`flatten_correct`).

`reorderOrSelf_correct` puts these together: `reorderOrSelf` checks its result
with `arranges`, so whatever `orderFromPin` produced, the result means what the
inverse meant.
-/
namespace JinagaSpec

variable {G : Graph}

theorem allHold_iff {env : Env} {u : Name} :
    ∀ cs : List Condition, allHold G env u cs = true ↔ ∀ c ∈ cs, holds G env u c = true
  | [] => by simp [allHold]
  | c :: cs => by simp [allHold, allHold_iff cs]

/-- The finished binding: everything outside the matches is as in `env`, each
unknown is a fact of its type, and every condition holds. -/
structure Satisfies (G : Graph) (env : Env) (ms : List Match) (σ : Env) : Prop where
  frame : ∀ x, x ∉ names ms → σ x = env x
  typed : ∀ m ∈ ms, ∃ x ∈ G, x.type = m.unknown.type ∧ σ m.unknown.name = some x.id
  hold : ∀ m ∈ ms, allHold G σ m.unknown.name m.conditions = true

/-- Read in order, a list that binds each unknown once, and names only labels
already bound, is the conjunction `Satisfies`. -/
theorem evalMatches_iff :
    ∀ (ms : List Match) (S : List Name) (env σ : Env), ScopedMatches S ms → (names ms).Nodup →
      (∀ x ∈ names ms, x ∉ S) → (σ ∈ evalMatches G env ms ↔ Satisfies G env ms σ)
  | [], _, env, σ, _, _, _ => by
    simp only [evalMatches, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨fun _ _ => rfl, by simp, by simp⟩
    · intro h; funext x; exact h.frame x (by simp [names])
  | .mk u cs :: rest, S, env, σ, ⟨hcs, hrest⟩, hnd, hdis => by
    simp only [names, List.map_cons, List.nodup_cons] at hnd
    have hdis' : ∀ x ∈ names rest, x ∉ u.name :: S := by
      intro x hx hxS
      rcases List.mem_cons.mp hxS with rfl | hxS
      · exact hnd.1 hx
      · exact hdis x (by simp [names] at hx ⊢; exact Or.inr hx) hxS
    -- Once `rest` is read, its bindings leave `u` and the scope alone.
    have hagree : ∀ e1, σ ∈ evalMatches G e1 rest → Agree (u.name :: S) e1 σ := fun e1 h x hx =>
      (evalMatches_frame h x fun hm => hdis' x hm hx).symm
    constructor
    · intro h
      obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
      have ih := (evalMatches_iff rest (u.name :: S) _ σ hrest hnd.2 hdis').mp hr
      have hag := hagree _ hr
      refine ⟨fun y hy => ?_, ?_, ?_⟩
      · simp only [names, List.map_cons, List.mem_cons, not_or, Match.unknown_mk] at hy
        rw [ih.frame y hy.2]; simp [Env.bind, hy.1]
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨x, hx, ht, by simp only [Match.unknown_mk]; rw [← hag u.name (by simp)]; simp [Env.bind]⟩
        · exact ih.typed m hm
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · simp only [Match.unknown_mk, Match.conditions_mk]
          rw [← allHold_agree G cs u.name S _ _ hcs hag]; exact hc
        · exact ih.hold m hm
    · intro h
      obtain ⟨x, hx, ht, hσ⟩ := h.typed (.mk u cs) (by simp)
      let e1 := env.bind u.name x.id
      have hsat : Satisfies G e1 rest σ := by
        refine ⟨fun y hy => ?_, fun m hm => h.typed m (by simp [hm]), fun m hm => h.hold m (by simp [hm])⟩
        by_cases hyu : y = u.name
        · subst hyu; simpa [e1, Env.bind] using hσ
        · rw [h.frame y (by simp [names, hyu]; simpa [names] using hy)]; simp [e1, Env.bind, hyu]
      have hr := (evalMatches_iff rest (u.name :: S) e1 σ hrest hnd.2 hdis').mpr hsat
      refine mem_evalMatches_cons.mpr ⟨x, hx, ht, ?_, hr⟩
      rw [allHold_agree G cs u.name S _ _ hcs (hagree e1 hr)]
      exact h.hold (.mk u cs) (by simp)

/-- The same condition, reversed or moved, answers the same. -/
theorem sameConstraint_holds {σ : Env} :
    ∀ {a b : Name × Condition}, sameConstraint a b = true → holds G σ a.1 a.2 = holds G σ b.1 b.2
  | (u1, .path pc), (u2, .path pc2), h => by
    simp only [sameConstraint, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, h⟩
    · rfl
    · simp only [Edge.reverse, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [holds, PathCondition.holds]
      split <;> split <;> simp_all <;> grind
  | (_, .path _), (_, .existential _ _), h | (_, .existential _ _), (_, .path _), h => by
    simp [sameConstraint, BEq.beq, Condition.beq] at h
  | (_, .existential _ _), (_, .existential _ _), h => by
    simp only [sameConstraint] at h
    rw [Condition.eq_of_beq' h]
    rfl

theorem all_hold_of_covers {σ : Env} {ms1 ms2 : List Match} (hcov : covers ms1 ms2 = true)
    (h : ∀ m ∈ ms2, allHold G σ m.unknown.name m.conditions = true) :
    ∀ m ∈ ms1, allHold G σ m.unknown.name m.conditions = true := by
  intro m hm
  refine (allHold_iff _).mpr fun c hc => ?_
  obtain ⟨b, hb, hsame⟩ := List.any_eq_true.mp
    (List.all_eq_true.mp hcov (m.unknown.name, c) (List.mem_flatMap.mpr ⟨m, hm, List.mem_map_of_mem hc⟩))
  obtain ⟨m2, hm2, hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨c2, hc2, rfl⟩ := List.mem_map.mp hb
  rw [sameConstraint_holds hsame]
  exact (allHold_iff _).mp (h m2 hm2) c2 hc2

mutual
  theorem isScopedMatches_spec : ∀ (scope : List Name) (ms : List Match),
      isScopedMatches scope ms = true → ScopedMatches scope ms
    | _, [], _ => trivial
    | scope, .mk u cs :: rest, h => by
      simp only [isScopedMatches, Bool.and_eq_true] at h
      exact ⟨isScopedConditions_spec _ _ cs h.1, isScopedMatches_spec _ rest h.2⟩

  theorem isScopedConditions_spec : ∀ (inner outer : List Name) (cs : List Condition),
      isScopedConditions inner outer cs = true → ScopedConditions inner outer cs
    | _, _, [], _ => trivial
    | inner, outer, c :: cs, h => by
      simp only [isScopedConditions, Bool.and_eq_true] at h
      exact ⟨isScopedCondition_spec _ _ c h.1, isScopedConditions_spec _ _ cs h.2⟩

  theorem isScopedCondition_spec : ∀ (inner outer : List Name) (c : Condition),
      isScopedCondition inner outer c = true → ScopedCondition inner outer c
    | _, outer, .path pc, h => by
      simp only [isScopedCondition, List.contains_iff_mem] at h
      exact h
    | inner, _, .existential _ ms, h => isScopedMatches_spec inner ms h
end

theorem bindsOnce_spec {scope : List Name} {ms : List Match} (h : bindsOnce scope ms = true) :
    ScopedMatches scope ms ∧ (names ms).Nodup ∧ ∀ x ∈ names ms, x ∉ scope := by
  simp only [bindsOnce, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨isScopedMatches_spec _ _ h.2, h.1.1, fun x hx hxs => ?_⟩
  have := h.1.2 x hx
  simp at this
  exact this hxs

/-- An arrangement has the same solutions. -/
theorem arranges_correct {scope : List Name} {ms1 ms2 : List Match} (h : arranges scope ms1 ms2 = true)
    (env σ : Env) : σ ∈ evalMatches G env ms1 ↔ σ ∈ evalMatches G env ms2 := by
  simp only [arranges, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, hl12⟩, hl21⟩, hc12⟩, hc21⟩ := h
  obtain ⟨hsc1, hnd1, hdis1⟩ := bindsOnce_spec h1
  obtain ⟨hsc2, hnd2, hdis2⟩ := bindsOnce_spec h2
  rw [evalMatches_iff ms1 scope env σ hsc1 hnd1 hdis1, evalMatches_iff ms2 scope env σ hsc2 hnd2 hdis2]
  -- The same labels, so the same names and the same types.
  have hlab : ∀ l, l ∈ ms1.map (·.unknown) ↔ l ∈ ms2.map (·.unknown) := fun l =>
    ⟨fun hl => List.contains_iff_mem.mp (List.all_eq_true.mp hl12 l hl),
     fun hl => List.contains_iff_mem.mp (List.all_eq_true.mp hl21 l hl)⟩
  have hnames : ∀ x, x ∈ names ms1 ↔ x ∈ names ms2 := by
    intro x
    simp only [names, List.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨m2, hm2, he⟩ := List.mem_map.mp ((hlab m.unknown).mp (List.mem_map_of_mem hm))
      exact ⟨m2, hm2, by rw [he]⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨m1, hm1, he⟩ := List.mem_map.mp ((hlab m.unknown).mpr (List.mem_map_of_mem hm))
      exact ⟨m1, hm1, by rw [he]⟩
  have htyped : ∀ {a b : List Match}, (∀ l, l ∈ a.map (·.unknown) → l ∈ b.map (·.unknown)) →
      (∀ m ∈ b, ∃ x ∈ G, x.type = m.unknown.type ∧ σ m.unknown.name = some x.id) →
      ∀ m ∈ a, ∃ x ∈ G, x.type = m.unknown.type ∧ σ m.unknown.name = some x.id := by
    intro a b hab hb m hm
    obtain ⟨m', hm', he⟩ := List.mem_map.mp (hab _ (List.mem_map_of_mem hm))
    rw [← he]; exact hb m' hm'
  constructor
  · intro h
    exact ⟨fun x hx => h.frame x (fun h' => hx ((hnames x).mp h')),
      htyped (fun l => (hlab l).mpr) h.typed, all_hold_of_covers hc21 h.hold⟩
  · intro h
    exact ⟨fun x hx => h.frame x (fun h' => hx ((hnames x).mpr h')),
      htyped (fun l => (hlab l).mp) h.typed, all_hold_of_covers hc12 h.hold⟩

/-! ## Flattening -/

theorem names_append (a b : List Match) : names (a ++ b) = names a ++ names b := List.map_append

theorem flattenConditions_keep_scoped {inner outer : List Name} :
    ∀ cs : List Condition, ScopedConditions inner outer cs →
      ScopedConditions inner outer (flattenConditions cs).1
  | [], _ => by unfold flattenConditions; trivial
  | c :: cs, ⟨hc, hcs⟩ => by
    have ih := flattenConditions_keep_scoped cs hcs
    unfold flattenConditions
    cases c with
    | path => exact ⟨hc, ih⟩
    | existential e ms =>
      cases e with
      | false => exact ⟨hc, ih⟩
      | true => dsimp only; split <;> first | exact ih | exact ⟨hc, ih⟩

/-- Flattening keeps the top-level unknowns. -/
theorem mem_names_flatten {x : Name} : ∀ {ms : List Match}, x ∈ names ms → x ∈ names (flattenMatches ms)
  | [], h => by simpa [flattenMatches] using h
  | .mk u cs :: rest, h => by
    have hflat : flattenMatches (.mk u cs :: rest) =
        .mk u (flattenConditions cs).1 :: ((flattenConditions cs).2 ++ flattenMatches rest) := by
      rw [flattenMatches]; rcases flattenConditions cs with ⟨k, l⟩; rfl
    rw [hflat]
    simp only [names, List.map_cons, List.mem_cons, Match.unknown_mk, List.map_append,
      List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (mem_names_flatten h))

mutual
  /-- Flattening keeps the solutions: each solution of the original extends to
  one of the flattened list, and back, agreeing on the original's unknowns. -/
  theorem flatten_correct :
      ∀ (ms : List Match) (S : List Name) (env : Env), ScopedMatches S ms →
        (names (flattenMatches ms)).Nodup → (∀ x ∈ names (flattenMatches ms), x ∉ S) →
        (∀ σ ∈ evalMatches G env ms, ∃ σ' ∈ evalMatches G env (flattenMatches ms), Agree (names ms) σ σ') ∧
        (∀ σ' ∈ evalMatches G env (flattenMatches ms), ∃ σ ∈ evalMatches G env ms, Agree (names ms) σ σ')
    | [], _, env, _, _, _ => by
      simp only [flattenMatches, evalMatches, List.mem_singleton]
      exact ⟨fun σ h => ⟨σ, h, fun _ h => by simp [names] at h⟩,
        fun σ h => ⟨σ, h, fun _ h => by simp [names] at h⟩⟩
    | .mk u cs :: rest, S, env, ⟨hcs, hrest⟩, hnd, hdis => by
      -- The flattened list: `u` with the conditions kept, the lifted matches, then `rest` flattened.
      have hflat : flattenMatches (.mk u cs :: rest) =
          .mk u (flattenConditions cs).1 :: ((flattenConditions cs).2 ++ flattenMatches rest) := by
        rw [flattenMatches]; rcases flattenConditions cs with ⟨k, l⟩; rfl
      rw [hflat] at hnd hdis ⊢
      simp only [names, List.map_cons, List.map_append, List.nodup_cons, Match.unknown_mk,
        List.mem_append, not_or] at hnd
      obtain ⟨⟨huL, huR⟩, hndLR⟩ := hnd
      have hndL := (List.nodup_append.mp hndLR).1
      have hndR := (List.nodup_append.mp hndLR).2.1
      have hdisL : ∀ x ∈ names (flattenConditions cs).2, x ∉ u.name :: S := by
        intro x hx hxS
        rcases List.mem_cons.mp hxS with rfl | hxS
        · exact huL hx
        · exact hdis x (by simp [names] at hx ⊢; exact Or.inr (Or.inl hx)) hxS
      have hdisR : ∀ x ∈ names (flattenMatches rest), x ∉ u.name :: S := by
        intro x hx hxS
        rcases List.mem_cons.mp hxS with rfl | hxS
        · exact huR hx
        · exact hdis x (by simp [names] at hx ⊢; exact Or.inr (Or.inr hx)) hxS
      have hcond := fun e => flattenConditions_correct cs u.name S e hcs hndL hdisL
      have ih := fun e => flatten_correct rest (u.name :: S) e hrest hndR hdisR
      -- Lifted bindings leave `u` and the scope alone.
      have hframeL : ∀ e1 σ1, σ1 ∈ evalMatches G e1 (flattenConditions cs).2 → Agree (u.name :: S) e1 σ1 :=
        fun e1 σ1 h x hx => (evalMatches_frame h x fun hm => hdisL x hm hx).symm
      -- `u` itself is untouched by everything after it.
      have hu_rest : u.name ∉ names rest := fun h => huR (mem_names_flatten h)
      -- On `u`, both sides read what `x` was bound to.
      have hu_eq : ∀ e1 σ σ1 σ3, σ ∈ evalMatches G e1 rest → σ1 ∈ evalMatches G e1 (flattenConditions cs).2 →
          σ3 ∈ evalMatches G σ1 (flattenMatches rest) → σ u.name = σ3 u.name := by
        intro e1 σ σ1 σ3 hσ hσ1 hσ3
        rw [evalMatches_frame hσ _ hu_rest, evalMatches_frame hσ3 _ huR, evalMatches_frame hσ1 _ huL]
      constructor
      · intro σ h
        obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
        obtain ⟨hkeep, σ1, hσ1, -⟩ := (hcond _).mp hc
        obtain ⟨σ2, hσ2, hag2⟩ := evalMatches_agree G rest (u.name :: S) _ σ1 hrest (hframeL _ _ hσ1) σ hr
        obtain ⟨σ3, hσ3, hag3⟩ := (ih σ1).1 σ2 hσ2
        refine ⟨σ3, mem_evalMatches_cons.mpr ⟨x, hx, ht, hkeep, mem_evalMatches_append.mpr ⟨σ1, hσ1, hσ3⟩⟩, ?_⟩
        intro y hy
        simp only [names, List.map_cons, List.mem_cons, Match.unknown_mk] at hy
        rcases hy with rfl | hy
        · exact hu_eq _ σ σ1 σ3 hr hσ1 hσ3
        · exact (hag2 y (List.mem_append_right _ hy)).trans (hag3 y hy)
      · intro σ3 h
        obtain ⟨x, hx, ht, hkeep, h⟩ := mem_evalMatches_cons.mp h
        obtain ⟨σ1, hσ1, hσ3⟩ := mem_evalMatches_append.mp h
        have hc := (hcond _).mpr ⟨hkeep, σ1, hσ1, trivial⟩
        obtain ⟨σ2, hσ2, hag2⟩ := (ih σ1).2 σ3 hσ3
        obtain ⟨σ, hσ, hag⟩ := evalMatches_agree G rest (u.name :: S) σ1 _ hrest (hframeL _ _ hσ1).symm σ2 hσ2
        refine ⟨σ, mem_evalMatches_cons.mpr ⟨x, hx, ht, hc, hσ⟩, ?_⟩
        intro y hy
        simp only [names, List.map_cons, List.mem_cons, Match.unknown_mk] at hy
        rcases hy with rfl | hy
        · exact hu_eq _ σ σ1 σ3 hσ hσ1 hσ3
        · exact (hag y (List.mem_append_right _ hy)).symm.trans (hag2 y hy)

  /-- Lifting an `exists` condition's matches: the conditions hold exactly when
  the kept ones hold and the lifted matches have a solution. -/
  theorem flattenConditions_correct :
      ∀ (cs : List Condition) (u : Name) (S : List Name) (env : Env),
        ScopedConditions (u :: S) S cs → (names (flattenConditions cs).2).Nodup →
        (∀ x ∈ names (flattenConditions cs).2, x ∉ u :: S) →
        (allHold G env u cs = true ↔
          allHold G env u (flattenConditions cs).1 = true ∧
            ∃ σ ∈ evalMatches G env (flattenConditions cs).2, True)
    | [], _, _, env, _, _, _ => by simp [flattenConditions, allHold, evalMatches]
    | c :: cs, u, S, env, ⟨hc, hcs⟩, hnd, hdis => by
      -- The kept conditions read only `u` and the scope, so any binding that
      -- agrees there answers the same.
      have hkeep := flattenConditions_keep_scoped cs hcs
      cases c with
      | path pc =>
        have hfc : flattenConditions (.path pc :: cs) = (.path pc :: (flattenConditions cs).1, (flattenConditions cs).2) := by
          rw [flattenConditions]
        rw [hfc] at hnd hdis ⊢
        simp only [allHold, Bool.and_eq_true]
        rw [flattenConditions_correct cs u S env hcs hnd hdis]
        exact and_assoc.symm
      | existential e ms =>
        by_cases hlift : e = true ∧ pinnedMatches ms = true
        · obtain ⟨rfl, hp⟩ := hlift
          have hfc : flattenConditions (.existential true ms :: cs) =
              ((flattenConditions cs).1, flattenMatches ms ++ (flattenConditions cs).2) := by
            rw [flattenConditions]; simp [hp]
          rw [hfc] at hnd hdis ⊢
          simp only [names_append, List.nodup_append, List.mem_append] at hnd hdis
          have hdisM : ∀ x ∈ names (flattenMatches ms), x ∉ u :: S := fun x hx => hdis x (Or.inl hx)
          have hdisC : ∀ x ∈ names (flattenConditions cs).2, x ∉ u :: S := fun x hx => hdis x (Or.inr hx)
          have hms := flatten_correct ms (u :: S) env hc hnd.1 hdisM
          have hagM : ∀ σ1 ∈ evalMatches G env (flattenMatches ms), Agree (u :: S) env σ1 :=
            fun σ1 h x hx => (evalMatches_frame h x fun hm => hdisM x hm hx).symm
          simp only [allHold, Bool.and_eq_true, holds_exists]
          constructor
          · rintro ⟨⟨σ0, hσ0⟩, hcs'⟩
            obtain ⟨σ1, hσ1, -⟩ := hms.1 σ0 hσ0
            rw [allHold_agree G cs u S env σ1 hcs (hagM σ1 hσ1)] at hcs'
            obtain ⟨hk, σ2, hσ2, -⟩ := (flattenConditions_correct cs u S σ1 hcs hnd.2.1 hdisC).mp hcs'
            exact ⟨by rwa [allHold_agree G _ u S env σ1 hkeep (hagM σ1 hσ1)],
              σ2, mem_evalMatches_append.mpr ⟨σ1, hσ1, hσ2⟩, trivial⟩
          · rintro ⟨hk, σ2, hσ2, -⟩
            obtain ⟨σ1, hσ1, hσ2⟩ := mem_evalMatches_append.mp hσ2
            obtain ⟨σ0, hσ0, -⟩ := hms.2 σ1 hσ1
            rw [allHold_agree G _ u S env σ1 hkeep (hagM σ1 hσ1)] at hk
            have := (flattenConditions_correct cs u S σ1 hcs hnd.2.1 hdisC).mpr ⟨hk, σ2, hσ2, trivial⟩
            exact ⟨⟨σ0, hσ0⟩, by rwa [allHold_agree G cs u S env σ1 hcs (hagM σ1 hσ1)]⟩
        · have hfc : flattenConditions (.existential e ms :: cs) =
              (.existential e ms :: (flattenConditions cs).1, (flattenConditions cs).2) := by
            rw [flattenConditions]
            cases e with
            | false => rfl
            | true => simp at hlift; simp [hlift]
          rw [hfc] at hnd hdis ⊢
          simp only [allHold, Bool.and_eq_true]
          rw [flattenConditions_correct cs u S env hcs hnd hdis]
          exact and_assoc.symm
end

/-! ## Putting it together -/

/-- **`reorderOrSelf_correct`.** A reordered inverse has the inverse's results,
for every inverse, graph and binding of its givens. -/
theorem reorderOrSelf_correct (i : Specification) (env : Env) (row : List (Option FactId)) :
    row ∈ (reorderOrSelf i).evaluate G env ↔ row ∈ i.evaluate G env := by
  unfold reorderOrSelf
  cases h : reorderChecked i with
  | none => rfl
  | some r =>
    simp only [Option.getD_some]
    simp only [reorderChecked, Option.filter_eq_some_iff, Bool.and_eq_true] at h
    obtain ⟨hre, ⟨hsc, harr⟩, hproj⟩ := h
    -- `reorder` changes only the matches.
    obtain ⟨ms, -, rfl⟩ : ∃ ms, orderFromPin _ _ = some ms ∧ r = { i with matchList := ms } := by
      simp only [reorder, Option.map_eq_some_iff] at hre
      obtain ⟨ms, hms, rfl⟩ := hre
      exact ⟨ms, hms, rfl⟩
    generalize hscope : pinLabel :: (i.given.map (·.name)).filter (· != pinLabel) = scope at hsc harr hproj
    have hflat := harr
    simp only [arranges, Bool.and_eq_true] at hflat
    obtain ⟨-, hndF, hdisF⟩ := bindsOnce_spec hflat.1.1.1.1.1
    have hfc := flatten_correct (G := G) i.matchList scope env (isScopedMatches_spec _ _ hsc) hndF hdisF
    -- A binding of the original and of the flattened list that agree on the
    -- original's unknowns project the same result.
    have hsame : ∀ σ ∈ evalMatches G env i.matchList, ∀ σ' ∈ evalMatches G env (flattenMatches i.matchList),
        Agree (names i.matchList) σ σ' → i.projection.labels.map σ = i.projection.labels.map σ' := by
      intro σ hσ σ' hσ' hag
      refine List.map_congr_left fun l hl => ?_
      have := List.all_eq_true.mp hproj l hl
      simp only [Bool.or_eq_true, List.contains_iff_mem] at this
      by_cases hn : l ∈ names i.matchList
      · exact hag l hn
      · rcases this with hs | hn'
        · rw [evalMatches_frame hσ l hn, evalMatches_frame hσ' l fun h => hdisF l h hs]
        · exact absurd hn' hn
    simp only [Specification.evaluate, List.mem_map]
    constructor
    · rintro ⟨σ', hσ', rfl⟩
      obtain ⟨σ, hσ, hag⟩ := hfc.2 σ' ((arranges_correct harr env σ').mpr hσ')
      exact ⟨σ, hσ, hsame σ hσ σ' ((arranges_correct harr env σ').mpr hσ') hag⟩
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨σ', hσ', hag⟩ := hfc.1 σ hσ
      exact ⟨σ', (arranges_correct harr env σ').mp hσ', (hsame σ hσ σ' hσ' hag).symm⟩

end JinagaSpec
