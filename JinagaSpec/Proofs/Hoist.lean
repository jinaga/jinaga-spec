import JinagaSpec.Hoist
import JinagaSpec.Proofs.Main
import JinagaSpec.Proofs.Derivation

/-!
# The split agrees with the reference semantics

A hoisted label is bound in the head, so it is existentially quantified
outside every quantifier of the tail; the original condition quantifies
existentially over the walk inside whatever encloses it. Existentials commute
with existentials, so pulling the walk out through positive existentials and
through the tail's own match unknowns preserves meaning. A negative
existential is a universal, and an existential cannot be pulled out through a
universal: that is exactly why `hoistCondition` only rewrites a condition at
positive polarity, monotonically (`docs/findings.md`).

At negative polarity `hoistMatches`/`hoistConditions`/`hoistCondition` are the
identity outright (`hoist_false_id`): eligibility is gated on `pos = true`
syntactically, not on anything about the scope or the condition, so there is
nothing to prove there. The remaining, positive-polarity case is proved by one
mutual induction mirroring `hoistMatches`/`hoistConditions`/`hoistCondition`'s
own recursion, generalizing `Locality.lean`'s agreement argument (an
environment agreement propagates through matches and conditions) to the whole
tree at once: at any depth, a condition hoisted out of an existential, and the
head match that witnesses it, say the same thing, not only at the pivot's own
top level.
-/
namespace JinagaSpec

/-! ## At negative polarity, hoisting is the identity -/

mutual
  theorem hoistMatches_false_id (scope : List Name) :
      ∀ (i : Nat) (ms : List Match), hoistMatches scope i false ms = (i, [], ms)
    | i, [] => rfl
    | i, .mk u cs :: rest => by
      have h1 := hoistConditions_false_id scope i cs
      have h2 := hoistMatches_false_id scope i rest
      calc hoistMatches scope i false (.mk u cs :: rest)
          = (let (i1, headCs, cs') := hoistConditions scope i false cs
             let (i2, headRest, rest') := hoistMatches scope i1 false rest
             (i2, headCs ++ headRest, .mk u cs' :: rest')) := rfl
        _ = (i, [], .mk u cs :: rest) := by simp [h1, h2]

  theorem hoistConditions_false_id (scope : List Name) :
      ∀ (i : Nat) (cs : List Condition), hoistConditions scope i false cs = (i, [], cs)
    | i, [] => rfl
    | i, c :: cs => by
      have h1 := hoistCondition_false_id scope i c
      have h2 := hoistConditions_false_id scope i cs
      calc hoistConditions scope i false (c :: cs)
          = (let (i1, headC, c') := hoistCondition scope i false c
             let (i2, headCs, cs') := hoistConditions scope i1 false cs
             (i2, headC ++ headCs, c' :: cs')) := rfl
        _ = (i, [], c :: cs) := by simp [h1, h2]

  theorem hoistCondition_false_id (scope : List Name) :
      ∀ (i : Nat) (c : Condition), hoistCondition scope i false c = (i, [], c)
    | i, .path pc => by
      show hoistCondition scope i false (.path pc) = (i, [], .path pc)
      unfold hoistCondition
      cases pc.rolesRight.getLast? <;> cases scope.contains pc.labelRight <;> rfl
    | i, .existential e ms => by
      have h := hoistMatches_false_id scope i ms
      calc hoistCondition scope i false (.existential e ms)
          = (let (i1, headMs, ms') := hoistMatches scope i (false && e) ms
             (i1, headMs, .existential e ms')) := rfl
        _ = (i, [], .existential e ms) := by simp [h]
end

/-! ## The split-label counter never goes backwards -/

mutual
  theorem hoistMatches_mono (scope : List Name) :
      ∀ (i : Nat) (pos : Bool) (ms : List Match), i ≤ (hoistMatches scope i pos ms).1
    | i, _, [] => Nat.le_refl _
    | i, pos, .mk u cs :: rest => by
      rcases hgenC : hoistConditions scope i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches scope i1 pos rest with ⟨i2, headRest, rest'⟩
      have heq : (hoistMatches scope i pos (.mk u cs :: rest)).1 = i2 := by
        show (hoistMatches scope i pos (.mk u cs :: rest)).1 = _
        unfold hoistMatches
        simp [hgenC, hgenM]
      rw [heq]
      have h1 := hoistConditions_mono scope i pos cs
      have h2 := hoistMatches_mono scope i1 pos rest
      rw [hgenC] at h1
      rw [hgenM] at h2
      simp only at h1 h2
      omega

  theorem hoistConditions_mono (scope : List Name) :
      ∀ (i : Nat) (pos : Bool) (cs : List Condition), i ≤ (hoistConditions scope i pos cs).1
    | i, _, [] => Nat.le_refl _
    | i, pos, c :: cs => by
      rcases hgenC : hoistCondition scope i pos c with ⟨i1, headC, c'⟩
      rcases hgenCs : hoistConditions scope i1 pos cs with ⟨i2, headCs, cs'⟩
      have heq : (hoistConditions scope i pos (c :: cs)).1 = i2 := by
        show (hoistConditions scope i pos (c :: cs)).1 = _
        unfold hoistConditions
        simp [hgenC, hgenCs]
      rw [heq]
      have h1 := hoistCondition_mono scope i pos c
      have h2 := hoistConditions_mono scope i1 pos cs
      rw [hgenC] at h1
      rw [hgenCs] at h2
      simp only at h1 h2
      omega

  theorem hoistCondition_mono (scope : List Name) :
      ∀ (i : Nat) (pos : Bool) (c : Condition), i ≤ (hoistCondition scope i pos c).1
    | i, pos, .path pc => by
      show i ≤ (hoistCondition scope i pos (.path pc)).1
      unfold hoistCondition
      match pos, pc.rolesRight.getLast?, scope.contains pc.labelRight with
      | true, some _, true => exact Nat.le_succ i
      | true, none, _ => exact Nat.le_refl _
      | true, some _, false => exact Nat.le_refl _
      | false, _, _ => exact Nat.le_refl _
    | i, pos, .existential e ms => by
      have h := hoistMatches_mono scope i (pos && e) ms
      show i ≤ (hoistCondition scope i pos (.existential e ms)).1
      unfold hoistCondition
      rcases hgenM : hoistMatches scope i (pos && e) ms with ⟨i1, headMs, ms'⟩
      simp only [hgenM] at h
      simpa using h
end

/-! ## The head matches a hoist produces bind fresh, ordered split labels -/

mutual
  theorem hoistMatches_index (scope : List Name) :
      ∀ (i : Nat) (pos : Bool) (ms : List Match),
        ∀ m ∈ (hoistMatches scope i pos ms).2.1,
          ∃ j, i ≤ j ∧ j < (hoistMatches scope i pos ms).1 ∧ m.unknown.name = splitLabel j
    | i, _, [] => by simp [hoistMatches]
    | i, pos, .mk u cs :: rest => by
      rcases hgenC : hoistConditions scope i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches scope i1 pos rest with ⟨i2, headRest, rest'⟩
      have heq1 : (hoistMatches scope i pos (.mk u cs :: rest)).1 = i2 := by
        show (hoistMatches scope i pos (.mk u cs :: rest)).1 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      have heq2 : (hoistMatches scope i pos (.mk u cs :: rest)).2.1 = headCs ++ headRest := by
        show (hoistMatches scope i pos (.mk u cs :: rest)).2.1 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      rw [heq1, heq2]
      intro m hm
      have hmono1 := hoistConditions_mono scope i pos cs
      rw [hgenC] at hmono1
      simp only at hmono1
      have hmono2 := hoistMatches_mono scope i1 pos rest
      rw [hgenM] at hmono2
      simp only at hmono2
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨j, hj1, hj2, hn⟩ := hoistConditions_index scope i pos cs m (by rw [hgenC]; exact hm)
        rw [hgenC] at hj2
        simp only at hj2
        exact ⟨j, hj1, by omega, hn⟩
      · obtain ⟨j, hj1, hj2, hn⟩ := hoistMatches_index scope i1 pos rest m (by rw [hgenM]; exact hm)
        rw [hgenM] at hj2
        simp only at hj2
        exact ⟨j, by omega, hj2, hn⟩

  theorem hoistConditions_index (scope : List Name) :
      ∀ (i : Nat) (pos : Bool) (cs : List Condition),
        ∀ m ∈ (hoistConditions scope i pos cs).2.1,
          ∃ j, i ≤ j ∧ j < (hoistConditions scope i pos cs).1 ∧ m.unknown.name = splitLabel j
    | i, _, [] => by simp [hoistConditions]
    | i, pos, c :: cs => by
      rcases hgenC : hoistCondition scope i pos c with ⟨i1, headC, c'⟩
      rcases hgenCs : hoistConditions scope i1 pos cs with ⟨i2, headCs, cs'⟩
      have heq1 : (hoistConditions scope i pos (c :: cs)).1 = i2 := by
        show (hoistConditions scope i pos (c :: cs)).1 = _
        unfold hoistConditions; simp [hgenC, hgenCs]
      have heq2 : (hoistConditions scope i pos (c :: cs)).2.1 = headC ++ headCs := by
        show (hoistConditions scope i pos (c :: cs)).2.1 = _
        unfold hoistConditions; simp [hgenC, hgenCs]
      rw [heq1, heq2]
      intro m hm
      have hmono1 := hoistCondition_mono scope i pos c
      rw [hgenC] at hmono1
      simp only at hmono1
      have hmono2 := hoistConditions_mono scope i1 pos cs
      rw [hgenCs] at hmono2
      simp only at hmono2
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨j, hj1, hj2, hn⟩ := hoistCondition_index scope i pos c m (by rw [hgenC]; exact hm)
        rw [hgenC] at hj2
        simp only at hj2
        exact ⟨j, hj1, by omega, hn⟩
      · obtain ⟨j, hj1, hj2, hn⟩ := hoistConditions_index scope i1 pos cs m (by rw [hgenCs]; exact hm)
        rw [hgenCs] at hj2
        simp only at hj2
        exact ⟨j, by omega, hj2, hn⟩

  theorem hoistCondition_index (scope : List Name) :
      ∀ (i : Nat) (pos : Bool) (c : Condition),
        ∀ m ∈ (hoistCondition scope i pos c).2.1,
          ∃ j, i ≤ j ∧ j < (hoistCondition scope i pos c).1 ∧ m.unknown.name = splitLabel j
    | i, pos, .path pc => by
      show ∀ m ∈ (hoistCondition scope i pos (.path pc)).2.1, _
      unfold hoistCondition
      match pos, pc.rolesRight.getLast?, scope.contains pc.labelRight with
      | true, some _, true =>
        intro m hm
        simp only [List.mem_singleton] at hm
        subst hm
        exact ⟨i, Nat.le_refl _, Nat.lt_succ_self _, rfl⟩
      | true, none, _ => simp
      | true, some _, false => simp
      | false, _, _ => simp
    | i, pos, .existential e ms => by
      rcases hgenM : hoistMatches scope i (pos && e) ms with ⟨i1, headMs, ms'⟩
      have heq1 : (hoistCondition scope i pos (.existential e ms)).1 = i1 := by
        show (hoistCondition scope i pos (.existential e ms)).1 = _
        unfold hoistCondition; simp [hgenM]
      have heq2 : (hoistCondition scope i pos (.existential e ms)).2.1 = headMs := by
        show (hoistCondition scope i pos (.existential e ms)).2.1 = _
        unfold hoistCondition; simp [hgenM]
      rw [heq1, heq2]
      intro m hm
      obtain ⟨j, hj1, hj2, hn⟩ := hoistMatches_index scope i (pos && e) ms m (by rw [hgenM]; exact hm)
      rw [hgenM] at hj2
      simp only at hj2
      exact ⟨j, hj1, hj2, hn⟩
end

/-- Every name a hoist's head matches bind, at any depth, is reserved. -/
theorem hoistMatches_reserved (scope : List Name) (i : Nat) (pos : Bool) (ms : List Match) :
    ∀ m ∈ (hoistMatches scope i pos ms).2.1, isReserved m.unknown.name = true := by
  intro m hm
  obtain ⟨j, -, -, hn⟩ := hoistMatches_index scope i pos ms m hm
  rw [hn]
  exact isReserved_splitLabel j

/-- Two lists of hoisted head matches, one numbered entirely below a
boundary and the other entirely at or above it, bind disjoint names: a
shared name would give the same split label two different indices. Used
wherever a "before"/"after" pair of `hoistMatches`/`hoistConditions`/
`hoistCondition` calls, sharing a counter at the boundary, need their head
matches kept apart. -/
theorem hoistIndex_disjoint {mA mB : List Match} {i1 : Nat}
    (hA : ∀ m ∈ mA, ∃ j, j < i1 ∧ m.unknown.name = splitLabel j)
    (hB : ∀ m ∈ mB, ∃ j, i1 ≤ j ∧ m.unknown.name = splitLabel j) :
    ∀ x ∈ mA.map (·.unknown.name), x ∉ mB.map (·.unknown.name) := by
  intro x hxA hxB
  obtain ⟨mA', hmA', hmAn⟩ := List.mem_map.mp hxA
  obtain ⟨mB', hmB', hmBn⟩ := List.mem_map.mp hxB
  obtain ⟨jA, hjA, hnA⟩ := hA mA' hmA'
  obtain ⟨jB, hjB, hnB⟩ := hB mB' hmB'
  have heqn : splitLabel jA = splitLabel jB := by rw [← hnA, hmAn, ← hmBn, hnB]
  have := splitLabel_injective heqn
  omega

theorem hoistConditions_reserved (scope : List Name) (i : Nat) (pos : Bool) (cs : List Condition) :
    ∀ m ∈ (hoistConditions scope i pos cs).2.1, isReserved m.unknown.name = true := by
  intro m hm
  obtain ⟨j, -, -, hn⟩ := hoistConditions_index scope i pos cs m hm
  rw [hn]
  exact isReserved_splitLabel j

/-- Running a hoist's head matches from an environment that agrees with a
reference on a reserved-free scope gives a result that still agrees: the head
matches only ever bind reserved names. -/
theorem hoistMatches_agree {g : Graph} (A : List Name) (hordA : ∀ x ∈ A, isReserved x = false)
    (scope : List Name) (i : Nat) (pos : Bool) (ms : List Match) (env1 env2 : Env)
    (hag : Agree A env1 env2) :
    ∀ eh ∈ evalMatches g env2 (hoistMatches scope i pos ms).2.1, Agree A env1 eh := by
  intro eh heh x hx
  rw [hag x hx]
  symm
  apply evalMatches_frame heh
  intro hmem
  obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
  have hres := hoistMatches_reserved scope i pos ms m hm
  rw [hmn, hordA x hx] at hres
  exact absurd hres (by simp)

theorem hoistConditions_agree {g : Graph} (A : List Name) (hordA : ∀ x ∈ A, isReserved x = false)
    (scope : List Name) (i : Nat) (pos : Bool) (cs : List Condition) (env1 env2 : Env)
    (hag : Agree A env1 env2) :
    ∀ eh ∈ evalMatches g env2 (hoistConditions scope i pos cs).2.1, Agree A env1 eh := by
  intro eh heh x hx
  rw [hag x hx]
  symm
  apply evalMatches_frame heh
  intro hmem
  obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
  have hres := hoistConditions_reserved scope i pos cs m hm
  rw [hmn, hordA x hx] at hres
  exact absurd hres (by simp)

theorem hoistCondition_reserved (scope : List Name) (i : Nat) (pos : Bool) (c : Condition) :
    ∀ m ∈ (hoistCondition scope i pos c).2.1, isReserved m.unknown.name = true := by
  intro m hm
  obtain ⟨j, -, -, hn⟩ := hoistCondition_index scope i pos c m hm
  rw [hn]
  exact isReserved_splitLabel j

theorem hoistCondition_agree {g : Graph} (A : List Name) (hordA : ∀ x ∈ A, isReserved x = false)
    (scope : List Name) (i : Nat) (pos : Bool) (c : Condition) (env1 env2 : Env)
    (hag : Agree A env1 env2) :
    ∀ eh ∈ evalMatches g env2 (hoistCondition scope i pos c).2.1, Agree A env1 eh := by
  intro eh heh x hx
  rw [hag x hx]
  symm
  apply evalMatches_frame heh
  intro hmem
  obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
  have hres := hoistCondition_reserved scope i pos c m hm
  rw [hmn, hordA x hx] at hres
  exact absurd hres (by simp)

/-! ## Hoisting preserves each match's own unknown -/

theorem hoistMatches_unknowns (scope : List Name) :
    ∀ (i : Nat) (pos : Bool) (ms : List Match),
      (hoistMatches scope i pos ms).2.2.map (·.unknown.name) = ms.map (·.unknown.name)
  | i, _, [] => rfl
  | i, pos, .mk u cs :: rest => by
    rcases hgenC : hoistConditions scope i pos cs with ⟨i1, headCs, cs'⟩
    rcases hgenM : hoistMatches scope i1 pos rest with ⟨i2, headRest, rest'⟩
    have heq : (hoistMatches scope i pos (.mk u cs :: rest)).2.2 = .mk u cs' :: rest' := by
      show (hoistMatches scope i pos (.mk u cs :: rest)).2.2 = _
      unfold hoistMatches
      simp [hgenC, hgenM]
    have hih := hoistMatches_unknowns scope i1 pos rest
    rw [hgenM] at hih
    simp only at hih
    simp [heq, Match.unknown_mk, hih]

/-! ## Scope is monotone in the allowed names -/

mutual
  theorem scopedMatches_mono :
      ∀ (ms : List Match) (A B : List Name), (∀ x ∈ A, x ∈ B) → ScopedMatches A ms → ScopedMatches B ms
    | [], _, _, _, _ => trivial
    | .mk u cs :: rest, A, B, hsub, h => by
      obtain ⟨h1, h2⟩ : ScopedConditions (u.name :: A) A cs ∧ ScopedMatches (u.name :: A) rest := h
      have hsub' : ∀ x ∈ u.name :: A, x ∈ u.name :: B := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub x hx)
      exact ⟨scopedConditions_mono cs (u.name :: A) (u.name :: B) A B hsub' hsub h1,
        scopedMatches_mono rest (u.name :: A) (u.name :: B) hsub' h2⟩

  theorem scopedConditions_mono :
      ∀ (cs : List Condition) (inner1 inner2 outer1 outer2 : List Name),
        (∀ x ∈ inner1, x ∈ inner2) → (∀ x ∈ outer1, x ∈ outer2) →
        ScopedConditions inner1 outer1 cs → ScopedConditions inner2 outer2 cs
    | [], _, _, _, _, _, _, _ => trivial
    | c :: cs, inner1, inner2, outer1, outer2, hi, ho, h => by
      obtain ⟨h1, h2⟩ : ScopedCondition inner1 outer1 c ∧ ScopedConditions inner1 outer1 cs := h
      exact ⟨scopedCondition_mono c inner1 inner2 outer1 outer2 hi ho h1,
        scopedConditions_mono cs inner1 inner2 outer1 outer2 hi ho h2⟩

  theorem scopedCondition_mono :
      ∀ (c : Condition) (inner1 inner2 outer1 outer2 : List Name),
        (∀ x ∈ inner1, x ∈ inner2) → (∀ x ∈ outer1, x ∈ outer2) →
        ScopedCondition inner1 outer1 c → ScopedCondition inner2 outer2 c
    | .path _, _, _, _, _, _, ho, h => ho _ h
    | .existential _ ms, inner1, inner2, _, _, hi, _, h => scopedMatches_mono ms inner1 inner2 hi h
end

/-! ## Hoisting preserves scope, adding the split labels it introduces -/

mutual
  theorem hoistMatches_scoped (S : List Name) :
      ∀ (ms : List Match) (scope : List Name), ScopedMatches scope ms →
        ∀ (i : Nat) (pos : Bool),
          ScopedMatches (scope ++ (hoistMatches S i pos ms).2.1.map (·.unknown.name))
            (hoistMatches S i pos ms).2.2
    | [], scope, _, i, pos => by simp [hoistMatches, ScopedMatches]
    | .mk u cs :: rest, scope, hsc, i, pos => by
      obtain ⟨hcs, hrest⟩ : ScopedConditions (u.name :: scope) scope cs ∧
          ScopedMatches (u.name :: scope) rest := hsc
      rcases hgenC : hoistConditions S i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches S i1 pos rest with ⟨i2, headRest, rest'⟩
      have heq1 : (hoistMatches S i pos (.mk u cs :: rest)).2.1 = headCs ++ headRest := by
        show (hoistMatches S i pos (.mk u cs :: rest)).2.1 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      have heq2 : (hoistMatches S i pos (.mk u cs :: rest)).2.2 = .mk u cs' :: rest' := by
        show (hoistMatches S i pos (.mk u cs :: rest)).2.2 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      rw [heq1, heq2]
      have ihC := hoistConditions_scoped S cs (u.name :: scope) scope hcs i pos
      have ihM := hoistMatches_scoped S rest (u.name :: scope) hrest i1 pos
      rw [hgenC] at ihC
      rw [hgenM] at ihM
      simp only at ihC ihM
      have hsub1 : ∀ x ∈ scope ++ headCs.map (·.unknown.name), x ∈ scope ++ (headCs ++ headRest).map (·.unknown.name) := by
        intro x hx
        simp only [List.mem_append, List.map_append] at hx ⊢
        grind
      have hsub2 : ∀ x ∈ scope ++ headRest.map (·.unknown.name), x ∈ scope ++ (headCs ++ headRest).map (·.unknown.name) := by
        intro x hx
        simp only [List.mem_append, List.map_append] at hx ⊢
        grind
      have hsubI : ∀ x ∈ (u.name :: scope) ++ headCs.map (·.unknown.name),
          x ∈ (u.name :: scope) ++ (headCs ++ headRest).map (·.unknown.name) := by
        intro x hx
        simp only [List.mem_append, List.map_append] at hx ⊢
        grind
      have key1 : ScopedConditions ((u.name :: scope) ++ (headCs ++ headRest).map (·.unknown.name))
          (scope ++ (headCs ++ headRest).map (·.unknown.name)) cs' :=
        scopedConditions_mono cs' _ _ _ _ hsubI hsub1 ihC
      have key2 : ScopedMatches ((u.name :: scope) ++ (headCs ++ headRest).map (·.unknown.name)) rest' := by
        refine scopedMatches_mono rest' _ _ ?_ ihM
        intro x hx
        simp only [List.mem_append, List.map_append] at hx ⊢
        grind
      refine ⟨?_, ?_⟩
      · simpa [List.cons_append] using key1
      · simpa [List.cons_append] using key2

  theorem hoistConditions_scoped (S : List Name) :
      ∀ (cs : List Condition) (inner outer : List Name), ScopedConditions inner outer cs →
        ∀ (i : Nat) (pos : Bool),
          ScopedConditions (inner ++ (hoistConditions S i pos cs).2.1.map (·.unknown.name))
            (outer ++ (hoistConditions S i pos cs).2.1.map (·.unknown.name))
            (hoistConditions S i pos cs).2.2
    | [], inner, outer, _, i, pos => by simp [hoistConditions, ScopedConditions]
    | c :: cs, inner, outer, hsc, i, pos => by
      obtain ⟨hc, hcs⟩ : ScopedCondition inner outer c ∧ ScopedConditions inner outer cs := hsc
      rcases hgenC : hoistCondition S i pos c with ⟨i1, headC, c'⟩
      rcases hgenCs : hoistConditions S i1 pos cs with ⟨i2, headCs, cs'⟩
      have heq1 : (hoistConditions S i pos (c :: cs)).2.1 = headC ++ headCs := by
        show (hoistConditions S i pos (c :: cs)).2.1 = _
        unfold hoistConditions; simp [hgenC, hgenCs]
      have heq2 : (hoistConditions S i pos (c :: cs)).2.2 = c' :: cs' := by
        show (hoistConditions S i pos (c :: cs)).2.2 = _
        unfold hoistConditions; simp [hgenC, hgenCs]
      rw [heq1, heq2]
      have ihc := hoistCondition_scoped S c inner outer hc i pos
      have ihcs := hoistConditions_scoped S cs inner outer hcs i1 pos
      rw [hgenC] at ihc
      rw [hgenCs] at ihcs
      simp only at ihc ihcs
      have hsubI : ∀ x ∈ inner ++ headC.map (·.unknown.name), x ∈ inner ++ (headC ++ headCs).map (·.unknown.name) := by
        intro x hx; simp only [List.mem_append, List.map_append] at hx ⊢; grind
      have hsubO : ∀ x ∈ outer ++ headC.map (·.unknown.name), x ∈ outer ++ (headC ++ headCs).map (·.unknown.name) := by
        intro x hx; simp only [List.mem_append, List.map_append] at hx ⊢; grind
      have hsubI2 : ∀ x ∈ inner ++ headCs.map (·.unknown.name), x ∈ inner ++ (headC ++ headCs).map (·.unknown.name) := by
        intro x hx; simp only [List.mem_append, List.map_append] at hx ⊢; grind
      have hsubO2 : ∀ x ∈ outer ++ headCs.map (·.unknown.name), x ∈ outer ++ (headC ++ headCs).map (·.unknown.name) := by
        intro x hx; simp only [List.mem_append, List.map_append] at hx ⊢; grind
      exact ⟨scopedCondition_mono c' _ _ _ _ hsubI hsubO ihc,
        scopedConditions_mono cs' _ _ _ _ hsubI2 hsubO2 ihcs⟩

  theorem hoistCondition_scoped (S : List Name) :
      ∀ (c : Condition) (inner outer : List Name), ScopedCondition inner outer c →
        ∀ (i : Nat) (pos : Bool),
          ScopedCondition (inner ++ (hoistCondition S i pos c).2.1.map (·.unknown.name))
            (outer ++ (hoistCondition S i pos c).2.1.map (·.unknown.name))
            (hoistCondition S i pos c).2.2
    | .path pc, inner, outer, hsc, i, pos => by
      show ScopedCondition (inner ++ (hoistCondition S i pos (.path pc)).2.1.map (·.unknown.name))
        (outer ++ (hoistCondition S i pos (.path pc)).2.1.map (·.unknown.name))
        (hoistCondition S i pos (.path pc)).2.2
      have hsc' : pc.labelRight ∈ outer := hsc
      unfold hoistCondition
      match pos, pc.rolesRight.getLast?, S.contains pc.labelRight with
      | true, some _, true => simp [ScopedCondition]
      | true, none, _ => simpa [ScopedCondition]
      | true, some _, false => simpa [ScopedCondition]
      | false, _, _ => simpa [ScopedCondition]
    | .existential e ms, inner, outer, hsc, i, pos => by
      show ScopedCondition (inner ++ (hoistCondition S i pos (.existential e ms)).2.1.map (·.unknown.name))
        (outer ++ (hoistCondition S i pos (.existential e ms)).2.1.map (·.unknown.name))
        (hoistCondition S i pos (.existential e ms)).2.2
      have hsc' : ScopedMatches inner ms := hsc
      rcases hgenM : hoistMatches S i (pos && e) ms with ⟨i1, headMs, ms'⟩
      have heq : (hoistCondition S i pos (.existential e ms)).2.1.map (·.unknown.name) =
          headMs.map (·.unknown.name) ∧
          (hoistCondition S i pos (.existential e ms)).2.2 = .existential e ms' := by
        show _ ∧ _
        unfold hoistCondition
        simp [hgenM]
      have ih := hoistMatches_scoped S ms inner hsc' i (pos && e)
      rw [hgenM] at ih
      simp only at ih
      rw [heq.1, heq.2]
      exact ih
end

/-! ## The head matches a hoist produces are themselves scoped in `S`

Every head match's own condition walks from a label already in `S`, `hoist`'s
eligibility scope: that is exactly what makes it eligible. -/

mutual
  theorem hoistMatches_head_scoped (S : List Name) :
      ∀ (i : Nat) (pos : Bool) (ms : List Match), ScopedMatches S (hoistMatches S i pos ms).2.1
    | i, pos, [] => by simp [hoistMatches, ScopedMatches]
    | i, pos, .mk u cs :: rest => by
      rcases hgenC : hoistConditions S i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches S i1 pos rest with ⟨i2, headRest, rest'⟩
      have heq : (hoistMatches S i pos (.mk u cs :: rest)).2.1 = headCs ++ headRest := by
        show (hoistMatches S i pos (.mk u cs :: rest)).2.1 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      rw [heq, scopedMatches_append]
      have ihC := hoistConditions_head_scoped S i pos cs
      have ihM := hoistMatches_head_scoped S i1 pos rest
      rw [hgenC] at ihC
      rw [hgenM] at ihM
      simp only at ihC ihM
      refine ⟨ihC, scopedMatches_mono headRest S (scopeAfter S headCs) ?_ ihM⟩
      intro x hx
      rw [mem_scopeAfter]
      exact Or.inr hx

  theorem hoistConditions_head_scoped (S : List Name) :
      ∀ (i : Nat) (pos : Bool) (cs : List Condition), ScopedMatches S (hoistConditions S i pos cs).2.1
    | i, pos, [] => by simp [hoistConditions, ScopedMatches]
    | i, pos, c :: cs => by
      rcases hgenC : hoistCondition S i pos c with ⟨i1, headC, c'⟩
      rcases hgenCs : hoistConditions S i1 pos cs with ⟨i2, headCs, cs'⟩
      have heq : (hoistConditions S i pos (c :: cs)).2.1 = headC ++ headCs := by
        show (hoistConditions S i pos (c :: cs)).2.1 = _
        unfold hoistConditions; simp [hgenC, hgenCs]
      rw [heq, scopedMatches_append]
      have ihc := hoistCondition_head_scoped S i pos c
      have ihcs := hoistConditions_head_scoped S i1 pos cs
      rw [hgenC] at ihc
      rw [hgenCs] at ihcs
      simp only at ihc ihcs
      refine ⟨ihc, scopedMatches_mono headCs S (scopeAfter S headC) ?_ ihcs⟩
      intro x hx
      rw [mem_scopeAfter]
      exact Or.inr hx

  theorem hoistCondition_head_scoped (S : List Name) :
      ∀ (i : Nat) (pos : Bool) (c : Condition), ScopedMatches S (hoistCondition S i pos c).2.1
    | i, pos, .path pc => by
      show ScopedMatches S (hoistCondition S i pos (.path pc)).2.1
      unfold hoistCondition
      match pos, hl : pc.rolesRight.getLast?, hc : S.contains pc.labelRight with
      | true, some _, true =>
        have hmem : pc.labelRight ∈ S := by
          simpa only [List.contains_eq_mem, decide_eq_true_eq] using hc
        simp only [ScopedMatches, ScopedConditions, ScopedCondition]
        exact ⟨⟨hmem, trivial⟩, trivial⟩
      | true, none, _ => simp [ScopedMatches]
      | true, some _, false => simp [ScopedMatches]
      | false, _, _ => simp [ScopedMatches]
    | i, pos, .existential e ms => by
      rcases hgenM : hoistMatches S i (pos && e) ms with ⟨i1, headMs, ms'⟩
      have heq : (hoistCondition S i pos (.existential e ms)).2.1 = headMs := by
        show (hoistCondition S i pos (.existential e ms)).2.1 = _
        unfold hoistCondition; simp [hgenM]
      rw [heq]
      have ih := hoistMatches_head_scoped S i (pos && e) ms
      rw [hgenM] at ih
      simpa using ih
end

/-- Binding a name outside a scope the head matches are known to respect,
before running them, changes nothing but that one binding: the head matches
never refer to it. Stated for an arbitrary such scope `G` (found, in practice,
by widening `hoistMatches_head_scoped`'s own `S` via `scopedMatches_mono`), not
just `S` itself, since the caller's own agreement scope is usually bigger. -/
theorem hoistMatches_head_irrel {g : Graph} (S G : List Name) (i : Nat) (pos : Bool) (ms : List Match)
    (hG : ScopedMatches G (hoistMatches S i pos ms).2.1)
    (n : Name) (hn : n ∉ G) (v : FactId) (env : Env) (e' : Env)
    (he' : e' ∈ evalMatches g (env.bind n v) (hoistMatches S i pos ms).2.1) :
    ∃ e'' ∈ evalMatches g env (hoistMatches S i pos ms).2.1,
      Agree (G ++ (hoistMatches S i pos ms).2.1.map (·.unknown.name)) e' e'' := by
  have hag : Agree G (env.bind n v) env := by
    intro x hx
    have hxn : x ≠ n := fun h => hn (h ▸ hx)
    simp [Env.bind, hxn]
  exact evalMatches_agree g (hoistMatches S i pos ms).2.1 G (env.bind n v) env hG hag e' he'

theorem hoistConditions_head_irrel {g : Graph} (S G : List Name) (i : Nat) (pos : Bool) (cs : List Condition)
    (hG : ScopedMatches G (hoistConditions S i pos cs).2.1)
    (n : Name) (hn : n ∉ G) (v : FactId) (env : Env) (e' : Env)
    (he' : e' ∈ evalMatches g (env.bind n v) (hoistConditions S i pos cs).2.1) :
    ∃ e'' ∈ evalMatches g env (hoistConditions S i pos cs).2.1,
      Agree (G ++ (hoistConditions S i pos cs).2.1.map (·.unknown.name)) e' e'' := by
  have hag : Agree G (env.bind n v) env := by
    intro x hx
    have hxn : x ≠ n := fun h => hn (h ▸ hx)
    simp [Env.bind, hxn]
  exact evalMatches_agree g (hoistConditions S i pos cs).2.1 G (env.bind n v) env hG hag e' he'

/-! ## The general correctness argument -/

mutual
  theorem hoistCondition_correct (g : Graph) (S : List Name) (u : Name) (f : FactId) :
      ∀ (c : Condition) (A : List Name), (∀ x ∈ S, x ∈ A) → (∀ x ∈ A, isReserved x = false) →
        u ∉ A → isReserved u = false →
        ScopedCondition (u :: A) A c → WellNamedCondition (u :: A) c →
        (∀ x ∈ usedInCondition c, isReserved x = false) →
        ∀ (i : Nat) (pos : Bool) (env1 env2 : Env), Agree A env1 env2 →
          ((∃ eh ∈ evalMatches g env2 (hoistCondition S i pos c).2.1,
              holds g (eh.bind u f) u (hoistCondition S i pos c).2.2 = true)
            ↔ holds g (env1.bind u f) u c = true)
    | .path pc, A, hSA, hordA, hun, hordU, hsc, _, hused, i, pos, env1, env2, hag => by
      have hpcOrd : isReserved pc.labelRight = false := hused pc.labelRight (by simp [usedInCondition])
      have hpcA : pc.labelRight ∈ A := hsc
      show ((∃ eh ∈ evalMatches g env2 (hoistCondition S i pos (.path pc)).2.1,
          holds g (eh.bind u f) u (hoistCondition S i pos (.path pc)).2.2 = true)
          ↔ holds g (env1.bind u f) u (.path pc) = true)
      unfold hoistCondition
      match pos, hl : pc.rolesRight.getLast?, hcont : S.contains pc.labelRight with
      | true, some last, true =>
        show ((∃ eh ∈ evalMatches g env2
              [.mk { name := splitLabel i, type := last.predecessorType }
                  [.path { rolesLeft := [], labelRight := pc.labelRight, rolesRight := pc.rolesRight }]],
              holds g (eh.bind u f) u
                (.path { rolesLeft := pc.rolesLeft, labelRight := splitLabel i, rolesRight := [] }) = true)
            ↔ holds g (env1.bind u f) u (.path pc) = true)
        have hpcS : pc.labelRight ∈ S := by
          simpa only [List.contains_eq_mem, decide_eq_true_eq] using hcont
        have hnlr_u : pc.labelRight ≠ u := fun h => hun (h ▸ hSA _ hpcS)
        have hnlr_split : pc.labelRight ≠ splitLabel i := by
          intro h; have hres := isReserved_splitLabel i; rw [← h, hpcOrd] at hres; simp at hres
        have hnu_split : splitLabel i ≠ u := by
          intro h; have hres := isReserved_splitLabel i; rw [h, hordU] at hres; simp at hres
        have hrEq : env1 pc.labelRight = env2 pc.labelRight := hag pc.labelRight hpcA
        cases hr : env2 pc.labelRight with
        | none =>
          have hL : holds g (env1.bind u f) u (.path pc) = false := by
            simp [holds, PathCondition.holds, Env.bind, hnlr_u, hrEq, hr]
          constructor
          · rintro ⟨eh, heh, hh⟩
            exfalso
            obtain ⟨f', hf', hty, hall, heh2⟩ := mem_evalMatches_cons.mp heh
            simp [allHold, holds, PathCondition.holds, Env.bind, hnlr_split, hr] at hall
          · intro h; rw [hL] at h; simp at h
        | some r =>
          have hhead : ∀ f' : Fact,
              allHold g (env2.bind (splitLabel i) f'.id) (splitLabel i)
                [.path { rolesLeft := [], labelRight := pc.labelRight, rolesRight := pc.rolesRight }] = true
              ↔ f'.id ∈ g.walk r pc.rolesRight := by
            intro f'
            simp [allHold, holds, PathCondition.holds, Env.bind, hnlr_split, hr, Graph.walk]
          have htail : ∀ (e' : Env) (x : FactId), e' (splitLabel i) = some x →
              (PathCondition.holds g (e'.bind u f) u
                { rolesLeft := pc.rolesLeft, labelRight := splitLabel i, rolesRight := [] } = true
              ↔ x ∈ g.walk f pc.rolesLeft) := by
            intro e' x hx
            simp [PathCondition.holds, Env.bind, hnu_split, hx, Graph.walk]
          have horig : holds g (env1.bind u f) u (.path pc) = true ↔
              ∃ a, a ∈ g.walk f pc.rolesLeft ∧ a ∈ g.walk r pc.rolesRight := by
            simp [holds, PathCondition.holds, Env.bind, hnlr_u, hrEq, hr]
          constructor
          · rintro ⟨eh, heh, hh⟩
            obtain ⟨f', hf', hty, hall, heh2⟩ := mem_evalMatches_cons.mp heh
            simp only [evalMatches, List.mem_singleton] at heh2
            subst heh2
            have hname' : (env2.bind (splitLabel i) f'.id) (splitLabel i) = some f'.id := by
              simp [Env.bind]
            have h1 := (htail (env2.bind (splitLabel i) f'.id) f'.id hname').mp hh
            have h2 := (hhead f').mp hall
            exact horig.mpr ⟨_, h1, h2⟩
          · intro h
            obtain ⟨a, ha1, ha2⟩ := horig.mp h
            obtain ⟨f', hf', hid, hty⟩ := walk_mem_type pc.rolesRight r a ha2 hl
            refine ⟨(env2.bind (splitLabel i) f'.id), mem_evalMatches_cons.mpr
              ⟨f', hf', hty, (hhead f').mpr (hid ▸ ha2), by simp [evalMatches]⟩, ?_⟩
            have hname' : (env2.bind (splitLabel i) f'.id) (splitLabel i) = some f'.id := by
              simp [Env.bind]
            exact (htail (env2.bind (splitLabel i) f'.id) f'.id hname').mpr (hid ▸ ha1)
      | true, none, _ =>
        show ((∃ eh ∈ evalMatches g env2 [], holds g (eh.bind u f) u (.path pc) = true)
            ↔ holds g (env1.bind u f) u (.path pc) = true)
        rw [holds_agree g (.path pc) u A (env1.bind u f) (env2.bind u f) hsc (hag.bind u f)]
        simp [evalMatches]
      | true, some _, false =>
        show ((∃ eh ∈ evalMatches g env2 [], holds g (eh.bind u f) u (.path pc) = true)
            ↔ holds g (env1.bind u f) u (.path pc) = true)
        rw [holds_agree g (.path pc) u A (env1.bind u f) (env2.bind u f) hsc (hag.bind u f)]
        simp [evalMatches]
      | false, _, _ =>
        show ((∃ eh ∈ evalMatches g env2 [], holds g (eh.bind u f) u (.path pc) = true)
            ↔ holds g (env1.bind u f) u (.path pc) = true)
        rw [holds_agree g (.path pc) u A (env1.bind u f) (env2.bind u f) hsc (hag.bind u f)]
        simp [evalMatches]
    | .existential expect ms, A, hSA, hordA, hun, hordU, hsc, hwn, hused, i, pos, env1, env2, hag => by
      have hscMs : ScopedMatches (u :: A) ms := hsc
      have hwnMs : WellNamedMatches (u :: A) ms := hwn
      have husedMs : ∀ x ∈ usedInMatches ms, isReserved x = false := hused
      rcases hgenM : hoistMatches S i (pos && expect) ms with ⟨i1, headMs, ms'⟩
      have heq2 : (hoistCondition S i pos (.existential expect ms)).2.1 = headMs := by
        show (hoistCondition S i pos (.existential expect ms)).2.1 = _
        unfold hoistCondition; simp [hgenM]
      have heq3 : (hoistCondition S i pos (.existential expect ms)).2.2 = .existential expect ms' := by
        show (hoistCondition S i pos (.existential expect ms)).2.2 = _
        unfold hoistCondition; simp [hgenM]
      rw [heq2, heq3]
      by_cases hnewpos : (pos && expect) = true
      · obtain ⟨hposT, hexpT⟩ : pos = true ∧ expect = true := by
          rcases pos <;> rcases expect <;> simp_all
        subst hposT; subst hexpT
        simp only [Bool.and_self] at hgenM
        have hSAu : ∀ x ∈ S, x ∈ u :: A := fun x hx => List.mem_cons_of_mem _ (hSA x hx)
        have hordAu : ∀ x ∈ u :: A, isReserved x = false := by
          intro x hx; rcases List.mem_cons.mp hx with rfl | hx
          · exact hordU
          · exact hordA x hx
        have hagUF : Agree (u :: A) (env1.bind u f) (env2.bind u f) := hag.bind u f
        have hGscoped : ScopedMatches A headMs := by
          have h := hoistMatches_head_scoped S i true ms
          rw [hgenM] at h; simp only at h
          exact scopedMatches_mono headMs S A hSA h
        have hScopedMs' : ScopedMatches (u :: (A ++ headMs.map (·.unknown.name))) ms' := by
          have h := hoistMatches_scoped S ms (u :: A) hscMs i true
          rw [hgenM] at h; simp only at h
          simpa [List.cons_append] using h
        have hunHeadMs : u ∉ headMs.map (·.unknown.name) := by
          intro hmem
          obtain ⟨mM, hmM, hmMn⟩ := List.mem_map.mp hmem
          have hres := hoistMatches_reserved S i true ms mM (by rw [hgenM]; exact hmM)
          rw [hmMn, hordU] at hres
          exact absurd hres (by simp)
        have hAgreeUFrame : ∀ e : Env, Agree A e (e.bind u f) := by
          intro e x hx
          have hxn : x ≠ u := fun h => hun (h ▸ hx)
          simp [Env.bind, hxn]
        have hChar : ∀ (env : Env) (mss : List Match),
            holds g env u (.existential true mss) = true ↔ ∃ e, e ∈ evalMatches g env mss := by
          intro env mss
          show (true == !(evalMatches g env mss).isEmpty) = true ↔ _
          rcases evalMatches g env mss with _ | ⟨e2, l2⟩
          · simp
          · simp
        rw [hChar (env1.bind u f) ms]
        constructor
        · rintro ⟨eh, heh, hh⟩
          rw [hChar (eh.bind u f) ms'] at hh
          obtain ⟨e3, he3⟩ := hh
          obtain ⟨ehR, hehR, hagUB⟩ :=
            evalMatches_agree g headMs A env2 (env2.bind u f) hGscoped (hAgreeUFrame env2) eh heh
          have hAgreeMs' : Agree (u :: (A ++ headMs.map (·.unknown.name))) (eh.bind u f) ehR := by
            intro x hx0
            rcases List.mem_cons.mp hx0 with heq | hxA
            · have hehRu : ehR u = some f := by
                rw [evalMatches_frame hehR u hunHeadMs]
                simp [Env.bind]
              rw [heq]
              simp [Env.bind, hehRu]
            · have hxu : x ≠ u := by
                intro heq2
                rcases List.mem_append.mp hxA with hxA' | hxA'
                · rw [heq2] at hxA'; exact hun hxA'
                · rw [heq2] at hxA'; exact hunHeadMs hxA'
              rw [Env.bind, if_neg hxu]
              exact hagUB x hxA
          obtain ⟨e3', he3', -⟩ :=
            evalMatches_agree g ms' (u :: (A ++ headMs.map (·.unknown.name)))
              (eh.bind u f) ehR hScopedMs' hAgreeMs' e3 he3
          have := (hoistMatches_correct g S ms (u :: A) hSAu hordAu hscMs hwnMs husedMs
            i true (env1.bind u f) (env2.bind u f) hagUF [] (by simp) []).mpr
              ⟨ehR, by rw [hgenM]; exact hehR, e3', by rw [hgenM]; exact he3', rfl⟩
          obtain ⟨e, he, -⟩ := this
          exact ⟨e, he⟩
        · rintro ⟨e, he⟩
          obtain ⟨eh, heh, e3, he3, -⟩ :=
            (hoistMatches_correct g S ms (u :: A) hSAu hordAu hscMs hwnMs husedMs
              i true (env1.bind u f) (env2.bind u f) hagUF [] (by simp) []).mp ⟨e, he, rfl⟩
          have hehC : eh ∈ evalMatches g (env2.bind u f) headMs := by rw [hgenM] at heh; exact heh
          obtain ⟨eh', heh', hagEh'⟩ :=
            hoistMatches_head_irrel S A i true ms (by rw [hgenM]; exact hGscoped) u hun f env2 eh heh
          rw [hgenM] at he3
          simp only at he3
          have hAgreeUB' : Agree (A ++ headMs.map (·.unknown.name)) eh eh' := by
            rw [hgenM] at hagEh'; exact hagEh'
          have hAgreeMs' : Agree (u :: (A ++ headMs.map (·.unknown.name))) eh (eh'.bind u f) := by
            intro x hx0
            rcases List.mem_cons.mp hx0 with heq | hxA
            · have hehu : eh u = some f := by
                rw [evalMatches_frame hehC u hunHeadMs]
                simp [Env.bind]
              rw [heq]
              simp [Env.bind, hehu]
            · have hxu : x ≠ u := by
                intro heq2
                rcases List.mem_append.mp hxA with hxA' | hxA'
                · rw [heq2] at hxA'; exact hun hxA'
                · rw [heq2] at hxA'; exact hunHeadMs hxA'
              rw [Env.bind, if_neg hxu]
              exact hAgreeUB' x hxA
          obtain ⟨e3', he3', -⟩ :=
            evalMatches_agree g ms' (u :: (A ++ headMs.map (·.unknown.name)))
              eh (eh'.bind u f) hScopedMs' hAgreeMs' e3 he3
          have heh'C : eh' ∈ evalMatches g env2 headMs := by rw [hgenM] at heh'; exact heh'
          exact ⟨eh', heh'C, by rw [hChar (eh'.bind u f) ms']; exact ⟨e3', he3'⟩⟩
      · have hidNeg : (pos && expect) = false := by
          cases h : (pos && expect) with
          | false => rfl
          | true => exact absurd h hnewpos
        have hFalseId : hoistMatches S i (pos && expect) ms = (i, [], ms) := by
          rw [hidNeg]; exact hoistMatches_false_id S i ms
        have hEq : (i1, headMs, ms') = (i, ([] : List Match), ms) := hgenM.symm.trans hFalseId
        simp only [Prod.mk.injEq] at hEq
        obtain ⟨-, hheadMs, hms'⟩ := hEq
        rw [hheadMs, hms']
        show ((∃ eh ∈ evalMatches g env2 [], holds g (eh.bind u f) u (.existential expect ms) = true)
            ↔ holds g (env1.bind u f) u (.existential expect ms) = true)
        rw [holds_agree g (.existential expect ms) u A (env1.bind u f) (env2.bind u f) hsc (hag.bind u f)]
        simp [evalMatches]

  theorem hoistConditions_correct (g : Graph) (S : List Name) (u : Name) (f : FactId) :
      ∀ (cs : List Condition) (A : List Name), (∀ x ∈ S, x ∈ A) → (∀ x ∈ A, isReserved x = false) →
        u ∉ A → isReserved u = false →
        ScopedConditions (u :: A) A cs → WellNamedConditions (u :: A) cs →
        (∀ x ∈ usedInConditions cs, isReserved x = false) →
        ∀ (i : Nat) (pos : Bool) (env1 env2 : Env), Agree A env1 env2 →
          ((∃ eh ∈ evalMatches g env2 (hoistConditions S i pos cs).2.1,
              allHold g (eh.bind u f) u (hoistConditions S i pos cs).2.2 = true)
            ↔ allHold g (env1.bind u f) u cs = true)
    | [], A, hSA, hordA, hun, hordU, hsc, hwn, hused, i, pos, env1, env2, hag => by
      show ((∃ eh ∈ evalMatches g env2 [], allHold g (eh.bind u f) u [] = true) ↔
        allHold g (env1.bind u f) u [] = true)
      simp [evalMatches, allHold]
    | c :: cs, A, hSA, hordA, hun, hordU, hsc, hwn, hused, i, pos, env1, env2, hag => by
      obtain ⟨hc0, hcs⟩ : ScopedCondition (u :: A) A c ∧ ScopedConditions (u :: A) A cs := hsc
      obtain ⟨hwnc, hwncs⟩ : WellNamedCondition (u :: A) c ∧ WellNamedConditions (u :: A) cs := hwn
      have husedC : ∀ x ∈ usedInCondition c, isReserved x = false :=
        fun x hx => hused x (by simp [usedInConditions, hx])
      have husedCs : ∀ x ∈ usedInConditions cs, isReserved x = false :=
        fun x hx => hused x (by simp [usedInConditions, hx])
      rcases hgenc : hoistCondition S i pos c with ⟨i1, headC, c'⟩
      rcases hgencs : hoistConditions S i1 pos cs with ⟨i2, headCs, cs'⟩
      have heq1 : (hoistConditions S i pos (c :: cs)).2.1 = headC ++ headCs := by
        show (hoistConditions S i pos (c :: cs)).2.1 = _
        unfold hoistConditions; simp [hgenc, hgencs]
      have heq2 : (hoistConditions S i pos (c :: cs)).2.2 = c' :: cs' := by
        show (hoistConditions S i pos (c :: cs)).2.2 = _
        unfold hoistConditions; simp [hgenc, hgencs]
      rw [heq1, heq2]
      -- `headC` and `headCs` bind disjoint split labels.
      have hIdxDisjoint : ∀ x ∈ headC.map (·.unknown.name), x ∉ headCs.map (·.unknown.name) :=
        hoistIndex_disjoint
          (fun m hm => by
            obtain ⟨j, -, hj2, hn⟩ := hoistCondition_index S i pos c m (by rw [hgenc]; exact hm)
            rw [hgenc] at hj2; simp only at hj2; exact ⟨j, hj2, hn⟩)
          (fun m hm => by
            obtain ⟨j, hj1, -, hn⟩ := hoistConditions_index S i1 pos cs m (by rw [hgencs]; exact hm)
            exact ⟨j, hj1, hn⟩)
      have hScopedCs' : ScopedCondition (u :: (A ++ headC.map (·.unknown.name)))
          (A ++ headC.map (·.unknown.name)) c' := by
        have h := hoistCondition_scoped S c (u :: A) A hc0 i pos
        rw [hgenc] at h; simp only at h
        simpa [List.cons_append] using h
      have hAgreeSplit : ∀ (ehc eh : Env), eh ∈ evalMatches g ehc headCs →
          Agree (A ++ headC.map (·.unknown.name)) ehc eh := by
        intro ehc eh heh' x hx
        symm
        apply evalMatches_frame heh'
        intro hxCs
        simp only [List.mem_append] at hx
        rcases hx with hx | hx
        · obtain ⟨mCs, hmCs, hmCsn⟩ := List.mem_map.mp hxCs
          have hres := hoistConditions_reserved S i1 pos cs mCs (by rw [hgencs]; exact hmCs)
          rw [hmCsn, hordA x hx] at hres
          exact absurd hres (by simp)
        · exact hIdxDisjoint x hx hxCs
      constructor
      · rintro ⟨eh, heh, hall⟩
        obtain ⟨ehc, hehc, heh'⟩ := mem_evalMatches_append.mp heh
        have hall' : holds g (eh.bind u f) u c' = true ∧ allHold g (eh.bind u f) u cs' = true := by
          simpa [allHold, Bool.and_eq_true] using hall
        have hc' : holds g (ehc.bind u f) u c' = true := by
          rw [holds_agree g c' u (A ++ headC.map (·.unknown.name)) (ehc.bind u f) (eh.bind u f)
            hScopedCs' ((hAgreeSplit ehc eh heh').bind u f)]
          exact hall'.1
        have hehcP : ehc ∈ evalMatches g env2 (hoistCondition S i pos c).2.1 := by
          rw [hgenc]; exact hehc
        have hHold := (hoistCondition_correct g S u f c A hSA hordA hun hordU hc0 hwnc husedC
          i pos env1 env2 hag).mp ⟨ehc, hehcP, by rw [hgenc]; simp only; exact hc'⟩
        have hAgreeEnv1 : Agree A env1 ehc := hoistCondition_agree A hordA S i pos c env1 env2 hag ehc hehcP
        have hCS := (hoistConditions_correct g S u f cs A hSA hordA hun hordU hcs hwncs husedCs
          i1 pos env1 ehc hAgreeEnv1).mp ⟨eh, by rw [hgencs]; exact heh', by
            rw [hgencs]; simp only; exact hall'.2⟩
        simp [allHold, hHold, hCS]
      · intro h
        have hall : holds g (env1.bind u f) u c = true ∧ allHold g (env1.bind u f) u cs = true := by
          simpa [allHold, Bool.and_eq_true] using h
        obtain ⟨ehc, hehcP, hc'P⟩ :=
          (hoistCondition_correct g S u f c A hSA hordA hun hordU hc0 hwnc husedC
            i pos env1 env2 hag).mpr hall.1
        have hehc : ehc ∈ evalMatches g env2 headC := by rw [hgenc] at hehcP; exact hehcP
        have hc' : holds g (ehc.bind u f) u c' = true := by rw [hgenc] at hc'P; exact hc'P
        have hAgreeEnv1 : Agree A env1 ehc := hoistCondition_agree A hordA S i pos c env1 env2 hag ehc hehcP
        obtain ⟨eh, hehP, hcs'P⟩ :=
          (hoistConditions_correct g S u f cs A hSA hordA hun hordU hcs hwncs husedCs
            i1 pos env1 ehc hAgreeEnv1).mpr hall.2
        have heh' : eh ∈ evalMatches g ehc headCs := by rw [hgencs] at hehP; exact hehP
        have hcs' : allHold g (eh.bind u f) u cs' = true := by rw [hgencs] at hcs'P; exact hcs'P
        refine ⟨eh, mem_evalMatches_append.mpr ⟨ehc, hehc, heh'⟩, ?_⟩
        have hc'' : holds g (eh.bind u f) u c' = true := by
          rw [← holds_agree g c' u (A ++ headC.map (·.unknown.name)) (ehc.bind u f) (eh.bind u f)
            hScopedCs' ((hAgreeSplit ehc eh heh').bind u f)]
          exact hc'
        simp [allHold, hc'', hcs']

  theorem hoistMatches_correct (g : Graph) (S : List Name) :
      ∀ (ms : List Match) (A : List Name), (∀ x ∈ S, x ∈ A) → (∀ x ∈ A, isReserved x = false) →
        ScopedMatches A ms → WellNamedMatches A ms → (∀ x ∈ usedInMatches ms, isReserved x = false) →
        ∀ (i : Nat) (pos : Bool) (e1 e2 : Env), Agree A e1 e2 →
          ∀ (L : List Name), (∀ x ∈ L, x ∈ A ++ ms.map (·.unknown.name)) → ∀ (r : List (Option FactId)),
            ((∃ e ∈ evalMatches g e1 ms, L.map e = r) ↔
              (∃ eh ∈ evalMatches g e2 (hoistMatches S i pos ms).2.1,
                ∃ e3 ∈ evalMatches g eh (hoistMatches S i pos ms).2.2, L.map e3 = r))
    | [], A, hSA, hordA, hsc, hwn, hused, i, pos, e1, e2, hag, L, hL, r => by
      show ((∃ e ∈ evalMatches g e1 [], L.map e = r) ↔ (∃ eh ∈ evalMatches g e2 [], ∃ e3 ∈ evalMatches g eh [], L.map e3 = r))
      have hLA : ∀ x ∈ L, x ∈ A := by simpa using hL
      have hmap : L.map e1 = L.map e2 := (hag.mono hLA).map
      simp only [evalMatches, List.mem_singleton, exists_eq_left]
      rw [hmap]
    | .mk u cs :: rest, A, hSA, hordA, hsc, hwn, hused, i, pos, e1, e2, hag, L, hL, r => by
      obtain ⟨hcs, hrest⟩ : ScopedConditions (u.name :: A) A cs ∧ ScopedMatches (u.name :: A) rest := hsc
      obtain ⟨hun, hordU, hwncs, hwnrest⟩ :
          u.name ∉ A ∧ isReserved u.name = false ∧ WellNamedConditions (u.name :: A) cs ∧
            WellNamedMatches (u.name :: A) rest := hwn
      have husedCs : ∀ x ∈ usedInConditions cs, isReserved x = false :=
        fun x hx => hused x (by simp [usedInMatches, hx])
      have husedRest : ∀ x ∈ usedInMatches rest, isReserved x = false :=
        fun x hx => hused x (by simp [usedInMatches, hx])
      rcases hgenC : hoistConditions S i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches S i1 pos rest with ⟨i2, headRest, rest'⟩
      have heq1 : (hoistMatches S i pos (.mk u cs :: rest)).2.1 = headCs ++ headRest := by
        show (hoistMatches S i pos (.mk u cs :: rest)).2.1 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      have heq2 : (hoistMatches S i pos (.mk u cs :: rest)).2.2 = .mk u cs' :: rest' := by
        show (hoistMatches S i pos (.mk u cs :: rest)).2.2 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      rw [heq1, heq2]
      have hSAu : ∀ x ∈ S, x ∈ u.name :: A := fun x hx => List.mem_cons_of_mem _ (hSA x hx)
      have hordAu : ∀ x ∈ u.name :: A, isReserved x = false := by
        intro x hx; rcases List.mem_cons.mp hx with rfl | hx
        · exact hordU
        · exact hordA x hx
      have hLrest : ∀ x ∈ L, x ∈ (u.name :: A) ++ rest.map (·.unknown.name) := by
        intro x hx
        have hmem := hL x hx
        simp only [List.mem_append, List.map_cons, List.mem_cons, Match.unknown_mk] at hmem
        simp only [List.mem_append, List.mem_cons]
        rcases hmem with hmem | hmem | hmem
        · exact Or.inl (Or.inr hmem)
        · exact Or.inl (Or.inl hmem)
        · exact Or.inr hmem
      -- `headCs` and `headRest` bind disjoint split labels.
      have hIdxDisjoint : ∀ x ∈ headCs.map (·.unknown.name), x ∉ headRest.map (·.unknown.name) :=
        hoistIndex_disjoint
          (fun m hm => by
            obtain ⟨j, -, hj2, hn⟩ := hoistConditions_index S i pos cs m (by rw [hgenC]; exact hm)
            rw [hgenC] at hj2; simp only at hj2; exact ⟨j, hj2, hn⟩)
          (fun m hm => by
            obtain ⟨j, hj1, -, hn⟩ := hoistMatches_index S i1 pos rest m (by rw [hgenM]; exact hm)
            exact ⟨j, hj1, hn⟩)
      have hGscopedRest : ScopedMatches A headRest := by
        have h := hoistMatches_head_scoped S i1 pos rest
        rw [hgenM] at h; simp only at h
        exact scopedMatches_mono headRest S A hSA h
      have hScopedCs' : ScopedConditions (u.name :: (A ++ headCs.map (·.unknown.name)))
          (A ++ headCs.map (·.unknown.name)) cs' := by
        have h := hoistConditions_scoped S cs (u.name :: A) A hcs i pos
        rw [hgenC] at h; simp only at h
        simpa [List.cons_append] using h
      have hScopedRest' : ScopedMatches (u.name :: (A ++ headRest.map (·.unknown.name))) rest' := by
        have h := hoistMatches_scoped S rest (u.name :: A) hrest i1 pos
        rw [hgenM] at h; simp only at h
        simpa [List.cons_append] using h
      -- Per candidate fact `f` for `u`.
      have hf : ∀ f : Fact,
          (allHold g (e1.bind u.name f.id) u.name cs = true ∧
            ∃ e2' ∈ evalMatches g (e1.bind u.name f.id) rest, L.map e2' = r) ↔
          (∃ eh ∈ evalMatches g e2 (headCs ++ headRest),
            allHold g (eh.bind u.name f.id) u.name cs' = true ∧
            ∃ e3 ∈ evalMatches g (eh.bind u.name f.id) rest', L.map e3 = r) := by
        intro f
        have hCS := hoistConditions_correct g S u.name f.id cs A hSA hordA hun hordU hcs hwncs husedCs
          i pos e1 e2 hag
        rw [hgenC] at hCS
        simp only at hCS
        have hunHeadRest : u.name ∉ headRest.map (·.unknown.name) := by
          intro hmem
          obtain ⟨mR, hmR, hmRn⟩ := List.mem_map.mp hmem
          have hres := hoistMatches_reserved S i1 pos rest mR (by rw [hgenM]; exact hmR)
          rw [hmRn, hordU] at hres
          exact absurd hres (by simp)
        -- `headCs` binds only reserved names disjoint from `headRest`'s own
        -- (`hIdxDisjoint`), so running `headRest` from any `eh1` (in place of
        -- `e2`) never disturbs what `headCs` bound.
        have h1 : ∀ (eh1 eh' : Env), eh' ∈ evalMatches g eh1 headRest →
            Agree (A ++ headCs.map (·.unknown.name)) eh1 eh' := by
          intro eh1 eh' heh' x hx
          symm
          apply evalMatches_frame heh'
          intro hxR
          simp only [List.mem_append] at hx
          rcases hx with hx | hx
          · obtain ⟨mR, hmR, hmRn⟩ := List.mem_map.mp hxR
            have hres := hoistMatches_reserved S i1 pos rest mR (by rw [hgenM]; exact hmR)
            rw [hmRn, hordA x hx] at hres
            exact absurd hres (by simp)
          · exact hIdxDisjoint x hx hxR
        -- Binding `u` before or after running `headRest` makes no difference:
        -- `headRest` never refers to `u`.
        have h2 : ∀ (eh1 ehR eh' : Env), Agree (A ++ headRest.map (·.unknown.name)) ehR eh' →
            ehR ∈ evalMatches g (eh1.bind u.name f.id) headRest →
            Agree (u.name :: (A ++ headRest.map (·.unknown.name))) ehR (eh'.bind u.name f.id) := by
          intro eh1 ehR eh' hagEhR' hehR
          have hehRu : ehR u.name = some f.id := by
            rw [evalMatches_frame hehR u.name hunHeadRest]
            simp [Env.bind]
          have hEq : ehR.bind u.name f.id = ehR := by
            funext y
            by_cases hy : y = u.name
            · simp [Env.bind, hy, hehRu]
            · simp [Env.bind, hy]
          have := hagEhR'.bind u.name f.id
          rwa [hEq] at this
        have hLsub : ∀ x ∈ L, x ∈ u.name :: (A ++ headRest.map (·.unknown.name)) ++ rest'.map (·.unknown.name) := by
          intro x hx
          have hmem := hLrest x hx
          rw [List.mem_append, List.mem_cons] at hmem
          have hrest'eq : rest'.map (·.unknown.name) = rest.map (·.unknown.name) := by
            have h := hoistMatches_unknowns S i1 pos rest
            rw [hgenM] at h
            simpa using h
          rw [List.mem_append, List.mem_cons, List.mem_append, hrest'eq]
          rcases hmem with (rfl | hA) | hRest
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr (Or.inl hA))
          · exact Or.inr hRest
        constructor
        · rintro ⟨hc, e2', he2', hLr⟩
          obtain ⟨eh1, heh1, hcs'⟩ := hCS.mpr hc
          have hagEh1 : Agree A e1 eh1 :=
            hoistConditions_agree A hordA S i pos cs e1 e2 hag eh1 (by rw [hgenC]; exact heh1)
          have hagRest : Agree (u.name :: A) (e1.bind u.name f.id) (eh1.bind u.name f.id) :=
            hagEh1.bind u.name f.id
          obtain ⟨ehR, hehR, e3, he3, hLr3⟩ :=
            (hoistMatches_correct g S rest (u.name :: A) hSAu hordAu hrest hwnrest husedRest
              i1 pos (e1.bind u.name f.id) (eh1.bind u.name f.id) hagRest L hLrest r).mp ⟨e2', he2', hLr⟩
          obtain ⟨eh', heh', hagEh'⟩ :=
            hoistMatches_head_irrel S A i1 pos rest (by rw [hgenM]; exact hGscopedRest)
              u.name hun f.id eh1 ehR hehR
          rw [hgenM] at he3 heh' hagEh' hehR
          simp only at he3 heh' hagEh' hehR
          refine ⟨eh', mem_evalMatches_append.mpr ⟨eh1, heh1, heh'⟩, ?_, ?_⟩
          · rw [allHold_agree g cs' u.name (A ++ headCs.map (·.unknown.name))
              (eh1.bind u.name f.id) (eh'.bind u.name f.id) hScopedCs'
              ((h1 eh1 eh' heh').bind u.name f.id)] at hcs'
            exact hcs'
          · obtain ⟨e3', he3', hagE3⟩ :=
              evalMatches_agree g rest' (u.name :: (A ++ headRest.map (·.unknown.name)))
                ehR (eh'.bind u.name f.id) hScopedRest' (h2 eh1 ehR eh' hagEh' hehR) e3 he3
            exact ⟨e3', he3', by rw [← hLr3, (hagE3.mono hLsub).map]⟩
        · rintro ⟨eh, heh, hcs', e3, he3, hLr⟩
          obtain ⟨eh1, heh1, heh'⟩ := mem_evalMatches_append.mp heh
          have hagEh1 : Agree A e1 eh1 :=
            hoistConditions_agree A hordA S i pos cs e1 e2 hag eh1 (by rw [hgenC]; exact heh1)
          have hagRest : Agree (u.name :: A) (e1.bind u.name f.id) (eh1.bind u.name f.id) :=
            hagEh1.bind u.name f.id
          have hc : allHold g (e1.bind u.name f.id) u.name cs = true := by
            apply hCS.mp
            refine ⟨eh1, heh1, ?_⟩
            rw [allHold_agree g cs' u.name (A ++ headCs.map (·.unknown.name))
              (eh1.bind u.name f.id) (eh.bind u.name f.id) hScopedCs' ((h1 eh1 eh heh').bind u.name f.id)]
            exact hcs'
          have hAgreeUB : Agree A eh1 (eh1.bind u.name f.id) := by
            intro x hx
            have hxn : x ≠ u.name := fun h => hun (h ▸ hx)
            simp [Env.bind, hxn]
          obtain ⟨ehR, hehR, hagUB⟩ :=
            evalMatches_agree g headRest A eh1 (eh1.bind u.name f.id) hGscopedRest hAgreeUB eh heh'
          have hAgreeRest' : Agree (u.name :: (A ++ headRest.map (·.unknown.name))) (eh.bind u.name f.id) ehR := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · have hehRu : ehR u.name = some f.id := by
                rw [evalMatches_frame hehR u.name hunHeadRest]
                simp [Env.bind]
              simp [Env.bind, hehRu]
            · simp only [Env.bind]
              have hxn : x ≠ u.name := by
                rintro rfl
                simp only [List.mem_append] at hx
                rcases hx with hx | hx
                · exact hun hx
                · exact hunHeadRest hx
              rw [if_neg hxn]
              exact hagUB x hx
          obtain ⟨e3', he3', hagE3⟩ :=
            evalMatches_agree g rest' (u.name :: (A ++ headRest.map (·.unknown.name)))
              (eh.bind u.name f.id) ehR hScopedRest' hAgreeRest' e3 he3
          obtain ⟨e2', he2', hLr2⟩ :=
            (hoistMatches_correct g S rest (u.name :: A) hSAu hordAu hrest hwnrest husedRest
              i1 pos (e1.bind u.name f.id) (eh1.bind u.name f.id) hagRest L hLrest r).mpr
              ⟨ehR, by rw [hgenM]; exact hehR, e3', by rw [hgenM]; exact he3',
                by rw [← hLr, (hagE3.mono hLsub).map]⟩
          exact ⟨hc, e2', he2', hLr2⟩
      constructor
      · rintro ⟨e, he, hLr⟩
        obtain ⟨f, hf', hty, hc, he2'⟩ := mem_evalMatches_cons.mp he
        obtain ⟨eh, heh, hcs', e3, he3, hLr3⟩ := (hf f).mp ⟨hc, e, he2', hLr⟩
        exact ⟨eh, heh, e3, mem_evalMatches_cons.mpr ⟨f, hf', hty, hcs', he3⟩, hLr3⟩
      · rintro ⟨eh, heh, e3, he3, hLr⟩
        obtain ⟨f, hf', hty, hcs', he3'⟩ := mem_evalMatches_cons.mp he3
        obtain ⟨hc, e2', he2', hLr2⟩ := (hf f).mpr ⟨eh, heh, hcs', e3, he3', hLr⟩
        exact ⟨e2', mem_evalMatches_cons.mpr ⟨f, hf', hty, hc, he2'⟩, hLr2⟩
end

/-! ## Assembling the split's correctness -/

section Pivot

variable {s : Specification} {before after : List Match} {pivot : Match}

/-- The derivation of the tail's givens is closed: every path condition the
tail's matches name, at any depth, joins a label that is one of the tail's
givens or is declared earlier in it, and so does every label the projection
names — using `hoistMatches_scoped` to reach every depth at once, rather than
only the pivot's own top level. -/
theorem hoist_tail_scoped (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after)
    (n : Nat) (hm tailMatches : List Match)
    (hgenM : hoistMatches (scopeAt s before) 0 true (pivot :: after) = (n, hm, tailMatches)) :
    ScopedMatches ((tailGivenAt s (before ++ hm) tailMatches).map (·.name)) tailMatches ∧
      ∀ x ∈ s.projection.labels,
        x ∈ (tailGivenAt s (before ++ hm) tailMatches).map (·.name) ∨
        x ∈ tailMatches.map (·.unknown.name) := by
  have h1 := hwf.inScope
  rw [hs, scopedMatches_append] at h1
  obtain ⟨-, h2⟩ := h1
  have hScoped := hoistMatches_scoped (scopeAt s before) (pivot :: after) (scopeAt s before) h2 0 true
  rw [hgenM] at hScoped
  simp only at hScoped
  have hUnk : tailMatches.map (·.unknown.name) = (pivot :: after).map (·.unknown.name) := by
    have h := hoistMatches_unknowns (scopeAt s before) 0 true (pivot :: after)
    rw [hgenM] at h
    simpa using h
  have hgivenMem : ∀ x, x ∈ (tailGivenAt s (before ++ hm) tailMatches).map (·.name) ↔
      x ∈ (s.given ++ (before ++ hm).map (·.unknown)).map (·.name) ∧
        x ∈ usedInMatches tailMatches ++ s.projection.labels := by
    intro x
    simp only [tailGivenAt, List.mem_map, List.mem_filter, List.contains_iff_mem]
    constructor
    · rintro ⟨l, ⟨hl, hu⟩, rfl⟩
      exact ⟨⟨l, hl, rfl⟩, hu⟩
    · rintro ⟨⟨l, hl, rfl⟩, hu⟩
      exact ⟨l, ⟨hl, hu⟩, rfl⟩
  have hMemAll : ∀ x ∈ scopeAt s before ++ hm.map (·.unknown.name),
      x ∈ (s.given ++ (before ++ hm).map (·.unknown)).map (·.name) := by
    intro x hx
    simp only [List.mem_append, List.map_append, List.map_map] at hx ⊢
    rcases hx with hx | hx
    · unfold scopeAt at hx
      rw [mem_scopeAfter] at hx
      rcases hx with hx | hx
      · exact Or.inr (Or.inl (by simpa [Function.comp_def] using hx))
      · exact Or.inl (by simpa using hx)
    · exact Or.inr (Or.inr (by simpa [Function.comp_def] using hx))
  refine ⟨scopedMatches_shrink tailMatches _ _ hScoped ?_, ?_⟩
  · intro x hx hxA
    rw [hgivenMem]
    exact ⟨hMemAll x hxA, by simp [hx]⟩
  · intro x hx
    rcases pivot_scoped hwf hs x hx with hproj | hproj
    · exact Or.inl (by rw [hgivenMem]; exact ⟨hMemAll x (List.mem_append_left _ hproj), by simp [hx]⟩)
    · exact Or.inr (hUnk ▸ hproj)

/-- Solving the pivot and everything after it from `e` is the same as
hoisting every eligible path condition into the head, at any depth, then
solving the tail from the tail's givens alone. -/
theorem hoist_step (hwf : WellFormed s) (hs : s.matchList = before ++ pivot :: after)
    (n : Nat) (hm tailMatches : List Match)
    (hgenM : hoistMatches (scopeAt s before) 0 true (pivot :: after) = (n, hm, tailMatches))
    (g : Graph) (e : Env) (r : List (Option FactId)) :
    (∃ e2 ∈ evalMatches g e (pivot :: after), s.projection.labels.map e2 = r) ↔
    (∃ e' ∈ evalMatches g e hm,
      ∃ e3 ∈ evalMatches g
          (e'.restrictTo ((tailGivenAt s (before ++ hm) tailMatches).map (·.name)))
          tailMatches,
        s.projection.labels.map e3 = r) := by
  have h1 := hwf.inScope
  rw [hs, scopedMatches_append] at h1
  obtain ⟨-, h2⟩ := h1
  have hwn1 := hwf.wellNamed
  rw [hs, wellNamedMatches_append] at hwn1
  obtain ⟨-, hwn2⟩ := hwn1
  have hordScope : ∀ x ∈ scopeAt s before, isReserved x = false := scopeAt_ordinary hwf hs
  have hused := usedInMatches_ordinary (pivot :: after) (scopeAt s before) h2 hwn2 hordScope
  have hLproj : ∀ x ∈ s.projection.labels,
      x ∈ scopeAt s before ++ (pivot :: after).map (·.unknown.name) := by
    intro x hx
    simpa using pivot_scoped hwf hs x hx
  have hMain := hoistMatches_correct g (scopeAt s before) (pivot :: after) (scopeAt s before)
    (fun _ hx => hx) hordScope h2 hwn2 hused 0 true e e (fun _ hx => rfl)
    s.projection.labels hLproj r
  rw [hgenM] at hMain
  simp only at hMain
  rw [hMain]
  obtain ⟨hTscoped, hTproj⟩ := hoist_tail_scoped hwf hs n hm tailMatches hgenM
  have hTproj' : ∀ x ∈ s.projection.labels,
      x ∈ (tailGivenAt s (before ++ hm) tailMatches).map (·.name) ++ tailMatches.map (·.unknown.name) := by
    intro x hx
    simpa using hTproj x hx
  constructor
  · rintro ⟨e', he', e3, he3, hr⟩
    exact ⟨e', he', (exists_projection_iff hTscoped
      (Env.restrictTo_agree ((tailGivenAt s (before ++ hm) tailMatches).map (·.name)) e')
      hTproj' r).mpr ⟨e3, he3, hr⟩⟩
  · rintro ⟨e', he', e3, he3, hr⟩
    exact ⟨e', he', (exists_projection_iff hTscoped
      (Env.restrictTo_agree ((tailGivenAt s (before ++ hm) tailMatches).map (·.name)) e')
      hTproj' r).mp ⟨e3, he3, hr⟩⟩

end Pivot

/-- The split preserves the meaning of a well-formed specification. -/
theorem split_correct (s : Specification) (hwf : WellFormed s) (g : Graph) (env : Env)
    (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluate g env ↔ r ∈ s.evaluate g env := by
  unfold splitBeforeFirstSuccessor
  generalize hspan : s.matchList.span matchIsDeterministic = sp
  obtain ⟨before, rest⟩ := sp
  cases rest with
  | nil =>
    simp [Split.evaluate]
  | cons pivot after =>
    have hs : s.matchList = before ++ pivot :: after := by
      have h := span_loop_append matchIsDeterministic s.matchList []
      unfold List.span at hspan
      rw [hspan] at h
      simpa using h.symm
    have hlhs : r ∈ s.evaluate g env ↔
        ∃ e2 ∈ evalMatches g env (before ++ pivot :: after), s.projection.labels.map e2 = r := by
      unfold Specification.evaluate
      rw [hs, List.mem_map]
    unfold hoistAt
    rcases hgenM : hoistMatches (scopeAt s before) 0 true (pivot :: after) with ⟨n, hm, tailMatches⟩
    simp only [hgenM]
    rw [hlhs]
    simp only [Split.evaluate, Specification.evaluate]
    rw [List.mem_flatMap]
    simp only [List.mem_map, mem_evalMatches_append]
    constructor
    · rintro ⟨tuple, ⟨e, he, he'⟩, e3, he3, hr⟩
      obtain ⟨e2, he2, hr2⟩ := (hoist_step hwf hs n hm tailMatches hgenM g e r).mpr ⟨tuple, he', e3, he3, hr⟩
      exact ⟨e2, ⟨e, he, he2⟩, hr2⟩
    · rintro ⟨e2, ⟨e, he, he2⟩, hr⟩
      obtain ⟨tuple, ht, e3, he3, hr3⟩ := (hoist_step hwf hs n hm tailMatches hgenM g e r).mp ⟨e2, he2, hr⟩
      exact ⟨tuple, ⟨e, he, ht⟩, e3, he3, hr3⟩

end JinagaSpec
