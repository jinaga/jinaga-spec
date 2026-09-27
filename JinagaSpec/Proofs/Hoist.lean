import JinagaSpec.Hoist
import JinagaSpec.Proofs.Main

/-!
# `hoist` agrees with the reference semantics, in a reduced scope

`hoist_correct` in full generality needs the polarity argument sketched in
`docs/findings.md`: hoisting a condition out of a positive existential and into
the head does not change whether the existential has a solution, because an
existential over a union is the union of the existentials, and the head's
enumeration of a hoisted label is exactly such a union. That argument is not
proved here.

What is proved is the base case the general argument reduces to: a
specification where nothing hoistable sits below the pivot's own top level,
*and* every one of the pivot's own top-level path conditions is itself
hoistable (`ReducedHoistScope`). The second conjunct is not needed for
soundness; it is needed only so that `hoist`'s split-label numbering, which
(unlike `splitPaths`) advances only when a condition is actually hoisted,
lines up exactly with `splitPaths`' own numbering, which advances once per
top-level path condition regardless. Under both, `hoist` and
`splitBeforeFirstSuccessor` compute the same split, up to the order of the
pivot's own conditions (which `allHold` and `tailGivenAt` cannot tell apart),
so `hoist_correct` reduces to `split_correct`.

This covers a pivot whose own top-level path conditions are all hoistable
(`predecessor-and-successor-in-one-match`, `existential-on-the-pivot`,
`several-paths-each-walk-predecessors`, `projected-label-reaches-the-tail`) or
has none to hoist at all, and every specification with no pivot at all. It
does not cover a pivot with a *mix* of hoistable and non-hoistable top-level
conditions (most of the remaining named cases), where the numbering mismatch
above means `hoist` and `splitPaths` pick different, merely differently-named,
split labels; nor formulation D, where something below the top level is
genuinely hoisted. Both remain correct, by the randomized check
(`Check.lean`), but not proved here. -/
namespace JinagaSpec

mutual
  /-- Nothing in `ms`, at any depth including its own top level, is eligible
  for hoisting: hoisting leaves it untouched. Used for the matches after the
  pivot, which the split never reaches into. -/
  def NoHoistMatches (scope : List Name) : List Match → Prop
    | [] => True
    | .mk _ cs :: rest => NoHoistConditions scope cs ∧ NoHoistMatches scope rest

  def NoHoistConditions (scope : List Name) : List Condition → Prop
    | [] => True
    | c :: cs => NoHoistCondition scope c ∧ NoHoistConditions scope cs

  def NoHoistCondition (scope : List Name) : Condition → Prop
    | .path pc => pc.rolesRight.getLast? = none ∨ scope.contains pc.labelRight = false
    | .existential _ ms => NoHoistMatches scope ms
end

/-- Nothing below the top level of `cs` is eligible for hoisting: every
existential condition's own matches are untouched. The top level itself may
still be hoisted, exactly as `splitPaths` already hoists it. -/
def NoDeepHoistCondition (scope : List Name) : Condition → Prop
  | .path _ => True
  | .existential _ ms => NoHoistMatches scope ms

def NoDeepHoistConditions (scope : List Name) : List Condition → Prop
  | [] => True
  | c :: cs => NoDeepHoistCondition scope c ∧ NoDeepHoistConditions scope cs

/-! ## Nothing eligible means hoisting does nothing -/

mutual
  theorem noHoist_matches_id {scope : List Name} :
      ∀ {ms : List Match}, NoHoistMatches scope ms → ∀ i pos, hoistMatches scope i pos ms = (i, [], ms)
    | [], _, _, _ => rfl
    | .mk u cs :: rest, h, i, pos => by
      obtain ⟨hcs, hrest⟩ : NoHoistConditions scope cs ∧ NoHoistMatches scope rest := h
      have h1 := noHoist_conditions_id hcs i pos
      have h2 := noHoist_matches_id hrest i pos
      calc hoistMatches scope i pos (.mk u cs :: rest)
          = (let (i1, headCs, cs') := hoistConditions scope i pos cs
             let (i2, headRest, rest') := hoistMatches scope i1 pos rest
             (i2, headCs ++ headRest, .mk u cs' :: rest')) := rfl
        _ = (i, [], .mk u cs :: rest) := by simp [h1, h2]

  theorem noHoist_conditions_id {scope : List Name} :
      ∀ {cs : List Condition}, NoHoistConditions scope cs → ∀ i pos, hoistConditions scope i pos cs = (i, [], cs)
    | [], _, _, _ => rfl
    | c :: cs, h, i, pos => by
      obtain ⟨hc, hcs⟩ : NoHoistCondition scope c ∧ NoHoistConditions scope cs := h
      have h1 := noHoist_condition_id hc i pos
      have h2 := noHoist_conditions_id hcs i pos
      calc hoistConditions scope i pos (c :: cs)
          = (let (i1, headC, c') := hoistCondition scope i pos c
             let (i2, headCs, cs') := hoistConditions scope i1 pos cs
             (i2, headC ++ headCs, c' :: cs')) := rfl
        _ = (i, [], c :: cs) := by simp [h1, h2]

  theorem noHoist_condition_id {scope : List Name} :
      ∀ {c : Condition}, NoHoistCondition scope c → ∀ i pos, hoistCondition scope i pos c = (i, [], c)
    | .path pc, h, i, pos => by
      show hoistCondition scope i pos (.path pc) = (i, [], .path pc)
      unfold hoistCondition
      rcases h with h | h
      · simp [h]
      · simp only [List.contains_eq_mem] at h
        simp [h]
    | .existential e ms, h, i, pos => by
      have h1 : NoHoistMatches scope ms := h
      have h2 := noHoist_matches_id h1 i (pos && e)
      calc hoistCondition scope i pos (.existential e ms)
          = (let (i1, headMs, ms') := hoistMatches scope i (pos && e) ms
             (i1, headMs, .existential e ms')) := rfl
        _ = (i, [], .existential e ms) := by simp only [h2]
end

/-! ## Where nothing is hoisted below the top level, `hoist` numbers exactly as
`splitPaths` does -/

/-- Every one of `ps` is itself eligible: `splitPaths`' index `i` and `hoist`'s
index (which only advances when something is actually hoisted) then advance
together, so the two agree on which split label numbers which condition. -/
def AllEligible (scope : List Name) (ps : List PathCondition) : Prop :=
  ∀ c ∈ ps, c.rolesRight.getLast? ≠ none ∧ scope.contains c.labelRight = true

private theorem pathsOf_cons_path {pc : PathCondition} {cs : List Condition} :
    pathsOf (.path pc :: cs) = pc :: pathsOf cs := rfl

private theorem pathsOf_cons_ex {e : Bool} {ms : List Match} {cs : List Condition} :
    pathsOf (.existential e ms :: cs) = pathsOf cs := rfl

private theorem existentialsOf_cons_path {pc : PathCondition} {cs : List Condition} :
    existentialsOf (.path pc :: cs) = existentialsOf cs := rfl

private theorem existentialsOf_cons_ex {e : Bool} {ms : List Match} {cs : List Condition} :
    existentialsOf (.existential e ms :: cs) = .existential e ms :: existentialsOf cs := rfl

private theorem pathsOf_map_path {tps : List PathCondition} : pathsOf (tps.map .path) = tps := by
  induction tps with
  | nil => rfl
  | cons t ts ih => simp [pathsOf_cons_path, ih]

private theorem existentialsOf_map_path {tps : List PathCondition} :
    existentialsOf (tps.map .path) = [] := by
  induction tps with
  | nil => rfl
  | cons t ts ih => simpa [existentialsOf_cons_path] using ih

private theorem pathsOf_append {cs1 cs2 : List Condition} :
    pathsOf (cs1 ++ cs2) = pathsOf cs1 ++ pathsOf cs2 := by
  simp [pathsOf, List.filterMap_append]

private theorem existentialsOf_append {cs1 cs2 : List Condition} :
    existentialsOf (cs1 ++ cs2) = existentialsOf cs1 ++ existentialsOf cs2 := by
  simp [existentialsOf, List.filter_append]

private theorem pathsOf_existentialsOf {cs : List Condition} : pathsOf (existentialsOf cs) = [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | path p => simpa [existentialsOf_cons_path] using ih
    | existential e ms => simpa [existentialsOf_cons_ex, pathsOf_cons_ex] using ih

private theorem existentialsOf_existentialsOf {cs : List Condition} :
    existentialsOf (existentialsOf cs) = existentialsOf cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | path p => simpa [existentialsOf_cons_path] using ih
    | existential e ms => simp [existentialsOf_cons_ex, ih]

private theorem hoistConditions_cons {scope : List Name} {c : Condition} {cs : List Condition}
    {i : Nat} {pos : Bool} :
    hoistConditions scope i pos (c :: cs) =
      (let (i1, headC, c') := hoistCondition scope i pos c
       let (i2, headCs, cs') := hoistConditions scope i1 pos cs
       (i2, headC ++ headCs, c' :: cs')) := rfl

theorem hoistConditions_eq_splitPaths {scope : List Name} :
    ∀ (cs : List Condition), NoDeepHoistConditions scope cs → AllEligible scope (pathsOf cs) →
      ∀ i, (hoistConditions scope i true cs).2.1 = (splitPaths i (pathsOf cs)).1 ∧
           pathsOf (hoistConditions scope i true cs).2.2 = (splitPaths i (pathsOf cs)).2 ∧
           existentialsOf (hoistConditions scope i true cs).2.2 = existentialsOf cs
  | [], _, _, _ => by simp [hoistConditions, splitPaths, pathsOf, existentialsOf]
  | .path pc :: cs, hnd, hae, i => by
    obtain ⟨-, hndcs⟩ : NoDeepHoistCondition scope (.path pc) ∧ NoDeepHoistConditions scope cs := hnd
    have hpc : pc.rolesRight.getLast? ≠ none ∧ scope.contains pc.labelRight = true :=
      hae pc (pathsOf_cons_path ▸ List.mem_cons_self)
    have haecs : AllEligible scope (pathsOf cs) := fun c hc =>
      hae c (pathsOf_cons_path ▸ List.mem_cons_of_mem _ hc)
    obtain ⟨ih1, ih2, ih3⟩ := hoistConditions_eq_splitPaths cs hndcs haecs (i + 1)
    generalize hgen : hoistConditions scope (i + 1) true cs = res at ih1 ih2 ih3
    obtain ⟨i2, headCs, cs''⟩ := res
    generalize hgen2 : splitPaths (i + 1) (pathsOf cs) = res2 at ih1 ih2
    obtain ⟨sm2, tps2⟩ := res2
    simp only at ih1 ih2 ih3
    cases hlast : pc.rolesRight.getLast? with
    | none => exact absurd hlast hpc.1
    | some last =>
      have hc : hoistCondition scope i true (.path pc) =
          (i + 1,
           [.mk { name := splitLabel i, type := last.predecessorType }
               [.path { rolesLeft := [], labelRight := pc.labelRight, rolesRight := pc.rolesRight }]],
           .path { rolesLeft := pc.rolesLeft, labelRight := splitLabel i, rolesRight := [] }) := by
        show hoistCondition scope i true (.path pc) = _
        unfold hoistCondition
        simp only [List.contains_eq_mem] at hpc
        simp [hlast, hpc.2]
      have hs : splitPaths i (pathsOf (.path pc :: cs)) =
          (.mk { name := splitLabel i, type := last.predecessorType }
              [.path { rolesLeft := [], labelRight := pc.labelRight, rolesRight := pc.rolesRight }] :: sm2,
           { rolesLeft := pc.rolesLeft, labelRight := splitLabel i, rolesRight := [] } :: tps2) := by
        rw [pathsOf_cons_path]
        show splitPaths i (pc :: pathsOf cs) = _
        unfold splitPaths
        simp [hlast, hgen2]
      simp only [hoistConditions_cons, hc, hgen]
      refine ⟨?_, ?_, ?_⟩
      · simp [hs, ih1]
      · rw [hs]
        simp [pathsOf_cons_path, ih2]
      · simp only [existentialsOf_cons_path]
        exact ih3
  | .existential e ms :: cs, hnd, hae, i => by
    obtain ⟨hms, hndcs⟩ : NoHoistMatches scope ms ∧ NoDeepHoistConditions scope cs := hnd
    have haecs : AllEligible scope (pathsOf cs) := pathsOf_cons_ex ▸ hae
    obtain ⟨ih1, ih2, ih3⟩ := hoistConditions_eq_splitPaths cs hndcs haecs i
    have hc : hoistCondition scope i true (.existential e ms) = (i, [], .existential e ms) :=
      noHoist_condition_id (c := .existential e ms) hms i true
    simp only [hoistConditions_cons, hc]
    refine ⟨?_, ?_, ?_⟩
    · simpa [pathsOf_cons_ex] using ih1
    · simp only [pathsOf_cons_ex]
      simpa using ih2
    · simp only [existentialsOf_cons_ex]
      simpa using ih3

/-! ## The reduced-scope theorem -/

/-- A condition list's used labels are exactly its path conditions' and its
existential conditions' used labels, however they are interleaved: splitting a
condition list into its paths and its existentials (`SplitPaths.lean`,
`allHold_pathsOf_existentialsOf`) does not change which labels it uses either. -/
theorem usedInConditions_perm (cs : List Condition) :
    ∀ x, x ∈ usedInConditions cs ↔
      x ∈ (pathsOf cs).map (·.labelRight) ∨ x ∈ usedInConditions (existentialsOf cs) := by
  induction cs with
  | nil => intro x; simp [usedInConditions, pathsOf, existentialsOf]
  | cons c cs ih =>
    intro x
    cases c with
    | path pc =>
      simp only [usedInConditions, usedInCondition, pathsOf_cons_path, existentialsOf_cons_path,
        List.map_cons, List.mem_cons, List.mem_append]
      rw [ih x]
      grind
    | existential e ms =>
      simp only [usedInConditions, usedInCondition, pathsOf_cons_ex, existentialsOf_cons_ex,
        List.mem_append]
      rw [ih x]
      grind

/-- Two condition lists whose paths and whose existentials agree (as `hoist`'s
rewrite of the pivot's conditions and `splitPaths`' do, `hoistConditions_eq_splitPaths`)
use the same labels, whatever order the conditions themselves come in. -/
theorem usedInConditions_congr {cs1 cs2 : List Condition}
    (hp : pathsOf cs1 = pathsOf cs2) (he : existentialsOf cs1 = existentialsOf cs2) (x : Name) :
    x ∈ usedInConditions cs1 ↔ x ∈ usedInConditions cs2 := by
  rw [usedInConditions_perm cs1 x, usedInConditions_perm cs2 x, hp, he]

private theorem flatMap_congr' {l : List α} {g h : α → List β} (he : ∀ x ∈ l, g x = h x) :
    l.flatMap g = l.flatMap h := by
  simp only [List.flatMap_def]
  congr 1
  exact List.map_congr_left he

/-- Two condition lists with the same `allHold` value, for every environment,
give the same `evalMatches` on a match declaring them, whatever else follows. -/
theorem evalMatches_congr_allHold {g : Graph} {u : Label} {cs1 cs2 : List Condition}
    {rest : List Match} (h : ∀ env' : Env, allHold g env' u.name cs1 = allHold g env' u.name cs2)
    (env : Env) : evalMatches g env (.mk u cs1 :: rest) = evalMatches g env (.mk u cs2 :: rest) := by
  calc evalMatches g env (.mk u cs1 :: rest)
      = (g.filter (fun f => f.type == u.type)).flatMap (fun f =>
          let env' := env.bind u.name f.id
          if allHold g env' u.name cs1 = true then evalMatches g env' rest else []) := rfl
    _ = (g.filter (fun f => f.type == u.type)).flatMap (fun f =>
          let env' := env.bind u.name f.id
          if allHold g env' u.name cs2 = true then evalMatches g env' rest else []) := by
        apply flatMap_congr'
        intro f _
        simp only [h]
    _ = evalMatches g env (.mk u cs2 :: rest) := rfl

/-- `tailGivenAt` depends on its tail's matches only through which labels they
use, and using the same paths and the same existentials (in whatever order)
uses the same labels. -/
theorem tailGivenAt_congr (s : Specification) (hm : List Match) {u : Label} {cs1 cs2 : List Condition}
    {after : List Match} (hp : pathsOf cs1 = pathsOf cs2) (he : existentialsOf cs1 = existentialsOf cs2) :
    tailGivenAt s hm (.mk u cs1 :: after) = tailGivenAt s hm (.mk u cs2 :: after) := by
  have hmem : ∀ x, x ∈ usedInMatches (.mk u cs1 :: after) ↔ x ∈ usedInMatches (.mk u cs2 :: after) := by
    intro x
    show x ∈ usedInConditions cs1 ++ usedInMatches after ↔ x ∈ usedInConditions cs2 ++ usedInMatches after
    simp only [List.mem_append]
    rw [usedInConditions_congr hp he x]
  show (s.given ++ hm.map (·.unknown)).filter (fun l => (usedInMatches (.mk u cs1 :: after) ++
        s.projection.labels).contains l.name) =
      (s.given ++ hm.map (·.unknown)).filter (fun l => (usedInMatches (.mk u cs2 :: after) ++
        s.projection.labels).contains l.name)
  apply List.filter_congr
  intro l _
  have h1 : l.name ∈ usedInMatches (.mk u cs1 :: after) ++ s.projection.labels ↔
      l.name ∈ usedInMatches (.mk u cs2 :: after) ++ s.projection.labels := by
    simp only [List.mem_append, hmem]
  simp only [List.contains_eq_mem, decide_eq_decide]
  exact h1

/-- The two halves of `span` make up the list. -/
private theorem hoist_span_loop_append (p : Match → Bool) :
    ∀ (l acc : List Match), (List.span.loop p l acc).1 ++ (List.span.loop p l acc).2 = acc.reverse ++ l := by
  intro l
  induction l with
  | nil => intro acc; simp [List.span.loop]
  | cons a as ih =>
    intro acc
    simp only [List.span.loop]
    cases p a <;> simp [ih]

/-- The scope the reduced theorem is proved for: at the pivot, nothing below
its own top level is eligible for hoisting, and every one of its own top-level
path conditions is (so `hoist`'s numbering agrees with `splitPaths`'), and
nothing in the matches after the pivot is eligible either, matching that the
split never reaches into them. -/
def ReducedHoistScope (s : Specification) : Prop :=
  match s.matchList.span matchIsDeterministic with
  | (_, []) => True
  | (before, pivot :: after) =>
    NoDeepHoistConditions (scopeAt s before) pivot.conditions ∧
    AllEligible (scopeAt s before) (pathsOf pivot.conditions) ∧
    NoHoistMatches (scopeAt s before) after

/-- In its reduced scope, `hoist` means what the whole specification means: it
computes the same split as `splitBeforeFirstSuccessor`, up to the order of the
pivot's own conditions, which `allHold` and `tailGivenAt` cannot tell apart
(`hoistConditions_eq_splitPaths`, `evalMatches_congr_allHold`,
`tailGivenAt_congr`), so the claim reduces to `split_correct`. -/
theorem hoist_correct_reduced (s : Specification) (hwf : WellFormed s) (hr : ReducedHoistScope s)
    (g : Graph) (env : Env) (r : List (Option FactId)) :
    r ∈ (hoist s).evaluate g env ↔ r ∈ s.evaluate g env := by
  rw [← split_correct s hwf g env r]
  unfold ReducedHoistScope at hr
  unfold hoist splitBeforeFirstSuccessor
  rcases hspan : s.matchList.span matchIsDeterministic with ⟨before, rest⟩
  simp only [hspan] at hr
  cases rest with
  | nil => rfl
  | cons pivot after =>
    obtain ⟨hnd, hae, hna⟩ := hr
    obtain ⟨u, cs⟩ := pivot
    simp only [Match.conditions_mk] at hnd hae
    rcases hgenC : hoistConditions (scopeAt s before) 0 true cs with ⟨i1, sm, cs'⟩
    rcases hsp : splitPaths 0 (pathsOf cs) with ⟨sm2, tps⟩
    have hcorr := hoistConditions_eq_splitPaths cs hnd hae 0
    rw [hgenC, hsp] at hcorr
    simp only at hcorr
    obtain ⟨hc1, hc2, hc3⟩ := hcorr
    have hna' := noHoist_matches_id hna i1 true
    -- `hoist`'s tail keeps the pivot's conditions in their original,
    -- interleaved order; `splitAt`'s puts the rewritten paths first. Neither
    -- `allHold` nor `tailGivenAt` can tell the difference.
    have hp : tps = pathsOf (tps.map .path ++ existentialsOf cs) := by
      rw [pathsOf_append, pathsOf_map_path, pathsOf_existentialsOf]
      simp
    have he : existentialsOf cs = existentialsOf (tps.map .path ++ existentialsOf cs) := by
      rw [existentialsOf_append, existentialsOf_map_path, existentialsOf_existentialsOf]
      simp
    have hHM : hoistMatches (scopeAt s before) 0 true (.mk u cs :: after) =
        (i1, sm, .mk u cs' :: after) := by
      calc hoistMatches (scopeAt s before) 0 true (.mk u cs :: after)
          = (let (i1', headCs, cs'') := hoistConditions (scopeAt s before) 0 true cs
             let (i2, headRest, rest') := hoistMatches (scopeAt s before) i1' true after
             (i2, headCs ++ headRest, .mk u cs'' :: rest')) := rfl
        _ = (i1, sm, .mk u cs' :: after) := by rw [hgenC]; simp [hna']
    have hHoistAt : hoistAt s before (.mk u cs) after =
        Split.mk
          (Specification.mk s.given (before ++ sm)
            (.composite ((tailGivenAt s (before ++ sm) (.mk u cs' :: after)).map
              fun l => { name := l.name, label := l.name })))
          (some (Specification.mk (tailGivenAt s (before ++ sm) (.mk u cs' :: after))
            (.mk u cs' :: after) s.projection)) := by
      show hoistAt s before (.mk u cs) after = _
      unfold hoistAt
      simp only [hHM]
    have hSplitAt : splitAt s before (.mk u cs) after =
        Split.mk
          (Specification.mk s.given (before ++ sm2)
            (.composite ((tailGivenAt s (before ++ sm2)
              (.mk u (tps.map .path ++ existentialsOf cs) :: after)).map
              fun l => { name := l.name, label := l.name })))
          (some (Specification.mk (tailGivenAt s (before ++ sm2)
            (.mk u (tps.map .path ++ existentialsOf cs) :: after))
            (.mk u (tps.map .path ++ existentialsOf cs) :: after) s.projection)) := by
      show splitAt s before (.mk u cs) after = _
      unfold splitAt
      simp only [Match.conditions_mk, Match.unknown_mk, tailMatchesAt, hsp]
    have htailGivenEq :
        tailGivenAt s (before ++ sm) (.mk u cs' :: after) =
        tailGivenAt s (before ++ sm2) (.mk u (tps.map .path ++ existentialsOf cs) :: after) := by
      rw [hc1]
      exact tailGivenAt_congr s (before ++ sm2) (hc2.trans hp) (hc3.trans he)
    rw [htailGivenEq, hc1] at hHoistAt
    show r ∈ (hoistAt s before (.mk u cs) after).evaluate g env ↔
      r ∈ (splitAt s before (.mk u cs) after).evaluate g env
    rw [hHoistAt, hSplitAt]
    unfold Split.evaluate
    apply Iff.of_eq
    apply congrArg (r ∈ ·)
    apply flatMap_congr'
    intro tuple _
    unfold Specification.evaluate
    congr 1
    apply evalMatches_congr_allHold
    intro env'
    rw [allHold_pathsOf_existentialsOf, allHold_append, hc2, hc3]

end JinagaSpec
