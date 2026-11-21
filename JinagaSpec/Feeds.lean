import JinagaSpec.Reorder

/-!
# Feeds

A replica does not run a specification on the replicator. It asks for the
specification's *feeds* (`POST /feeds`), reads each one page by page
(`GET /feeds/{hash}`), loads the facts the pages name together with their
predecessors (`/load`), and runs the specification on what it then holds. This
is chapter 12 of *The Art of Immutable Architecture*.

A feed is a specification with no projection. What it delivers is the facts its
tuples bind to its unknowns (`Specification.tuples`). Three requirements decide
what the feeds are:

1. **Consistency.** A replica holding what the feeds deliver, with their
   predecessors, and any other facts of the replicator's graph, reads what the
   replicator reads (`feeds_cover`).
2. **Append-only.** A tuple is never inserted behind a bookmark. So a feed has
   only path conditions, and negative conditions over matches with only path
   conditions, which can only ever remove a tuple (`feed_antitone`).
3. **Deferral.** A new client is not sent the details of an entity that is
   excluded by a negative condition none of whose facts has been cancelled: a
   deleted menu item's names, until it is restored (`feeds_defer`).

## The feeds

Walk the specification's matches, each joined with its positive conditions (as
the inverse algorithm flattens them: `flattenMatches`, `Reorder.lean`). At each
negative condition, every feed so far

* emits an **excluding** feed: itself, then the condition's *level* (its matches,
  positive conditions joined, path conditions only), and stops, since an
  excluded entity's details are deferred;
* goes on **filtered** by the condition's level, which removes an entity once a
  fact excludes it, and never brings it back; and
* goes on **restored**: through the condition's level and then the level of one
  of that level's own negative conditions, walked the same way. This is the
  feed that delivers an entity, and its details, once what excluded it is
  cancelled. It asks nothing more of the excluded fact: any one of its negative
  conditions cancels it.

A feed that walks no successor edge is dropped (`traversesSuccessors`): it
delivers only predecessors of the givens, which a replica already holds.

These are the ordinary, excluding and restoring feeds of the chapter. The
requirements settle what the chapter leaves open. An excluding feed stops
(deferral). A restoring feed drops the other negative conditions of the fact it
restores, and a positive condition inside a negative one joins its level
(consistency); `jinaga.js` does neither (`docs/findings.md`). And an excluding
feed is not itself filtered, since what a filter would remove from it a
restoring feed delivers anyway.
-/
namespace JinagaSpec

/-- The match with only its path conditions. -/
def Match.paths : Match → Match
  | .mk u cs => .mk u (cs.filter (·.isPath))

/-- The negative conditions of a match: what flattening leaves besides its path
conditions. -/
def Match.negatives : Match → List (List Match)
  | .mk _ cs => cs.filterMap fun
    | .existential false ms => some ms
    | _ => none

/-- Join every positive condition into its level. -/
abbrev flatten (ms : List Match) : List Match := flattenMatches (fun _ => true) ms

/-- A match's negative conditions are the negative conditions among its conditions. -/
theorem Match.mem_negatives {u : Label} {cs : List Condition} {ns : List Match} :
    ns ∈ (Match.mk u cs).negatives ↔ Condition.existential false ns ∈ cs := by
  simp only [Match.negatives, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, h⟩
    cases c with
    | path => simp at h
    | existential e ms => cases e <;> simp_all
  · exact fun h => ⟨_, h, rfl⟩

mutual
  /-- A negative condition left by flattening is smaller than the level it is in. -/
  theorem sizeOf_negatives_flattenMatches (lift : List Match → Bool) :
      ∀ {ms : List Match} {m : Match}, m ∈ flattenMatches lift ms → ∀ ns ∈ m.negatives, sizeOf ns < sizeOf ms
    | [], _, h, _, _ => by simp [flattenMatches] at h
    | .mk u cs :: rest, m, h, ns, hns => by
      have hfl : flattenMatches lift (.mk u cs :: rest) =
          .mk u (flattenConditions lift cs).1 :: ((flattenConditions lift cs).2 ++ flattenMatches lift rest) := by
        rw [flattenMatches]; rcases flattenConditions lift cs with ⟨k, l⟩; rfl
      have hcs : sizeOf cs < sizeOf (Match.mk u cs :: rest) := by simp; omega
      have hrest : sizeOf rest < sizeOf (Match.mk u cs :: rest) := by simp; omega
      rw [hfl] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.lt_trans (List.sizeOf_lt_of_mem
          ((sizeOf_kept_flattenConditions lift cs) _ (Match.mem_negatives.mp hns)) |> fun h => by simp at h; omega) hcs
      · rcases List.mem_append.mp h with h | h
        · exact Nat.lt_trans (sizeOf_lifted_flattenConditions lift h ns hns) hcs
        · exact Nat.lt_trans (sizeOf_negatives_flattenMatches lift h ns hns) hrest

  /-- What flattening keeps of the conditions is among them. -/
  theorem sizeOf_kept_flattenConditions (lift : List Match → Bool) :
      ∀ (cs : List Condition), ∀ c ∈ (flattenConditions lift cs).1, c ∈ cs
    | [], c, h => by simp [flattenConditions] at h
    | c :: cs, d, h => by
      have ih := sizeOf_kept_flattenConditions lift cs
      simp only [flattenConditions] at h
      split at h
      · split at h
        · exact List.mem_cons_of_mem _ (ih d h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih d h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih d h)

  theorem sizeOf_lifted_flattenConditions (lift : List Match → Bool) :
      ∀ {cs : List Condition} {m : Match}, m ∈ (flattenConditions lift cs).2 → ∀ ns ∈ m.negatives, sizeOf ns < sizeOf cs
    | [], _, h, _, _ => by simp [flattenConditions] at h
    | c :: cs, m, h, ns, hns => by
      have hcs : sizeOf cs < sizeOf (c :: cs) := by simp; omega
      simp only [flattenConditions] at h
      split at h
      · rename_i ms
        split at h
        · rcases List.mem_append.mp h with h | h
          · exact Nat.lt_trans (sizeOf_negatives_flattenMatches lift h ns hns) (by simp; omega)
          · exact Nat.lt_trans (sizeOf_lifted_flattenConditions lift h ns hns) hcs
        · exact Nat.lt_trans (sizeOf_lifted_flattenConditions lift h ns hns) hcs
      · exact Nat.lt_trans (sizeOf_lifted_flattenConditions lift h ns hns) hcs
end

/-- A negative condition's level is smaller than the level it is in. -/
theorem sizeOf_negatives_flatten {ms : List Match} {m : Match} (h : m ∈ flatten ms) :
    ∀ ns ∈ m.negatives, sizeOf ns < sizeOf ms :=
  sizeOf_negatives_flattenMatches _ h

/-- A negative condition's level, as a feed continues with it: its matches with
every positive condition joined in, keeping only path conditions. -/
def level (ns : List Match) : List Match := (flatten ns).map Match.paths

/-- The negative conditions of a level: those of its matches, with every
positive condition joined in. -/
def negativesOf (ms : List Match) : List (List Match) := (flatten ms).flatMap Match.negatives

def Match.addCondition (c : Condition) : Match → Match
  | .mk u cs => .mk u (cs ++ [c])

/-- Add a condition to the last match of a feed. Every label a filter names is
bound by then, so it is checked once the feed so far is matched. -/
def addLast (c : Condition) : List Match → List Match
  | [] => []
  | [m] => [m.addCondition c]
  | m :: m' :: ms => m :: addLast c (m' :: ms)

/-- The largest of the conditions' sizes. -/
noncomputable def maxSize (L : List (List Match)) : Nat := (L.map sizeOf).foldr max 0

theorem le_maxSize : ∀ {L : List (List Match)} {ns : List Match}, ns ∈ L → sizeOf ns ≤ maxSize L
  | q :: L, ns, h => by
    simp only [maxSize, List.map_cons, List.foldr_cons] at *
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_maxSize (L := L) h; simp only [maxSize] at this; omega

theorem maxSize_cons (ns : List Match) (L : List (List Match)) : maxSize L ≤ maxSize (ns :: L) := by
  simp only [maxSize, List.map_cons, List.foldr_cons]; omega

theorem maxSize_lt {L : List (List Match)} {b : Nat} (hb : 0 < b) (h : ∀ ns ∈ L, sizeOf ns < b) :
    maxSize L < b := by
  induction L with
  | nil => simpa [maxSize]
  | cons q L ih =>
    simp only [maxSize, List.map_cons, List.foldr_cons] at ih ⊢
    have := h q (List.mem_cons_self ..)
    have := ih fun p hp => h p (List.mem_cons_of_mem _ hp)
    omega

theorem maxSize_lex (ns : List Match) (rest : List (List Match)) :
    Prod.Lex (· < ·) (· < ·) (maxSize rest, rest.length) (maxSize (ns :: rest), (ns :: rest).length) := by
  simp only [Prod.lex_def, List.length_cons]; have := maxSize_cons ns rest; omega

theorem sizeOf_negativesOf {ms : List Match} : ∀ ns ∈ negativesOf ms, sizeOf ns < sizeOf ms := by
  intro ns h
  obtain ⟨x, hx, h⟩ := List.mem_flatMap.mp h
  exact sizeOf_negatives_flatten hx ns h

theorem sizeOf_negativesOf_unit {m : Match} {rest : List Match} :
    ∀ ns ∈ negativesOf [m], sizeOf ns < sizeOf (m :: rest) := by
  intro ns h
  have h1 := sizeOf_negativesOf ns h
  have h2 : sizeOf [m] ≤ sizeOf (m :: rest) := by
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]; cases rest <;> simp <;> omega
  exact Nat.lt_of_lt_of_le h1 h2

mutual
  /-- The feeds of the level `ms`, after the partial feed `P`. Each match joins
  the feed with its positive conditions; then each of its negative conditions
  is walked (`negFeeds`). Each feed that completes the level is handed to `k`,
  which goes on with whatever encloses the level. -/
  def levelFeeds (k : List Match → List (List Match)) (P : List Match) : List Match → List (List Match)
    | [] => k P
    | m :: rest => negFeeds (fun Q => levelFeeds k Q rest) (P ++ level [m]) (negativesOf [m])
  termination_by ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (m :: rest)) (by simp; omega) fun p hp => sizeOf_negativesOf_unit p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

  /-- The feeds of the partial feed `Q` with the negative conditions `negs` still
  to walk. At each, the feed so far emits an excluding feed, which goes on to
  the condition's level and stops; and it goes on both filtered by the
  condition's level and restored, through the condition's level and the level
  of one of its own negative conditions. -/
  def negFeeds (k : List Match → List (List Match)) (Q : List Match) : List (List Match) → List (List Match)
    | [] => k Q
    | ns :: rest =>
      (Q ++ level ns) :: (negFeeds k (addLast (.existential false (level ns)) Q) rest ++
        (negativesOf ns).attach.flatMap fun ⟨ns', _h⟩ =>
          levelFeeds (fun Q' => negFeeds k Q' rest) (Q ++ level ns) ns')
  termination_by negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact maxSize_lex _ _
      | exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (sizeOf_negativesOf _ ‹_›) (le_maxSize (List.mem_cons_self ..)))
end

/-- The givens a feed names, in its path conditions or its filters, in the
specification's order. -/
def usedGivens (givens : List Label) (ms : List Match) : List Label :=
  givens.filter fun l => (freeInMatches [] ms).contains l.name

/-- A feed walks at least one successor edge: some path condition of its
matches walks from the unknown. -/
def traversesSuccessors (feed : Specification) : Bool :=
  feed.matchList.any fun m => m.conditions.any fun
    | .path pc => !pc.rolesLeft.isEmpty
    | .existential .. => false

/-- The feeds of a specification. -/
def buildFeeds (s : Specification) : List Specification :=
  ((levelFeeds (fun P => [P]) [] s.matchList).map fun ms =>
    { given := usedGivens s.given ms, matchList := ms, projection := .composite [] }).filter traversesSuccessors

/-- A feed's tuples on `g`: for each solution, the facts it binds to the feed's
unknowns, in order. These are what a page of the feed names. -/
def Specification.tuples (f : Specification) (g : Graph) (env : Env) : List (List FactId) :=
  (evalMatches g env f.matchList).map fun e => (f.matchList.map (·.unknown.name)).filterMap e

/-- Every fact the feeds of `s` deliver on `g`. -/
def delivered (s : Specification) (g : Graph) (env : Env) : List FactId :=
  (buildFeeds s).flatMap fun f => (f.tuples g env).flatten

mutual
  /-- Every label the matches declare, at any depth. -/
  def declaredMatches : List Match → List Name
    | [] => []
    | .mk u cs :: rest => u.name :: (declaredConditions cs ++ declaredMatches rest)

  def declaredConditions : List Condition → List Name
    | [] => []
    | .path _ :: cs => declaredConditions cs
    | .existential _ ms :: cs => declaredMatches ms ++ declaredConditions cs
end

/-- No two matches of the specification, at any depth, declare the same label.
`WellFormed` lets sibling existential conditions reuse a name; joining them
into one level would then bind it twice. -/
def DistinctLabels (s : Specification) : Prop := (declaredMatches s.matchList).Nodup

mutual
  /-- Every match, at any depth, has a path condition. `jinaga.js` refuses a
  match that does not begin with one. -/
  def RootedMatches : List Match → Prop
    | [] => True
    | .mk _ cs :: rest => (∃ c ∈ cs, c.isPath = true) ∧ RootedConditions cs ∧ RootedMatches rest

  def RootedConditions : List Condition → Prop
    | [] => True
    | .path _ :: cs => RootedConditions cs
    | .existential _ ms :: cs => RootedMatches ms ∧ RootedConditions cs
end

end JinagaSpec
