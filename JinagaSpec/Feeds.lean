import JinagaSpec.Reorder

/-!
# Feeds

A replica does not run a specification on the replicator. It asks for the
specification's *feeds* (`POST /feeds`), reads each one page by page
(`GET /feeds/{hash}`), loads the facts the pages name together with their
predecessors (`/load`), and runs the specification on what it then holds.

A feed is a specification with no projection, and only path conditions. What
it delivers is the facts its tuples bind to its unknowns
(`Specification.tuples`). With only path conditions, a tuple that is new to a
feed binds a new fact, which lets a replicator page a feed by a bookmark
(`feed_antitone`, `Proofs/Feeds.lean`).

## Levels

A specification's *levels* are its matches, and the matches of each of its
negative existential conditions, at any depth. Each level is one feed:

* A positive condition's matches join the level of the match it qualifies, as
  the inverse algorithm flattens them (`flattenMatches`, `Reorder.lean`).
  A feed never delivers what a positive condition rules out, which is what
  lets a distribution rule's positive conditions authorize.
* The feed of a level is its matches, so joined, with their path conditions,
  after the matches of the levels that enclose it: those name the labels the
  level's own path conditions join to.
* A negative condition is not a filter. Its level is a feed of its own, which
  delivers the facts that exclude a result, and the facts that cancel them, at
  the next level down.

So a specification has one feed for its matches and one for each negative
condition. A feed that walks no successor edge is dropped
(`traversesSuccessors`): it delivers only predecessors of the givens, which a
replica already holds.

## What this replaces

`jinaga.js`'s `buildFeeds` filters each feed by the negative conditions it
passes, stripped of the negative conditions inside them, and so must add a
*restoring* feed for every result a stripped condition wrongly excludes, which
goes on to match the rest of the specification. Getting that bookkeeping right
took two fixes there (jinaga/jinaga.js#368 and the one before it), and checking
it here found two more defects (`docs/findings.md`). Levels need none of it: a
feed is a conjunctive query, and what a negative condition excludes, the
replica works out from the facts the condition's own feed delivers.
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

/-- The feeds of the level `ms`, after the matches `pre` of the levels that
enclose it: the level's own feed, then the feeds of its negative conditions. -/
def levelFeeds (pre ms : List Match) : List (List Match) :=
  let here := pre ++ (flatten ms).map Match.paths
  here :: ((flatten ms).attach.flatMap fun ⟨m, hm⟩ => m.negatives.attach.flatMap fun ⟨ns, hns⟩ =>
    have := sizeOf_negatives_flatten hm ns hns
    levelFeeds here ns)
termination_by sizeOf ms

/-- The givens a feed's path conditions name, in the specification's order. -/
def usedGivens (givens : List Label) (ms : List Match) : List Label :=
  givens.filter fun l => ms.any fun m => m.conditions.any fun
    | .path pc => pc.labelRight == l.name
    | .existential .. => false

/-- A feed walks at least one successor edge: some path condition of its
matches walks from the unknown. -/
def traversesSuccessors (feed : Specification) : Bool :=
  feed.matchList.any fun m => m.conditions.any fun
    | .path pc => !pc.rolesLeft.isEmpty
    | .existential .. => false

/-- The feeds of a specification. -/
def buildFeeds (s : Specification) : List Specification :=
  ((levelFeeds [] s.matchList).map fun ms =>
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
