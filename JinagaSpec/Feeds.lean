import JinagaSpec.Semantics

/-!
# Feeds

A replica does not run a specification on the replicator. It asks for the
specification's *feeds* (`POST /feeds`), reads each one page by page
(`GET /feeds/{hash}`), loads the facts the pages name together with their
predecessors (`/load`), and runs the specification on what it then holds.
`buildFeeds` is `jinaga.js`'s `src/specification/feed-builder.ts`, with the
corrections below.

A feed is a specification with no projection. What it delivers is the facts its
tuples bind to its unknowns (`Specification.tuples`). Every feed has the same
narrow shape (`FeedShape`): its matches carry path conditions, and negative
existential conditions whose matches carry only path conditions. That shape is
what lets a replicator page a feed by a bookmark: a new tuple always binds a
new fact (`feed_antitone`, `Proofs/Feeds.lean`).

To reach that shape, `buildFeeds` takes a specification apart.

* A positive existential condition's matches join the feed: they are tuples
  the results are built from.
* A negative existential condition branches a feed off the current one, which
  follows the condition's matches. At odd nesting depth that branch is
  *excluding*: its tuples are evidence that results should be removed, and it
  stops at the end of the condition. At even depth it is *restoring*: it shows
  that the fact its excluding feed follows is cancelled, so its tuples
  contribute results, and it goes on to match everything the specification
  has after the excluded condition, at that level and every enclosing one.
* The current feed keeps the negative condition, stripped of every negative
  condition inside it (`stripped`). The stripped condition excludes more than
  the original. The restoring feeds deliver what it excludes wrongly.
* A feed that walks no successor edge is dropped (`traversesSuccessors`): it
  delivers only predecessors of the givens, which a replica already holds.

## Where this differs from `jinaga.js`

An excluded fact is cancelled when *any one* of its negative conditions fails:
a delete with `!E { Restore }` and `!E { Undo }` is cancelled by either. A
restoring branch shows that one did, and needs nothing more of the fact. So it
drops the negative conditions its excluding feed attached to the fact
(`unattach`), and skips the excluded condition's remaining conditions and
matches (`afterStop`). `jinaga.js` keeps both, so its restoring feed for a
restored delete also asks the delete to have no undo; a delete that is both
restored and undone is then restored by no feed, and the results after it are
delivered by none (`vectors/feeds/not-exists-cancelled-twice.json`). Dropping the
attached conditions is what correctness needs (`check-feeds`'s mutants); skipping
the rest makes fewer feeds.

A positive condition inside a negative one joins the stripped condition as
matches (`exists-inside-not-exists.json`). `jinaga.js` replaces the stripped
condition with the positive one, whose matches name a label the feed does not
bind.
## The remainder as a list

`jinaga.js` carries what a branch must still match in a `Continuation`: the
conditions still waiting on the match the branch left from, the matches after
it, and the parent continuation. Here it is a list of `Work`, read front to
back, and `run` is a machine over it. A positive condition is flattened by
pushing its matches onto the front. An excluding branch is the same list with
the condition's matches and then a `stop` pushed onto the front. A restoring
branch is the condition's matches followed by what comes after that `stop`.
The feeds come out in the order `buildFeeds` emits them.
-/
namespace JinagaSpec

/-- What a feed still has to match. -/
inductive Work where
  /-- Matches to add to the feed, in order. -/
  | matches (ms : List Match)
  /-- Conditions still waiting on the match whose unknown is `label`, which the
  feed already holds. -/
  | conditions (label : Name) (cs : List Condition)
  /-- The end of an excluding branch of this parity. -/
  | stop (parity : Nat)

mutual
  /-- The matches of a negative condition as a feed applies it: each match with
  only its path conditions, followed by the matches of every positive condition
  inside it, at any depth. Negative conditions inside it are dropped. -/
  def stripped : List Match → List Match
    | [] => []
    | .mk u cs :: rest => .mk u (cs.filter (·.isPath)) :: (strippedPositives cs ++ stripped rest)

  def strippedPositives : List Condition → List Match
    | [] => []
    | .existential true ms :: cs => stripped ms ++ strippedPositives cs
    | _ :: cs => strippedPositives cs
end

/-- Add to the feed's givens each of the specification's givens that one of
these path conditions names and the feed does not have yet, in order. -/
def useGivens (givens : List Label) (feed : List Label) (cs : List Condition) : List Label :=
  cs.foldl (fun feed c => match c with
    | .path pc => match givens.find? (·.name == pc.labelRight) with
      | some l => if feed.contains l then feed else feed ++ [l]
      | none => feed
    | .existential .. => feed) feed

/-- Add a match to the feed, with only its path conditions. -/
def withMatch (givens : List Label) (feed : Specification) : Match → Specification
  | .mk u cs =>
    let paths := cs.filter (·.isPath)
    { feed with given := useGivens givens feed.given paths, matchList := feed.matchList ++ [.mk u paths] }

/-- Attach a condition to the last match of the feed whose unknown is `label`. -/
def attach (label : Name) (c : Condition) : List Match → List Match
  | [] => []
  | .mk u cs :: rest =>
    if (rest.map (·.unknown.name)).contains label then .mk u cs :: attach label c rest
    else if u.name == label then .mk u (cs ++ [c]) :: rest
    else .mk u cs :: rest

/-- Attach a negative condition, stripped, to the match whose unknown is `label`. -/
def withCondition (givens : List Label) (feed : Specification) (label : Name) (ms : List Match) : Specification :=
  let ms := stripped ms
  { feed with
    given := useGivens givens feed.given (ms.flatMap (·.conditions))
    matchList := attach label (.existential false ms) feed.matchList }

mutual
  def Match.weight : Match → Nat
    | .mk _ cs => 1 + Condition.weightList cs

  def Match.weightList : List Match → Nat
    | [] => 0
    | m :: ms => m.weight + Match.weightList ms

  def Condition.weight : Condition → Nat
    | .path _ => 1
    | .existential _ ms => 1 + Match.weightList ms

  def Condition.weightList : List Condition → Nat
    | [] => 0
    | c :: cs => c.weight + Condition.weightList cs
end

def Work.weight : Work → Nat
  | .matches ms => Match.weightList ms
  | .conditions _ cs => Condition.weightList cs
  | .stop _ => 0

def workWeight (w : List Work) : Nat := (w.map Work.weight).sum

/-- What follows the end of the excluding branch of parity `p`. -/
def afterStop (p : Nat) : List Work → List Work
  | [] => []
  | .stop q :: w => if q == p then w else afterStop p w
  | _ :: w => afterStop p w

theorem afterStop_weight (p : Nat) : ∀ w, workWeight (afterStop p w) ≤ workWeight w ∧ (afterStop p w).length ≤ w.length
  | [] => by simp [afterStop]
  | .stop q :: w => by
    have := afterStop_weight p w
    simp only [afterStop, workWeight, List.map_cons, List.sum_cons, List.length_cons] at *
    split <;> omega
  | .matches _ :: w | .conditions _ _ :: w => by
    have := afterStop_weight p w
    simp only [afterStop, workWeight, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- The match with only its path conditions. -/
def Match.paths : Match → Match
  | .mk u cs => .mk u (cs.filter (·.isPath))

/-- The feed with the negative conditions of its matches from `base` on
removed: those an excluding branch attached to the matches it added. -/
def unattach (base : Nat) (feed : Specification) : Specification :=
  { feed with matchList := feed.matchList.take base ++ (feed.matchList.drop base).map Match.paths }

/-- The feeds that start from `feed`, at nesting depth `parity`, with `work`
still to match. In an excluding feed, `base` counts the matches it began with:
those before the condition it follows. -/
def run (givens : List Label) (feed : Specification) (parity base : Nat) : List Work → List Specification
  | [] => [feed]
  | .stop p :: w => if p == parity then [feed] else run givens feed parity base w
  | .matches [] :: w => run givens feed parity base w
  | .matches (.mk u cs :: ms) :: w =>
    run givens (withMatch givens feed (.mk u cs)) parity base (.conditions u.name cs :: .matches ms :: w)
  | .conditions _ [] :: w => run givens feed parity base w
  | .conditions l (.path _ :: cs) :: w => run givens feed parity base (.conditions l cs :: w)
  | .conditions l (.existential true ms :: cs) :: w =>
    run givens feed parity base (.matches ms :: .conditions l cs :: w)
  | .conditions l (.existential false ms :: cs) :: w =>
    let rest := .conditions l cs :: w
    -- An excluding branch follows the condition's matches and stops at their
    -- end. A restoring branch shows that the fact its excluding feed follows
    -- is cancelled, which any one of that fact's negative conditions does. So
    -- it drops the conditions the excluding feed attached, and skips the rest
    -- of the excluded condition, going on with what follows it.
    let branch := if parity % 2 == 0
      then run givens feed (parity + 1) feed.matchList.length (.matches ms :: .stop (parity + 1) :: rest)
      else run givens (unattach base feed) (parity + 1) base (.matches ms :: afterStop parity rest)
    branch ++ run givens (withCondition givens feed l ms) parity base rest
termination_by w => (workWeight w, w.length)
decreasing_by
  all_goals
    simp_wf
    simp only [workWeight, Work.weight, Match.weightList, Match.weight, Condition.weightList,
      Condition.weight, List.map_cons, List.sum_cons, Prod.lex_def]
    try split
    all_goals try simp only [Work.weight, List.map_cons, List.sum_cons, List.length_cons]
    all_goals first
      | omega
      | (have := afterStop_weight parity (Work.conditions l cs :: w)
         simp only [workWeight, Work.weight, List.map_cons, List.sum_cons, List.length_cons] at this
         omega)

/-- A feed walks at least one successor edge: some path condition of its
matches walks from the unknown. -/
def traversesSuccessors (feed : Specification) : Bool :=
  feed.matchList.any fun m => m.conditions.any fun
    | .path pc => !pc.rolesLeft.isEmpty
    | .existential .. => false

/-- The feeds of a specification, as `jinaga.js`'s `buildFeeds` returns them. -/
def buildFeeds (s : Specification) : List Specification :=
  (run s.given { given := [], matchList := [], projection := .composite [] } 0 0 [.matches s.matchList]).filter
    traversesSuccessors

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
`WellFormed` lets sibling existential conditions reuse a name; a feed that
joins them would then declare it twice. -/
def DistinctLabels (s : Specification) : Prop := (declaredMatches s.matchList).Nodup

/-- The shape of a feed: path conditions, and negative existential conditions
whose matches carry only path conditions. -/
def FeedShape (ms : List Match) : Prop :=
  ∀ m ∈ ms, ∀ c ∈ m.conditions, c.isPath = true ∨
    ∃ ms', c = .existential false ms' ∧ ∀ m' ∈ ms', ∀ c' ∈ m'.conditions, c'.isPath = true

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

/-- Every predecessor of a fact of the graph is a fact of the graph. A replica
saves a fact with its predecessors. -/
def Graph.Closed (S : Graph) : Prop := ∀ x ∈ S, ∀ p ∈ x.predecessors, ∃ y ∈ S, y.id = p.2

/-- **The feeds cover the specification.** A replica holding the givens, every
fact the feeds deliver on the replicator's graph `G`, and the predecessors of
each, and any other facts of `G`, reads what the replicator reads.

This is the statement `check-feeds` tests on random specifications and graphs
(`cover`), and `feed_converges` (`Proofs/Cursor.lean`) assumes. It is not yet
proved. -/
def FeedsCover (s : Specification) : Prop :=
  ∀ (G S : Graph) (env : Env), G.IdsUnique → (∀ x ∈ S, x ∈ G) → S.Closed →
    (∀ l ∈ s.given, S.has env l = true) → (∀ id ∈ delivered s G env, ∃ x ∈ S, x.id = id) →
    ∀ r, r ∈ s.read S env ↔ r ∈ s.read G env

end JinagaSpec
