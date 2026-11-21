import JinagaSpec
import CheckGen
import JinagaSpec.FeedCases

/-!
# Randomized check of feeds

`lake exe check-feeds [seed] [reuse]` checks, on random well-formed
specifications and graphs:

* **shape** — every feed has only path conditions (`buildFeeds_paths`), and
  binds each of its labels once.
* **antitone** — a tuple a feed finds after a fresh batch arrives, all of whose
  facts were there before, was a tuple before (`feed_antitone`). This is what
  lets a replicator page a feed by a bookmark.
* **cover** — a replica that holds the givens and every fact the feeds deliver,
  with their predecessors, and any other facts of the graph it likes, reads
  what the replicator reads (`feeds_cover`).

Each mutant changes one rule of `levelFeeds`. Every one must be caught by one
of the checks, or the check is not testing that rule. The mutants are one
builder, `levelFeedsWith`, parameterized over the rule that varies;
`levelFeeds` itself stays as the specification reads.
-/
open JinagaSpec Build

/-- Which rule of `levelFeeds` a mutant changes. -/
structure Mutant where
  /-- Which positive conditions join their level. -/
  lift : List Match → Bool := fun _ => true
  /-- A negative condition's feed starts after the levels that enclose it. -/
  keepsPrefix : Bool := true
  /-- Negative conditions inside negative ones have feeds. -/
  nested : Bool := true
  /-- A feed keeps its negative conditions as filters. -/
  filters : Bool := false
  /-- Which feeds are kept. -/
  keep : Specification → Bool := traversesSuccessors

partial def levelFeedsWith (mu : Mutant) (depth : Nat) (pre ms : List Match) : List (List Match) :=
  let flat := flattenMatches mu.lift ms
  let here := pre ++ if mu.filters then flat else flat.map Match.paths
  here :: if !mu.nested && depth > 0 then [] else
    (flat.flatMap Match.negatives).flatMap (levelFeedsWith mu (depth + 1) (if mu.keepsPrefix then here else []))

def buildFeedsWith (mu : Mutant) (s : Specification) : List Specification :=
  ((levelFeedsWith mu 0 [] s.matchList).map fun ms =>
    { given := usedGivens s.given ms, matchList := ms, projection := .composite [] }).filter mu.keep

def deliveredWith (mu : Mutant) (s : Specification) (g : Graph) (env : Env) : List FactId :=
  (buildFeedsWith mu s).flatMap fun f => (f.tuples g env).flatten

def mutants : List (String × Mutant) := [
  ("a negative condition's feed loses the levels that enclose it", { keepsPrefix := false }),
  ("negative conditions inside negative ones have no feed", { nested := false }),
  ("positive conditions stay conditions, so no negative condition inside one has a feed", { lift := fun _ => false }),
  ("a feed keeps its negative conditions as filters", { filters := true }),
  ("only feeds whose first match walks to a successor are kept",
    { keep := fun f => match f.matchList with
        | m :: _ => m.conditions.any fun | .path pc => !pc.rolesLeft.isEmpty | _ => false
        | [] => false })]

/-! ## The filtered algorithm, for comparison

The corrected ordinary, excluding and restoring feeds of chapter 12, as the
first port wrote them (commit 374bd83). Kept here to check the deferral
requirement against while the specification's own definition is redesigned. -/

namespace Filtered
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

/-- What follows the end of the excluding branch of parity `p`. -/
def afterStop (p : Nat) : List Work → List Work
  | [] => []
  | .stop q :: w => if q == p then w else afterStop p w
  | _ :: w => afterStop p w

/-- The feed with the negative conditions of its matches from `base` on
removed: those an excluding branch attached to the matches it added. -/
def unattach (base : Nat) (feed : Specification) : Specification :=
  { feed with matchList := feed.matchList.take base ++ (feed.matchList.drop base).map Match.paths }

/-- The feeds that start from `feed`, at nesting depth `parity`, with `work`
still to match. In an excluding feed, `base` counts the matches it began with:
those before the condition it follows. -/
partial def run (givens : List Label) (feed : Specification) (parity base : Nat) : List Work → List Specification
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

def buildFeeds (s : Specification) : List Specification :=
  (run s.given { given := [], matchList := [], projection := .composite [] } 0 0 [.matches s.matchList]).filter
    traversesSuccessors

def delivered (s : Specification) (g : Graph) (env : Env) : List FactId :=
  (buildFeeds s).flatMap fun f => (f.tuples g env).flatten

end Filtered

/-! ## Feeds derived from the requirements

Walk a level's matches, each joined with its positive conditions. At each
negative condition, every feed so far emits an excluding feed (itself, then the
condition's level), and continues both filtered by the condition and restored
through the condition's level and the level of one of its negative conditions.
Returns the positive feeds and the excluding feeds. -/

mutual
  partial def derivedLevel (pre : List Match) : List Match → List (List Match) × List (List Match)
    | [] => ([pre], [])
    | m :: rest =>
      let (units, exc) := derivedUnit pre m
      let rs := units.map (derivedLevel · rest)
      (rs.flatMap (·.1), exc ++ rs.flatMap (·.2))

  partial def derivedUnit (pre : List Match) (m : Match) : List (List Match) × List (List Match) := Id.run do
    let unit := flatten [m]
    let negs := unit.flatMap fun x => x.negatives.map fun ns => (x.unknown.name, ns)
    let mut pos := [pre ++ unit.map Match.paths]
    let mut exc := []
    for (host, ns) in negs do
      let level := (flatten ns).map Match.paths
      let mut next := []
      for P in pos do
        exc := exc ++ [P ++ level]
        next := next ++ [Filtered.attach host (.existential false level) P]
        for x in flatten ns do
          for ns' in x.negatives do
            let (rp, re) := derivedLevel (P ++ level) ns'
            next := next ++ rp
            exc := exc ++ re
      pos := next
    return (pos, exc)
end

def derivedFeeds (s : Specification) : List Specification :=
  let (pos, exc) := derivedLevel [] s.matchList
  ((pos ++ exc).map fun ms => { given := usedGivens s.given ms, matchList := ms, projection := .composite [] }).filter
    traversesSuccessors

def derivedDelivered (s : Specification) (g : Graph) (env : Env) : List FactId :=
  (derivedFeeds s).flatMap fun f => (f.tuples g env).flatten

/-! ## Deferral

A new client must not receive the details of an entity that is excluded and
whose exclusion nothing has cancelled. Over the top level, joined: for each
prefix `p` through a match `m`, and each negative condition of `m` whose
witnesses at `p` all stand, no feed's tuple binds `p` and goes on to a match
after `m`. -/

def keyOn (names : List Name) (e : Env) : List (Option FactId) := names.map e

/-- How many excluded, uncontested prefixes some feed carries past their match.
A prefix binds the top-level matches through `m`, each with its positive
conditions joined: those are part of the entity. Its details are the top-level
matches after `m`. The negative condition is any one of `m`'s, or of a match a
positive condition of `m` joins. -/
def deferViolations (s : Specification) (G : Graph) (env : Env) (feeds : List Specification) : Nat := Id.run do
  let tuples := feeds.map fun f => (f, evalMatches G env f.matchList)
  let mut n := 0
  for i in [0:s.matchList.length] do
    let pre := flatten (s.matchList.take (i + 1))
    let unit := flatten ((s.matchList.drop i).take 1)
    let later := names (flatten (s.matchList.drop (i + 1)))
    for p in evalMatches G env (pre.map Match.paths) do
      for m in unit do
        for ns in m.negatives do
          let level := flatten ns
          let keys := names pre ++ names level
          let witnesses := (evalMatches G p (level.map Match.paths)).map (keyOn keys)
          let standing := (evalMatches G p level).map (keyOn keys)
          if !witnesses.isEmpty && witnesses.all standing.contains then
            for (f, ts) in tuples do
              let fn := names f.matchList
              if later.any fn.contains then
                if ts.any fun τ => keyOn (names pre) τ == keyOn (names pre) p &&
                    later.any fun y => fn.contains y && (τ y).isSome then
                  n := n + 1
  return n

/-! ## What a new client downloads

Events of a tenant, each with a history of names; most deleted, some of those
restored. A new client holds what the feeds deliver and its predecessors. -/

def eventsSpec : Specification :=
  spec [("t", "Tenant")]
    [unknown "e" "Event" [path [role "tenant" "Tenant"] "t",
      notExists [unknown "d" "Delete" [path [role "event" "Event"] "e",
        notExists [unknown "x" "Restore" [path [role "delete" "Delete"] "d"]]]]],
     unknown "n" "Name" [path [role "event" "Event"] "e"]]
    (.composite [{ name := "event", label := "e" }, { name := "name", label := "n" }])

/-- `events` events with `history` names each; event `i` is deleted when
`i % 5 < 3`, and its delete restored when `i % 5 = 0`. -/
def eventsGraph (events history : Nat) : Graph := Id.run do
  let mut g : Graph := [⟨0, "Tenant", []⟩]
  let mut id := 1
  for i in [0:events] do
    let e := id
    g := g ++ [⟨e, "Event", [("tenant", 0)]⟩]
    id := id + 1
    for _ in [0:history] do
      g := g ++ [⟨id, "Name", [("event", e)]⟩]
      id := id + 1
    if i % 5 < 3 then
      let d := id
      g := g ++ [⟨d, "Delete", [("event", e)]⟩]
      id := id + 1
      if i % 5 == 0 then
        g := g ++ [⟨id, "Restore", [("delete", d)]⟩]
        id := id + 1
  return g

def newClientFacts (s : Specification) (g : Graph) (env : Env) (D : List FactId) : Nat :=
  (replica s g env D []).length

def measureDownload : IO Unit := do
  let g := eventsGraph 50 10
  let env := eventsSpec.bindGivens [0]
  let levels := newClientFacts eventsSpec g env (delivered eventsSpec g env)
  let filtered := newClientFacts eventsSpec g env (Filtered.delivered eventsSpec g env)
  let derived := newClientFacts eventsSpec g env (derivedDelivered eventsSpec g env)
  let results := (eventsSpec.read g env).length
  IO.println s!"new client, 50 events of 10 names, 30 deleted, 10 of those restored: graph {g.length} facts, {results} results; levels download {levels}, filtered {filtered}, derived {derived}"

/-! ## The checks -/

def pathsOnly (ms : List Match) : Bool := ms.all (·.conditions.all (·.isPath))

def coverHolds (s : Specification) (g : Graph) (env : Env) (D extra : List FactId) : Bool :=
  sameSet (s.read (replica s g env D extra) env) (s.read g env)

/-- Tuples of `f` after `B` whose facts were all in `g` were tuples before. -/
def antitoneHolds (f : Specification) (g : Graph) (B : List Fact) (env : Env) : Bool :=
  let before := f.tuples g env
  (f.tuples (g ++ B) env).all fun t => t.any (fun id => B.any (·.id == id)) || before.contains t

structure Tally where
  specs : Nat := 0
  graphs : Nat := 0
  feeds : Nat := 0
  facts : Nat := 0
  tuples : Nat := 0
  shape : Nat := 0
  antitone : Nat := 0
  cover : Nat := 0
  coverFiltered : Nat := 0
  deferLevels : Nat := 0
  deferFiltered : Nat := 0
  deferDerived : Nat := 0
  coverDerived : Nat := 0
  antitoneDerived : Nat := 0
  derivedFeedCount : Nat := 0
  filteredFeedCount : Nat := 0
  firstDefer : Option String := none
  first : Option String := none

def report (s : Specification) (g : Graph) (env : Env) (what : String) : String :=
  s!"{what}\n{describeSpecification s}\ngraph: {g.map fun f => (f.id, f.type, f.predecessors)}\n" ++
    s!"givens: {s.given.map fun l => (l.name, env l.name)}"

def main (args : List String) : IO UInt32 := do
  let seed := (args.head?.bind String.toNat?).getD 1
  let reuse := args.contains "reuse"
  let mut gen : StdGen × Nat := (mkStdGen seed, 0)
  let mut t : Tally := {}
  let mut caught : List Nat := mutants.map fun _ => 0
  -- The production builder is the mutant family with no rule changed.
  for c in feedCases do
    unless levelFeedsWith {} 0 [] c.spec.matchList == levelFeeds [] c.spec.matchList do
      throw <| IO.userError s!"levelFeedsWith differs from levelFeeds on {c.name}"
  -- The named cases: each holds on its own graph, with and without every other
  -- fact of the graph held as well.
  for c in feedCases do
    unless isWellFormed c.spec do
      throw <| IO.userError s!"feed case {c.name} is not well-formed"
    let all := c.graph.map (·.id)
    for extra in [[], all] do
      unless coverHolds c.spec c.graph c.env (delivered c.spec c.graph c.env) extra do
        t := { t with cover := t.cover + 1 }
        if t.first.isNone then t := { t with first := some (report c.spec c.graph c.env s!"cover, case {c.name}, extra {extra}") }
    caught := (caught.zip mutants).map fun (n, (_, mu)) =>
      if [[], all].any (fun extra => !coverHolds c.spec c.graph c.env (deliveredWith mu c.spec c.graph c.env) extra)
      then n + 1 else n
  for _ in [0:600] do
    let (s, g) := (if t.specs % 2 == 0 then genFeedSpec else genSpec false 3 reuse).run gen
    gen := g
    unless isWellFormed s do
      throw <| IO.userError s!"the generator made a specification that is not well-formed:\n{describeSpecification s}"
    t := { t with specs := t.specs + 1 }
    let feeds := buildFeeds s
    t := { t with feeds := t.feeds + feeds.length }
    for f in feeds do
      let names := f.matchList.map (·.unknown.name)
      unless pathsOnly f.matchList && (reuse || names.eraseDups.length == names.length) do
        t := { t with shape := t.shape + 1 }
        if t.first.isNone then t := { t with first := some s!"shape\n{describeSpecification s}\nfeed:\n{describeSpecification f}" }
    let mut found := mutants.map fun _ => false
    for _ in [0:30] do
      let ((G, env, B, extra), g) := (do
        let G ← if t.specs % 2 == 0 then genAcyclicGraph s 8 else genFeedGraph s 8
        let env ← genEnv s G
        let B ← genBatch s G 2
        let extra ← repeatGen (← below 3) (below 8)
        return (G, env, B, extra) : Gen (Graph × Env × List Fact × List FactId)).run gen
      gen := g
      t := { t with graphs := t.graphs + 1 }
      let D := delivered s G env
      t := { t with facts := t.facts + D.eraseDups.length }
      t := { t with tuples := t.tuples + (feeds.map fun f => (f.tuples G env).length).sum }
      for f in feeds do
        unless antitoneHolds f G B env do
          t := { t with antitone := t.antitone + 1 }
          if t.first.isNone then t := { t with first := some (report s G env s!"antitone, batch {B.map fun f => (f.id, f.type, f.predecessors)}") }
      t := { t with deferLevels := t.deferLevels + deferViolations s G env feeds }
      let dv := deferViolations s G env (Filtered.buildFeeds s)
      t := { t with deferFiltered := t.deferFiltered + dv }
      if dv > 0 && t.firstDefer.isNone then
        t := { t with firstDefer := some (report s G env "deferral (filtered)" ++ "\nfeeds:\n" ++
          String.intercalate "\n" ((Filtered.buildFeeds s).map describeSpecification)) }
      t := { t with deferDerived := t.deferDerived + deferViolations s G env (derivedFeeds s) }
      t := { t with derivedFeedCount := t.derivedFeedCount + (derivedFeeds s).length,
                    filteredFeedCount := t.filteredFeedCount + (Filtered.buildFeeds s).length }
      unless coverHolds s G env (derivedDelivered s G env) extra do
        t := { t with coverDerived := t.coverDerived + 1 }
      for f in derivedFeeds s do
        unless antitoneHolds f G B env do
          t := { t with antitoneDerived := t.antitoneDerived + 1 }
      unless coverHolds s G env (Filtered.delivered s G env) extra do
        t := { t with coverFiltered := t.coverFiltered + 1 }
      unless coverHolds s G env D extra do
        t := { t with cover := t.cover + 1 }
        if t.first.isNone then t := { t with first := some (report s G env s!"cover, extra {extra}") }
      found := (found.zip mutants).map fun (was, (_, mu)) =>
        was || !coverHolds s G env (deliveredWith mu s G env) extra ||
          (buildFeedsWith mu s).any fun f => !antitoneHolds f G B env
    caught := (caught.zip found).map fun (n, b) => if b then n + 1 else n
  measureDownload
  IO.println s!"specifications {t.specs}, graphs {t.graphs}, feeds {t.feeds}, facts delivered {t.facts}, tuples {t.tuples}"
  IO.println s!"shape: {t.shape} feeds wrong"
  IO.println s!"antitone: {t.antitone} wrong"
  IO.println s!"cover: {t.cover} wrong"
  IO.println s!"filtered: cover {t.coverFiltered} wrong; deferral violations: levels {t.deferLevels}, filtered {t.deferFiltered}"
  IO.println s!"derived: cover {t.coverDerived} wrong, antitone {t.antitoneDerived} wrong, deferral {t.deferDerived} violations; feeds {t.derivedFeedCount / 30} vs filtered {t.filteredFeedCount / 30}"
  for ((label, _), n) in mutants.zip caught do
    IO.println s!"  mutant \"{label}\": caught on {n} of {t.specs + feedCases.length} specifications"
  if let some r := t.firstDefer then IO.println s!"\nFIRST DEFERRAL VIOLATION\n{r}"
  match t.first with
  | none => return (if caught.any (· == 0) then 1 else 0)
  | some r => IO.println s!"\nFIRST FAILURE\n{r}"; return 1
