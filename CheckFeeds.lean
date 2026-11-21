import JinagaSpec
import CheckGen
import JinagaSpec.FeedCases

/-!
# Randomized check of feeds

`lake exe check-feeds [seed] [reuse]` checks, on random well-formed
specifications and graphs, the requirements of chapter 12:

* **shape** — every feed has path conditions, and negative conditions over
  matches with only path conditions (`buildFeeds_feedShape`), and binds each of
  its labels once.
* **antitone** — a tuple a feed finds after a fresh batch arrives, all of whose
  facts were there before, was a tuple before (`feed_antitone`): tuples are
  never inserted behind a bookmark.
* **cover** — a replica that holds the givens and every fact the feeds deliver,
  with their predecessors, and any other facts of the graph it likes, reads
  what the replicator reads, child specifications' results included.
* **deferral** — a new client is not sent the details of an entity that is
  excluded and whose exclusion nothing has cancelled, a child specification's
  facts about it included.

A third of the specifications have child specifications, two deep at most
(`genChildSpec`).

Each mutant changes one rule of `buildFeeds`. Every one must be caught by one
of the checks, or the check is not testing that rule. The mutants are one
builder, `buildFeedsWith`, parameterized over the rule that varies;
`buildFeeds` itself stays as the specification reads, and is checked to make the
same feeds as the mutant family with no rule changed.
-/
open JinagaSpec Build

/-- Which rule of `buildFeeds` a mutant changes. -/
structure Mutant where
  /-- Each negative condition emits an excluding feed. -/
  excludes : Bool := true
  /-- An excluding feed stops at its condition's level. -/
  excludingStops : Bool := true
  /-- A feed is filtered by each negative condition. -/
  filters : Bool := true
  /-- A filter is the condition's level, rather than the whole condition. -/
  filtersLevel : Bool := true
  /-- Each negative condition is restored through a canceller's level. -/
  restores : Bool := true
  /-- A restoring feed drops the negative conditions of the fact it restores. -/
  restoringDrops : Bool := true
  /-- A positive feed goes on to each child specification. -/
  children : Bool := true
  /-- A restoring feed goes on to each child specification too. -/
  restoredChildren : Bool := true
  /-- A child specification's feeds go on from the parent's feed with its filters. -/
  childFilters : Bool := true
  /-- An excluding feed goes on to each child specification too. -/
  excludedChildren : Bool := false
  /-- Which feeds are kept. -/
  keep : Specification → Bool := traversesSuccessors

mutual
  /-- The positive feeds of a level after `pre`, each tagged with whether it was
  restored, and its excluding feeds. -/
  partial def levelWith (mu : Mutant) (pre : List Match × Bool) :
      List Match → List (List Match × Bool) × List (List Match)
    | [] => ([pre], [])
    | m :: rest =>
      let (units, exc) := unitWith mu pre m
      let rs := units.map (levelWith mu · rest)
      (rs.flatMap (·.1), exc ++ rs.flatMap (·.2))

  partial def unitWith (mu : Mutant) (pre : List Match × Bool) (m : Match) :
      List (List Match × Bool) × List (List Match) := Id.run do
    let mut pos := [(pre.1 ++ (flatten [m]).map Match.paths, pre.2)]
    let mut exc := []
    for ns in negativesOf [m] do
      let lvl := level ns
      let chain := if mu.restoringDrops then lvl
        else (flatten ns).map fun | .mk u cs => .mk u (cs.filterMap fun
          | .path pc => some (.path pc)
          | .existential false ms => some (.existential false (level ms))
          | _ => none)
      let mut next := []
      for (P, restored) in pos do
        if mu.excludes then
          if mu.excludingStops then exc := exc ++ [P ++ lvl] else next := next ++ [(P ++ lvl, restored)]
        next := next ++ [(if mu.filters then addLast (.existential false (if mu.filtersLevel then lvl else ns)) P else P,
          restored)]
        if mu.restores then
          for ns' in negativesOf ns do
            let (rp, re) := levelWith mu (P ++ chain, true) ns'
            next := next ++ rp
            exc := exc ++ re
      pos := next
    return (pos, exc)
end

mutual
  /-- A positive feed, and the feeds it goes on to through each child
  specification of `p`. -/
  partial def projectionWith (mu : Mutant) (p : Projection) : List Match × Bool → List (List Match)
    | (P, restored) =>
      P :: if mu.children && (mu.restoredChildren || !restored) then
        p.children.flatMap fun (ms, q) =>
          withChildren mu q (levelWith mu (if mu.childFilters then P else P.map Match.paths, restored) ms)
      else []

  /-- The feeds of a walk: each positive feed with what it goes on to, and each
  excluding feed. -/
  partial def withChildren (mu : Mutant) (p : Projection) :
      List (List Match × Bool) × List (List Match) → List (List Match)
    | (pos, exc) =>
      pos.flatMap (projectionWith mu p) ++
        if mu.excludedChildren then exc.flatMap fun E => projectionWith mu p (E, false) else exc
end

def toFeeds (s : Specification) (keep : Specification → Bool) (Fs : List (List Match)) : List Specification :=
  (Fs.map fun ms => ({ given := usedGivens s.given ms, matchList := ms, projection := .composite [] } : Specification)).filter keep

def buildFeedsWith (mu : Mutant) (s : Specification) : List Specification :=
  toFeeds s mu.keep (withChildren mu s.projection (levelWith mu ([], false) s.matchList))

def deliveredWith (mu : Mutant) (s : Specification) (g : Graph) (env : Env) : List FactId :=
  (buildFeedsWith mu s).flatMap fun f => (f.tuples g env).flatten

def mutants : List (String × Mutant) := [
  ("no excluding feeds", { excludes := false }),
  ("an excluding feed goes on with the rest of the level", { excludingStops := false }),
  ("no filters", { filters := false }),
  ("a filter is the whole condition", { filtersLevel := false }),
  ("no restoring feeds", { restores := false }),
  ("a restoring feed keeps the negative conditions of the fact it restores", { restoringDrops := false }),
  ("no child specification feeds", { children := false }),
  ("a restoring feed does not go on to child specifications", { restoredChildren := false }),
  ("a child specification's feeds drop the parent's filters", { childFilters := false }),
  ("an excluding feed goes on to child specifications", { excludedChildren := true }),
  ("only feeds whose first match walks to a successor are kept",
    { keep := fun f => match f.matchList with
        | m :: _ => m.conditions.any fun | .path pc => !pc.rolesLeft.isEmpty | _ => false
        | [] => false })]

/-! ## Levels, for comparison

The feeds of 13daae9: one per level, with no filters. They cover the
specification, but a new client downloads the details of every excluded entity. -/

partial def levels (pre ms : List Match) : List (List Match) :=
  let flat := flatten ms
  let here := pre ++ flat.map Match.paths
  here :: (flat.flatMap Match.negatives).flatMap (levels here)

def levelsDelivered (s : Specification) (g : Graph) (env : Env) : List FactId :=
  (toFeeds s traversesSuccessors (levels [] s.matchList)).flatMap fun f => (f.tuples g env).flatten

/-! ## Deferral

A new client must not receive the details of an entity that is excluded by a
negative condition, none of whose witnesses has any cancelling fact
(`feeds_defer`). Each feed must be a feed of some descendant, binding only its
labels, that carries no such details of the descendant's entities. Over the
descendant's top level, joined: for each prefix `p` through a match `m`, and
each negative condition of `m` that is witnessed at `p` and none of whose
witnesses has a fact of any of its own negative conditions, no tuple of the
feed binds `p` and goes on to a match after `m`. -/

def keyOn (names : List Name) (e : Env) : List (Option FactId) := names.map e

/-- How many excluded, uncancelled prefixes of `d`'s matches the feed `f` carries
past their match. A prefix binds the top-level matches through `m`, each with
its positive conditions joined: those are part of the entity. Its details are
the top-level matches after `m`, a child specification's included. -/
def violationsOn (d : Specification) (G : Graph) (env : Env) (f : Specification) : Nat := Id.run do
  let ts := evalMatches G env f.matchList
  let fn := names f.matchList
  let mut n := 0
  for i in [0:d.matchList.length] do
    let pre := flatten (d.matchList.take (i + 1))
    let later := names (flatten (d.matchList.drop (i + 1)))
    if later.any fn.contains then
      for p in evalMatches G env (pre.map Match.paths) do
        for ns in negativesOf ((d.matchList.drop i).take 1) do
          let witnesses := evalMatches G p (level ns)
          let uncancelled := witnesses.all fun w => (negativesOf ns).all fun ns' => (evalMatches G w (level ns')).isEmpty
          if !witnesses.isEmpty && uncancelled then
            if ts.any fun τ => keyOn (names pre) τ == keyOn (names pre) p &&
                later.any fun y => fn.contains y && (τ y).isSome then
              n := n + 1
  return n

/-- How many feeds are not a feed of a descendant of `s`, binding only its
labels, that carries none of its excluded, uncancelled entities' details. -/
def deferViolations (s : Specification) (G : Graph) (env : Env) (feeds : List Specification) : Nat :=
  (feeds.filter fun f => !s.descendants.any fun d =>
    (names f.matchList).all (declaredMatches d.matchList).contains && violationsOn d G env f == 0).length

/-! ## What a new client downloads

Events of a tenant, each with a history of names; most deleted, some of those
restored. A new client holds what the feeds deliver and its predecessors. -/

def eventsSpec : Specification :=
  spec [("t", "Tenant")]
    [unknown "e" "Event" [path [role "tenant" "Tenant"] "t",
      notExists [unknown "d" "Delete" [path [role "event" "Event"] "e",
        notExists [unknown "x" "Restore" [path [role "delete" "Delete"] "d"]]]]],
     unknown "n" "Name" [path [role "event" "Event"] "e"]]
    (.composite [.fact "event" "e", .fact "name" "n"])

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
  let levels := newClientFacts eventsSpec g env (levelsDelivered eventsSpec g env)
  let feeds := newClientFacts eventsSpec g env (delivered eventsSpec g env)
  let results := (eventsSpec.read g env).length
  IO.println s!"new client, 50 events of 10 names, 30 deleted, 10 of those restored: graph {g.length} facts, {results} results; levels download {levels}, feeds {feeds}"


/-! ## The checks -/

def feedShape (ms : List Match) : Bool :=
  ms.all fun m => m.conditions.all fun
    | .path _ => true
    | .existential false ns => ns.all (·.conditions.all (·.isPath))
    | .existential true _ => false

def coverHolds (s : Specification) (g : Graph) (env : Env) (D extra : List FactId) : Bool :=
  sameResults (readsOf s (replica s g env D extra) env) (readsOf s g env)

/-- Tuples of `f` after `B` whose facts were all in `g` were tuples before. -/
def antitoneHolds (f : Specification) (g : Graph) (B : List Fact) (env : Env) : Bool :=
  let before := f.tuples g env
  (f.tuples (g ++ B) env).all fun t => t.any (fun id => B.any (·.id == id)) || before.contains t

structure Tally where
  specs : Nat := 0
  graphs : Nat := 0
  feeds : Nat := 0
  facts : Nat := 0
  shape : Nat := 0
  antitone : Nat := 0
  cover : Nat := 0
  defer : Nat := 0
  first : Option String := none

def report (s : Specification) (g : Graph) (env : Env) (what : String) : String :=
  s!"{what}\n{describeSpecification s}\ngraph: {g.map fun f => (f.id, f.type, f.predecessors)}\n" ++
    s!"givens: {s.given.map fun l => (l.name, env l.name)}"

/-- A mutant is caught on a graph when a replica of its feeds reads something
else, a tuple of one of its feeds appears behind a bookmark, or it sends a new
client the details of an excluded entity. -/
def caughtOn (mu : Mutant) (s : Specification) (G : Graph) (env : Env) (B : List Fact) (extra : List FactId) : Bool :=
  !coverHolds s G env (deliveredWith mu s G env) extra ||
    (buildFeedsWith mu s).any (fun f => !antitoneHolds f G B env) ||
    deferViolations s G env (buildFeedsWith mu s) > 0

def main (args : List String) : IO UInt32 := do
  let seed := (args.head?.bind String.toNat?).getD 1
  let reuse := args.contains "reuse"
  let mut gen : StdGen × Nat := (mkStdGen seed, 0)
  let mut t : Tally := {}
  let mut caught : List Nat := mutants.map fun _ => 0
  for c in feedCases do
    unless feedReady c.spec do
      throw <| IO.userError s!"feed case {c.name} is not well-formed, or repeats a label"
    -- The production builder makes the mutant family's feeds, with no rule changed.
    unless sameSet ((buildFeeds c.spec).map (·.matchList)) ((buildFeedsWith {} c.spec).map (·.matchList)) do
      throw <| IO.userError s!"buildFeeds differs from the mutant family on {c.name}"
    let all := c.graph.map (·.id)
    for extra in [[], all] do
      unless coverHolds c.spec c.graph c.env (delivered c.spec c.graph c.env) extra do
        t := { t with cover := t.cover + 1 }
        if t.first.isNone then t := { t with first := some (report c.spec c.graph c.env s!"cover, case {c.name}, extra {extra}") }
    if deferViolations c.spec c.graph c.env (buildFeeds c.spec) > 0 then
      t := { t with defer := t.defer + 1 }
      if t.first.isNone then t := { t with first := some (report c.spec c.graph c.env s!"deferral, case {c.name}") }
    caught := (caught.zip mutants).map fun (n, (_, mu)) =>
      if [[], all].any (fun extra => caughtOn mu c.spec c.graph c.env [] extra) then n + 1 else n
  for _ in [0:600] do
    let (s, g) := (match t.specs % 3 with
      | 0 => genFeedSpec
      | 1 => genChildSpec
      | _ => genSpec false 3 reuse).run gen
    gen := g
    unless s.descendants.all isWellFormed do
      throw <| IO.userError s!"the generator made a specification that is not well-formed:\n{describeSpecification s}"
    t := { t with specs := t.specs + 1 }
    let feeds := buildFeeds s
    unless sameSet (feeds.map (·.matchList)) ((buildFeedsWith {} s).map (·.matchList)) do
      throw <| IO.userError s!"buildFeeds differs from the mutant family:\n{describeSpecification s}"
    t := { t with feeds := t.feeds + feeds.length }
    for f in feeds do
      let names := f.matchList.map (·.unknown.name)
      unless feedShape f.matchList && (reuse || names.eraseDups.length == names.length) do
        t := { t with shape := t.shape + 1 }
        if t.first.isNone then t := { t with first := some s!"shape\n{describeSpecification s}\nfeed:\n{describeSpecification f}" }
    let mut found := mutants.map fun _ => false
    for _ in [0:30] do
      let ((G, env, B, extra), g) := (do
        let G ← if t.specs % 3 == 0 then genAcyclicGraph s 8 else genFeedGraph s 8
        let env ← genEnv s G
        let B ← genBatch s G 2
        let extra ← repeatGen (← below 3) (below 8)
        return (G, env, B, extra) : Gen (Graph × Env × List Fact × List FactId)).run gen
      gen := g
      t := { t with graphs := t.graphs + 1 }
      let D := delivered s G env
      t := { t with facts := t.facts + D.eraseDups.length }
      for f in feeds do
        unless antitoneHolds f G B env do
          t := { t with antitone := t.antitone + 1 }
          if t.first.isNone then t := { t with first := some (report s G env s!"antitone, batch {B.map fun f => (f.id, f.type, f.predecessors)}") }
      unless coverHolds s G env D extra do
        t := { t with cover := t.cover + 1 }
        if t.first.isNone then t := { t with first := some (report s G env s!"cover, extra {extra}") }
      unless reuse do
        if deferViolations s G env feeds > 0 then
          t := { t with defer := t.defer + 1 }
          if t.first.isNone then t := { t with first := some (report s G env "deferral") }
      found := (found.zip mutants).map fun (was, (_, mu)) => was || caughtOn mu s G env B extra
    caught := (caught.zip found).map fun (n, b) => if b then n + 1 else n
  measureDownload
  IO.println s!"specifications {t.specs}, graphs {t.graphs}, feeds {t.feeds}, facts delivered {t.facts}"
  IO.println s!"shape: {t.shape} feeds wrong"
  IO.println s!"antitone: {t.antitone} wrong"
  IO.println s!"cover: {t.cover} wrong"
  IO.println s!"deferral: {t.defer} wrong"
  for ((label, _), n) in mutants.zip caught do
    IO.println s!"  mutant \"{label}\": caught on {n} of {t.specs + feedCases.length} specifications"
  match t.first with
  | none => return (if caught.any (· == 0) then 1 else 0)
  | some r => IO.println s!"\nFIRST FAILURE\n{r}"; return 1
