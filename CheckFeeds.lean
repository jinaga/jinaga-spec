import JinagaSpec
import CheckGen
import JinagaSpec.FeedCases

/-!
# Randomized check of feeds

`lake exe check-feeds [seed] [reuse]` checks, on random well-formed
specifications and graphs:

* **shape** — every feed `buildFeeds` makes has `FeedShape`, and declares each
  of its labels once (`buildFeeds_shape`).
* **antitone** — a tuple a feed finds after a fresh batch arrives, all of whose
  facts were there before, was a tuple before (`feed_antitone`). This is what
  lets a replicator page a feed by a bookmark.
* **cover** — a replica that holds the givens and every fact the feeds deliver,
  with their predecessors, and any other facts of the graph it likes, reads
  what the replicator reads (`feeds_cover`, stated in `Proofs/Feeds.lean`).

Each mutant changes one rule of `buildFeeds`. Every one must be caught by one
of the checks, or the check is not testing that rule. The mutants are one
machine, `runWith`, parameterized over the rule that varies; `run` itself stays
as `jinaga.js` reads.
-/
open JinagaSpec Build

/-- Which rule of `buildFeeds` a mutant changes. -/
structure Mutant where
  /-- A restoring branch stops at the end of its condition, as an excluding one does. -/
  restoringStops : Bool := false
  /-- An excluding branch is handed the conditions still waiting on its match. -/
  branchKeepsPending : Bool := true
  /-- A restoring branch skips the rest of the excluded condition. -/
  restoringSkips : Bool := true
  /-- A restoring branch drops the conditions its excluding feed attached. -/
  restoringUnattaches : Bool := true
  /-- The current feed keeps a negative condition stripped. -/
  strip : Bool := true
  /-- Restoring branches are emitted. -/
  restoring : Bool := true
  /-- Which feeds are kept. -/
  keep : Specification → Bool := traversesSuccessors

partial def runWith (mu : Mutant) (givens : List Label) (feed : Specification) (parity base : Nat) : List Work → List Specification
  | [] => [feed]
  | .stop p :: w => if p == parity then [feed] else runWith mu givens feed parity base w
  | .matches [] :: w => runWith mu givens feed parity base w
  | .matches (.mk u cs :: ms) :: w =>
    runWith mu givens (withMatch givens feed (.mk u cs)) parity base (.conditions u.name cs :: .matches ms :: w)
  | .conditions _ [] :: w => runWith mu givens feed parity base w
  | .conditions l (.path _ :: cs) :: w => runWith mu givens feed parity base (.conditions l cs :: w)
  | .conditions l (.existential true ms :: cs) :: w =>
    runWith mu givens feed parity base (.matches ms :: .conditions l cs :: w)
  | .conditions l (.existential false ms :: cs) :: w =>
    let rest := .conditions l cs :: w
    let branch := if parity % 2 == 0
      then runWith mu givens feed (parity + 1) feed.matchList.length
        (.matches ms :: .stop (parity + 1) :: if mu.branchKeepsPending then rest else w)
      else if !mu.restoring then []
      else
        let rest := if mu.restoringSkips then afterStop parity rest else rest
        runWith mu givens (if mu.restoringUnattaches then unattach base feed else feed) (parity + 1) base
          (.matches ms :: if mu.restoringStops then .stop (parity + 1) :: rest else rest)
    let kept := if mu.strip then withCondition givens feed l ms
      else { feed with matchList := attach l (.existential false ms) feed.matchList }
    branch ++ runWith mu givens kept parity base rest

def buildFeedsWith (mu : Mutant) (s : Specification) : List Specification :=
  (runWith mu s.given { given := [], matchList := [], projection := .composite [] } 0 0 [.matches s.matchList]).filter mu.keep

def deliveredWith (mu : Mutant) (s : Specification) (g : Graph) (env : Env) : List FactId :=
  (buildFeedsWith mu s).flatMap fun f => (f.tuples g env).flatten

def mutants : List (String × Mutant) := [
  ("restoring feeds stop", { restoringStops := true }),
  ("an excluding branch loses the conditions waiting on its match (jinaga.js#368)", { branchKeepsPending := false }),
  ("a restoring branch keeps the conditions its excluding feed attached", { restoringUnattaches := false }),
  ("both, as jinaga.js does today", { restoringSkips := false, restoringUnattaches := false }),
  ("negative conditions are kept whole", { strip := false }),
  ("no restoring feeds", { restoring := false }),
  ("only feeds whose first match walks to a successor are kept",
    { keep := fun f => match f.matchList with
        | m :: _ => m.conditions.any fun | .path pc => !pc.rolesLeft.isEmpty | _ => false
        | [] => false })]

/-! ## The checks -/

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
  /-- Feeds made by restoring branches that do not skip the rest of the excluded condition. -/
  unskipped : Nat := 0
  shape : Nat := 0
  antitone : Nat := 0
  cover : Nat := 0
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
    let (s, g) := (if ← pure (t.specs % 2 == 0) then genFeedSpec else genSpec false 3 reuse).run gen
    gen := g
    unless isWellFormed s do
      throw <| IO.userError s!"the generator made a specification that is not well-formed:\n{describeSpecification s}"
    t := { t with specs := t.specs + 1 }
    let feeds := buildFeeds s
    t := { t with feeds := t.feeds + feeds.length, unskipped := t.unskipped + (buildFeedsWith { restoringSkips := false } s).length }
    for f in feeds do
      let names := f.matchList.map (·.unknown.name)
      unless feedShape f.matchList && names.eraseDups.length == names.length do
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
      for f in feeds do
        unless antitoneHolds f G B env do
          t := { t with antitone := t.antitone + 1 }
          if t.first.isNone then t := { t with first := some (report s G env s!"antitone, batch {B.map fun f => (f.id, f.type, f.predecessors)}") }
      unless coverHolds s G env (delivered s G env) extra do
        t := { t with cover := t.cover + 1 }
        if t.first.isNone then t := { t with first := some (report s G env s!"cover, extra {extra}") }
      found := (found.zip mutants).map fun (was, (_, mu)) =>
        was || !coverHolds s G env (deliveredWith mu s G env) extra ||
          (buildFeedsWith mu s).any fun f => !antitoneHolds f G B env
    caught := (caught.zip found).map fun (n, b) => if b then n + 1 else n
  IO.println s!"specifications {t.specs}, graphs {t.graphs}, feeds {t.feeds} ({t.unskipped} if a restoring branch did not skip the rest of the excluded condition)"
  IO.println s!"shape: {t.shape} feeds wrong"
  IO.println s!"antitone: {t.antitone} wrong"
  IO.println s!"cover: {t.cover} wrong"
  for ((label, _), n) in mutants.zip caught do
    IO.println s!"  mutant \"{label}\": caught on {n} of {t.specs + feedCases.length} specifications"
  match t.first with
  | none => return (if caught.any (· == 0) then 1 else 0)
  | some r => IO.println s!"\nFIRST FAILURE\n{r}"; return 1
