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
      unless coverHolds s G env D extra do
        t := { t with cover := t.cover + 1 }
        if t.first.isNone then t := { t with first := some (report s G env s!"cover, extra {extra}") }
      found := (found.zip mutants).map fun (was, (_, mu)) =>
        was || !coverHolds s G env (deliveredWith mu s G env) extra ||
          (buildFeedsWith mu s).any fun f => !antitoneHolds f G B env
    caught := (caught.zip found).map fun (n, b) => if b then n + 1 else n
  IO.println s!"specifications {t.specs}, graphs {t.graphs}, feeds {t.feeds}, facts delivered {t.facts}, tuples {t.tuples}"
  IO.println s!"shape: {t.shape} feeds wrong"
  IO.println s!"antitone: {t.antitone} wrong"
  IO.println s!"cover: {t.cover} wrong"
  for ((label, _), n) in mutants.zip caught do
    IO.println s!"  mutant \"{label}\": caught on {n} of {t.specs + feedCases.length} specifications"
  match t.first with
  | none => return (if caught.any (· == 0) then 1 else 0)
  | some r => IO.println s!"\nFIRST FAILURE\n{r}"; return 1
