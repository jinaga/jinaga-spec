import CheckGen

/-!
# Randomized check of inversion

`lake exe check-inverse [seed]` measures `invertSpecification` against law L4 of
jinaga.js's `docs/analysis/specification-invariants.md`, on random well-formed
specifications with existential conditions nested to depth 3, random graphs,
and a fresh fact `f` (its id is new, and its predecessors are in the graph):

* **Complete.** Every result gained by inserting `f` is reported by an "add"
  inverse, and every result lost is reported by a "remove" inverse.
* **Sound**, in the weak sense a re-checking stream needs nothing of, but a
  stream that trusts its inverses does: an "add" never reports a result the
  graph does not have, and a "remove" never reports one it still has.

`lake exe check-inverse dump <file>` writes random specifications and this
port's inverses as JSON, for `ports/typescript/inverse-diff.ts` to compare with
jinaga.js. It proves nothing.
-/
open JinagaSpec Build
open Lean (Json)

deriving instance Inhabited for Fact

def JinagaSpec.Operation.name : Operation → String
  | .add => "add"
  | .remove => "remove"

def JinagaSpec.Inverse.describe (ι : Inverse) : String :=
  s!"{ι.operation.name}\n" ++ describeMatch 0 ι.given ++ describeMatches 1 ι.matchList

/-! ## Counting -/

structure Tally where
  graphs : Nat := 0
  gained : Nat := 0
  lost : Nat := 0
  missedGained : Nat := 0
  missedLost : Nat := 0
  addAbsent : Nat := 0
  removePresent : Nat := 0
deriving Inhabited

def Tally.add (t u : Tally) : Tally :=
  { graphs := t.graphs + u.graphs, gained := t.gained + u.gained, lost := t.lost + u.lost,
    missedGained := t.missedGained + u.missedGained, missedLost := t.missedLost + u.missedLost,
    addAbsent := t.addAbsent + u.addAbsent, removePresent := t.removePresent + u.removePresent }

def fired (inverses : List Inverse) (op : Operation) (s : Specification) (g : Graph) (env : Env) (f : Fact) : List Row :=
  (inverses.filter (·.operation == op)).flatMap (·.fire s g env f)

def showGraph (g : Graph) : String :=
  "\n".intercalate (g.map fun f => s!"  {f.id}: {f.type} {f.predecessors}")

/-- One graph and one fresh fact: what L4 asks, and a report of the first miss. -/
def measureL4 (s : Specification) (inverses : List Inverse) (store : Graph) (env : Env) (f : Fact) :
    Tally × Option String × Option String :=
  let g' := store ++ [f]
  let old := s.evaluate store env
  let new := s.evaluate g' env
  let gained := new.filter (!old.contains ·)
  let lost := old.filter (!new.contains ·)
  let adds := fired inverses .add s g' env f
  let removes := fired inverses .remove s g' env f
  let missedGained := gained.filter (!adds.contains ·)
  let missedLost := lost.filter (!removes.contains ·)
  let t : Tally := {
    graphs := 1
    gained := gained.length
    lost := lost.length
    missedGained := missedGained.length
    missedLost := missedLost.length
    addAbsent := (adds.filter (!new.contains ·)).length
    removePresent := (removes.filter (new.contains ·)).length }
  let givens := s.given.map fun l => (l.name, env l.name)
  let report (rows : List Row) := if rows.isEmpty then none else
    some s!"{describeSpecification s}givens {givens}\ngraph\n{showGraph store}\nnew fact {f.id}: {f.type} {f.predecessors}\nmissed {rows}"
  (t, report missedGained, report missedLost)

def checkSpec (s : Specification) (inverses : List Inverse) (graphs : Nat) :
    Gen (Tally × Option String × Option String) := do
  let mut tally : Tally := {}
  let mut gainedReport := none
  let mut lostReport := none
  for n in [0:graphs] do
    -- Half the time, look for a graph that already has a result, so that a
    -- new fact has something to remove.
    let mut store ← genGraph s 8
    let mut env ← genEnv s store
    if n % 2 == 0 then
      for _ in [0:10] do
        if (s.evaluate store env).isEmpty then
          store ← genGraph s 8
          env ← genEnv s store
    let f ← genFreshFact s store 8
    let (t, rg, rl) := measureL4 s inverses store env f
    tally := tally.add t
    if gainedReport.isNone then gainedReport := rg
    if lostReport.isNone then lostReport := rl
  return (tally, gainedReport, lostReport)

/-! ## Mutants

Each must be caught, or the check is not testing what it claims. -/

/-- A fact the store already holds, notified again (jinaga/jinaga.js#337).
Every inverse assumes its fact has no successors; this one may. Caught when an
"add" reports a result the store does not have. -/
def notFreshCaught (s : Specification) (inverses : List Inverse) (graphs : Nat) : Gen Bool := do
  let mut caught := false
  for _ in [0:graphs] do
    let store ← genGraph s 8
    let env ← genEnv s store
    -- Prefer a fact with successors: those are the ones whose inverses
    -- skipped a condition they should not have.
    let withSuccessors := store.filter fun p => store.any (·.predecessors.any (·.2 == p.id))
    let f ← pick (if withSuccessors.isEmpty then store else withSuccessors)
    let result := s.evaluate store env
    if (fired inverses .add s store env f).any (!result.contains ·) then caught := true
  return caught

def dropExistentials : Match → Match
  | .mk u cs => .mk u (cs.filter (·.isPath))

/-- Every inverse loses its existential conditions. Caught when an "add"
reports a result the graph does not have. -/
def dropConditions (ι : Inverse) : Inverse :=
  { ι with given := dropExistentials ι.given, matchList := ι.matchList.map dropExistentials }

/-! ## Inverses built from the specification, by rule

To decide which rule an inverse must follow before proving one, these build an
inverse directly from the specification for each way `f` can reach a result,
without `shakeTree` or `simplifyMatches`: the semantics ranges over every fact,
so the order of the matches only has to keep every label bound before it is
used.

A *chain* is a path from the specification's matches down through existential
conditions, one per level, to an unknown that `f` is bound to. The inverse
flattens the chain: each level's matches become ordinary matches, and the
condition the chain passes through is removed. What happens to the *other*
existential conditions at each level is the rule under test. -/

/-- Each chain: the levels it passes through, each with the condition it
takes, and the unknown at the bottom. -/
partial def chains (level : List Match) : List (List (List Match × Condition) × Label) :=
  level.map (([], ·.unknown)) ++
    (level.flatMap (·.conditions)).flatMap fun c =>
      match c with
      | .path _ => []
      | .existential _ inner => (chains inner).map fun (steps, pin) => ((level, c) :: steps, pin)

/-- A rule says what becomes of a level's conditions. It is told whether the
level gained its solution or lost it, the condition the chain takes from this
level (if any), and whether the result as a whole was gained. -/
abbrev Rule := (levelGained : Bool) → (taken : Option Condition) → (resultGained : Bool) → Condition → Option Condition

def flatten (rule : Rule) (top : List Match) (steps : List (List Match × Condition)) : List Match :=
  let flags := steps.map fun (_, c) => match c with | .existential e _ => e | .path _ => true
  let finalLevel := match steps.getLast? with
    | some (_, .existential _ inner) => inner
    | _ => top
  let levels := (steps.map (·.1)) ++ [finalLevel]
  let resultGained := (flags.filter (!·)).length % 2 == 0
  (levels.zip (List.range levels.length)).flatMap fun (ms, k) =>
    let gained := ((flags.drop k).filter (!·)).length % 2 == 0
    let taken := (steps[k]?).map (·.2)
    ms.map fun m => .mk m.unknown (m.conditions.filterMap (rule gained taken resultGained))

/-- Every result any chain's inverse reports, whatever its operation. -/
def ruleCandidates (rule : Rule) (s : Specification) (g : Graph) (env : Env) (f : Fact) : List Row :=
  let top := s.given.map (fun l => Match.mk l []) ++ s.matchList
  ((chains top).filter (·.2.type == f.type)).flatMap fun (steps, pin) =>
    ((evalMatches g (fun _ => none) (flatten rule top steps)).filter fun σ =>
      σ pin.name == some f.id && s.given.all fun l => σ l.name == env l.name).map
      fun σ => s.projection.labels.map σ

/-- jinaga.js#338 as proposed: keep the enclosing conditions as written when the
result was gained, negate them when it was lost, keep every sibling. -/
def rule338 : Rule := fun _ taken resultGained c =>
  if some c == taken then
    match c with
    | .existential e ms => if resultGained then some c else some (.existential (!e) ms)
    | .path _ => some c
  else some c

/-- What a producer of candidates is given: the specification, the givens, the
graph before `f`, and `f`. -/
abbrev Producer := Specification → Env → Graph → Fact → List Row

def byRule (rule : Rule) : Producer := fun s env store f => ruleCandidates rule s (store ++ [f]) env f

/-- Results gained or lost that a producer's candidates miss. -/
def ruleMisses (produce : Producer) (s : Specification) (graphs : Nat) : Gen (Nat × Option String) := do
  let mut missed := 0
  let mut report := none
  for n in [0:graphs] do
    let mut store ← genGraph s 8
    let mut env ← genEnv s store
    if n % 2 == 0 then
      for _ in [0:10] do
        if (s.evaluate store env).isEmpty then
          store ← genGraph s 8
          env ← genEnv s store
    let f ← genFreshFact s store 8
    let g' := store ++ [f]
    let old := s.evaluate store env
    let new := s.evaluate g' env
    let changed := new.filter (!old.contains ·) ++ old.filter (!new.contains ·)
    let m := if changed.isEmpty then [] else
      let candidates := produce s env store f
      changed.filter (!candidates.contains ·)
    missed := missed + m.length
    if !m.isEmpty && report.isNone then
      report := some s!"{describeSpecification s}graph\n{showGraph store}\nnew fact {f.id}: {f.type} {f.predecessors}\nmissed {m}"
  return (missed, report)

/-! ## Named cases -/

/-- jinaga/jinaga.js#338: "accounts with a current mirror", `exists { notExists }`.
Retiring the only current mirror removes the account. -/
def existsNotExists : Specification × Graph × Fact :=
  let s := spec [("p1", "Root")]
    [unknown "u1" "Account" [path [role "root" "Root"] "p1",
      exists' [unknown "e1" "Mirror" [path [role "account" "Account"] "u1",
        notExists [unknown "e2" "Retired" [path [role "mirror" "Mirror"] "e1"]]]]]]
    (fact "u1")
  let g : Graph := [
    { id := 0, type := "Root", predecessors := [] },
    { id := 1, type := "Account", predecessors := [("root", 0)] },
    { id := 2, type := "Mirror", predecessors := [("account", 1)] }]
  (s, g, { id := 3, type := "Retired", predecessors := [("mirror", 2)] })

/-- Two sibling `notExists` conditions that one fact falsifies together. Each
inverse removes its own condition and keeps the other, which the same fact
falsifies on the new graph. -/
def siblingNotExists : Specification × Graph × Fact :=
  let s := spec [("p1", "Root")]
    [unknown "u1" "Task" [path [role "root" "Root"] "p1",
      notExists [unknown "e1" "Done" [path [role "task" "Task"] "u1"]],
      notExists [unknown "e2" "Done" [path [role "other" "Task"] "u1"]]]]
    (fact "u1")
  let g : Graph := [
    { id := 0, type := "Root", predecessors := [] },
    { id := 1, type := "Task", predecessors := [("root", 0)] }]
  (s, g, { id := 2, type := "Done", predecessors := [("task", 1), ("other", 1)] })

def namedCase (label : String) (c : Specification × Graph × Fact) : IO Unit := do
  let (s, g, f) := c
  let env : Env := fun n => if n = "p1" then some 0 else none
  match invertSpecification s with
  | .error e => IO.println s!"  {label}: cannot invert: {e.message}"
  | .ok inverses =>
    let (t, _, _) := measureL4 s inverses g env f
    let g' := g ++ [f]
    let old := s.evaluate g env
    let new := s.evaluate g' env
    let changed := new.filter (!old.contains ·) ++ old.filter (!new.contains ·)
    let missedBy (produce : Producer) := (changed.filter (!(produce s env g f).contains ·)).length
    IO.println s!"  {label}: gained {t.gained} (missed {t.missedGained}), lost {t.lost} (missed {t.missedLost}); #338 as proposed misses {missedBy (byRule rule338)}, `candidates` {missedBy candidates}"

/-! ## Reordering (layer 4) -/

/-- Every match leads with a path condition from a label already bound, so a
reader can walk to it. -/
def navigable (bound : List Name) : List Match → Bool
  | [] => true
  | .mk u cs :: rest =>
    (match cs.head? with
      | some (.path pc) => bound.contains pc.labelRight
      | _ => false) && navigable (u.name :: bound) rest

structure ReorderTally where
  inverses : Nat := 0
  refused : Nat := 0
  notNavigable : Nat := 0
  startsAtPin : Nat := 0
  disagree : Nat := 0
  withResults : Nat := 0
  mutantCaught : Nat := 0

/-- Reorder every inverse of `s`; compare each with the original on random graphs. -/
def checkReorder (s : Specification) (graphs : Nat) : Gen (ReorderTally × Option String) := do
  let mut t : ReorderTally := {}
  let mut report := none
  let givens := s.given.map (·.name)
  for i in inverses s do
    t := { t with inverses := t.inverses + 1 }
    match reorderChecked i with
    | none => t := { t with refused := t.refused + 1 }
    | some r =>
      if !navigable (pinLabel :: givens) r.matchList then
        t := { t with notNavigable := t.notNavigable + 1 }
        if report.isNone then report := some s!"not navigable\n{describeSpecification i}reordered\n{describeSpecification r}"
      if (r.matchList.head?.bind (·.conditions.head?)) == some pinCondition then
        t := { t with startsAtPin := t.startsAtPin + 1 }
      for _ in [0:graphs] do
        let store ← genGraph s 8
        let env ← genEnv s store
        let f ← genFreshFact s store 8
        let g' := store ++ [f]
        let e := pinEnv s env f
        let expected := i.evaluate g' e
        if !expected.isEmpty then t := { t with withResults := t.withResults + 1 }
        -- Mutant: a reordering that forgets to reverse the edges it moves.
        let unreversed := r.matchList.map fun
          | .mk u cs => .mk u (cs.map fun
            | .path pc => .path { rolesLeft := pc.rolesRight, labelRight := pc.labelRight, rolesRight := pc.rolesLeft }
            | c => c)
        if !sameSet expected ({ r with matchList := unreversed }.evaluate g' e) then
          t := { t with mutantCaught := t.mutantCaught + 1 }
        if !sameSet expected (r.evaluate g' e) then
          t := { t with disagree := t.disagree + 1 }
          if report.isNone then report := some s!"reordering changed the results\n{describeSpecification i}reordered\n{describeSpecification r}"
  return (t, report)

/-! ## Dump for the TypeScript comparison -/

/-- Random specifications, reused names included, with the inverses
`candidates` builds and reorders, for `ports/typescript/reference-diff.ts`. -/
def dumpCandidates (path : System.FilePath) (seed : Nat) : IO Unit := do
  let mut gen : StdGen × Nat := (mkStdGen seed, 0)
  let mut out : Array Json := #[]
  for _ in [0:400] do
    let (s, g) := (genSpec false 3 true).run gen
    gen := g
    let is := inverses s
    out := out.push (Json.mkObj [("specification", specificationToJson s),
      ("inverses", Json.arr (is.map specificationToJson).toArray),
      ("reordered", Json.arr (is.map (specificationToJson ∘ reorderOrSelf)).toArray)])
  IO.FS.writeFile path ((Json.arr out).compress ++ "\n")
  IO.println s!"wrote {out.size} specifications to {path}"

def dump (path : System.FilePath) (seed : Nat) : IO Unit := do
  let mut gen : StdGen × Nat := (mkStdGen seed, 0)
  let mut out : Array Json := #[]
  for _ in [0:400] do
    -- No reused names: with them, two matches of one name can carry the same
    -- condition, and the TypeScript removes it by identity where the port
    -- removes it by equality (`Inverse.lean`). jinaga.js#343 is that case.
    let (s, g) := (genSpec false 3 false).run gen
    gen := g
    let inverses := match invertSpecification s with
      | .ok is => Json.arr (is.map fun ι => Json.str ι.describe).toArray
      | .error e => Json.mkObj [("error", Json.str e.message)]
    out := out.push (Json.mkObj [("specification", specificationToJson s), ("inverses", inverses)])
  IO.FS.writeFile path ((Json.arr out).compress ++ "\n")
  IO.println s!"wrote {out.size} specifications to {path}"

def main (args : List String) : IO UInt32 := do
  if args.head? == some "dump-candidates" then
    dumpCandidates (args.getD 1 "candidates-dump.json") ((args.getD 2 "1").toNat?.getD 1)
    return 0
  if args.head? == some "dump" then
    dump (args.getD 1 "inverse-dump.json") ((args.getD 2 "1").toNat?.getD 1)
    return 0
  let seed := (args.head?.bind String.toNat?).getD 1
  let mut gen : StdGen × Nat := (mkStdGen seed, 0)
  let mut specs : List Specification := cases.map (·.spec)
  for _ in [0:1500] do
    let (s, g) := (genSpec false 3 !(args.contains "noreuse")).run gen
    gen := g
    unless isWellFormed s do
      throw <| IO.userError s!"the generator made a specification that is not well-formed:\n{describeSpecification s}"
    specs := specs ++ [s]
  let mut tally : Tally := {}
  let mut inverted := 0
  let mut refusals : List (String × String) := []
  let mut firstGained : Option String := none
  let mut firstLost : Option String := none
  let mut notFresh := (0, 0)
  let mut dropped := (0, 0)
  for s in specs do
    match invertSpecification s with
    | .error e =>
      let reason := match e with
        | .notConnected _ => "shakeTree: labels not connected by a path condition"
        | e => e.message
      refusals := refusals ++ [(reason, describeSpecification s)]
    | .ok inverses =>
      inverted := inverted + 1
      let ((t, rg, rl), g) := (checkSpec s inverses 40).run gen
      gen := g
      tally := tally.add t
      if firstGained.isNone then firstGained := rg
      if firstLost.isNone then firstLost := rl
      let (caught, g) := (notFreshCaught s inverses 40).run gen
      gen := g
      notFresh := (notFresh.1 + (if caught then 1 else 0), notFresh.2 + 1)
      if inverses.any fun ι => (ι.given :: ι.matchList).any (·.conditions.any (!·.isPath)) then
        let ((tm, _, _), g) := (checkSpec s (inverses.map dropConditions) 40).run gen
        gen := g
        dropped := (dropped.1 + (if tm.addAbsent > 0 then 1 else 0), dropped.2 + 1)
  let mut miss338 := 0
  let mut missCoarse := 0
  let mut firstCoarse : Option String := none
  for s in specs do
    let ((m, _), g) := (ruleMisses (byRule rule338) s 40).run gen
    gen := g
    miss338 := miss338 + m
    let ((m, r), g) := (ruleMisses candidates s 40).run gen
    gen := g
    missCoarse := missCoarse + m
    if firstCoarse.isNone then firstCoarse := r
  let mut rt : ReorderTally := {}
  let mut firstReorder : Option String := none
  for s in specs do
    let ((t, r), g) := (checkReorder s 10).run gen
    gen := g
    rt := { inverses := rt.inverses + t.inverses, refused := rt.refused + t.refused,
            notNavigable := rt.notNavigable + t.notNavigable, startsAtPin := rt.startsAtPin + t.startsAtPin,
            disagree := rt.disagree + t.disagree, withResults := rt.withResults + t.withResults,
            mutantCaught := rt.mutantCaught + t.mutantCaught }
    if firstReorder.isNone then firstReorder := r
  IO.println s!"reorder: {rt.inverses} inverses, {rt.refused} kept as they were (the check failed), {rt.notNavigable} not navigable, {rt.startsAtPin} start at the new fact, {rt.disagree} graphs where the results changed ({rt.withResults} with results); mutant \"swap roles of every path condition\" caught on {rt.mutantCaught} graphs"
  IO.println s!"specifications: {inverted} inverted, {refusals.length} refused"
  for reason in (refusals.map (·.1)).eraseDups do
    let these := refusals.filter (·.1 == reason)
    IO.println s!"  refused {these.length}: {reason}, for example\n{these.head!.2}"
  IO.println s!"graphs: {tally.graphs}, {tally.gained} results gained, {tally.lost} lost"
  IO.println s!"complete: {tally.missedGained} gained results no \"add\" reported, {tally.missedLost} lost results no \"remove\" reported"
  IO.println s!"sound:    {tally.addAbsent} \"add\" reports of a result the graph lacks, {tally.removePresent} \"remove\" reports of a result it still has"
  IO.println s!"by rule, over all {specs.length} specifications: #338 as proposed misses {miss338} changed results, `candidates` misses {missCoarse}"
  IO.println "named cases:"
  namedCase "exists { notExists } (jinaga.js#338)" existsNotExists
  namedCase "two sibling notExists" siblingNotExists
  IO.println "mutants:"
  IO.println s!"  \"notify a fact the store already has\": caught on {notFresh.1} of {notFresh.2} specifications"
  IO.println s!"  \"drop existential conditions\": caught on {dropped.1} of {dropped.2} specifications with one"
  -- jinaga.js's inverses (this port) are measured, not required to pass: their
  -- misses are recorded in docs/findings.md. What must hold is the coarse rule,
  -- and every mutant must be caught.
  if let some r := firstGained then IO.println s!"\nFIRST GAIN JINAGA.JS'S INVERSES MISS\n{r}"
  if let some r := firstLost then IO.println s!"\nFIRST LOSS JINAGA.JS'S INVERSES MISS\n{r}"
  if let some r := firstReorder then IO.println s!"\nFIRST REORDER PROBLEM\n{r}"
  if let some r := firstCoarse then IO.println s!"\nFIRST MISS BY `candidates`\n{r}"
  let uncaught := (if notFresh.1 == 0 then ["notify a fact the store already has"] else []) ++
    (if dropped.1 == 0 then ["drop existential conditions"] else []) ++
    (if miss338 == 0 then ["#338 as proposed"] else [])
  unless uncaught.isEmpty do IO.println s!"\nMUTANTS NOT CAUGHT: {uncaught}"
  let uncaught := uncaught ++ (if rt.mutantCaught == 0 then ["swap roles of every path condition"] else [])
  return if missCoarse == 0 && uncaught.isEmpty && firstReorder.isNone then 0 else 1
