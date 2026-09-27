import JinagaSpec

/-!
# Randomized check of the split theorem

`lake exe check [seed]` compares `Specification.evaluate` with
`Split.evaluate` on random graphs, for the named cases and for random
specifications. This is a cheap test that the theorem is true before it is
proved, and a way to see which hypotheses it needs. It proves nothing.
-/
open JinagaSpec Build

abbrev Gen := StateM (StdGen × Nat)

def below (n : Nat) : Gen Nat :=
  modifyGet fun (g, k) => let (x, g') := randNat g 0 (n - 1); (x, (g', k))

def chance (num den : Nat) : Gen Bool := do return (← below den) < num

def pick [Inhabited α] (xs : List α) : Gen α := do return xs[← below xs.length]!

def fresh : Gen Nat := modifyGet fun (g, k) => (k, (g, k + 1))

def repeatGen (n : Nat) (x : Gen α) : Gen (List α) := do
  let mut out := []
  for _ in [0:n] do out := (← x) :: out
  return out.reverse

/-! ## Facts and roles in a specification -/

mutual
  def typesInMatches : List Match → List Name
    | [] => []
    | .mk u cs :: rest => u.type :: (typesInConditions cs ++ typesInMatches rest)
  def typesInConditions : List Condition → List Name
    | [] => []
    | c :: cs => typesInCondition c ++ typesInConditions cs
  def typesInCondition : Condition → List Name
    | .path c => (c.rolesLeft ++ c.rolesRight).map (·.predecessorType)
    | .existential _ ms => typesInMatches ms
end

mutual
  def rolesInMatches : List Match → List Role
    | [] => []
    | .mk _ cs :: rest => rolesInConditions cs ++ rolesInMatches rest
  def rolesInConditions : List Condition → List Role
    | [] => []
    | c :: cs => rolesInCondition c ++ rolesInConditions cs
  def rolesInCondition : Condition → List Role
    | .path c => c.rolesLeft ++ c.rolesRight
    | .existential _ ms => rolesInMatches ms
end

/-! ## Random graphs -/

/-- Every type appears, so that a match has candidates. Each fact points, by
each role, to zero, one or two facts of that role's type. -/
def genGraph (s : Specification) (size : Nat) : Gen Graph := do
  let types := (s.given.map (·.type) ++ typesInMatches s.matchList).eraseDups
  let roles := (rolesInMatches s.matchList).eraseDups
  let types := if types.isEmpty then ["T"] else types
  let skeleton : List (Nat × Name) := (List.range size).map fun i => (i, types[i % types.length]!)
  let mut facts : Graph := []
  for (i, type) in skeleton do
    let mut preds : List (Name × Nat) := []
    for role in roles do
      if ← chance 3 4 then
        let targets := (skeleton.filter fun (j, t) => t == role.predecessorType && j != i).map (·.1)
        if !targets.isEmpty then
          preds := (role.name, ← pick targets) :: preds
          if ← chance 1 4 then preds := (role.name, ← pick targets) :: preds
    facts := facts ++ [{ id := i, type := type, predecessors := preds }]
  return facts

def genEnv (s : Specification) (g : Graph) : Gen Env := do
  let mut ids := []
  for l in s.given do
    let candidates := (g.filter (·.type == l.type)).map (·.id)
    let id ← if candidates.isEmpty then pure 0 else pick candidates
    ids := ids ++ [id]
  return s.bindGivens ids

/-- A fact of the given's type, under authorization: an id fresh with respect to
`store` (one past every id `genGraph` can produce), with predecessors chosen
from `store`'s own facts, so that `store.closed`, `f.id` absent from `store`, and
every predecessor of `f` present in `store` all hold by construction. -/
def genBatchFact (s : Specification) (g0 : Label) (store : Graph) (size : Nat) : Gen Fact := do
  let roles := (rolesInMatches s.matchList).eraseDups
  let mut preds : List (Name × Nat) := []
  for role in roles do
    if ← chance 3 4 then
      let targets := (store.filter fun sf => sf.type == role.predecessorType).map (·.id)
      if !targets.isEmpty then
        preds := (role.name, ← pick targets) :: preds
        if ← chance 1 4 then preds := (role.name, ← pick targets) :: preds
  return { id := size, type := g0.type, predecessors := preds }

/-! ## Random specifications, well scoped by construction -/

/-- Most specifications use one fact type, so that two walks often meet. -/
def factTypes : Gen (List Name) := do
  return if ← chance 3 4 then ["A"] else ["A", "B"]

def genRoles (types : List Name) : Gen (List Role) := do
  let length ← pick [0, 0, 1, 1, 1, 2]
  repeatGen length (do return role (← pick ["x", "y"]) (← pick types))

def genPath (types scope : List Name) : Gen Condition := do
  return path (← genRoles types) (← pick scope) (← genRoles types)

instance : Inhabited Match := ⟨.mk { name := "", type := "" } []⟩

partial def genMatch (types scope : List Name) (name type : Name) (depth : Nat) : Gen Match := do
  let scope' := name :: scope
  let root ← genPath types scope
  let mut conditions := [root]
  for _ in [0:(← below 3)] do
    if depth < 2 && (← chance 1 3) then
      let inner ← genMatch types scope' s!"e{← fresh}" (← pick types) (depth + 1)
      conditions := conditions ++ [if ← chance 1 2 then exists' [inner] else notExists [inner]]
    else
      conditions := conditions ++ [← genPath types scope]
  return .mk { name := name, type := type } conditions

def genSpec (duplicates : Bool := false) : Gen Specification := do
  let types ← factTypes
  let count ← below 2
  let given := (List.range (count + 1)).map fun i => (s!"p{i + 1}", "A")
  let mut scope := given.map (·.1)
  let mut matchList := []
  for i in [0:(← below 4) + 1] do
    -- Sometimes name an unknown `s{i}`, so that split labels must avoid it.
    let collide ← chance 1 5
    let duplicate ← pick ["p1", "u1", "u2", "s1"]
    let name := if duplicates then duplicate
      else if collide then s!"s{i + 1}" else s!"u{i + 1}"
    matchList := matchList ++ [← genMatch types scope name (← pick types) 0]
    scope := scope ++ [name]
  let labels := (← repeatGen ((← below 2) + 1) (pick scope))
  let projection := match labels with
    | [l] => Projection.fact l
    | ls => Projection.composite (ls.map fun l => { name := l, label := l })
  return { given := givens given, matchList := matchList, projection := projection }

/-! ## The check -/

def sameSet (a b : List (List (Option Nat))) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

/-! ## Mutants

Deliberately wrong splits. The check must reject each, or it is not testing
anything. -/

def dropLast (xs : List α) : List α := xs.dropLast

def onTail (f : Specification → Specification) (sp : Split) : Split :=
  { sp with tail := sp.tail.map f }

def onHead (f : Specification → Specification) (sp : Split) : Split :=
  { sp with head := f sp.head }

def withoutExistentials : Match → Match
  | .mk u cs => .mk u (cs.filter fun | .path .. => true | .existential .. => false)

def mutants : List (String × (Split → Split)) := [
  ("tail loses a given", onTail fun t => { t with given := dropLast t.given }),
  ("tail loses its existential conditions", onTail fun t => { t with matchList := t.matchList.map withoutExistentials }),
  ("head loses its last match", onHead fun h => { h with matchList := dropLast h.matchList }),
  ("tail loses its first condition", onTail fun t => { t with matchList := t.matchList.map fun | .mk u cs => .mk u cs.tail })
]

structure Tally where
  checks : Nat := 0
  nonEmpty : Nat := 0
  split : Nat := 0
  failures : Nat := 0

def checkSpec (s : Specification) (graphs : Nat) : Gen (Tally × Option String) := do
  let mut tally : Tally := {}
  let sp := splitBeforeFirstSuccessor s
  let mut report := none
  for _ in [0:graphs] do
    let g ← genGraph s 10
    let env ← genEnv s g
    let expected := s.evaluate g env
    let actual := sp.evaluate g env
    tally := { tally with checks := tally.checks + 1,
                          nonEmpty := tally.nonEmpty + (if expected.isEmpty then 0 else 1),
                          split := tally.split + (if sp.tail.isSome then 1 else 0) }
    if !sameSet expected actual && report.isNone then
      tally := { tally with failures := tally.failures + 1 }
      report := some s!"{describeSpecification s}\nexpected {repr expected}\nactual   {repr actual}\nsplit head:\n{describeSpecification sp.head}\ntail:\n{sp.tail.map describeSpecification}"
    else if !sameSet expected actual then
      tally := { tally with failures := tally.failures + 1 }
  return (tally, report)

/-! ## Store check

Compares `Split.evaluateStore` against the reference semantics of authorization
(`s.evaluate (Graph.authGraph store f) env`) on random closed stores, split by
`tailReadsGiven`: agreement everywhere it is false, empty results everywhere it
is true. Only single-given specifications: `Store.lean`'s theorems are stated
for one given. -/

structure StoreTally where
  checks : Nat := 0
  tailReadsTrue : Nat := 0
  tailReadsFalse : Nat := 0
  failures : Nat := 0

def addStore (t u : StoreTally) : StoreTally :=
  { checks := t.checks + u.checks, tailReadsTrue := t.tailReadsTrue + u.tailReadsTrue,
    tailReadsFalse := t.tailReadsFalse + u.tailReadsFalse, failures := t.failures + u.failures }

def checkStoreSpec (s : Specification) (graphs : Nat) : Gen (StoreTally × Option String) := do
  match s.given with
  | [g0] =>
    let split := splitBeforeFirstSuccessor s
    let reads := tailReadsGiven split g0.name
    let mut tally : StoreTally := {}
    let mut report := none
    for _ in [0:graphs] do
      let store ← genGraph s 8
      let f ← genBatchFact s g0 store 8
      let env : Env := fun n => if n = g0.name then some f.id else none
      let expected := s.evaluate (Graph.authGraph store f) env
      let actual := split.evaluateStore store f env
      let ok := if reads then actual.isEmpty else sameSet expected actual
      tally := { tally with checks := tally.checks + 1,
                             tailReadsTrue := tally.tailReadsTrue + (if reads then 1 else 0),
                             tailReadsFalse := tally.tailReadsFalse + (if reads then 0 else 1),
                             failures := tally.failures + (if ok then 0 else 1) }
      if !ok && report.isNone then
        report := some s!"{describeSpecification s}\ntailReadsGiven={reads}\nexpected {repr expected}\nactual   {repr actual}"
    return (tally, report)
  | _ => return ({}, none)

/-- Without the absent-given rule, the tail would run on `store` regardless of
whether it is seeded with a fact the store does not have. -/
def evaluateStoreNoGuard (split : Split) (store : Graph) (f : Fact) (env : Env) :
    List (List (Option FactId)) :=
  match split.tail with
  | none => split.head.evaluate (Graph.authGraph store f) env
  | some tail =>
    (evalMatches (Graph.authGraph store f) env split.head.matchList).flatMap fun tuple =>
      tail.evaluate store (tuple.restrictTo (tail.given.map (·.name)))

/-- How often does dropping the absent-given rule change the result of a
specification whose tail reads the given? It must, every time, or the guard is
not doing anything `evaluateStore` didn't already do for free. -/
def storeMutationScore (specs : List Specification) (graphs : Nat) (gen : StdGen × Nat) : IO Unit := do
  let mut caught := 0
  let mut applicable := 0
  let mut g := gen
  for s in specs do
    match s.given with
    | [g0] =>
      let split := splitBeforeFirstSuccessor s
      if tailReadsGiven split g0.name then
        applicable := applicable + 1
        let mut found := false
        for _ in [0:graphs] do
          let ((store, f), g') :=
            (do let st ← genGraph s 8; return (st, ← genBatchFact s g0 st 8)).run g
          g := g'
          let env : Env := fun n => if n = g0.name then some f.id else none
          if !(evaluateStoreNoGuard split store f env).isEmpty then found := true
        if found then caught := caught + 1
    | _ => pure ()
  IO.println s!"  mutant \"drop the absent-given rule\": caught on {caught} of {applicable} tailReadsGiven specifications"

/-- How many of the specifications does a mutant get caught on? -/
def mutationScore (specs : List Specification) (graphs : Nat) (gen : StdGen × Nat) : IO Unit := do
  for (label, mutate) in mutants do
    let mut caught := 0
    let mut applicable := 0
    let mut g := gen
    for s in specs do
      let sp := splitBeforeFirstSuccessor s
      let m := mutate sp
      if sp.tail.isSome then
        applicable := applicable + 1
        let mut found := false
        for _ in [0:graphs] do
          let ((graph, env), g') := (do let gr ← genGraph s 10; return (gr, ← genEnv s gr)).run g
          g := g'
          if !sameSet (s.evaluate graph env) (m.evaluate graph env) then found := true
        if found then caught := caught + 1
    IO.println s!"  mutant \"{label}\": caught on {caught} of {applicable} split specifications"

/-! ## Hoisting: the polarity experiment

`splitBeforeFirstSuccessor` (`Hoist.lean`) hoists an eligible path condition
only when it sits at positive polarity, tracking polarity as it recurses into
existential conditions: a fresh polarity for the matches inside one, from the
polarity outside it and whether it is negative. Two wrong ways to track that
are kept here as permanent mutation checks, both found unsound by the
randomized check below before the split had the rule it does now:
`hoistNoPolarity` hoists regardless of polarity (`nextPos := fun _ _ => true`,
so the starting polarity `true` never changes); `hoistNaiveParity` toggles
polarity on every existential (`nextPos := fun pos e => if e then pos else
!pos`), reasoning that two negative existentials cancel back to positive. -/

mutual
  def hoistMatchesGen (nextPos : Bool → Bool → Bool) (scope : List Name) :
      Nat → Bool → List Match → Nat × List Match × List Match
    | i, _, [] => (i, [], [])
    | i, pos, .mk u cs :: rest =>
      let (i1, headCs, cs') := hoistConditionsGen nextPos scope i pos cs
      let (i2, headRest, rest') := hoistMatchesGen nextPos scope i1 pos rest
      (i2, headCs ++ headRest, .mk u cs' :: rest')

  def hoistConditionsGen (nextPos : Bool → Bool → Bool) (scope : List Name) :
      Nat → Bool → List Condition → Nat × List Match × List Condition
    | i, _, [] => (i, [], [])
    | i, pos, c :: cs =>
      let (i1, headC, c') := hoistConditionGen nextPos scope i pos c
      let (i2, headCs, cs') := hoistConditionsGen nextPos scope i1 pos cs
      (i2, headC ++ headCs, c' :: cs')

  def hoistConditionGen (nextPos : Bool → Bool → Bool) (scope : List Name) :
      Nat → Bool → Condition → Nat × List Match × Condition
    | i, pos, .path pc =>
      match pos, pc.rolesRight.getLast?, scope.contains pc.labelRight with
      | true, some last, true =>
        (i + 1,
         [.mk { name := splitLabel i, type := last.predecessorType }
             [.path { rolesLeft := [], labelRight := pc.labelRight, rolesRight := pc.rolesRight }]],
         .path { rolesLeft := pc.rolesLeft, labelRight := splitLabel i, rolesRight := [] })
      | _, _, _ => (i, [], .path pc)
    | i, pos, .existential e ms =>
      let (i1, headMs, ms') := hoistMatchesGen nextPos scope i (nextPos pos e) ms
      (i1, headMs, .existential e ms')
end

def hoistAtGen (nextPos : Bool → Bool → Bool) (s : Specification) (before : List Match)
    (pivot : Match) (after : List Match) : Split :=
  let scope := scopeAt s before
  let (_, headExtra, tailMatches) := hoistMatchesGen nextPos scope 0 true (pivot :: after)
  let headMatches := before ++ headExtra
  let tailGiven := tailGivenAt s headMatches tailMatches
  { head := { given := s.given, matchList := headMatches,
              projection := .composite (tailGiven.map fun l => { name := l.name, label := l.name }) },
    tail := some { given := tailGiven, matchList := tailMatches, projection := s.projection } }

def hoistGen (nextPos : Bool → Bool → Bool) (s : Specification) : Split :=
  match s.matchList.span matchIsDeterministic with
  | (_, []) => { head := s, tail := none }
  | (before, pivot :: after) => hoistAtGen nextPos s before pivot after

def hoistNoPolarity : Specification → Split := hoistGen fun _ _ => true
def hoistNaiveParity : Specification → Split := hoistGen fun pos e => if e then pos else !pos

/-- The counterexample `docs/findings.md` describes: given `p1` with a
multi-valued predecessor role `y`, and a pivot carrying a negative existential
`!E { u2: T [ u2->x = p1->y ] }`. A fact of type `T` reaches one of `p1->y`'s
two values (`a`) but not the other (`b`). The whole specification excludes the
pivot's solution, because that fact witnesses the existential; hoisting the
walk regardless of polarity runs the tail once per value and unions the
results, which does not. -/
def polarityCounterexample : Specification × Graph :=
  let y := role "y" "A"
  let x := role "x" "A"
  let z := role "z" "P"
  let s := spec [("p1", "P")]
    [unknown "u1" "Q" [path [z] "p1" [],
       notExists [unknown "u2" "T" [path [x] "p1" [y]]]]]
    (fact "u1")
  let g : Graph := [
    { id := 0, type := "P", predecessors := [("y", 2), ("y", 3)] },
    { id := 1, type := "Q", predecessors := [("z", 0)] },
    { id := 2, type := "A", predecessors := [] },
    { id := 3, type := "A", predecessors := [] },
    { id := 4, type := "T", predecessors := [("x", 2)] }]
  (s, g)

/-- `hoistNaiveParity` (above) found unsound too, on random specifications
with *two* nested negative existentials sharing a multi-valued label — one
level deeper than `polarityCounterexample`. Reasoning that two negative
existentials cancel back to positive is wrong; the split makes polarity
monotone instead (`Hoist.lean`): a negative existential's matches are
negative regardless of the polarity outside them, and nothing nested inside a
negative existential ever recovers positive polarity.

Two `e1` candidates, `e1A` and `e1B`, each rescued by a different value of
the given's multi-valued `x` role (`e2A` witnesses `e1A` only at `20`, `e2B`
witnesses `e1B` only at `21`), so the whole specification excludes `s1`'s
solution (every `e1` finds *some* rescuing value, `∀e1 ∃v`), but no single
value rescues both at once (no `v` has `∀e1`): naive-parity hoisting picks one
value for the whole head and unions afterward (`∃v ∀e1`), which is strictly
stronger, and empty here. -/
def polarityDoubleNegCounterexample : Specification × Graph :=
  let z := role "z" "P"
  let w := role "w" "A"
  let y := role "y" "A"
  let x := role "x" "A"
  let vR := role "v" "R"
  let vA := role "v" "A"
  let s := spec [("p1", "P")]
    [unknown "s1" "Q" [path [z] "p1" [],
       notExists [unknown "e1" "R" [path [w] "p1" [y],
         notExists [unknown "e2" "S" [path [vR] "e1" [], path [vA] "p1" [x]]]]]]]
    (fact "p1")
  let g : Graph := [
    { id := 0, type := "P", predecessors := [("y", 10), ("x", 20), ("x", 21)] },
    { id := 1, type := "Q", predecessors := [("z", 0)] },
    { id := 2, type := "R", predecessors := [("w", 10)] },
    { id := 3, type := "R", predecessors := [("w", 10)] },
    { id := 4, type := "S", predecessors := [("v", 2), ("v", 20)] },
    { id := 5, type := "S", predecessors := [("v", 3), ("v", 21)] },
    { id := 10, type := "A", predecessors := [] },
    { id := 20, type := "A", predecessors := [] },
    { id := 21, type := "A", predecessors := [] }]
  (s, g)

/-- Compares an arbitrary split-producing function against the reference
semantics, the way `checkSpec` does for `splitBeforeFirstSuccessor`. -/
def checkHoistSpec (split : Specification → Split) (s : Specification) (graphs : Nat) : Gen (Tally × Option String) := do
  let mut tally : Tally := {}
  let sp := split s
  let mut report := none
  for _ in [0:graphs] do
    let g ← genGraph s 10
    let env ← genEnv s g
    let expected := s.evaluate g env
    let actual := sp.evaluate g env
    tally := { tally with checks := tally.checks + 1,
                          nonEmpty := tally.nonEmpty + (if expected.isEmpty then 0 else 1),
                          split := tally.split + (if sp.tail.isSome then 1 else 0) }
    if !sameSet expected actual && report.isNone then
      tally := { tally with failures := tally.failures + 1 }
      report := some s!"{describeSpecification s}\nexpected {repr expected}\nactual   {repr actual}"
    else if !sameSet expected actual then
      tally := { tally with failures := tally.failures + 1 }
  return (tally, report)

def main (args : List String) : IO UInt32 := do
  let seed := (args.head?.bind String.toNat?).getD 1
  let duplicates := args.contains "duplicates"
  let mut gen : StdGen × Nat := (mkStdGen seed, 0)
  let mut total : Tally := {}
  let mut firstFailure : Option String := none
  let add (t : Tally) (u : Tally) : Tally :=
    { checks := t.checks + u.checks, nonEmpty := t.nonEmpty + u.nonEmpty, split := t.split + u.split, failures := t.failures + u.failures }
  -- The named cases.
  for c in cases do
    let ((t, r), g) := (checkSpec c.spec 300).run gen
    gen := g
    total := add total t
    if firstFailure.isNone then firstFailure := r.map (s!"case {c.name}\n" ++ ·)
  IO.println s!"named cases:   {total.checks} checks, {total.nonEmpty} with results, {total.split} split, {total.failures} failures"
  -- Random specifications.
  let mut random : Tally := {}
  for _ in [0:1500] do
    let (s, g) := (genSpec duplicates).run gen
    unless duplicates || isWellFormed s do
      throw <| IO.userError s!"the generator made a specification that is not well-formed:\n{describeSpecification s}"
    let ((t, r), g') := (checkSpec s 20).run g
    gen := g'
    random := add random t
    if firstFailure.isNone then firstFailure := r.map (s!"random spec\n" ++ ·)
  IO.println s!"random specs:  {random.checks} checks, {random.nonEmpty} with results, {random.split} split, {random.failures} failures"
  let mut pool := []
  let mut g := gen
  for _ in [0:300] do
    let (s, g') := genSpec.run g
    g := g'
    pool := pool ++ [s]
  -- The store check: Split.evaluateStore against the reference semantics on
  -- random closed stores, split by tailReadsGiven.
  let mut storeTotal : StoreTally := {}
  for c in cases do
    let ((t, r), g') := (checkStoreSpec c.spec 30).run g
    g := g'
    storeTotal := addStore storeTotal t
    if firstFailure.isNone then firstFailure := r.map (s!"store check, case {c.name}\n" ++ ·)
  for s in pool do
    let ((t, r), g') := (checkStoreSpec s 10).run g
    g := g'
    storeTotal := addStore storeTotal t
    if firstFailure.isNone then firstFailure := r.map (s!"store check, random spec\n" ++ ·)
  IO.println s!"store check:   {storeTotal.checks} checks, {storeTotal.tailReadsTrue} tailReadsGiven=true (must be empty), {storeTotal.tailReadsFalse} tailReadsGiven=false (must agree with the reference semantics), {storeTotal.failures} failures"
  -- The polarity experiment: hoisting under a negative existential disagrees;
  -- hoisting only at positive polarity (the real split) does not.
  let (cx, gx) := polarityCounterexample
  let cxEnv : Env := fun n => if n = "p1" then some 0 else none
  let cxExpected := cx.evaluate gx cxEnv
  let cxNoPolarity := (hoistNoPolarity cx).evaluate gx cxEnv
  let cxSplit := (splitBeforeFirstSuccessor cx).evaluate gx cxEnv
  IO.println s!"split counterexample: reference {repr cxExpected}, ignoring polarity {repr cxNoPolarity}, split {repr cxSplit}"
  unless !sameSet cxExpected cxNoPolarity do
    throw <| IO.userError "the polarity counterexample no longer disagrees when polarity is ignored"
  unless sameSet cxExpected cxSplit do
    throw <| IO.userError "the split (respecting polarity) disagreed on the polarity counterexample"
  let (cx2, gx2) := polarityDoubleNegCounterexample
  let cx2Env : Env := fun n => if n = "p1" then some 0 else none
  let cx2Expected := cx2.evaluate gx2 cx2Env
  let cx2NaiveParity := (hoistNaiveParity cx2).evaluate gx2 cx2Env
  let cx2Split := (splitBeforeFirstSuccessor cx2).evaluate gx2 cx2Env
  IO.println s!"split double-negation counterexample: reference {repr cx2Expected}, naive parity {repr cx2NaiveParity}, split {repr cx2Split}"
  unless !sameSet cx2Expected cx2NaiveParity do
    throw <| IO.userError "the double-negation counterexample no longer disagrees under naive parity"
  unless sameSet cx2Expected cx2Split do
    throw <| IO.userError "the split (monotone polarity) disagreed on the double-negation counterexample"
  let mut hoistNoPolTotal : Tally := {}
  let mut hoistNaiveTotal : Tally := {}
  let mut hoistTotal : Tally := {}
  for c in cases do
    let ((t1, _), g') := (checkHoistSpec hoistNoPolarity c.spec 30).run g
    g := g'
    hoistNoPolTotal := add hoistNoPolTotal t1
    let ((t3, _), g3) := (checkHoistSpec hoistNaiveParity c.spec 30).run g
    g := g3
    hoistNaiveTotal := add hoistNaiveTotal t3
    let ((t2, r2), g'') := (checkHoistSpec splitBeforeFirstSuccessor c.spec 30).run g
    g := g''
    hoistTotal := add hoistTotal t2
    if firstFailure.isNone then firstFailure := r2.map (s!"hoist check, case {c.name}\n" ++ ·)
  for s in pool do
    let ((t1, _), g') := (checkHoistSpec hoistNoPolarity s 10).run g
    g := g'
    hoistNoPolTotal := add hoistNoPolTotal t1
    let ((t3, _), g3) := (checkHoistSpec hoistNaiveParity s 10).run g
    g := g3
    hoistNaiveTotal := add hoistNaiveTotal t3
    let ((t2, r2), g'') := (checkHoistSpec splitBeforeFirstSuccessor s 10).run g
    g := g''
    hoistTotal := add hoistTotal t2
    if firstFailure.isNone then firstFailure := r2.map (s!"hoist check, random spec\n" ++ ·)
  IO.println s!"hoist, ignoring polarity: {hoistNoPolTotal.checks} checks, {hoistNoPolTotal.failures} failures"
  IO.println s!"hoist, naive parity: {hoistNaiveTotal.checks} checks, {hoistNaiveTotal.failures} failures"
  IO.println s!"hoist, respecting polarity (monotone): {hoistTotal.checks} checks, {hoistTotal.failures} failures"
  IO.println "mutation check (each wrong split must be caught):"
  mutationScore (cases.map (·.spec) ++ pool) 30 g
  storeMutationScore (cases.map (·.spec) ++ pool) 30 g
  match firstFailure with
  | none => return 0
  | some report => IO.println s!"\nFIRST FAILURE\n{report}"; return 1
