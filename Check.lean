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
  { sp with head := sp.head.map f }

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
                          split := tally.split + (if sp.head.isSome && sp.tail.isSome then 1 else 0) }
    if !sameSet expected actual && report.isNone then
      tally := { tally with failures := tally.failures + 1 }
      report := some s!"{describeSpecification s}\nexpected {repr expected}\nactual   {repr actual}\nsplit head:\n{sp.head.map describeSpecification}\ntail:\n{sp.tail.map describeSpecification}"
    else if !sameSet expected actual then
      tally := { tally with failures := tally.failures + 1 }
  return (tally, report)

/-- How many of the specifications does a mutant get caught on? -/
def mutationScore (specs : List Specification) (graphs : Nat) (gen : StdGen × Nat) : IO Unit := do
  for (label, mutate) in mutants do
    let mut caught := 0
    let mut applicable := 0
    let mut g := gen
    for s in specs do
      let sp := splitBeforeFirstSuccessor s
      let m := mutate sp
      if sp.head.isSome && sp.tail.isSome then
        applicable := applicable + 1
        let mut found := false
        for _ in [0:graphs] do
          let ((graph, env), g') := (do let gr ← genGraph s 10; return (gr, ← genEnv s gr)).run g
          g := g'
          if !sameSet (s.evaluate graph env) (m.evaluate graph env) then found := true
        if found then caught := caught + 1
    IO.println s!"  mutant \"{label}\": caught on {caught} of {applicable} split specifications"

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
    let ((t, r), g') := (checkSpec s 20).run g
    gen := g'
    random := add random t
    if firstFailure.isNone then firstFailure := r.map (s!"random spec\n" ++ ·)
  IO.println s!"random specs:  {random.checks} checks, {random.nonEmpty} with results, {random.split} split, {random.failures} failures"
  IO.println "mutation check (each wrong split must be caught):"
  let mut pool := []
  let mut g := gen
  for _ in [0:300] do
    let (s, g') := genSpec.run g
    g := g'
    pool := pool ++ [s]
  mutationScore (cases.map (·.spec) ++ pool) 30 g
  match firstFailure with
  | none => return 0
  | some report => IO.println s!"\nFIRST FAILURE\n{report}"; return 1
