import JinagaSpec

/-!
# Random specifications and graphs

Shared by the randomized checks (`Check.lean`, `CheckInverse.lean`). Every
specification `genSpec` makes is well scoped by construction.
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

partial def genMatch (maxDepth : Nat) (types scope : List Name) (name type : Name) (depth : Nat) : Gen Match := do
  let scope' := name :: scope
  let root ← genPath types scope
  let mut conditions := [root]
  for _ in [0:(← below 3)] do
    if depth < maxDepth && (← chance 1 3) then
      let inner ← genMatch maxDepth types scope' s!"e{← fresh}" (← pick types) (depth + 1)
      conditions := conditions ++ [if ← chance 1 2 then exists' [inner] else notExists [inner]]
    else
      conditions := conditions ++ [← genPath types scope]
  return .mk { name := name, type := type } conditions

mutual
  /-- Labels declared inside existential conditions, at any depth. -/
  partial def innerNamesMatches : List Match → List Name
    | [] => []
    | .mk _ cs :: rest => cs.flatMap innerNamesCondition ++ innerNamesMatches rest
  partial def innerNamesCondition : Condition → List Name
    | .path _ => []
    | .existential _ ms => ms.map (·.unknown.name) ++ innerNamesMatches ms
end

/-- `maxDepth` bounds how deeply existential conditions nest. With `reuse`, a
match sometimes takes a name an earlier existential condition declared, which
the parser allows because that name went out of scope with the condition. -/
def genSpec (duplicates : Bool := false) (maxDepth : Nat := 2) (reuse : Bool := false) : Gen Specification := do
  let types ← factTypes
  let count ← below 2
  let given := (List.range (count + 1)).map fun i => (s!"p{i + 1}", "A")
  let mut scope := given.map (·.1)
  let mut matchList := []
  for i in [0:(← below 4) + 1] do
    -- Sometimes name an unknown `s{i}`, so that split labels must avoid it.
    let collide ← chance 1 5
    let duplicate ← pick ["p1", "u1", "u2", "s1"]
    let outOfScope := (innerNamesMatches matchList).filter (!scope.contains ·)
    let fresh := if collide then s!"s{i + 1}" else s!"u{i + 1}"
    let name ← if duplicates then pure duplicate
      else if reuse && !outOfScope.isEmpty then do
        if ← chance 1 3 then pick outOfScope else pure fresh
      else pure fresh
    matchList := matchList ++ [← genMatch maxDepth types scope name (← pick types) 0]
    scope := scope ++ [name]
  let labels := (← repeatGen ((← below 2) + 1) (pick scope))
  let projection := match labels with
    | [l] => Projection.fact l
    | ls => Projection.composite (ls.map fun l => { name := l, label := l })
  return { given := givens given, matchList := matchList, projection := projection }

def sameSet [BEq α] (a b : List α) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)
