import JinagaSpec.Semantics

/-!
# Splitting a specification

`splitBeforeFirstSuccessor`, as `jinaga.js` implements it in
`src/specification/specification.ts`. The graph can run a *head* of predecessor
walks. A *tail* needs the store. The split cuts at the first match the graph
cannot run.

This file is written in the portable subset: inductive types, total pure
functions, structural recursion, and lists. It uses no tactic, no `Mathlib`,
and no dependent type. A port to another language should read line for line.
Theorems live in `JinagaSpec/Proofs/`.

Where this differs from the TypeScript in shape but not in meaning:
* `List.span` replaces `findIndex` followed by two `slice`s.
* `splitPaths` threads the names already taken through the walk over the
  pivot's conditions. TypeScript allocates the names up front with
  `allocateLabels` and indexes into them. The names are the same.
-/
namespace JinagaSpec

/-- A match is deterministic when every condition is a path condition with no
successor roles: the graph can run it by walking predecessors. -/
def matchIsDeterministic (m : Match) : Bool :=
  m.conditions.all fun
    | .path c => c.rolesLeft.isEmpty
    | .existential .. => false

/-! ## Labels -/

mutual
  /-- The labels that conditions name on their right-hand side, including those
  inside existential conditions. -/
  def usedInMatches : List Match → List Name
    | [] => []
    | .mk _ conditions :: rest => usedInConditions conditions ++ usedInMatches rest

  def usedInConditions : List Condition → List Name
    | [] => []
    | c :: cs => usedInCondition c ++ usedInConditions cs

  def usedInCondition : Condition → List Name
    | .path c => [c.labelRight]
    | .existential _ ms => usedInMatches ms
end

mutual
  /-- Every label the matches declare, including those inside existential
  conditions. -/
  def declaredInMatches : List Match → List Name
    | [] => []
    | .mk unknown conditions :: rest =>
      unknown.name :: (declaredInConditions conditions ++ declaredInMatches rest)

  def declaredInConditions : List Condition → List Name
    | [] => []
    | c :: cs => declaredInCondition c ++ declaredInConditions cs

  def declaredInCondition : Condition → List Name
    | .path _ => []
    | .existential _ ms => declaredInMatches ms
end

def declaredLabels (s : Specification) : List Name :=
  s.given.map (·.name) ++ declaredInMatches s.matchList

/-- The labels, in their order, that the matches and the projection use but the
matches do not define. -/
def referencedLabels (matchList : List Match) (labels : List Label) (projection : Projection) : List Label :=
  let defined := matchList.map (·.unknown.name)
  let used := (usedInMatches matchList ++ projection.labels).filter fun name => !defined.contains name
  labels.filter fun label => used.contains label.name

/-- The first of `s1`, `s2`, ... that is not taken. Among the first
`taken.length + 1` candidates, one must be free. -/
def freshFrom (taken : List Name) : Nat → Nat → Name
  | 0, n => s!"s{n}"
  | fuel + 1, n => if taken.contains s!"s{n}" then freshFrom taken fuel (n + 1) else s!"s{n}"

def freshLabel (taken : List Name) : Name :=
  freshFrom taken taken.length 1

def projectLabels (labels : List Label) : Projection :=
  match labels with
  | [label] => .fact label.name
  | _ => .composite (labels.map fun label => { name := label.name, label := label.name })

/-! ## Splitting the pivot -/

/-- Split each path condition of the pivot. One that walks predecessors gives
the head a match that binds a split label, and the tail joins to that label
instead. One that walks none already names a label the head binds. -/
def splitPaths (taken : List Name) : List PathCondition → List Match × List PathCondition
  | [] => ([], [])
  | c :: cs =>
    match c.rolesRight.getLast? with
    | none =>
      let (headMatches, tailPaths) := splitPaths taken cs
      (headMatches, c :: tailPaths)
    | some last =>
      let name := freshLabel taken
      let (headMatches, tailPaths) := splitPaths (name :: taken) cs
      (.mk { name := name, type := last.predecessorType }
          [.path { rolesLeft := [], labelRight := c.labelRight, rolesRight := c.rolesRight }] :: headMatches,
       { rolesLeft := c.rolesLeft, labelRight := name, rolesRight := [] } :: tailPaths)

structure Split where
  head : Option Specification
  tail : Option Specification

/-- The path conditions of a match, in order. -/
def pathsOf (conditions : List Condition) : List PathCondition :=
  conditions.filterMap fun
    | .path c => some c
    | .existential .. => none

/-- The existential conditions of a match, in order. -/
def existentialsOf (conditions : List Condition) : List Condition :=
  conditions.filter fun
    | .path .. => false
    | .existential .. => true

/-- The tail's matches: the pivot with its path conditions rewritten to join
the split labels, and the matches after it. Existential conditions stay with
the pivot, which the tail runs. -/
def tailMatchesAt (pivot : Match) (tailPaths : List PathCondition) (after : List Match) : List Match :=
  .mk pivot.unknown (tailPaths.map .path ++ existentialsOf pivot.conditions) :: after

/-- The tail's givens are the labels it uses but does not define. -/
def tailGivenAt (s : Specification) (splitMatches tailMatches : List Match) : List Label :=
  let allLabels := s.given ++ s.matchList.map (·.unknown) ++ splitMatches.map (·.unknown)
  referencedLabels tailMatches allLabels s.projection

/-- Split at a pivot: the first match the graph cannot run, with the matches
before and after it. -/
def splitAt (s : Specification) (before : List Match) (pivot : Match) (after : List Match) : Split :=
  let (splitMatches, tailPaths) := splitPaths (declaredLabels s) (pathsOf pivot.conditions)
  let headMatches := before ++ splitMatches
  if headMatches.isEmpty then
    -- Nothing precedes the pivot and none of its conditions walks a
    -- predecessor, so there is nothing for the graph to run.
    { head := none, tail := some s }
  else
    let tailMatches := tailMatchesAt pivot tailPaths after
    let tailGiven := tailGivenAt s splitMatches tailMatches
    let headProjection := projectLabels tailGiven
    -- The head projects the tail's givens, so its projection takes part.
    let headGiven := referencedLabels headMatches s.given headProjection
    { head := some { given := headGiven, matchList := headMatches, projection := headProjection },
      tail := some { given := tailGiven, matchList := tailMatches, projection := s.projection } }

def splitBeforeFirstSuccessor (s : Specification) : Split :=
  match s.matchList.span matchIsDeterministic with
  | (_, []) =>
    -- No match seeks successors, so the whole specification is deterministic.
    { head := some s, tail := none }
  | (before, pivot :: after) => splitAt s before pivot after

/-! ## Evaluating a split -/

/-- Keep only the bindings the tail is given. -/
def Env.restrictTo (names : List Name) (env : Env) : Env :=
  fun n => if names.contains n then env n else none

/-- Evaluate a split as the authorization engine does: the head on the graph
gives one tuple per solution, and each tuple seeds the tail with one fact per
tail given. -/
def Split.evaluate (split : Split) (g : Graph) (env : Env) : List (List (Option FactId)) :=
  match split.head, split.tail with
  | some head, some tail =>
    (evalMatches g env head.matchList).flatMap fun tuple =>
      tail.evaluate g (tuple.restrictTo (tail.given.map (·.name)))
  | some head, none => head.evaluate g env
  | none, some tail => tail.evaluate g env
  | none, none => []

end JinagaSpec
