import JinagaSpec.Semantics

/-!
# Splitting a specification

`splitBeforeFirstSuccessor`. The graph can run a *head* of predecessor walks. A
*tail* needs the store. The split cuts at the first match the graph cannot run,
which is the *pivot*.

The split assumes its input is well-formed (`JinagaSpec/WellFormed.lean`), and
so needs no check of its own. In particular, no declared label is reserved, so
the labels the split makes up for itself cannot collide with any the
specification declares.

This file is written in the portable subset: inductive types, total pure
functions, structural recursion, and lists. It uses no tactic, no `Mathlib`,
and no dependent type. A port to another language should read line for line.
Theorems live in `JinagaSpec/Proofs/`.
-/
namespace JinagaSpec

/-- A match is deterministic when every condition is a path condition with no
successor roles: the graph can run it by walking predecessors. -/
def matchIsDeterministic (m : Match) : Bool :=
  m.conditions.all fun
    | .path c => c.rolesLeft.isEmpty
    | .existential .. => false

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

/-! ## Splitting the pivot -/

/-- The label the split gives the fact that the head walks to for the `i`th path
condition of the pivot. -/
def splitLabel (i : Nat) : Name := s!"__s{i}"

/-- Split each path condition of the pivot, numbering them from `i`. One that
walks predecessors gives the head a match that binds a split label, and the tail
joins to that label instead. One that walks none already names a label the head
binds. -/
def splitPaths (i : Nat) : List PathCondition → List Match × List PathCondition
  | [] => ([], [])
  | c :: cs =>
    let (headMatches, tailPaths) := splitPaths (i + 1) cs
    match c.rolesRight.getLast? with
    | none => (headMatches, c :: tailPaths)
    | some last =>
      (.mk { name := splitLabel i, type := last.predecessorType }
          [.path { rolesLeft := [], labelRight := c.labelRight, rolesRight := c.rolesRight }] :: headMatches,
       { rolesLeft := c.rolesLeft, labelRight := splitLabel i, rolesRight := [] } :: tailPaths)

/-- The head always exists, and has no matches when the pivot is the first
match and walks no predecessors. The tail is absent when nothing seeks
successors. -/
structure Split where
  head : Specification
  tail : Option Specification

/-- The tail's matches: the pivot with its path conditions rewritten to join the
split labels, and the matches after it. Existential conditions stay with the
pivot, which the tail runs. -/
def tailMatchesAt (pivot : Match) (tailPaths : List PathCondition) (after : List Match) : List Match :=
  .mk pivot.unknown (tailPaths.map .path ++ existentialsOf pivot.conditions) :: after

/-- The tail is given the labels in scope at the pivot that it uses. -/
def tailGivenAt (s : Specification) (headMatches tailMatches : List Match) : List Label :=
  let used := usedInMatches tailMatches ++ s.projection.labels
  (s.given ++ headMatches.map (·.unknown)).filter fun label => used.contains label.name

/-- Split at a pivot: the first match the graph cannot run, with the matches
before and after it. -/
def splitAt (s : Specification) (before : List Match) (pivot : Match) (after : List Match) : Split :=
  let (splitMatches, tailPaths) := splitPaths 0 (pathsOf pivot.conditions)
  let headMatches := before ++ splitMatches
  let tailMatches := tailMatchesAt pivot tailPaths after
  let tailGiven := tailGivenAt s headMatches tailMatches
  -- The head projects the tail's givens.
  { head := { given := s.given, matchList := headMatches,
              projection := .composite (tailGiven.map fun l => { name := l.name, label := l.name }) },
    tail := some { given := tailGiven, matchList := tailMatches, projection := s.projection } }

def splitBeforeFirstSuccessor (s : Specification) : Split :=
  match s.matchList.span matchIsDeterministic with
  | (_, []) =>
    -- No match seeks successors, so the whole specification is the head.
    { head := s, tail := none }
  | (before, pivot :: after) => splitAt s before pivot after

/-! ## Evaluating a split -/

/-- Keep only the bindings the tail is given. -/
def Env.restrictTo (names : List Name) (env : Env) : Env :=
  fun n => if names.contains n then env n else none

/-- Evaluate a split as the authorization engine does: the head on the graph
gives one tuple per solution, and each tuple seeds the tail with one fact per
tail given. -/
def Split.evaluate (split : Split) (g : Graph) (env : Env) : List (List (Option FactId)) :=
  match split.tail with
  | none => split.head.evaluate g env
  | some tail =>
    (evalMatches g env split.head.matchList).flatMap fun tuple =>
      tail.evaluate g (tuple.restrictTo (tail.given.map (·.name)))

end JinagaSpec
