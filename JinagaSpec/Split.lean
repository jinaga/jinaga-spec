import JinagaSpec.Semantics

/-!
# Splitting a specification: shared plumbing

The split (`JinagaSpec/Hoist.lean`) cuts a specification at the first match the
graph cannot run — the *pivot* — into a *head* the graph runs, and a *tail* that
needs the store, seeded with only the labels it uses. This file holds what a
split's result is and how it evaluates, independent of the algorithm that
produces it.

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

/-- The label the split gives the fact that the head walks to for the `i`th
hoisted path condition. -/
def splitLabel (i : Nat) : Name := s!"__s{i}"

/-- The head always exists, and has no matches when the pivot is the first
match and walks no predecessors. The tail is absent when nothing seeks
successors. -/
structure Split where
  head : Specification
  tail : Option Specification

/-- The tail is given the labels in scope at the pivot that it uses. -/
def tailGivenAt (s : Specification) (headMatches tailMatches : List Match) : List Label :=
  let used := usedInMatches tailMatches ++ s.projection.labels
  (s.given ++ headMatches.map (·.unknown)).filter fun label => used.contains label.name

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
