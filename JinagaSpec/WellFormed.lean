import JinagaSpec.Semantics

/-!
# Checking well-formedness

`isWellFormed` decides whether a specification meets the preconditions of the
split (`docs/contracts.md`). It is written in the portable subset, so a port can
run the same check at the boundary where a specification enters. Nothing
inside the library then needs to check again.

`JinagaSpec/Proofs/WellFormedCheck.lean` proves it agrees with the proposition
`WellFormed` that `split_correct` assumes. The conditions:

* **Scoped.** Every label a path condition names is in scope. A match adds its
  unknown to the scope of the matches after it, and of its own existential
  conditions. It never joins its own unknown.
* **Well-named.** Every declared label is new, not already in scope, and
  ordinary, not reserved for the split (`isReserved`). Scope is lexical, so
  sibling existential conditions may reuse a name.
* **Projected.** The projection names only givens and top-level unknowns.

`isWellFormedDeep` checks a specification's child specifications too, each as
a specification of its own.
-/
namespace JinagaSpec

mutual
  /-- `scope` holds the labels a match may join. -/
  def isWellFormedMatches : List Name → List Match → Bool
    | _, [] => true
    | scope, .mk unknown conditions :: rest =>
      !scope.contains unknown.name && !isReserved unknown.name &&
        isWellFormedConditions (unknown.name :: scope) scope conditions &&
        isWellFormedMatches (unknown.name :: scope) rest

  /-- `inner` is the scope of existential conditions, `outer` of path
  conditions. -/
  def isWellFormedConditions (inner outer : List Name) : List Condition → Bool
    | [] => true
    | c :: cs => isWellFormedCondition inner outer c && isWellFormedConditions inner outer cs

  def isWellFormedCondition (inner outer : List Name) : Condition → Bool
    | .path c => outer.contains c.labelRight
    | .existential _ ms => isWellFormedMatches inner ms
end

def isWellFormed (s : Specification) : Bool :=
  let givens := s.given.map (·.name)
  givens.all (!isReserved ·) &&
    isWellFormedMatches givens s.matchList &&
    s.projection.labels.all fun label => givens.contains label || (s.matchList.map (·.unknown.name)).contains label

/-- A specification and each of its child specifications, at every depth, are
well formed: each child as a specification whose matches go on from its
parent's (`Specification.descendants`). The feeds theorems assume it. -/
def isWellFormedDeep (s : Specification) : Bool := s.descendants.all isWellFormed

end JinagaSpec
