import JinagaSpec.Semantics

/-!
# Checking well-formedness

`isWellFormed` decides whether a specification meets the preconditions of the
split (`docs/contracts.md`). It is written in the portable subset, so a port can
run the same check at the boundary where a specification enters: before the
split, and wherever a rule is constructed.

`JinagaSpec/Proofs/WellFormedCheck.lean` proves it agrees with the proposition
`WellFormed` that `split_correct` assumes.

The check has three parts, and reports each separately so that a port can name
the condition a specification violates:

* `isScoped`: every label a path condition names is in scope. A match adds its
  unknown to the scope of the matches after it, and of its own existential
  conditions. It never joins its own unknown.
* `isUnshadowed`: no match declares a label that is already in scope. Scope is
  lexical, so sibling existential conditions may reuse a name.
* `isProjected`: the projection names only givens and top-level unknowns.
-/
namespace JinagaSpec

mutual
  def isScopedMatches : List Name → List Match → Bool
    | _, [] => true
    | scope, .mk unknown conditions :: rest =>
      isScopedConditions (unknown.name :: scope) scope conditions &&
        isScopedMatches (unknown.name :: scope) rest

  /-- `inner` is the scope of existential conditions, `outer` of path
  conditions. -/
  def isScopedConditions (inner outer : List Name) : List Condition → Bool
    | [] => true
    | c :: cs => isScopedCondition inner outer c && isScopedConditions inner outer cs

  def isScopedCondition (inner outer : List Name) : Condition → Bool
    | .path c => outer.contains c.labelRight
    | .existential _ ms => isScopedMatches inner ms
end

mutual
  def isUnshadowedMatches : List Name → List Match → Bool
    | _, [] => true
    | scope, .mk unknown conditions :: rest =>
      !scope.contains unknown.name &&
        isUnshadowedConditions (unknown.name :: scope) conditions &&
        isUnshadowedMatches (unknown.name :: scope) rest

  def isUnshadowedConditions (inner : List Name) : List Condition → Bool
    | [] => true
    | c :: cs => isUnshadowedCondition inner c && isUnshadowedConditions inner cs

  def isUnshadowedCondition (inner : List Name) : Condition → Bool
    | .path _ => true
    | .existential _ ms => isUnshadowedMatches inner ms
end

def isScoped (s : Specification) : Bool :=
  isScopedMatches (s.given.map (·.name)) s.matchList

def isUnshadowed (s : Specification) : Bool :=
  isUnshadowedMatches (s.given.map (·.name)) s.matchList

def isProjected (s : Specification) : Bool :=
  s.projection.labels.all fun label =>
    (s.given.map (·.name)).contains label || (s.matchList.map (·.unknown.name)).contains label

def isWellFormed (s : Specification) : Bool :=
  isScoped s && isUnshadowed s && isProjected s

end JinagaSpec
