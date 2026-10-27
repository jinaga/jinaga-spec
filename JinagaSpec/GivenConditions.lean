import JinagaSpec.Split

/-!
# Conditions on a given

jinaga.js lets a given carry existential conditions (`SpecificationGiven`): a
specification `(p1: Root [!E { a: Archived [a->root: Root = p1] }]) { ... }`
has no results while its root is archived. A condition on a given reads the
subscription's givens and nothing else.

`reduceGivenConditions` writes such a specification in the language without
them, so that everything proven about that language applies: it moves every
condition onto a new first match, `x: T [x = g, ...]`, bound to the first given
that has any. An existential condition does not read the match it is written
on, so one match serves the conditions of every given, and it has one solution
when they hold and none when they do not. `Proofs/GivenConditions.lean` proves
that the reduced specification reads the same results
(`read_reduceGivenConditions`), and so that the stream of its candidates is
exact.

The new match needs a label the specification does not use.
`givenConditionsLabel` picks the first of `given`, `given2`, `given3`, ... that
the specification does not name anywhere. The theorem holds for any unused
label, and the vector generator checks the one this picks.
-/
namespace JinagaSpec

/-- An existential condition on a given: whether its matches must exist, and
the matches. -/
abbrev GivenCondition := Bool × List Match

/-- A specification whose givens carry conditions, as jinaga.js writes it. -/
structure ConditionedSpecification where
  given : List (Label × List GivenCondition)
  matchList : List Match
  projection : Projection

/-- A specification whose givens have no conditions. -/
def ConditionedSpecification.ofSpecification (s : Specification) : ConditionedSpecification :=
  { given := s.given.map (·, []), matchList := s.matchList, projection := s.projection }

/-- The specification without the conditions on its givens. -/
def ConditionedSpecification.spec (c : ConditionedSpecification) : Specification :=
  { given := c.given.map (·.1), matchList := c.matchList, projection := c.projection }

/-- The conditions on every given, in order, as conditions of a match. -/
def ConditionedSpecification.conditions (c : ConditionedSpecification) : List Condition :=
  c.given.flatMap fun (_, gcs) => gcs.map fun (e, ms) => .existential e ms

/-- Every condition on a given holds: its matches have a solution, or have
none, as it asks. -/
def ConditionedSpecification.conditionsHold (c : ConditionedSpecification) (g : Graph) (env : Env) : Bool :=
  c.given.all fun (_, gcs) => gcs.all fun (e, ms) => e == !(evalMatches g env ms).isEmpty

/-- The results a replica reads: none while a condition on a given fails. -/
def ConditionedSpecification.read (c : ConditionedSpecification) (g : Graph) (env : Env) :
    List (List (Option FactId)) :=
  if c.conditionsHold g env then c.spec.read g env else []

/-- Move every condition on a given onto a new first match, labelled `x`, bound
to the first given that has a condition. Without conditions, the specification
is unchanged. -/
def reduceGivenConditions (x : Name) (c : ConditionedSpecification) : Specification :=
  match c.given.find? (!·.2.isEmpty) with
  | some (g0, _) =>
    { c.spec with
      matchList := .mk { name := x, type := g0.type }
        (.path { rolesLeft := [], labelRight := g0.name, rolesRight := [] } :: c.conditions) :: c.matchList }
  | none => c.spec

/-- Every label the specification names: its givens, every label declared or
named at any depth, and its projection. -/
def ConditionedSpecification.labels (c : ConditionedSpecification) : List Name :=
  c.given.map (·.1.name) ++ declaredInConditions c.conditions ++ usedInConditions c.conditions ++
    declaredInMatches c.matchList ++ usedInMatches c.matchList ++ c.projection.labels

/-- The label of the match `reduceGivenConditions` adds: the first of `given`,
`given2`, `given3`, ... that the specification does not name. -/
def givenConditionsLabel (c : ConditionedSpecification) : Name :=
  let candidates := "given" :: (List.range c.labels.length).map fun i => s!"given{i + 2}"
  (candidates.find? (!c.labels.contains ·)).getD "given"

end JinagaSpec
