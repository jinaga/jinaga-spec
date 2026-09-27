import JinagaSpec.Split

/-!
# Store semantics

An authorization rule runs while its fact is being authorized, before that fact
is saved (`SpecificationRunner.read` in `jinaga.js`). At evaluation time the
fact bound to the given, call it `f`, is absent from the store: the head walks
predecessors of `f` on an in-memory graph that holds it, but no unknown of an
ordinary type may ever be bound to `f` itself, and the tail, which runs on the
store, reads nothing when a given it is seeded with is `f`.

This file models both consequences. `Graph.authGraph` is the graph the head
runs on: the store, plus `f` retyped to a reserved type nothing else uses. The
retyping is the whole trick (`docs/findings.md`): a walk from `f` still reaches
its predecessors, because `Graph.step` looks a start fact up by id and checks
types only on the facts it reaches, but no unknown of an ordinary type ranges
over `f`, because `evalMatches` filters candidates by type first.

`Split.evaluateStore` is the runner's behaviour: the head runs on `authGraph`,
and for each of its solutions, the tail runs on the store, seeded as
`Split.evaluate` seeds it, but only if every fact it is seeded with is already
in the store. `tailReadsGiven` is what `jinaga.js`'s constructor checks: whether
the tail is given the rule's own given.

Written in the same portable subset as `Split.lean`.
-/
namespace JinagaSpec

/-- Every predecessor id named by a fact in `g` is the id of a fact in `g`. A
walk that starts inside a closed graph never leaves it. -/
def Graph.closed (g : Graph) : Prop :=
  ∀ f ∈ g, ∀ p ∈ f.predecessors, ∃ f' ∈ g, f'.id = p.2

/-- Reserved for the fact under authorization, so that no unknown of an
ordinary type ever ranges over it. Not a label: a type name, so it is not
covered by `isReserved`, which reserves label names. -/
def batchType : Name := "__batch"

/-- The graph the head runs on while `f` is being authorized: the store, plus
`f` itself, retyped so that it is reachable by predecessor walks but invisible
to any match of an ordinary type. -/
def Graph.authGraph (store : Graph) (f : Fact) : Graph :=
  store ++ [{ f with type := batchType }]

mutual
  /-- No unknown anywhere in `s`, including inside existential conditions, has
  the reserved batch type. A hypothesis of the theorems below, not folded into
  `WellFormed`: it is about the graph a rule runs on, not about the
  specification's own scoping. -/
  def OrdinaryTypesMatches : List Match → Prop
    | [] => True
    | .mk u cs :: rest => u.type ≠ batchType ∧ OrdinaryTypesConditions cs ∧ OrdinaryTypesMatches rest

  def OrdinaryTypesConditions : List Condition → Prop
    | [] => True
    | c :: cs => OrdinaryTypesCondition c ∧ OrdinaryTypesConditions cs

  def OrdinaryTypesCondition : Condition → Prop
    | .path _ => True
    | .existential _ ms => OrdinaryTypesMatches ms
end

def OrdinaryTypes (s : Specification) : Prop := OrdinaryTypesMatches s.matchList

/-- The tail exists, and one of its givens is named `given`: the shape
`jinaga.js`'s constructor refuses. -/
def tailReadsGiven (split : Split) (given : Name) : Bool :=
  match split.tail with
  | none => false
  | some tail => tail.given.any fun l => l.name == given

/-- A fact of this id is in `g`. -/
def Graph.hasFact (g : Graph) (id : FactId) : Bool :=
  (g.factOf id).isSome

/-- Evaluate a split against a store, while `f` is under authorization: the
head runs on `authGraph store f`, and each of its solutions seeds the tail,
which runs on `store` alone. A tuple that would seed the tail with a fact
absent from the store contributes nothing: this is the runner's rule
(`SpecificationRunner.read`), stated here rather than derived, because the
graph semantics of a walk from an absent id is the empty list, not a whole-read
refusal. -/
def Split.evaluateStore (split : Split) (store : Graph) (f : Fact) (env : Env) :
    List (List (Option FactId)) :=
  match split.tail with
  | none => split.head.evaluate (Graph.authGraph store f) env
  | some tail =>
    (evalMatches (Graph.authGraph store f) env split.head.matchList).flatMap fun tuple =>
      let tailEnv := tuple.restrictTo (tail.given.map (·.name))
      if tail.given.all fun l => match tailEnv l.name with
          | some id => store.hasFact id
          | none => false
      then tail.evaluate store tailEnv
      else []

end JinagaSpec
