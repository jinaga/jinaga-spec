import JinagaSpec.Syntax

/-!
# Semantics

What a specification means over a fact graph. This is the definition of
"correct" that every transformation is proved against, so it is deliberately
naive: an unknown ranges over every fact of its type, and a candidate is kept
if all of its conditions hold.

A match must begin with a path condition (`validateSpecification`), which lets
an implementation reach candidates by walking edges instead of scanning the
graph. That is a rule for making the semantics computable efficiently. It does
not change what the semantics is.
-/
namespace JinagaSpec

abbrev FactId := Nat

/-- A fact: its type and, for each role, the facts it points to. A role may
name several predecessors. -/
structure Fact where
  id : FactId
  type : Name
  predecessors : List (Name × FactId)

abbrev Graph := List Fact

def Graph.factOf (g : Graph) (id : FactId) : Option Fact :=
  g.find? fun f => f.id == id

/-- An id names at most one fact of the graph. -/
def Graph.IdsUnique (g : Graph) : Prop := ∀ a ∈ g, ∀ b ∈ g, a.id = b.id → a = b

/-- The facts a fact points to by one role. Only a predecessor of the role's
declared type is reached. -/
def Graph.step (g : Graph) (role : Role) (id : FactId) : List FactId :=
  match g.factOf id with
  | none => []
  | some fact =>
    (fact.predecessors.filter fun (name, _) => name == role.name).map Prod.snd
      |>.filter fun p =>
        match g.factOf p with
        | some f => f.type == role.predecessorType
        | none => false

/-- Every fact reached from `start` by following the roles in order. -/
def Graph.walk (g : Graph) (start : FactId) : List Role → List FactId
  | [] => [start]
  | role :: roles => (g.step role start).flatMap fun p => g.walk p roles

/-- What each label is bound to. -/
abbrev Env := Name → Option FactId

def Env.bind (env : Env) (name : Name) (id : FactId) : Env :=
  fun n => if n = name then some id else env n

/-- `unknown->rolesLeft = labelRight->rolesRight`: the two walks reach a
common fact. -/
def PathCondition.holds (g : Graph) (env : Env) (unknown : Name) (c : PathCondition) : Bool :=
  match env unknown, env c.labelRight with
  | some u, some r => (g.walk u c.rolesLeft).any fun a => (g.walk r c.rolesRight).contains a
  | _, _ => false

mutual
  /-- Every way to bind the unknowns of the matches, in order, so that each
  match's conditions hold. -/
  def evalMatches (g : Graph) (env : Env) : List Match → List Env
    | [] => [env]
    | .mk unknown conditions :: rest =>
      (g.filter fun f => f.type == unknown.type).flatMap fun f =>
        let env' := env.bind unknown.name f.id
        if allHold g env' unknown.name conditions then evalMatches g env' rest else []

  def allHold (g : Graph) (env : Env) (unknown : Name) : List Condition → Bool
    | [] => true
    | c :: cs => holds g env unknown c && allHold g env unknown cs

  /-- A path condition compares two walks. An existential condition asks
  whether its matches have a solution, and whether that is what it expects. -/
  def holds (g : Graph) (env : Env) (unknown : Name) : Condition → Bool
    | .path c => c.holds g env unknown
    | .existential e ms => e == !(evalMatches g env ms).isEmpty
end

def Component.labels : Component → List Name
  | .fact _ label => [label]
  | .specification .. => []

/-- The labels whose facts a projection names. A child specification names its
own, in its own results. -/
def Projection.labels : Projection → List Name
  | .fact label => [label]
  | .composite components => components.flatMap Component.labels

/-- A projection's child specifications: each one's matches and projection. -/
def Projection.children : Projection → List (List Match × Projection)
  | .fact _ => []
  | .composite components => components.filterMap fun
    | .specification _ ms p => some (ms, p)
    | .fact .. => none

theorem Projection.sizeOf_children {p : Projection} {c : List Match × Projection} (h : c ∈ p.children) :
    sizeOf c.2 < sizeOf p := by
  cases p with
  | fact => simp [Projection.children] at h
  | composite cs =>
    simp only [Projection.children, List.mem_filterMap] at h
    obtain ⟨x, hx, hc⟩ := h
    have := List.sizeOf_lt_of_mem hx
    cases x with
    | fact => simp at hc
    | specification n ms q => simp at hc; subst hc; simp at this ⊢; omega

/-- The results of a specification: for each solution, the facts its
projection names. Results are compared as sets. -/
def Specification.evaluate (s : Specification) (g : Graph) (env : Env) : List (List (Option FactId)) :=
  (evalMatches g env s.matchList).map fun e => s.projection.labels.map e

/-- A result of a specification with child specifications: the facts its
projection names, and, for each child specification, its results. -/
inductive Result where
  | mk (row : List (Option FactId)) (children : List (List Result))

/-- `r` is a result of the projection `p` read on `g` from the one solution
`σ`: `σ` projects to its row, and for each child specification, each listed
result is read from some solution of the child's matches, and each such
solution has some listed result read from it. So results are compared as sets
at every depth: neither the order of a child's results, nor a repeated one,
nor which of two equal results is listed, matters. A child's list needs only
one result per solution, so a finite one always exists (`readsAt_resultsAt`). -/
def Projection.ReadsAt (g : Graph) : Projection → Env → Result → Prop
  | p, σ, .mk row cs => row = p.labels.map σ ∧ cs.length = p.children.length ∧
      ∀ x ∈ p.children.attach.zip cs,
        (∀ r ∈ x.2, ∃ τ ∈ evalMatches g σ x.1.1.1, x.1.1.2.ReadsAt g τ r) ∧
        (∀ τ ∈ evalMatches g σ x.1.1.1, ∃ r ∈ x.2, x.1.1.2.ReadsAt g τ r)
termination_by p => sizeOf p
decreasing_by all_goals exact Projection.sizeOf_children x.1.2

/-- `r` is a result of the matches `ms` with the projection `p`, read on `g`
from `env`: it is read (`ReadsAt`) from some solution of the matches. -/
def Projection.Reads (g : Graph) (p : Projection) (ms : List Match) (env : Env) (r : Result) : Prop :=
  ∃ σ ∈ evalMatches g env ms, p.ReadsAt g σ r

/-- The result read from the solution `σ`, child specifications included: one
result for each solution of each child's matches, in the order `evalMatches`
finds them, as jinaga.js's `SpecificationRunner.read` builds it. It is a
result in the sense of `ReadsAt` (`readsAt_resultsAt`). -/
def Projection.resultsAt (g : Graph) : Projection → Env → Result
  | p, σ => .mk (p.labels.map σ) (p.children.attach.map fun c => (evalMatches g σ c.1.1).map (c.1.2.resultsAt g))
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children c.2

/-- The results of the matches `ms` with the projection `p`: one for each
solution. Each is a result in the sense of `Reads` (`reads_of_mem_resultsOf`). -/
def Projection.resultsOf (g : Graph) (p : Projection) (ms : List Match) (env : Env) : List Result :=
  (evalMatches g env ms).map (p.resultsAt g)

/-- The label is bound to a fact of `g` of the label's type. -/
def Graph.has (g : Graph) (env : Env) (l : Label) : Bool :=
  match env l.name with
  | some id => (g.factOf id).any (·.type == l.type)
  | none => false

/-- The results as a replica reads them: none until every given is a fact the
replica holds, as jinaga.js's `SpecificationRunner.read` does. `evaluate`
binds a given whether or not its fact is stored, so before the given arrives
it can find results that a replica would not. -/
def Specification.read (s : Specification) (g : Graph) (env : Env) : List (List (Option FactId)) :=
  if s.given.all (g.has env) then s.evaluate g env else []

/-- What a replica reads, child specifications included: nothing until every
given is a fact it holds, as for `read`. -/
def Specification.Reads (s : Specification) (g : Graph) (env : Env) (r : Result) : Prop :=
  s.given.all (g.has env) = true ∧ s.projection.Reads g s.matchList env r

/-- What a replica reads, child specifications included, as a list: nothing
until every given is a fact it holds, then `Projection.resultsOf`. Each is a
result in the sense of `Specification.Reads` (`reads_of_mem_readsOf`). -/
def Specification.readsOf (s : Specification) (g : Graph) (env : Env) : List Result :=
  if s.given.all (g.has env) then s.projection.resultsOf g s.matchList env else []

/-- The paths from a projection to each of its child specifications, at every
depth, and to itself: the matches on the way, and the projection reached. -/
def Projection.paths : Projection → List (List Match × Projection)
  | p => ([], p) :: p.children.attach.flatMap fun ⟨c, _⟩ => c.2.paths.map fun x => (c.1 ++ x.1, x.2)
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children ‹_›

/-- A specification and its child specifications at every depth, each as a
specification. A child's matches go on from its parent's, so a child
specification is one with the same givens whose matches are its parent's
followed by its own. -/
def Specification.descendants (s : Specification) : List Specification :=
  s.projection.paths.map fun x => { given := s.given, matchList := s.matchList ++ x.1, projection := x.2 }

/-- Bind the givens, in order, to the facts a caller supplies. -/
def Specification.bindGivens (s : Specification) (facts : List FactId) : Env :=
  fun n => ((s.given.map (·.name)).zip facts).lookup n

end JinagaSpec
