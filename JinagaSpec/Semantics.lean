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

def Projection.labels : Projection → List Name
  | .fact label => [label]
  | .composite components => components.map (·.label)

/-- The results of a specification: for each solution, the facts its
projection names. Results are compared as sets. -/
def Specification.evaluate (s : Specification) (g : Graph) (env : Env) : List (List (Option FactId)) :=
  (evalMatches g env s.matchList).map fun e => s.projection.labels.map e

/-- Bind the givens, in order, to the facts a caller supplies. -/
def Specification.bindGivens (s : Specification) (facts : List FactId) : Env :=
  fun n => ((s.given.map (·.name)).zip facts).lookup n

end JinagaSpec
