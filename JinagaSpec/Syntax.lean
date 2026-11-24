/-!
# Syntax

The specification language, field for field as `jinaga.js` declares it in
`src/specification/specification.ts`. A `Match` and a `Condition` are mutually
recursive because an existential condition holds matches.

Glossary: `matches` is reserved in Lean, so `matches` in TypeScript is
`matchList` here. Everything else keeps its name.
-/
namespace JinagaSpec

abbrev Name := String

structure Label where
  name : Name
  type : Name
deriving Repr, DecidableEq

structure Role where
  name : Name
  predecessorType : Name
deriving Repr, DecidableEq

/-- `unknown->rolesLeft = labelRight->rolesRight`. -/
structure PathCondition where
  rolesLeft : List Role
  labelRight : Name
  rolesRight : List Role
deriving Repr, DecidableEq

mutual
  inductive Condition where
    | path (condition : PathCondition)
    | existential («exists» : Bool) (matchList : List Match)

  inductive Match where
    | mk (unknown : Label) (conditions : List Condition)
end

def Match.unknown : Match → Label
  | .mk unknown _ => unknown

def Match.conditions : Match → List Condition
  | .mk _ conditions => conditions

mutual
  /-- Structural equality. Written out, rather than derived, so that a proof
  can use it (`Proofs/Basic.lean`). -/
  def Condition.beq : Condition → Condition → Bool
    | .path a, .path b => a == b
    | .existential e1 ms1, .existential e2 ms2 => e1 == e2 && Match.beqList ms1 ms2
    | _, _ => false

  def Match.beqList : List Match → List Match → Bool
    | [], [] => true
    | .mk u1 cs1 :: r1, .mk u2 cs2 :: r2 => u1 == u2 && Condition.beqList cs1 cs2 && Match.beqList r1 r2
    | _, _ => false

  def Condition.beqList : List Condition → List Condition → Bool
    | [], [] => true
    | c1 :: r1, c2 :: r2 => Condition.beq c1 c2 && Condition.beqList r1 r2
    | _, _ => false
end

instance : BEq Condition := ⟨Condition.beq⟩
instance : BEq Match := ⟨fun m1 m2 => Match.beqList [m1] [m2]⟩

def Condition.isPath : Condition → Bool
  | .path _ => true
  | .existential .. => false

@[simp] theorem Match.unknown_mk (unknown : Label) (conditions : List Condition) :
    (Match.mk unknown conditions).unknown = unknown := rfl

@[simp] theorem Match.conditions_mk (unknown : Label) (conditions : List Condition) :
    (Match.mk unknown conditions).conditions = conditions := rfl

mutual
  /-- A projection names a fact, or composes named components. -/
  inductive Projection where
    | fact (label : Name)
    | composite (components : List Component)

  /-- A component names a fact, or holds a child specification: matches that
  go on from the parent's, with a projection of their own. -/
  inductive Component where
    | fact (name : Name) (label : Name)
    | specification (name : Name) (matchList : List Match) (projection : Projection)
end

def Component.name : Component → Name
  | .fact name _ => name
  | .specification name .. => name

mutual
  /-- Structural equality, written out as `Condition.beq` is, so that a proof
  can use it (`Proofs/Basic.lean`). -/
  def Projection.beq : Projection → Projection → Bool
    | .fact a, .fact b => a == b
    | .composite cs1, .composite cs2 => Component.beqList cs1 cs2
    | _, _ => false

  def Component.beqList : List Component → List Component → Bool
    | [], [] => true
    | c1 :: r1, c2 :: r2 => Component.beq c1 c2 && Component.beqList r1 r2
    | _, _ => false

  def Component.beq : Component → Component → Bool
    | .fact n1 l1, .fact n2 l2 => n1 == n2 && l1 == l2
    | .specification n1 ms1 p1, .specification n2 ms2 p2 =>
      n1 == n2 && Match.beqList ms1 ms2 && Projection.beq p1 p2
    | _, _ => false
end

structure Specification where
  given : List Label
  matchList : List Match
  projection : Projection

mutual
  /-- Labels the matches name but do not bind. `inner` holds the labels bound
  around them, including their own unknowns. -/
  def freeInMatches (inner : List Name) : List Match → List Name
    | [] => []
    | .mk _ cs :: rest => freeInConditions inner cs ++ freeInMatches inner rest

  def freeInConditions (inner : List Name) : List Condition → List Name
    | [] => []
    | .path pc :: cs =>
      (if inner.contains pc.labelRight then [] else [pc.labelRight]) ++ freeInConditions inner cs
    | .existential _ ms :: cs =>
      freeInMatches (inner ++ ms.map (·.unknown.name)) ms ++ freeInConditions inner cs
end

/-- The givens the matches use: those they name, in their path conditions or
their filters, in the specification's order. A feed takes only these
(`asFeed`), and so does the connectivity check (`isConnected`). -/
def usedGivens (givens : List Label) (ms : List Match) : List Label :=
  givens.filter fun l => (freeInMatches [] ms).contains l.name

/-- Labels that begin with `__` belong to the split, which names the facts it
hands from the head to the tail. A specification may not declare one, so a
split label can never collide with a label the specification declares. -/
def isReserved (name : Name) : Bool := name.startsWith "__"

end JinagaSpec
