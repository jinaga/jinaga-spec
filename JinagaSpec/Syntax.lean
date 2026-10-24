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

structure Component where
  name : Name
  label : Name
deriving Repr, DecidableEq

inductive Projection where
  | fact (label : Name)
  | composite (components : List Component)
deriving Repr, DecidableEq

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

/-- Labels that begin with `__` belong to the split, which names the facts it
hands from the head to the tail. A specification may not declare one, so a
split label can never collide with a label the specification declares. -/
def isReserved (name : Name) : Bool := name.startsWith "__"

end JinagaSpec
