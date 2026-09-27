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

/-- Labels that begin with `__` belong to the split, which names the facts it
hands from the head to the tail. A specification may not declare one, so a
split label can never collide with a label the specification declares. -/
def isReserved (name : Name) : Bool := name.startsWith "__"

end JinagaSpec
