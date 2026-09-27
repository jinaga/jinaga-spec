import Lean.Data.Json
import JinagaSpec.Split

/-!
# JSON form

The shapes `jinaga.js` uses when it serializes a specification. A conformance
vector holds a specification and the split the oracle expects, in this form, so
that any port can read it without linking to Lean.
-/
namespace JinagaSpec

open Lean (Json)

def roleToJson (r : Role) : Json :=
  Json.mkObj [("name", r.name), ("predecessorType", r.predecessorType)]

def labelToJson (l : Label) : Json :=
  Json.mkObj [("name", l.name), ("type", l.type)]

def rolesToJson (roles : List Role) : Json :=
  Json.arr (roles.map roleToJson).toArray

mutual
  partial def matchToJson : Match → Json
    | .mk unknown conditions =>
      Json.mkObj [("unknown", labelToJson unknown),
                  ("conditions", Json.arr (conditions.map conditionToJson).toArray)]

  partial def conditionToJson : Condition → Json
    | .path c =>
      Json.mkObj [("type", "path"), ("rolesLeft", rolesToJson c.rolesLeft),
                  ("labelRight", c.labelRight), ("rolesRight", rolesToJson c.rolesRight)]
    | .existential e ms =>
      Json.mkObj [("type", "existential"), ("exists", e),
                  ("matches", Json.arr (ms.map matchToJson).toArray)]
end

def projectionToJson : Projection → Json
  | .fact label => Json.mkObj [("type", "fact"), ("label", label)]
  | .composite components =>
    Json.mkObj [("type", "composite"),
      ("components", Json.arr (components.map fun c =>
        Json.mkObj [("type", "fact"), ("name", c.name), ("label", c.label)]).toArray)]

def specificationToJson (s : Specification) : Json :=
  Json.mkObj [
    ("given", Json.arr (s.given.map fun l =>
      Json.mkObj [("label", labelToJson l), ("conditions", Json.arr #[])]).toArray),
    ("matches", Json.arr (s.matchList.map matchToJson).toArray),
    ("projection", projectionToJson s.projection)]

def optionToJson (f : Specification → Json) : Option Specification → Json
  | none => Json.null
  | some s => f s

end JinagaSpec
