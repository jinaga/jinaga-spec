import Lean.Data.Json
import JinagaSpec

/-!
# Conformance vectors

`lake exe vectors [dir]` writes one JSON file per case to `dir/split/`. Each
holds a specification and the split this oracle computes for it. A port passes
when its own split of the same specification equals `expected`.
-/
open Lean (Json)
open JinagaSpec

def caseToJson (c : Case) : Json :=
  let split := splitBeforeFirstSuccessor c.spec
  let hoisted := hoist c.spec
  let text : Option Specification → Json
    | none => Json.null
    | some s => Json.str (describeSpecification s)
  -- The rule's own given, `given[0]` in `jinaga.js`: the fact under
  -- authorization, which the constructor refuses to let the tail read.
  let given0Name := match c.spec.given with
    | g0 :: _ => g0.name
    | [] => ""
  Json.mkObj [
    ("name", c.name),
    ("description", c.description),
    ("source", c.source),
    ("specification", specificationToJson c.spec),
    ("text", describeSpecification c.spec),
    ("expected", Json.mkObj [
      ("head", optionToJson specificationToJson split.head),
      ("tail", optionToJson specificationToJson split.tail),
      ("headText", text split.head),
      ("tailText", text split.tail),
      ("tailReadsGiven", tailReadsGiven split given0Name)]),
    -- Not part of the split's own contract: `hoist` (Hoist.lean, still
    -- unproved in general) reaches into the tail's existential conditions for
    -- predecessor walks of labels in scope at the pivot, at positive
    -- polarity. Recorded so a reader can see where it changes `expected`
    -- (it does not, for any of these cases) and where it changes
    -- `tailReadsGiven`.
    ("hoisted", Json.mkObj [
      ("head", optionToJson specificationToJson hoisted.head),
      ("tail", optionToJson specificationToJson hoisted.tail),
      ("headText", text hoisted.head),
      ("tailText", text hoisted.tail),
      ("tailReadsGiven", tailReadsGiven hoisted given0Name)])]

def wellFormedCaseToJson (c : WellFormedCase) : Json :=
  Json.mkObj [
    ("name", c.name),
    ("description", c.description),
    ("source", c.source),
    ("specification", specificationToJson c.spec),
    ("text", describeSpecification c.spec),
    ("violates", Json.arr (c.violates.map Json.str).toArray),
    ("expected", Json.mkObj [("wellFormed", isWellFormed c.spec)])]

/-- The vector's verdict comes from the oracle, but each case states which rules
a reader expects it to violate, and a disagreement is an error, not a vector. -/
def checkIntent (c : WellFormedCase) : IO Unit := do
  if isWellFormed c.spec != c.violates.isEmpty then
    throw <| IO.userError s!"{c.name}: the oracle says wellFormed={isWellFormed c.spec}, but the case violates {c.violates}"

def main (args : List String) : IO Unit := do
  let root : System.FilePath := args.headD "vectors"
  let splitDir := root / "split"
  let wfDir := root / "well-formed"
  IO.FS.createDirAll splitDir
  IO.FS.createDirAll wfDir
  for c in cases do
    -- Every specification the split vectors use is one the theorem covers.
    unless isWellFormed c.spec do
      throw <| IO.userError s!"split case {c.name} is not well-formed"
    IO.FS.writeFile (splitDir / s!"{c.name}.json") ((caseToJson c).pretty ++ "\n")
  for c in wellFormedCases do
    checkIntent c
    IO.FS.writeFile (wfDir / s!"{c.name}.json") ((wellFormedCaseToJson c).pretty ++ "\n")
  IO.println s!"wrote {cases.length} split vectors to {splitDir} and {wellFormedCases.length} well-formedness vectors to {wfDir}"
