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
  let text : Option Specification → Json
    | none => Json.null
    | some s => Json.str (describeSpecification s)
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
      ("tailText", text split.tail)])]

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := (args.headD "vectors") / "split"
  IO.FS.createDirAll dir
  for c in cases do
    IO.FS.writeFile (dir / s!"{c.name}.json") ((caseToJson c).pretty ++ "\n")
  IO.println s!"wrote {cases.length} vectors to {dir}"
