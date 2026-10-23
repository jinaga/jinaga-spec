import Lean.Data.Json
import JinagaSpec
import CheckGen

/-!
# Conformance vectors

`lake exe vectors [dir]` writes one JSON file per case to `dir/split/`. Each
holds a specification and the split this oracle computes for it. A port passes
when its own split of the same specification equals `expected`.

It also writes `dir/inverse/`: for each case, a specification, a graph, the
subscription's givens and a fresh fact, with the results gained and lost, the
inverses `candidates` builds and reorders, and the candidates they find
(`vectors/README.md`).
-/
open Lean (Json)
open JinagaSpec

def caseToJson (c : Case) : Json :=
  let split := splitBeforeFirstSuccessor c.spec
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
      ("tailReadsGiven", tailReadsGiven split given0Name)])]

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

def rowToJson (row : Row) : Json :=
  Json.arr (row.map fun | some id => Json.num id | none => Json.null).toArray

def rowsToJson (rows : List Row) : Json := Json.arr (rows.eraseDups.map rowToJson).toArray

def factToJson (f : Fact) : Json :=
  Json.mkObj [("id", Json.num f.id), ("type", f.type),
    ("predecessors", Json.arr (f.predecessors.map fun (role, id) =>
      Json.mkObj [("role", role), ("id", Json.num id)]).toArray)]

def inverseToJson (i : Specification) : Json :=
  Json.mkObj [("specification", specificationToJson i), ("text", describeSpecification i)]

def inverseVector (c : InverseCase) : Json :=
  let g' := c.graph ++ [c.fact]
  let old := c.spec.evaluate c.graph c.env
  let new := c.spec.evaluate g' c.env
  let is := inverses c.spec
  Json.mkObj [
    ("name", c.name),
    ("description", c.description),
    ("source", c.source),
    ("specification", specificationToJson c.spec),
    ("text", describeSpecification c.spec),
    ("rowLabels", Json.arr (c.spec.projection.labels.map Json.str).toArray),
    ("givens", Json.mkObj (c.givens.map fun (n, id) => (n, Json.num id))),
    ("graph", Json.arr (c.graph.map factToJson).toArray),
    ("fact", factToJson c.fact),
    ("expected", Json.mkObj [
      ("gained", rowsToJson (new.filter (!old.contains ·))),
      ("lost", rowsToJson (old.filter (!new.contains ·))),
      ("inverses", Json.arr (is.map inverseToJson).toArray),
      ("reordered", Json.arr (is.map (inverseToJson ∘ reorderOrSelf)).toArray),
      ("candidates", rowsToJson (candidates c.spec c.env c.graph c.fact))])]

/-- Random specifications, each with a graph and fresh fact that change its
result, from a fixed seed, so that a port is held to shapes nobody chose. -/
def randomInverseCases (count : Nat) : List InverseCase := Id.run do
  let mut gen : StdGen × Nat := (mkStdGen 7, 0)
  let mut out : List InverseCase := []
  for _ in [0:2000] do
    if out.length ≥ count then break
    let (s, g) := (genSpec false 3 true).run gen
    gen := g
    -- Only specifications jinaga.js accepts: every label joined to the others.
    unless isConnected s do continue
    for _ in [0:200] do
      let ((store, env, f), g) := (do
        let st ← genGraph s 8
        let env ← genEnv s st
        let f ← genFreshFact s st 8
        return (st, env, f) : Gen (Graph × Env × Fact)).run gen
      gen := g
      let givens := s.given.map fun l => (l.name, (env l.name).getD 0)
      if !sameSet (s.evaluate store env) (s.evaluate (store ++ [f]) env) &&
          !givens.any (·.2 == f.id) then
        out := out ++ [{ name := s!"random-{out.length + 1}"
                         description := "A random well-formed specification, graph and fresh fact that change the result."
                         source := "lake exe vectors, seed 7"
                         spec := s, givens := givens, graph := store, fact := f }]
        break
  return out

def main (args : List String) : IO Unit := do
  let root : System.FilePath := args.headD "vectors"
  let splitDir := root / "split"
  let wfDir := root / "well-formed"
  let inverseDir := root / "inverse"
  IO.FS.createDirAll splitDir
  IO.FS.createDirAll wfDir
  IO.FS.createDirAll inverseDir
  let inverseAll := inverseCases ++ randomInverseCases 12
  for c in inverseAll do
    unless isWellFormed c.spec do
      throw <| IO.userError s!"inverse case {c.name} is not well-formed"
    if sameSet (c.spec.evaluate c.graph c.env) (c.spec.evaluate (c.graph ++ [c.fact]) c.env) then
      throw <| IO.userError s!"inverse case {c.name} does not change the result"
    IO.FS.writeFile (inverseDir / s!"{c.name}.json") ((inverseVector c).pretty ++ "\n")
  for c in cases do
    -- Every specification the split vectors use is one the theorem covers.
    unless isWellFormed c.spec do
      throw <| IO.userError s!"split case {c.name} is not well-formed"
    IO.FS.writeFile (splitDir / s!"{c.name}.json") ((caseToJson c).pretty ++ "\n")
  for c in wellFormedCases do
    checkIntent c
    IO.FS.writeFile (wfDir / s!"{c.name}.json") ((wellFormedCaseToJson c).pretty ++ "\n")
  IO.println s!"wrote {cases.length} split vectors to {splitDir}, {wellFormedCases.length} well-formedness vectors to {wfDir}, and {inverseAll.length} inverse vectors to {inverseDir}"
