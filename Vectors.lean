import Lean.Data.Json
import JinagaSpec
import CheckGen

/-!
# Conformance vectors

`lake exe vectors [dir]` writes one JSON file per case to `dir/split/`. Each
holds a specification and the split this oracle computes for it. A port passes
when its own split of the same specification equals `expected`.

It also writes `dir/inverse/`: for each case, a specification, a graph, the
subscription's givens and a fresh fact or batch of facts, with the results
gained and lost, the inverses `candidates` builds and reorders, the
candidates they find, and, where they are exact for rows, the adds and removes
of the exact inverses (`vectors/README.md`).
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
  let g' := c.graph ++ c.batch
  let old := c.conditioned.read c.graph c.env
  let new := c.conditioned.read g' c.env
  let is := inverses c.reduced
  -- A vector with conditions on its givens also shows their reduction.
  let reduced := if c.conditioned.conditions.isEmpty then [] else [("reduced", inverseToJson c.reduced)]
  -- A batch of one is written as `fact`, so a port that reads only single
  -- facts reads those vectors unchanged.
  let arrived := match c.batch with
    | [f] => ("fact", factToJson f)
    | B => ("batch", Json.arr (B.map factToJson).toArray)
  Json.mkObj [
    ("name", c.name),
    ("description", c.description),
    ("source", c.source),
    ("specification", conditionedToJson c.conditioned),
    ("text", describeConditioned c.conditioned),
    ("rowLabels", Json.arr (c.spec.projection.labels.map Json.str).toArray),
    ("givens", Json.mkObj (c.givens.map fun (n, id) => (n, Json.num id))),
    ("graph", Json.arr (c.graph.map factToJson).toArray),
    arrived,
    ("expected", Json.mkObj <| reduced ++ [
      ("gained", rowsToJson (new.filter (!old.contains ·))),
      ("lost", rowsToJson (old.filter (!new.contains ·))),
      ("inverses", Json.arr (is.map inverseToJson).toArray),
      ("reordered", Json.arr (is.map (inverseToJson ∘ reorderOrSelf)).toArray),
      ("candidates", rowsToJson (candidates c.reduced c.env c.graph c.batch))] ++
      -- The exact inverses' changes, where they are exact for rows.
      (if projectsUnknowns c.reduced then
        let (adds, removes) := changes c.reduced c.env c.graph c.batch
        [("exact", Json.mkObj [("adds", rowsToJson adds), ("removes", rowsToJson removes)])]
      else []))]

/-- Random specifications, each with a graph and a fresh batch that change its
result, from a fixed seed, so that a port is held to shapes nobody chose. A
batch of `size` facts has at least one that names another, in a random order. -/
def randomInverseCases (namePrefix : String) (size count : Nat) : List InverseCase := Id.run do
  let mut gen : StdGen × Nat := (mkStdGen (7 + size - 1), 0)
  let mut out : List InverseCase := []
  for _ in [0:2000] do
    if out.length ≥ count then break
    let (s, g) := (genSpec false 3 true).run gen
    gen := g
    -- Only specifications jinaga.js accepts: every label joined to the others.
    unless isConnected s do continue
    for _ in [0:200] do
      let ((store, env, B), g) := (do
        let st ← genGraph s 8
        let env ← genEnv s st
        return (st, env, ← genBatch s st size) : Gen (Graph × Env × List Fact)).run gen
      gen := g
      -- The givens are stored facts; the named cases show a given arriving.
      let givens := s.given.map fun l => (l.name, (env l.name).getD 0)
      let linked := size == 1 || B.any fun f => B.any (·.predecessors.any (·.2 == f.id))
      if linked && !sameSet (s.read store env) (s.read (store ++ B) env) then
        out := out ++ [{ name := s!"{namePrefix}{out.length + 1}"
                         description := if size == 1
                           then "A random well-formed specification, graph and fresh fact that change the result."
                           else "A random well-formed specification, graph and fresh batch, some of whose facts name others, that change the result."
                         source := s!"lake exe vectors, seed {7 + size - 1}"
                         spec := s, givens := givens, graph := store, batch := B }]
        break
  return out

mutual
  /-- Some condition, at any depth, satisfies `p`. -/
  partial def anyConditionIn (p : Condition → Bool) : List Match → Bool
    | [] => false
    | .mk _ cs :: rest => cs.any (anyCondition p) || anyConditionIn p rest

  partial def anyCondition (p : Condition → Bool) (c : Condition) : Bool :=
    p c || match c with
      | .existential _ ms => anyConditionIn p ms
      | .path _ => false
end

/-- What the inverse vectors must show between them, each with the test that
a case shows it. `lake exe vectors` refuses to write a set in which no case
shows one, so a change to the generator cannot quietly drop a shape a port
must handle. -/
def inverseCoverage : List (String × (InverseCase → Bool)) := [
  ("an exists condition", fun c => anyConditionIn (fun | .existential true _ => true | _ => false) c.spec.matchList),
  ("a notExists condition", fun c => anyConditionIn (fun | .existential false _ => true | _ => false) c.spec.matchList),
  ("an existential condition with several matches",
    fun c => anyConditionIn (fun | .existential _ (_ :: _ :: _) => true | _ => false) c.spec.matchList),
  ("an existential condition inside another",
    fun c => anyConditionIn (fun | .existential _ ms => anyConditionIn (!·.isPath) ms | _ => false) c.spec.matchList),
  ("several givens", fun c => c.spec.given.length > 1),
  ("a composite projection", fun c => match c.spec.projection with | .composite _ => true | _ => false),
  ("a batch of several facts", fun c => c.batch.length > 1),
  ("a condition on a given", fun c => !c.conditioned.conditions.isEmpty),
  ("a batch that holds one of the subscription's givens",
    fun c => c.givens.any fun (_, id) => c.batch.any (·.id == id)),
  ("an inverse that cannot be reordered", fun c => (inverses c.spec).any fun i => (reorderChecked i).isNone)]

def main (args : List String) : IO Unit := do
  let root : System.FilePath := args.headD "vectors"
  let splitDir := root / "split"
  let wfDir := root / "well-formed"
  let inverseDir := root / "inverse"
  IO.FS.createDirAll splitDir
  IO.FS.createDirAll wfDir
  IO.FS.createDirAll inverseDir
  let inverseAll := inverseCases ++ randomInverseCases "random-" 1 12 ++ randomInverseCases "random-batch-" 3 6
  for (shape, shows) in inverseCoverage do
    unless inverseAll.any shows do
      throw <| IO.userError s!"no inverse vector shows {shape}"
  for c in inverseAll do
    -- The hypotheses of `read_reduceGivenConditions`, for the label the
    -- reduction picks.
    unless isWellFormed c.reduced do
      throw <| IO.userError s!"inverse case {c.name} is not well-formed"
    if c.conditioned.labels.contains (givenConditionsLabel c.conditioned) then
      throw <| IO.userError s!"inverse case {c.name}: the reduction's label is already used"
    if c.unchanged != sameSet (c.conditioned.read c.graph c.env) (c.conditioned.read (c.graph ++ c.batch) c.env) then
      throw <| IO.userError s!"inverse case {c.name} {if c.unchanged then "changes" else "does not change"} the result"
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
