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


/-! ## Cascade vectors -/

namespace CascadeVectors
open JinagaSpec.Cascade

/-- An array's items in a canonical order, so the file does not depend on the
order of the tree's list. -/
def sortJson (xs : List Lean.Json) : Lean.Json := Lean.Json.arr (xs.mergeSort fun a b => a.compress ≤ b.compress).toArray

/-- A model value as JSON. A map whose keys are all strings is an object. A map
keyed by node keys is an array of a copied row (`Tree.copy`): its children, as
the plain output gives them. -/
partial def valueJson : JinagaSpec.Cascade.Json → Lean.Json
  | .int n => Lean.Json.num n
  | .str s => Lean.Json.str s
  | .list vs => Lean.Json.arr (vs.map valueJson).toArray
  | .map es =>
    if es.all (fun e => match e.1 with | .str _ => true | _ => false) then
      Lean.Json.mkObj (es.map fun e => (match e.1 with | .str k => k | _ => "", valueJson e.2))
    else sortJson (es.map fun e => valueJson e.2)

def propsJson (ps : Props) : List (String × Lean.Json) := ps.entries.map fun (k, v) => (k, valueJson v)

/-- A node as the output shows it: its props, and each of its arrays. -/
def nodeJson (T : Tree) : Nat → Level → Key → Props → Lean.Json
  | 0, _, _, ps => Lean.Json.mkObj (propsJson ps)
  | n + 1, l, k, ps => Lean.Json.mkObj (propsJson ps ++ (T.arraysOf l k).map fun a =>
      (a, sortJson ((T.keysIn l k a).filterMap fun ck =>
        (T.get (l ++ [a], ck)).map fun c => nodeJson T n (l ++ [a]) ck c.props)))

/-- The output: the root rows, as `toPipelinePlainOutput` gives them. -/
def outputJson (T : Tree) : Lean.Json :=
  sortJson ((T.filter (·.1.1 = [])).map fun e => nodeJson T T.length [] e.1.2 e.2.props)

def typeOf : JinagaSpec.Cascade.Json → String
  | .int _ => "number"
  | .str _ => "string"
  | _ => "unknown"

def addsAt (ops : List Op) (l : Level) : List Props :=
  ops.filterMap fun | .add l' _ _ ps => if l' = l then some ps else none | _ => none

/-- A level's declared scalars and arrays, from every row the operations add:
the descriptor is complete. -/
partial def nodeDescriptor (ops : List Op) (l : Level) : Lean.Json :=
  let names : List (String × String) := dedup ((addsAt ops l).flatMap fun ps => ps.entries.map fun (k, v) => (k, typeOf v))
  let arrays : List String := dedup (ops.filterMap fun
    | .add l' _ _ _ => if l'.length = l.length + 1 ∧ l'.take l.length = l then l'.getLast? else none
    | _ => none)
  Lean.Json.mkObj [
    ("scalars", Lean.Json.arr (names.map fun (k, t) => Lean.Json.mkObj [("name", k), ("type", t)]).toArray),
    ("arrays", Lean.Json.arr (arrays.map fun a => Lean.Json.mkObj [("name", Lean.Json.str a), ("type", nodeDescriptor ops (l ++ [a]))]).toArray)]

/-- The operations on one input, the primary (`none`) or a source. -/
def opsOf (ops : List (Option Source × Op)) (src : Option Source) : List Op :=
  ops.filterMap fun (s, op) => if s = src then some op else none

def opJson (ops : List (Option Source × Op)) : Option Source × Op → Lean.Json
  | (src, op) =>
    let (name, l, keys, ps) : String × Level × List Nat × Props := match op with
      | .add l r rest ps => ("add", l, r :: rest, ps)
      -- The TypeScript's remove takes the row's props: those it was added with.
      | .remove l r rest => ("remove", l, r :: rest, ((opsOf ops src).findSome? fun
          | .add l' r' rest' ps => if l' = l ∧ r' = r ∧ rest' = rest then some ps else none
          | _ => none).getD CMap.empty)
    Lean.Json.mkObj ((src.toList.map fun q => ("source", Lean.Json.str q)) ++ [("op", Lean.Json.str name),
      ("path", Lean.Json.arr (l.map Lean.Json.str).toArray),
      ("keys", Lean.Json.arr (keys.map fun n => Lean.Json.str (toString n)).toArray),
      ("props", Lean.Json.mkObj (propsJson ps))])

def predJson : Pred → Lean.Json
  | .gt p n => Lean.Json.mkObj [("op", "gt"), ("property", p), ("value", Lean.Json.num n)]
  | .lt p n => Lean.Json.mkObj [("op", "lt"), ("property", p), ("value", Lean.Json.num n)]
  | .eq p v => Lean.Json.mkObj [("op", "eq"), ("property", p), ("value", valueJson v)]

def strs (l : List String) : Lean.Json := Lean.Json.arr (l.map Lean.Json.str).toArray

/-- A step as a builder call; `ops` give a secondary pipeline's source descriptor. -/
partial def stepJson (ops : List (Option Source × Op)) : PStep → Lean.Json
  | .groupBy G C => Lean.Json.mkObj [("step", "groupBy"), ("by", Lean.Json.arr (G.map Lean.Json.str).toArray), ("as", C)]
  | .sum a p q => Lean.Json.mkObj [("step", "sum"), ("array", a), ("property", p), ("as", q)]
  | .count a q => Lean.Json.mkObj [("step", "count"), ("array", a), ("as", q)]
  | .min a p q => Lean.Json.mkObj [("step", "min"), ("array", a), ("property", p), ("as", q)]
  | .max a p q => Lean.Json.mkObj [("step", "max"), ("array", a), ("property", p), ("as", q)]
  | .dropProperty p => Lean.Json.mkObj [("step", "dropProperty"), ("property", p)]
  | .flatten P C O => Lean.Json.mkObj [("step", "flatten"), ("parent", P), ("child", C), ("as", O)]
  | .filter P => Lean.Json.mkObj [("step", "filter"), ("predicate", predJson P)]
  | .cumulativeSum a O P => Lean.Json.mkObj [("step", "cumulativeSum"), ("array", a),
      ("orderBy", strs O), ("properties", strs P)]
  | .replaceToDelta e v O D => Lean.Json.mkObj [("step", "replaceToDelta"), ("entity", e), ("event", v),
      ("orderBy", strs O), ("properties", strs (D.map (·.1))), ("outputs", strs (D.map (·.2)))]
  | .pickByMin a p q => Lean.Json.mkObj [("step", "pickByMin"), ("array", a), ("property", p), ("as", q)]
  | .pickByMax a p q => Lean.Json.mkObj [("step", "pickByMax"), ("array", a), ("property", p), ("as", q)]
  | .enrich src r S K q w => Lean.Json.mkObj (([("step", "enrich"), ("source", Lean.Json.str src),
      ("pipeline", Lean.Json.mkObj [("root", r), ("source", nodeDescriptor (opsOf ops (some src)) []),
        ("steps", Lean.Json.arr (S.map (stepJson ops)).toArray)]),
      ("primaryKey", strs K), ("as", Lean.Json.str q)] : List (String × Lean.Json)) ++ w.toList.map fun ps => ("whenMissing", Lean.Json.mkObj (propsJson ps)))

/-- The level an ordered step sorts, the names it sorts by, and the names whose
values it adds or subtracts. -/
def ordered : PStep → Option (Level × List String × List String)
  | .cumulativeSum a O P => some ([a], O, P)
  | .replaceToDelta e v O D => some ([e, v], O, D.map (·.1))
  | _ => none

/-- The integers in a value. -/
partial def ints : JinagaSpec.Cascade.Json → List Int
  | .int n => [n]
  | .str _ => []
  | .list vs => vs.flatMap ints
  | .map es => es.flatMap fun (k, v) => ints k ++ ints v

/-- A value's type, as the ordered steps compare it: 0 a number, 1 a string. -/
def kind : Option JinagaSpec.Cascade.Json → Nat
  | some (.int _) => 0
  | some (.str _) => 1
  | _ => 2

/-- Refuse a pipeline's steps outside what the model and the TypeScript agree
on, given the stages of what its input holds after each prefix of the
operations, and each source's input after it. Each check holds in every input
the operations pass through: a descriptor declares every name a row ever
carried, and a value that passes through can leave its mark on an ordered
step's list. -/
partial def checkSteps (name : String) (steps : List PStep) (prefixes : List (List (String × Tree)))
    (sources : List (Source → Tree)) : IO Unit := do
  -- The TypeScript holds values as JavaScript numbers, exact only up to
  -- 2^53 - 1: every value a step reads or computes must be within it.
  let safe : Int := 2 ^ 53 - 1
  unless prefixes.all fun st => st.all fun (_, T) => T.all fun e =>
      e.2.props.entries.all fun (_, v) => (ints v).all fun i => -safe ≤ i ∧ i ≤ safe do
    throw <| IO.userError s!"cascade case {name}: an integer is outside JavaScript's safe range"
  for (s, j) in steps.zipIdx do
    let inputs := prefixes.filterMap fun st => st[j]?.map (·.2)
    -- The siblings an ordered step sorts must compare by their values alone:
    -- each order-by value present and of one type, and no two siblings tied.
    for (l, O, P) in (ordered s).toList do
      for T in inputs do
        let nodes := T.filter (·.1.1 = l)
        for p in O do
          let kinds := nodes.map fun e => kind (e.2.props p)
          unless kinds.all (· = kinds.headD 0) ∧ kinds.all (· < 2) do
            throw <| IO.userError s!"cascade case {name}: the values of {p} at {l} are not all numbers or all strings"
        for p in P do
          unless nodes.all fun e => (e.2.props p).all (· matches .int _) do
            throw <| IO.userError s!"cascade case {name}: a value of {p} at {l} is not a number"
        for x in nodes do
          for y in nodes do
            if x.1 ≠ y.1 ∧ x.2.parent = y.2.parent ∧ O.map x.2.props = O.map y.2.props then
              throw <| IO.userError s!"cascade case {name}: two siblings at {l} tie on {O}"
    match s with
    | .sum a p _ =>
      unless inputs.all fun T => (T.filter (·.1.1 = [a])).all fun e => e.2.props p matches some (.int _) do
        throw <| IO.userError s!"cascade case {name}: a child of {a} has no number {p} to sum"
    -- A pick compares the values it finds as numbers, converting a string
    -- with `Number()`: they must be numbers, and no two siblings tied.
    | .pickByMin a p _ | .pickByMax a p _ =>
      for T in inputs do
        let nodes := (T.filter (·.1.1 = [a])).filter fun e => (e.2.props p).isSome
        unless nodes.all fun e => e.2.props p matches some (.int _) do
          throw <| IO.userError s!"cascade case {name}: a value of {p} in {a} is not a number"
        for x in nodes do
          for y in nodes do
            if x.1 ≠ y.1 ∧ x.2.parent = y.2.parent ∧ x.2.props p = y.2.props p then
              throw <| IO.userError s!"cascade case {name}: two children in {a} tie on {p}"
    -- A flattened child's names, and its arrays' names, must avoid every
    -- name its parents ever carried.
    | .flatten P C _ =>
      let parents := inputs.flatMap fun T => T.namesAt [P]
      let children := inputs.flatMap fun T =>
        (T.filter (·.1.1 = [P, C])).flatMap (·.2.props.keys) ++
          (T.filterMap fun e => if e.1.1.length = 3 ∧ e.1.1.take 2 = [P, C] then e.1.1.getLast? else none)
      unless children.all (· ∉ parents) do
        throw <| IO.userError s!"cascade case {name}: a child of {P} shares a name with its parent"
    -- The secondary pipeline is checked as the primary is. A primary row with
    -- more than one match gets `whenMissing` in the model and the last match
    -- in the TypeScript: the secondary's rows must differ in their collection
    -- key. Source `""` is the model's primary.
    | .enrich src r S _ _ _ =>
      if src = "" then throw <| IO.userError s!"cascade case {name}: a source has an empty name"
      -- An operation names one source: a source's own sources, which
      -- cascade-core nests below it, are not modelled.
      if S.any (· matches .enrich ..) then
        throw <| IO.userError s!"cascade case {name}: the secondary pipeline of {src} enriches in turn"
      let stages := sources.map fun I => PStep.stages r I S (I src)
      checkSteps name S stages sources
      let CK := collectionKey S
      for st in stages do
        let rows := ((st.getLast?.map (·.2)).getD []).filter (·.1.1 = [])
        for x in rows do
          for y in rows do
            if x.1 ≠ y.1 ∧ CK.map x.2.props = CK.map y.2.props then
              throw <| IO.userError s!"cascade case {name}: two rows of {src} share their collection key {CK}"
    | _ => pure ()

/-- Refuse a case outside what the model and the TypeScript agree on, or whose
orders disagree. -/
def check (c : JinagaSpec.Cascade.Case) : IO Unit := do
  let n := c.ops.length
  for o in c.orders do
    unless o.length = n ∧ o.Nodup ∧ o.all (· < n) do
      throw <| IO.userError s!"cascade case {c.name}: an order is not a permutation of its operations"
  let outs := c.orders.map fun o => (outputJson (c.denote o)).compress
  unless outs.all (· = outs.headD "") do
    throw <| IO.userError s!"cascade case {c.name}: its orders give different outputs"
  for o in c.orders do
    let takes := (List.range (o.length + 1)).map o.take
    checkSteps c.name c.steps (takes.map c.stages) (takes.map c.sources)

def vector (c : JinagaSpec.Cascade.Case) : Lean.Json :=
  Lean.Json.mkObj [
    ("name", c.name),
    ("description", c.description),
    ("pipeline", Lean.Json.mkObj [
      ("root", c.root),
      ("source", nodeDescriptor (opsOf c.ops none) []),
      ("steps", Lean.Json.arr (c.steps.map (stepJson c.ops)).toArray)]),
    ("ops", Lean.Json.arr (c.ops.map (opJson c.ops)).toArray),
    ("orders", Lean.Json.arr (c.orders.map fun o => Lean.Json.arr (o.map fun (i : Nat) => Lean.Json.num i).toArray).toArray),
    ("expected", outputJson (c.denote (c.orders.headD [])))]

end CascadeVectors

def main (args : List String) : IO Unit := do
  let root : System.FilePath := args.headD "vectors"
  let splitDir := root / "split"
  let wfDir := root / "well-formed"
  let inverseDir := root / "inverse"
  let cascadeDir := root / "cascade"
  IO.FS.createDirAll splitDir
  IO.FS.createDirAll wfDir
  IO.FS.createDirAll inverseDir
  IO.FS.createDirAll cascadeDir
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
  for c in JinagaSpec.Cascade.cases do
    CascadeVectors.check c
    IO.FS.writeFile (cascadeDir / s!"{c.name}.json") ((CascadeVectors.vector c).pretty ++ "\n")
  IO.println s!"wrote {cases.length} split vectors to {splitDir}, {wellFormedCases.length} well-formedness vectors to {wfDir}, and {inverseAll.length} inverse vectors to {inverseDir}"
