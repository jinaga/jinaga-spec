import JinagaSpec.Reorder

/-!
# Exact inverses: adds and removes from one read each

`candidates` (`Reorder.lean`) is complete but not exact: a stream re-reads the
specification for each candidate (`recheck`). This strengthens each inverse
with a test against the new graph, so every row an inverse returns is a change
in its direction, and a replicator can push it without a second read.

* **An add inverse re-attaches every original top-level condition.** Every
  solution it finds is then a solution of the specification on the new
  graph, so its row is in the new result.
* **A remove inverse flips one top-level existential condition.** There is one
  for each lost-direction inverse and each existential condition `d` on a
  top-level match: the inverse, with `d` flipped attached to its match. Every
  solution it finds fails `d` on the new graph, so it is not a solution of the
  specification there. A row is absent from the new result when every
  solution that would project to it is gone, which this per-solution test
  shows only when the projection names every top-level unknown
  (`projectsUnknowns`): then a row determines its solution.

Neither test says anything about the old graph. It need not: adding a row the
set already holds, or removing one it lacks, changes nothing, so a test that
is sound on the new graph and complete (`Proofs/Exact.lean`) is exact. A row
cannot be both added and removed, so the order of the two does not matter.

Only the top level is tested. The levels below may stay relaxed: whatever
they find, the top-level test decides the row.

Written in the portable subset: inductive types, total functions, structural
recursion and lists.
-/
namespace JinagaSpec

/-- Two lists of matches over the same unknowns, as one: match by match, the
unknown, and the conditions of both. -/
def conj (ms1 ms2 : List Match) : List Match :=
  List.zipWith (fun m1 m2 => .mk m1.unknown (m1.conditions ++ m2.conditions)) ms1 ms2

/-- The existential condition that asks the opposite. A path condition has no
opposite here, and is left as it is (never used). -/
def Condition.flip : Condition → Condition
  | .existential e ms => .existential (!e) ms
  | c => c

/-- The inverses for gained results, each with every original top-level
condition re-attached. -/
def addInverses (s : Specification) : List Specification :=
  (inversesFor true s).map fun ι => { ι with matchList := conj ι.matchList s.matchList }

/-- For each top-level match and each existential condition `d` on it: the
same unknowns, with no conditions but `d` flipped, on that match. -/
def removeTests : List Match → List (List Match)
  | [] => []
  | .mk u cs :: rest =>
    (cs.filter (!·.isPath)).map (fun d => .mk u [d.flip] :: rest.map fun m => .mk m.unknown []) ++
    (removeTests rest).map (.mk u [] :: ·)

/-- The inverses for lost results, each strengthened by one remove test. None
when the specification has no top-level existential condition: a result can
be lost only when one of them flips. -/
def removeInverses (s : Specification) : List Specification :=
  (inversesFor false s).flatMap fun ι =>
    (removeTests s.matchList).map fun t => { ι with matchList := conj ι.matchList t }

/-- The projection names every top-level unknown, so a row determines its
solution. The remove inverses are exact under this. -/
def projectsUnknowns (s : Specification) : Bool :=
  s.matchList.all fun m => s.projection.labels.contains m.unknown.name

/-- The rows `f` adds and removes, read on `new`, the graph that holds it.

* If `f` is one of the subscription's givens, nothing was read before, so
  every row read now is added and none is removed (as `factCandidates`).
* If some given is not stored, `read` returns nothing, and there is no change.
  (`evaluate` binds a given whether or not its fact is stored, so the inverses
  alone could report a row that `read` lacks.)
* Otherwise, each exact inverse, reordered to start at `f`. -/
def factChanges (s : Specification) (env : Env) (new : Graph) (f : Fact) : List Row × List Row :=
  if s.given.any (env ·.name == some f.id) then
    (s.read new env, [])
  else if s.given.all (new.has env) then
    (((addInverses s).map reorderOrSelf).flatMap (·.evaluate new (pinEnv s env f)),
     ((removeInverses s).map reorderOrSelf).flatMap (·.evaluate new (pinEnv s env f)))
  else
    ([], [])

/-- The rows a batch `B` adds and removes: each fact's, every one read on
`g ++ B`. -/
def changes (s : Specification) (env : Env) (g : Graph) (B : List Fact) : List Row × List Row :=
  (B.flatMap fun f => (factChanges s env (g ++ B) f).1,
   B.flatMap fun f => (factChanges s env (g ++ B) f).2)

/-- Drop the removed rows, and add the added ones. -/
def applyChanges (adds removes held : List Row) : List Row :=
  held.filter (!removes.contains ·) ++ adds

/-- One batch: extend the graph, and apply the batch's changes, with no
second read. -/
def exactStep (s : Specification) (env : Env) : Graph × List Row → List Fact → Graph × List Row :=
  advance fun g B => applyChanges (changes s env g B).1 (changes s env g B).2

end JinagaSpec
