import JinagaSpec.Cascade.Input
import JinagaSpec.Cascade.Flatten

/-!
# Cascade: conformance cases

A case is a pipeline, written in a form an implementation can build (`PStep`),
the operations a caller performs, and several orders to perform them in. The
model's output is the pipeline's denotation of what the input holds after the
operations (`Case.output`); `run_correct` and `ops_correct` say the steps' events
reach it. `lake exe vectors` writes one vector per case (`vectors/cascade/`).

Every step here is at the root scope, as the model's steps are. Where the model
and the TypeScript are known to differ, a case stays inside what they agree on,
and the generator checks it (`Case.check`): summed children define the summed
property, and a flattened child carries no name of its parent's.
-/
namespace JinagaSpec.Cascade

/-- A comparison a `filter` makes of a root row's property with a constant. -/
inductive Pred where
  | gt (p : String) (n : Int)
  | lt (p : String) (n : Int)
  | eq (p : String) (v : Val)

def Pred.eval : Pred → Props → Bool
  | .gt p n, ps => match ps p with | some (.int m) => decide (m > n) | _ => false
  | .lt p n, ps => match ps p with | some (.int m) => decide (m < n) | _ => false
  | .eq p v, ps => ps p == some v

/-- A pipeline step, as the builder method that adds it. `groupBy(G, name)`
names the new collection of groups, the new root scope; the rows go below each
group in an array named for the scope they came from. -/
inductive PStep where
  | groupBy (by_ : List String) (as : String)
  | sum (array p as : String)
  | count (array as : String)
  | min (array p as : String)
  | max (array p as : String)
  | dropProperty (p : String)
  | flatten (parent child as : String)
  | filter (pred : Pred)

/-- The names the nodes at level `l` carry. -/
def Tree.namesAt (T : Tree) (l : Level) : List String :=
  dedup ((T.filter (·.1.1 = l)).flatMap (·.2.props.keys))

/-- A step's denotation, from the root scope's name. A flattened row inherits
every name its parents carry, which is the parents' descriptor when it is
complete. -/
def PStep.denote (root : String) : PStep → Tree → Tree
  | .groupBy G _ => groupBy.F G root
  | .sum a p q => aggregate.F [a] q (fun _ => true) (sumBy fun ps => ((ps p).map Val.num).getD 0)
  | .count a q => aggregate.F [a] q (fun _ => true) (sumBy fun _ => 1)
  | .min a p q => aggregate.F [a] q (fun _ => true) (minOf p)
  | .max a p q => aggregate.F [a] q (fun _ => true) (maxOf p)
  | .dropProperty p => dropProperty.F [] p
  | .flatten P C O => fun T => flatten.F P C O (T.namesAt [P]) T
  | .filter P => filter.F P.eval

/-- A conformance case. -/
structure Case where
  name : String
  description : String
  /-- The pipeline's root scope name (`createPipeline`'s first argument). -/
  root : String
  steps : List PStep
  ops : List Op
  /-- Orders to perform `ops` in, as lists of indices into it. -/
  orders : List (List Nat)

/-- What the input holds after the operations, in an order. -/
def Case.input (c : Case) (order : List Nat) : Tree :=
  (order.filterMap (c.ops[·]?)).foldl Tree.receive []

/-- The root scope's name after a step. -/
def PStep.root (root : String) : PStep → String
  | .groupBy _ r => r
  | _ => root

/-- The input to each step and the output, each with the root scope's name. -/
def Case.stages (c : Case) (T : Tree) : List (String × Tree) :=
  c.steps.scanl (fun (r, T) s => (s.root r, s.denote r T)) (c.root, T)

/-- The pipeline's output for what the input holds. -/
def Case.denote (c : Case) (T : Tree) : Tree :=
  ((c.stages T).getLast?.map (·.2)).getD T

/-! ## The cases -/

/-- Props from a list of names and values. -/
def mkProps (l : List (String × Val)) : Props := l.foldl (fun m (k, v) => m.set k (some v)) CMap.empty

def addRow (r : Nat) (l : List (String × Val)) : Op := .add [] r [] (mkProps l)
def addChild (a : String) (r k : Nat) (l : List (String × Val)) : Op := .add [a] r [k] (mkProps l)
def addGrandchild (a b : String) (r k j : Nat) (l : List (String × Val)) : Op := .add [a, b] r [k, j] (mkProps l)

def cases : List Case := [
  { name := "group-sum-count"
    description := "Rows grouped by a value, with each group's total and count; one row leaves."
    root := "rows"
    steps := [.groupBy ["cat"] "groups", .sum "rows" "v" "total", .count "rows" "n"]
    ops := [addRow 1 [("cat", .str "a"), ("v", 5)], addRow 2 [("cat", .str "a"), ("v", 3)],
      addRow 3 [("cat", .str "b"), ("v", 7)], .remove [] 1 [], addRow 4 [("cat", .str "b"), ("v", 1)]]
    orders := [[0, 1, 2, 3, 4], [2, 4, 0, 1, 3], [4, 0, 3, 2, 1]] },
  { name := "group-min-max"
    description := "Each group's least and greatest value, after its least row leaves."
    root := "rows"
    steps := [.groupBy ["cat"] "groups", .min "rows" "v" "lo", .max "rows" "v" "hi"]
    ops := [addRow 1 [("cat", .str "a"), ("v", 5)], addRow 2 [("cat", .str "a"), ("v", 3)],
      addRow 3 [("cat", .str "a"), ("v", 9)], .remove [] 2 [], addRow 4 [("cat", .str "b"), ("v", 2)]]
    orders := [[0, 1, 2, 3, 4], [1, 3, 4, 2, 0], [4, 2, 1, 0, 3]] },
  { name := "source-array-aggregates"
    description := "A count and a total over a declared source array, fed through collection()."
    root := "folders"
    steps := [.count "bookmarks" "n", .sum "bookmarks" "size" "total"]
    ops := [addRow 1 [("name", .str "home")], addRow 2 [("name", .str "work")],
      addChild "bookmarks" 1 1 [("size", 10)], addChild "bookmarks" 1 2 [("size", 32)],
      addChild "bookmarks" 2 1 [("size", 5)], .remove ["bookmarks"] 1 [2]]
    orders := [[0, 1, 2, 3, 4, 5], [1, 4, 0, 3, 5, 2], [0, 3, 2, 1, 5, 4]] },
  { name := "orphan-is-refused"
    description := "A child that arrives before its parent is refused, and stays out after the parent arrives (jinaga/jinaga-cascade-core#31)."
    root := "folders"
    steps := [.count "bookmarks" "n"]
    ops := [addChild "bookmarks" 1 1 [("size", 10)], addRow 1 [("name", .str "home")],
      addChild "bookmarks" 1 2 [("size", 4)]]
    orders := [[0, 1, 2]] },
  { name := "remove-row-removes-children"
    description := "Removing a row removes the children fed under it."
    root := "folders"
    steps := [.count "bookmarks" "n"]
    ops := [addRow 1 [("name", .str "home")], addChild "bookmarks" 1 1 [("size", 10)],
      addChild "bookmarks" 1 2 [("size", 4)], addRow 2 [("name", .str "work")], .remove [] 1 []]
    orders := [[0, 1, 2, 3, 4], [3, 0, 2, 1, 4]] },
  { name := "filter-by-value"
    description := "Root rows whose value is greater than a constant."
    root := "rows"
    steps := [.filter (.gt "v" 4)]
    ops := [addRow 1 [("v", 5)], addRow 2 [("v", 3)], addRow 3 [("v", 9)], .remove [] 3 []]
    orders := [[0, 1, 2, 3], [2, 3, 1, 0]] },
  { name := "drop-property"
    description := "A property dropped from every root row."
    root := "rows"
    steps := [.dropProperty "secret"]
    ops := [addRow 1 [("v", 5), ("secret", .str "x")], addRow 2 [("v", 3), ("secret", .str "y")]]
    orders := [[0, 1], [1, 0]] },
  { name := "flatten-projects-tasks"
    description := "Each team's projects and their tasks, flattened into one array of tasks that carry their project's values."
    root := "teams"
    steps := [.flatten "projects" "tasks" "work"]
    ops := [addRow 1 [("team", .str "core")],
      addChild "projects" 1 1 [("title", .str "spec")], addChild "projects" 1 2 [("title", .str "port")],
      addGrandchild "projects" "tasks" 1 1 1 [("hours", 3)], addGrandchild "projects" "tasks" 1 1 2 [("hours", 5)],
      addGrandchild "projects" "tasks" 1 2 1 [("hours", 2)], .remove ["projects", "tasks"] 1 [1, 2]]
    orders := [[0, 1, 2, 3, 4, 5, 6], [0, 2, 5, 1, 4, 3, 6], [0, 1, 4, 6, 2, 3, 5]] },
  { name := "regroup-by-total"
    description := "Folders grouped by their total, which a new bookmark changes: the folder moves to another group (jinaga/jinaga-cascade-core#29)."
    root := "folders"
    steps := [.sum "bookmarks" "size" "total", .groupBy ["total"] "totals"]
    ops := [addRow 1 [("name", .str "home")], addRow 2 [("name", .str "work")],
      addChild "bookmarks" 1 1 [("size", 10)], addChild "bookmarks" 2 1 [("size", 4)],
      addChild "bookmarks" 2 2 [("size", 6)]]
    orders := [[0, 1, 2, 3, 4], [1, 4, 3, 0, 2], [0, 2, 1, 3, 4]] }]

end JinagaSpec.Cascade
