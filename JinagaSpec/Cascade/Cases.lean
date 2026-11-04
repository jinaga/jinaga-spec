import JinagaSpec.Cascade.Input
import JinagaSpec.Cascade.Flatten
import JinagaSpec.Cascade.Ordered

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
property, a flattened child carries no name of its parent's, and the siblings an
ordered step sorts have order-by values of one type with no ties, and the
children a pick compares have numbers with no ties.
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

/-! ## The order of ordered steps -/

/-- An order-by value's place in the order: numbers by value, strings by their
characters, as the TypeScript compares two numbers or two strings. The generator
keeps each compared property to one of the two (`check`). -/
def orderValue : Option Val → List Int
  | some (.int n) => [n]
  | some (.str s) => s.toList.map fun c => (c.toNat : Int)
  | _ => []

/-- A node's place in an order by the names `O`: its values, then its key. -/
def sortKey (O : List String) (y : Key × Props) : List (List Int) :=
  O.map (fun p => orderValue (y.2 p)) ++ [Encode.enc y.1]

/-- The order of the ordered steps: by the values of `O` in turn, then by key. -/
def byOrder (O : List String) (a b : Key × Props) : Bool := decide (sortKey O a < sortKey O b)

theorem byOrder_strictTotal (O : List String) : StrictTotal (byOrder O) where
  irrefl a := by simp [byOrder, List.lt_irrefl]
  trans _ _ _ h h' := by simp only [byOrder, decide_eq_true_eq] at *; exact List.lt_trans h h'
  total a b h := by
    simp only [byOrder, decide_eq_true_eq]
    have hne : sortKey O a ≠ sortKey O b := fun e =>
      h (Encode.enc_inj (List.cons.inj (List.append_inj' e rfl).2).1)
    rcases List.le_total (sortKey O a) (sortKey O b) with h' | h' <;>
      rcases List.le_iff_lt_or_eq.mp h' with h' | h'
    · exact Or.inl h'
    · exact absurd h' hne
    · exact Or.inr h'
    · exact absurd h'.symm hne

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
  | cumulativeSum (array : String) (orderBy props : List String)
  | replaceToDelta (entity event : String) (orderBy : List String) (deltas : Deltas)
  | pickByMin (array p as : String)
  | pickByMax (array p as : String)

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
  | .cumulativeSum a O P => cumulativeSum.F [a] (byOrder O) P
  | .replaceToDelta e v O D => replaceToDelta.F [e, v] (byOrder O) D
  | .pickByMin a p q => pickBy.F [a] (fun x y => byOrder [p] y x) (fun ps => (ps p).isSome) q
  | .pickByMax a p q => pickBy.F [a] (byOrder [p]) (fun ps => (ps p).isSome) q

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
    orders := [[0, 1, 2, 3, 4], [1, 4, 3, 0, 2], [0, 2, 1, 3, 4]] },
  { name := "cumulative-sum-by-name"
    description := "Each folder's total, then a running total of the folders in each category by name; a folder loses its only bookmark."
    root := "folders"
    steps := [.sum "bookmarks" "size" "total", .groupBy ["cat"] "groups", .cumulativeSum "folders" ["name"] ["total"]]
    ops := [addRow 1 [("cat", .str "a"), ("name", .str "b")], addRow 2 [("cat", .str "a"), ("name", .str "a")],
      addRow 3 [("cat", .str "a"), ("name", .str "c")], addRow 4 [("cat", .str "b"), ("name", .str "a")],
      addChild "bookmarks" 1 1 [("size", 10)], addChild "bookmarks" 2 1 [("size", 4)],
      addChild "bookmarks" 3 1 [("size", 1)], addChild "bookmarks" 4 1 [("size", 7)],
      addChild "bookmarks" 2 2 [("size", 3)], .remove ["bookmarks"] 1 [1]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [3, 2, 7, 1, 0, 6, 5, 8, 4, 9], [1, 5, 8, 0, 4, 9, 2, 6, 3, 7]] },
  { name := "replace-to-delta-readings"
    description := "Each meter's readings, in time order, as the change since the reading before; a middle reading leaves."
    root := "sites"
    steps := [.replaceToDelta "meters" "readings" ["at"] [("value", "delta")]]
    ops := [addRow 1 [("name", .str "north")],
      addChild "meters" 1 1 [("label", .str "m1")], addChild "meters" 1 2 [("label", .str "m2")],
      addGrandchild "meters" "readings" 1 1 1 [("at", 10), ("value", 100)],
      addGrandchild "meters" "readings" 1 1 2 [("at", 20), ("value", 130)],
      addGrandchild "meters" "readings" 1 1 3 [("at", 30), ("value", 175)],
      addGrandchild "meters" "readings" 1 2 1 [("at", 15), ("value", 50)],
      addGrandchild "meters" "readings" 1 2 2 [("at", 5), ("value", 20)],
      .remove ["meters", "readings"] 1 [1, 2]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 2, 6, 1, 5, 7, 3, 4, 8], [0, 1, 2, 4, 3, 8, 5, 7, 6]] },
  { name := "pick-cheapest-priciest"
    description := "Each category's cheapest and priciest item, after its cheapest leaves; an item with no price is never picked."
    root := "categories"
    steps := [.pickByMin "items" "price" "cheapest", .pickByMax "items" "price" "priciest"]
    ops := [addRow 1 [("name", .str "tools")], addRow 2 [("name", .str "toys")],
      addChild "items" 1 1 [("name", .str "saw"), ("price", 5)], addChild "items" 1 2 [("name", .str "awl"), ("price", 3)],
      addChild "items" 1 3 [("name", .str "rag")], addChild "items" 1 4 [("name", .str "vise"), ("price", 9)],
      addChild "items" 2 1 [("name", .str "ball")], .remove ["items"] 1 [2]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7], [1, 6, 0, 5, 3, 4, 7, 2], [0, 3, 7, 4, 1, 2, 6, 5]] },
  { name := "pick-largest-total"
    description := "Folders grouped by category, each group picking its folder with the largest total, which changes as bookmarks arrive and leave."
    root := "folders"
    steps := [.sum "bookmarks" "size" "total", .groupBy ["cat"] "groups", .pickByMax "folders" "total" "largest"]
    ops := [addRow 1 [("cat", .str "a"), ("name", .str "home")], addRow 2 [("cat", .str "a"), ("name", .str "work")],
      addRow 3 [("cat", .str "a"), ("name", .str "misc")], addRow 4 [("cat", .str "b"), ("name", .str "play")],
      addChild "bookmarks" 1 1 [("size", 10)], addChild "bookmarks" 2 1 [("size", 4)],
      addChild "bookmarks" 2 2 [("size", 3)], addChild "bookmarks" 2 3 [("size", 5)],
      addChild "bookmarks" 3 1 [("size", 1)], addChild "bookmarks" 4 1 [("size", 2)], .remove ["bookmarks"] 3 [1]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [3, 9, 1, 7, 2, 8, 10, 0, 4, 5, 6], [2, 8, 0, 4, 10, 1, 6, 5, 3, 7, 9]] }]

end JinagaSpec.Cascade
