import JinagaSpec.Cascade.Input
import JinagaSpec.Cascade.Flatten
import JinagaSpec.Cascade.Ordered
import JinagaSpec.Cascade.Enrich
import JinagaSpec.Cascade.Within

/-!
# Cascade: conformance cases

A case is a pipeline, written in a form an implementation can build (`PStep`),
the operations a caller performs, and several orders to perform them in. The
model's output is the pipeline's denotation of what the input holds after the
operations (`Case.output`); `run_correct` and `ops_correct` say the steps' events
reach it. `lake exe vectors` writes one vector per case (`vectors/cascade/`).

Every step here is at the root scope, as the model's steps are. An operation
is on the primary input or on a named source, which an `enrich` step reads
through its own pipeline. Where the model
and the TypeScript are known to differ, a case stays inside what they agree on,
and the generator checks it (`Case.check`): summed children define the summed
property, a flattened child carries no name of its parent's, and the siblings an
ordered step sorts have order-by values of one type with no ties, the
children a pick compares have numbers with no ties, an enriching source's
rows differ in their collection key, and a defined property's expression reads
no changing property its dependencies leave out.
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

/-- The property a predicate reads. -/
def Pred.prop : Pred → String
  | .gt p _ | .lt p _ | .eq p _ => p

/-- An expression a `defineProperty` computes from a root row's props. -/
inductive Expr where
  | prop (p : String)
  | lit (v : Val)
  /-- The sum of two numbers, and no value unless both are numbers. -/
  | add (a b : Expr)
  | cond (pred : Pred) (a b : Expr)

def Expr.eval (ps : Props) : Expr → Option Val
  | .prop p => ps p
  | .lit v => some v
  | .add a b => match a.eval ps, b.eval ps with
    | some (.int m), some (.int n) => some (.int (m + n))
    | _, _ => none
  | .cond P a b => if P.eval ps then a.eval ps else b.eval ps

/-- The properties an expression reads. -/
def Expr.reads : Expr → List String
  | .prop p => [p]
  | .lit _ => []
  | .add a b => a.reads ++ b.reads
  | .cond P a b => P.prop :: (a.reads ++ b.reads)

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
  /-- `.in(...scope).groupBy(by, as)`. -/
  | groupBy (by_ : List String) (as : String) (scope : List String := [])
  | sum (array p as : String)
  | count (array as : String)
  | min (array p as : String)
  | max (array p as : String)
  | dropProperty (p : String)
  /-- `.in(...scope).flatten(parent, child, as)`. -/
  | flatten (parent child as : String) (scope : List String := [])
  /-- `.in(...scope).filter(pred, [pred's property])`. -/
  | filter (pred : Pred) (scope : List String := [])
  /-- `defineProperty(as, row => e, deps)`. -/
  | defineProperty (as : String) (e : Expr) (deps : List String)
  | cumulativeSum (array : String) (orderBy props : List String)
  | replaceToDelta (entity event : String) (orderBy : List String) (deltas : Deltas)
  | pickByMin (array p as : String)
  | pickByMax (array p as : String)
  /-- `enrich(source, secondary, key, as, whenMissing)`, the secondary pipeline
  given by its root scope name and steps. -/
  | enrich (source : Source) (root : String) (steps : List PStep) (key : List String) (as : String)
      (whenMissing : Option Props)

/-- The names the nodes at level `l` carry. -/
def Tree.namesAt (T : Tree) (l : Level) : List String :=
  dedup ((T.filter (·.1.1 = l)).flatMap (·.2.props.keys))

/-- The root scope's name after a step: a `groupBy` at the root renames it. -/
def PStep.root (root : String) : PStep → String
  | .groupBy _ r [] => r
  | _ => root

/-- `F` below scope `sc`, as `.in(...sc)` runs it: within each array of the
scope in turn, the innermost output in array `o`. `F` takes the root scope's
name, which below a scope is the scope's last array. -/
def scopedF (F : String → Tree → Tree) (o root : String) : List String → Tree → Tree
  | [] => F root
  | [a] => within.F a o (F a)
  | a :: b :: rest => within.F a a (scopedF F o a (b :: rest))

/-- A pipeline's root collection key: the names of its last root `groupBy`, or
none once a step drops one of them, as cascade-core clears it. -/
def collectionKey (S : List PStep) : List String :=
  S.foldl (fun ck s => match s with
    | .groupBy G _ [] => G
    | .dropProperty p => if p ∈ ck then [] else ck
    | _ => ck) []

mutual
/-- A step's denotation, from the root scope's name and each source's input `I`.
A flattened row inherits every name its parents carry, which is the parents'
descriptor when it is complete. `enrich` joins the primary tree, as source `""`,
with its secondary pipeline's output. -/
def PStep.denote (root : String) (I : Source → Tree) : PStep → Tree → Tree
  | .groupBy G C sc => scopedF (groupBy.F G) C root sc
  | .sum a p q => aggregate.F [a] q (fun _ => true) (sumBy fun ps => ((ps p).map Val.num).getD 0)
  | .count a q => aggregate.F [a] q (fun _ => true) (sumBy fun _ => 1)
  | .min a p q => aggregate.F [a] q (fun _ => true) (minOf p)
  | .max a p q => aggregate.F [a] q (fun _ => true) (maxOf p)
  | .dropProperty p => dropProperty.F [] p
  | .flatten P C O sc => scopedF (fun _ T => flatten.F P C O (T.namesAt [P]) T) (sc.getLast?.getD root) root sc
  | .filter P sc => scopedF (fun _ => filter.F P.eval) (sc.getLast?.getD root) root sc
  | .defineProperty q e _ => defineProperty.F [] q (Expr.eval · e)
  | .cumulativeSum a O P => cumulativeSum.F [a] (byOrder O) P
  | .replaceToDelta e v O D => replaceToDelta.F [e, v] (byOrder O) D
  | .pickByMin a p q => pickBy.F [a] (fun x y => byOrder [p] y x) (fun ps => (ps p).isSome) q
  | .pickByMax a p q => pickBy.F [a] (byOrder [p]) (fun ps => (ps p).isSome) q
  | .enrich src r S K q w => fun T =>
    enrich.F "" src [] q K (collectionKey S) (w.map Props.toJson)
      fun s => if s = src then PStep.run r I S (I src) else T

/-- A pipeline's denotation: its steps in turn. -/
def PStep.run (root : String) (I : Source → Tree) : List PStep → Tree → Tree
  | [], T => T
  | s :: S, T => PStep.run (s.root root) I S (s.denote root I T)
end

/-- A conformance case. -/
structure Case where
  name : String
  description : String
  /-- The pipeline's root scope name (`createPipeline`'s first argument). -/
  root : String
  steps : List PStep
  /-- The operations, each on the primary input (`none`) or on a source. -/
  ops : List (Option Source × Op)
  /-- Orders to perform `ops` in, as lists of indices into it. -/
  orders : List (List Nat)

/-- What an input, the primary or a source, holds after the operations, in an order. -/
def Case.input (c : Case) (src : Option Source) (order : List Nat) : Tree :=
  ((order.filterMap (c.ops[·]?)).filterMap fun (s, op) => if s = src then some op else none).foldl
    Tree.receive []

/-- The input to each of a pipeline's steps and its output, each with the root
scope's name. -/
def PStep.stages (root : String) (I : Source → Tree) (S : List PStep) (T : Tree) : List (String × Tree) :=
  S.scanl (fun (r, T) s => (s.root r, s.denote r I T)) (root, T)

/-- Each source's input after the operations, in an order. -/
def Case.sources (c : Case) (order : List Nat) : Source → Tree := fun q => c.input (some q) order

/-- The input to each step and the output, each with the root scope's name. -/
def Case.stages (c : Case) (order : List Nat) : List (String × Tree) :=
  PStep.stages c.root (c.sources order) c.steps (c.input none order)

/-- The pipeline's output after the operations, in an order. -/
def Case.denote (c : Case) (order : List Nat) : Tree :=
  ((c.stages order).getLast?.map (·.2)).getD []

/-! ## The cases -/

/-- Props from a list of names and values. -/
def mkProps (l : List (String × Val)) : Props := l.foldl (fun m (k, v) => m.set k (some v)) CMap.empty

def addRow (r : Nat) (l : List (String × Val)) : Op := .add [] r [] (mkProps l)
def addChild (a : String) (r k : Nat) (l : List (String × Val)) : Op := .add [a] r [k] (mkProps l)
def addGrandchild (a b : String) (r k j : Nat) (l : List (String × Val)) : Op := .add [a, b] r [k, j] (mkProps l)

/-- Operations on the primary input. -/
def primary (l : List Op) : List (Option Source × Op) := l.map (none, ·)

/-- An operation on source `q`. -/
def on (q : Source) (op : Op) : Option Source × Op := (some q, op)

def cases : List Case := [
  { name := "group-sum-count"
    description := "Rows grouped by a value, with each group's total and count; one row leaves."
    root := "rows"
    steps := [.groupBy ["cat"] "groups", .sum "rows" "v" "total", .count "rows" "n"]
    ops := primary [addRow 1 [("cat", .str "a"), ("v", 5)], addRow 2 [("cat", .str "a"), ("v", 3)],
      addRow 3 [("cat", .str "b"), ("v", 7)], .remove [] 1 [], addRow 4 [("cat", .str "b"), ("v", 1)]]
    orders := [[0, 1, 2, 3, 4], [2, 4, 0, 1, 3], [4, 0, 3, 2, 1]] },
  { name := "group-min-max"
    description := "Each group's least and greatest value, after its least row leaves."
    root := "rows"
    steps := [.groupBy ["cat"] "groups", .min "rows" "v" "lo", .max "rows" "v" "hi"]
    ops := primary [addRow 1 [("cat", .str "a"), ("v", 5)], addRow 2 [("cat", .str "a"), ("v", 3)],
      addRow 3 [("cat", .str "a"), ("v", 9)], .remove [] 2 [], addRow 4 [("cat", .str "b"), ("v", 2)]]
    orders := [[0, 1, 2, 3, 4], [1, 3, 4, 2, 0], [4, 2, 1, 0, 3]] },
  { name := "source-array-aggregates"
    description := "A count and a total over a declared source array, fed through collection()."
    root := "folders"
    steps := [.count "bookmarks" "n", .sum "bookmarks" "size" "total"]
    ops := primary [addRow 1 [("name", .str "home")], addRow 2 [("name", .str "work")],
      addChild "bookmarks" 1 1 [("size", 10)], addChild "bookmarks" 1 2 [("size", 32)],
      addChild "bookmarks" 2 1 [("size", 5)], .remove ["bookmarks"] 1 [2]]
    orders := [[0, 1, 2, 3, 4, 5], [1, 4, 0, 3, 5, 2], [0, 3, 2, 1, 5, 4]] },
  { name := "orphan-is-refused"
    description := "A child that arrives before its parent is refused, and stays out after the parent arrives (jinaga/jinaga-cascade-core#31)."
    root := "folders"
    steps := [.count "bookmarks" "n"]
    ops := primary [addChild "bookmarks" 1 1 [("size", 10)], addRow 1 [("name", .str "home")],
      addChild "bookmarks" 1 2 [("size", 4)]]
    orders := [[0, 1, 2]] },
  { name := "remove-row-removes-children"
    description := "Removing a row removes the children fed under it."
    root := "folders"
    steps := [.count "bookmarks" "n"]
    ops := primary [addRow 1 [("name", .str "home")], addChild "bookmarks" 1 1 [("size", 10)],
      addChild "bookmarks" 1 2 [("size", 4)], addRow 2 [("name", .str "work")], .remove [] 1 []]
    orders := [[0, 1, 2, 3, 4], [3, 0, 2, 1, 4]] },
  { name := "filter-by-value"
    description := "Root rows whose value is greater than a constant."
    root := "rows"
    steps := [.filter (.gt "v" 4)]
    ops := primary [addRow 1 [("v", 5)], addRow 2 [("v", 3)], addRow 3 [("v", 9)], .remove [] 3 []]
    orders := [[0, 1, 2, 3], [2, 3, 1, 0]] },
  { name := "drop-property"
    description := "A property dropped from every root row."
    root := "rows"
    steps := [.dropProperty "secret"]
    ops := primary [addRow 1 [("v", 5), ("secret", .str "x")], addRow 2 [("v", 3), ("secret", .str "y")]]
    orders := [[0, 1], [1, 0]] },
  { name := "flatten-projects-tasks"
    description := "Each team's projects and their tasks, flattened into one array of tasks that carry their project's values."
    root := "teams"
    steps := [.flatten "projects" "tasks" "work"]
    ops := primary [addRow 1 [("team", .str "core")],
      addChild "projects" 1 1 [("title", .str "spec")], addChild "projects" 1 2 [("title", .str "port")],
      addGrandchild "projects" "tasks" 1 1 1 [("hours", 3)], addGrandchild "projects" "tasks" 1 1 2 [("hours", 5)],
      addGrandchild "projects" "tasks" 1 2 1 [("hours", 2)], .remove ["projects", "tasks"] 1 [1, 2]]
    orders := [[0, 1, 2, 3, 4, 5, 6], [0, 2, 5, 1, 4, 3, 6], [0, 1, 4, 6, 2, 3, 5]] },
  { name := "regroup-by-total"
    description := "Folders grouped by their total, which a new bookmark changes: the folder moves to another group (jinaga/jinaga-cascade-core#29)."
    root := "folders"
    steps := [.sum "bookmarks" "size" "total", .groupBy ["total"] "totals"]
    ops := primary [addRow 1 [("name", .str "home")], addRow 2 [("name", .str "work")],
      addChild "bookmarks" 1 1 [("size", 10)], addChild "bookmarks" 2 1 [("size", 4)],
      addChild "bookmarks" 2 2 [("size", 6)]]
    orders := [[0, 1, 2, 3, 4], [1, 4, 3, 0, 2], [0, 2, 1, 3, 4]] },
  { name := "cumulative-sum-by-name"
    description := "Each folder's total, then a running total of the folders in each category by name; a folder loses its only bookmark."
    root := "folders"
    steps := [.sum "bookmarks" "size" "total", .groupBy ["cat"] "groups", .cumulativeSum "folders" ["name"] ["total"]]
    ops := primary [addRow 1 [("cat", .str "a"), ("name", .str "b")], addRow 2 [("cat", .str "a"), ("name", .str "a")],
      addRow 3 [("cat", .str "a"), ("name", .str "c")], addRow 4 [("cat", .str "b"), ("name", .str "a")],
      addChild "bookmarks" 1 1 [("size", 10)], addChild "bookmarks" 2 1 [("size", 4)],
      addChild "bookmarks" 3 1 [("size", 1)], addChild "bookmarks" 4 1 [("size", 7)],
      addChild "bookmarks" 2 2 [("size", 3)], .remove ["bookmarks"] 1 [1]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [3, 2, 7, 1, 0, 6, 5, 8, 4, 9], [1, 5, 8, 0, 4, 9, 2, 6, 3, 7]] },
  { name := "replace-to-delta-readings"
    description := "Each meter's readings, in time order, as the change since the reading before; a middle reading leaves."
    root := "sites"
    steps := [.replaceToDelta "meters" "readings" ["at"] [("value", "delta")]]
    ops := primary [addRow 1 [("name", .str "north")],
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
    ops := primary [addRow 1 [("name", .str "tools")], addRow 2 [("name", .str "toys")],
      addChild "items" 1 1 [("name", .str "saw"), ("price", 5)], addChild "items" 1 2 [("name", .str "awl"), ("price", 3)],
      addChild "items" 1 3 [("name", .str "rag")], addChild "items" 1 4 [("name", .str "vise"), ("price", 9)],
      addChild "items" 2 1 [("name", .str "ball")], .remove ["items"] 1 [2]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7], [1, 6, 0, 5, 3, 4, 7, 2], [0, 3, 7, 4, 1, 2, 6, 5]] },
  { name := "pick-largest-total"
    description := "Folders grouped by category, each group picking its folder with the largest total, which changes as bookmarks arrive and leave."
    root := "folders"
    steps := [.sum "bookmarks" "size" "total", .groupBy ["cat"] "groups", .pickByMax "folders" "total" "largest"]
    ops := primary [addRow 1 [("cat", .str "a"), ("name", .str "home")], addRow 2 [("cat", .str "a"), ("name", .str "work")],
      addRow 3 [("cat", .str "a"), ("name", .str "misc")], addRow 4 [("cat", .str "b"), ("name", .str "play")],
      addChild "bookmarks" 1 1 [("size", 10)], addChild "bookmarks" 2 1 [("size", 4)],
      addChild "bookmarks" 2 2 [("size", 3)], addChild "bookmarks" 2 3 [("size", 5)],
      addChild "bookmarks" 3 1 [("size", 1)], addChild "bookmarks" 4 1 [("size", 2)], .remove ["bookmarks"] 3 [1]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [3, 9, 1, 7, 2, 8, 10, 0, 4, 5, 6], [2, 8, 0, 4, 10, 1, 6, 5, 3, 7, 9]] },
  { name := "enrich-orders-catalog"
    description := "Orders enriched with their SKU's catalog entry, a group of prices; entries arrive before and after the orders, one leaves, and one order's SKU is never listed."
    root := "orders"
    steps := [.enrich "catalog" "prices" [.groupBy ["sku"] "skus"] ["sku"] "product" none]
    ops := [(none, addRow 1 [("sku", .str "a"), ("qty", 2)]),
      on "catalog" (addRow 1 [("sku", .str "a"), ("price", 5)]),
      on "catalog" (addRow 2 [("sku", .str "b"), ("price", 7)]),
      (none, addRow 2 [("sku", .str "b"), ("qty", 1)]),
      (none, addRow 3 [("sku", .str "c"), ("qty", 4)]),
      on "catalog" (addRow 3 [("sku", .str "a"), ("price", 6)]),
      on "catalog" (.remove [] 1 [])]
    orders := [[0, 1, 2, 3, 4, 5, 6], [1, 5, 6, 2, 0, 3, 4], [4, 3, 2, 0, 5, 1, 6]] },
  { name := "enrich-totals-when-missing"
    description := "Orders enriched with their SKU's stock on hand, a total over its lots; an order with no SKU, and one whose stock leaves, get whenMissing."
    root := "orders"
    steps := [.enrich "stock" "lots" [.groupBy ["sku"] "skus", .sum "lots" "qty" "onHand"] ["sku"] "stock"
      (some (mkProps [("onHand", 0)]))]
    ops := [(none, addRow 1 [("sku", .str "a")]),
      (none, addRow 2 [("note", .str "no sku")]),
      on "stock" (addRow 1 [("sku", .str "a"), ("qty", 3)]),
      on "stock" (addRow 2 [("sku", .str "a"), ("qty", 4)]),
      (none, addRow 3 [("sku", .str "b")]),
      on "stock" (addRow 3 [("sku", .str "b"), ("qty", 1)]),
      on "stock" (.remove [] 3 [])]
    orders := [[0, 1, 2, 3, 4, 5, 6], [2, 3, 5, 6, 0, 1, 4], [4, 5, 1, 2, 6, 0, 3]] },
  { name := "define-tier-regroup"
    description := "Each folder's tier, defined from its total, then the folders grouped by tier: a folder moves as its total crosses the threshold and back."
    root := "folders"
    steps := [.sum "bookmarks" "size" "total",
      .defineProperty "tier" (.cond (.gt "total" 10) (.lit (.str "big")) (.lit (.str "small"))) ["total"],
      .groupBy ["tier"] "tiers"]
    ops := primary [addRow 1 [("name", .str "home")], addRow 2 [("name", .str "work")],
      addChild "bookmarks" 1 1 [("size", 8)], addChild "bookmarks" 1 2 [("size", 5)],
      addChild "bookmarks" 2 1 [("size", 20)], .remove ["bookmarks"] 2 [1], addRow 3 [("name", .str "misc")]]
    orders := [[0, 1, 2, 3, 4, 5, 6], [1, 4, 0, 3, 5, 6, 2], [6, 0, 2, 1, 4, 3, 5]] },
  { name := "define-score-filter"
    description := "A score defined from two fixed values, with no dependencies, and the rows whose score is greater than 5; a row missing a value has no score."
    root := "rows"
    steps := [.defineProperty "score" (.add (.prop "a") (.prop "b")) [], .filter (.gt "score" 5)]
    ops := primary [addRow 1 [("a", 2), ("b", 5)], addRow 2 [("a", 1), ("b", 1)], addRow 3 [("a", 9)],
      addRow 4 [("a", 4), ("b", 4)], .remove [] 4 []]
    orders := [[0, 1, 2, 3, 4], [3, 2, 4, 1, 0], [1, 3, 0, 4, 2]] },
  { name := "define-key-enrich"
    description := "Each order's band, defined from its total, as the key that enriches it: an order changes bands, and its enrichment, as lines arrive."
    root := "orders"
    steps := [.sum "lines" "amount" "total",
      .defineProperty "band" (.cond (.gt "total" 50) (.lit (.str "high")) (.lit (.str "low"))) ["total"],
      .enrich "bands" "bandRows" [.groupBy ["band"] "bands"] ["band"] "bandInfo" none]
    ops := [on "bands" (addRow 1 [("band", .str "high"), ("label", .str "High")]),
      (none, addRow 1 [("id", .str "o1")]),
      (none, addChild "lines" 1 1 [("amount", 30)]),
      on "bands" (addRow 2 [("band", .str "low"), ("label", .str "Low")]),
      (none, addChild "lines" 1 2 [("amount", 40)]),
      (none, addRow 2 [("id", .str "o2")]),
      (none, addChild "lines" 2 1 [("amount", 10)])]
    orders := [[0, 1, 2, 3, 4, 5, 6], [1, 2, 4, 5, 6, 3, 0], [5, 3, 1, 6, 0, 2, 4]] },
  { name := "nested-group-tasks"
    description := "Each team's tasks grouped by status, apart from every other team's: two teams have an open group each."
    root := "teams"
    steps := [.groupBy ["status"] "byStatus" ["tasks"]]
    ops := primary [addRow 1 [("team", .str "core")], addRow 2 [("team", .str "port")],
      addChild "tasks" 1 1 [("status", .str "open"), ("hours", 3)],
      addChild "tasks" 1 2 [("status", .str "open"), ("hours", 5)],
      addChild "tasks" 1 3 [("status", .str "done"), ("hours", 1)],
      addChild "tasks" 2 1 [("status", .str "open"), ("hours", 2)], .remove ["tasks"] 1 [2]]
    orders := [[0, 1, 2, 3, 4, 5, 6], [1, 5, 0, 4, 3, 2, 6], [0, 3, 1, 2, 6, 5, 4]] },
  { name := "nested-filter-tasks"
    description := "Each team's tasks of more than 2 hours; a task that fails hides its steps."
    root := "teams"
    steps := [.filter (.gt "hours" 2) ["tasks"]]
    ops := primary [addRow 1 [("team", .str "core")],
      addChild "tasks" 1 1 [("hours", 3)], addChild "tasks" 1 2 [("hours", 1)],
      addGrandchild "tasks" "steps" 1 1 1 [("note", .str "draft")],
      addGrandchild "tasks" "steps" 1 2 1 [("note", .str "skip")],
      addChild "tasks" 1 3 [("hours", 4)], .remove ["tasks"] 1 [3]]
    orders := [[0, 1, 2, 3, 4, 5, 6], [0, 2, 4, 5, 1, 6, 3], [0, 5, 1, 3, 6, 2, 4]] },
  { name := "nested-flatten-depts"
    description := "In each department, the projects and their tasks flattened into one array of tasks that carry their project's values."
    root := "orgs"
    steps := [.flatten "projects" "tasks" "work" ["depts"]]
    ops := primary [addRow 1 [("org", .str "acme")],
      addChild "depts" 1 1 [("dept", .str "eng")], addChild "depts" 1 2 [("dept", .str "ops")],
      .add ["depts", "projects"] 1 [1, 1] (mkProps [("title", .str "spec")]),
      .add ["depts", "projects"] 1 [2, 1] (mkProps [("title", .str "infra")]),
      .add ["depts", "projects", "tasks"] 1 [1, 1, 1] (mkProps [("hours", 3)]),
      .add ["depts", "projects", "tasks"] 1 [1, 1, 2] (mkProps [("hours", 5)]),
      .add ["depts", "projects", "tasks"] 1 [2, 1, 1] (mkProps [("hours", 2)]),
      .remove ["depts", "projects", "tasks"] 1 [1, 1, 2]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 2, 1, 4, 3, 7, 6, 5, 8], [0, 1, 3, 5, 6, 8, 2, 4, 7]] },
  { name := "nested-group-moves"
    description := "Folders banded by their total, then each band's folders grouped by category: a folder and its bookmarks move to the other band, and back, as bookmarks arrive and leave."
    root := "folders"
    steps := [.sum "bookmarks" "size" "total",
      .defineProperty "band" (.cond (.gt "total" 10) (.lit (.str "big")) (.lit (.str "small"))) ["total"],
      .groupBy ["band"] "bands", .groupBy ["cat"] "cats" ["folders"]]
    ops := primary [addRow 1 [("cat", .str "a"), ("name", .str "home")],
      addRow 2 [("cat", .str "a"), ("name", .str "work")], addRow 3 [("cat", .str "b"), ("name", .str "misc")],
      addChild "bookmarks" 1 1 [("size", 8)], addChild "bookmarks" 1 2 [("size", 5)],
      addChild "bookmarks" 2 1 [("size", 20)], .remove ["bookmarks"] 2 [1],
      addChild "bookmarks" 3 1 [("size", 2)]]
    orders := [[0, 1, 2, 3, 4, 5, 6, 7], [2, 7, 1, 5, 0, 4, 6, 3], [0, 3, 1, 5, 2, 6, 4, 7]] },
  { name := "nested-group-two-levels"
    description := "In each department of each org, the projects grouped by status: a scope two arrays deep."
    root := "orgs"
    steps := [.groupBy ["status"] "byStatus" ["depts", "projects"]]
    ops := primary [addRow 1 [("org", .str "acme")],
      addChild "depts" 1 1 [("dept", .str "eng")], addChild "depts" 1 2 [("dept", .str "ops")],
      .add ["depts", "projects"] 1 [1, 1] (mkProps [("status", .str "live"), ("title", .str "spec")]),
      .add ["depts", "projects"] 1 [1, 2] (mkProps [("status", .str "live"), ("title", .str "port")]),
      .add ["depts", "projects"] 1 [2, 1] (mkProps [("status", .str "live"), ("title", .str "infra")]),
      .add ["depts", "projects"] 1 [2, 2] (mkProps [("status", .str "paused"), ("title", .str "audit")])]
    orders := [[0, 1, 2, 3, 4, 5, 6], [0, 2, 6, 5, 1, 4, 3], [0, 1, 3, 2, 4, 5, 6]] }]

end JinagaSpec.Cascade
