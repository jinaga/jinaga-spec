import JinagaSpec.Cascade.Step

/-!
# Cascade: the steps

Each step is a denotation, what its output is, and an implementation, which
events it emits for each input event. They are written to be read next to
`src/steps/*.ts` in `@jinaga/cascade-core`.

Only root-scope `groupBy` and `filter` are modelled here; a nested scope is a
later step.
-/
namespace JinagaSpec.Cascade

/-- Change the props of every node at level `s`. -/
def Tree.mapProps (T : Tree) (s : Level) (φ : Key → Props → Props) : Tree :=
  T.map fun e => if e.1.1 = s then (e.1, { e.2 with props := φ e.1.2 e.2.props }) else e

def Props.drop (ps : Props) (q : String) : Props := fun r => if r = q then none else ps r

/-! ## `dropProperty` -/

/-- `dropProperty(q)` at level `s`: nodes at `s` lose property `q`. -/
def dropProperty.F (s : Level) (q : String) (T : Tree) : Tree :=
  T.mapProps s fun _ ps => ps.drop q

/-- Strip `q` from nodes added at `s`, and drop changes to `q` at `s`: the
property no longer exists there, so neither do its changes. -/
def dropProperty (s : Level) (q : String) : Step where
  handle _ e := match e with
    | .added l k p ps => [.added l k p (if l = s then ps.drop q else ps)]
    | .modified l k p old new => if l = s ∧ p = q then [] else [.modified l k p old new]
    | e => [e]

/-! ## `defineProperty` -/

/-- `defineProperty(q, f, deps)` at level `s`: nodes at `s` gain property `q`,
computed by `f` from their other properties. -/
def defineProperty.F (s : Level) (q : String) (f : Props → Option Val) (T : Tree) : Tree :=
  T.mapProps s fun _ ps => ps.set q (f ps)

/-- Add `q` to nodes added at `s`. When a property in `deps` changes on a node
at `s`, forward the change and emit a change to `q` if its value changed.
Changes to `q` from upstream are hidden, because `q` is defined here.

`deps` is the caller's list of the properties `f` reads (`mutableProperties` in
TypeScript). The step is correct when `f` ignores every other property. -/
def defineProperty (s : Level) (q : String) (f : Props → Option Val) (deps : List String) :
    Step where
  handle T e := match e with
    | .added l k p ps => [.added l k p (if l = s then ps.set q (f ps) else ps)]
    | .modified l k p old new =>
      if l = s then
        if p = q then [] else
        match T.get (l, k) with
        | some n =>
          let before := f n.props
          let after := f (n.props.set p new)
          .modified l k p old new ::
            (if p ∈ deps ∧ before ≠ after then [.modified l k q before after] else [])
        | none => []
      else [.modified l k p old new]
    | e => [e]

/-! ## `sum` and `count` -/

/-- The children of `(c.dropLast, k)` at level `c` that contribute to its
aggregate. -/
def contributors (c : Level) (contributes : Props → Bool) (T : Tree) (k : Key) : Tree :=
  T.filter fun e => e.1.1 = c ∧ e.2.parent = some k ∧ contributes e.2.props

/-- The aggregate of a parent's contributing children. It is absent when there
are none, however many there were before. -/
def aggregate (c : Level) (contributes : Props → Bool) (w : Props → Int) (T : Tree) (k : Key) :
    Option Val :=
  match contributors c contributes T k with
  | [] => none
  | cs => some (cs.map (w ·.2.props)).sum

/-- A commutative aggregate over the children at level `c`, written to property
`q` of their parents. `sum(p)` contributes each child's `p`: from every child if
`p` is immutable (an absent value counts 0), and from the children where it is
defined if it is mutable. `count` contributes 1 from every child. -/
def aggregate.F (c : Level) (q : String) (contributes : Props → Bool) (w : Props → Int)
    (T : Tree) : Tree :=
  T.mapProps c.dropLast fun k ps => ps.set q (aggregate c contributes w T k)

/-- Forward each event. When a child at `c` arrives, leaves, changes or moves,
emit a change to the aggregate of each parent it affects, if the aggregate
changed. A parent arrives with its aggregate; upstream changes to `q` on a
parent are hidden. -/
def aggregateStep (c : Level) (q : String) (contributes : Props → Bool) (w : Props → Int) :
    Step where
  handle T e :=
    match T.apply e with
    | none => []
    | some T' =>
      let agg := aggregate c contributes w
      let touch (k : Key) : List Event :=
        if agg T k = agg T' k then [] else [.modified c.dropLast k q (agg T k) (agg T' k)]
      let parentOf (k : Key) : List Key := ((T.get (c, k)).bind (·.parent)).toList
      match e with
      | .added l k p ps =>
        if l = c.dropLast then [.added l k p (ps.set q (agg T' k))]
        else .added l k p ps :: (if l = c then p.toList.flatMap touch else [])
      | .removed l k => .removed l k :: (if l = c then (parentOf k).flatMap touch else [])
      | .modified l k p old new =>
        if l = c.dropLast ∧ p = q then []
        else .modified l k p old new :: (if l = c then (parentOf k).flatMap touch else [])
      | .placed l k a b => .placed l k a b :: (if l = c then touch a ++ touch b else [])

/-! ## `groupBy` at the root -/

/-- Keep the first of each repeated element. -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then dedup l else a :: dedup l

/-- The group a root row belongs to: its grouping values. -/
def groupKey (G : List String) (ps : Props) : Key := .group (G.map ps)

/-- A group's props: its grouping values. -/
def groupProps (G : List String) : Key → Props
  | .group vs => fun p => ((G.zip vs).find? (·.1 = p)).bind (·.2)
  | _ => fun _ => none

/-- A row's props without its grouping values, which belong to its group. -/
def omitProps (G : List String) (ps : Props) : Props := fun p => if p ∈ G then none else ps p

/-- Whether some root row of `T` belongs to group `g`. -/
def hasMember (G : List String) (T : Tree) (g : Key) : Bool :=
  T.any fun e => e.1.1.isEmpty && groupKey G e.2.props == g

/-- A node moved below the groups. A root row becomes a group's child. -/
def relevel (G : List String) (l : Level) (n : Node) : Node :=
  if l = [] then ⟨some (groupKey G n.props), omitProps G n.props⟩ else n

/-- `groupBy(G, …)` at the root: one group per distinct grouping values, at the
root; each root row below its group, at level `[C]`; the rest of the tree below
its root row, one level deeper. -/
def groupBy.F (G : List String) (C : String) (T : Tree) : Tree :=
  (dedup ((T.filter (·.1.1.isEmpty)).map fun e => groupKey G e.2.props)).map
      (fun g => (([], g), ⟨none, groupProps G g⟩)) ++
    T.map fun e => ((C :: e.1.1, e.1.2), relevel G e.1.1 e.2)

/-- A root row's arrival adds its group if it is the first member. Its removal
removes its group if it was the last. A change to a grouping value moves the row
to its new group with one `placed` event: the new group is added first if
needed, and the old group removed afterwards if it is now empty. Nothing below
the row is re-sent. Every other event moves one level down. -/
def groupBy (G : List String) (C : String) : Step where
  handle T e := match e with
    | .added [] k _ ps =>
      let g := groupKey G ps
      (if hasMember G T g then [] else [.added [] g none (groupProps G g)]) ++
        [.added [C] k (some g) (omitProps G ps)]
    | .added l k p ps => [.added (C :: l) k p ps]
    | .removed [] k =>
      match T.get ([], k) with
      | some n =>
        let g := groupKey G n.props
        .removed [C] k ::
          (if hasMember G (T.filter (·.1 != ([], k))) g then [] else [.removed [] g])
      | none => []
    | .removed l k => [.removed (C :: l) k]
    | .modified [] k p old new =>
      match T.get ([], k) with
      | some n =>
        if p ∈ G then
          let g := groupKey G n.props
          let g' := groupKey G (n.props.set p new)
          let rest := T.filter (·.1 != ([], k))
          (if hasMember G rest g' then [] else [.added [] g' none (groupProps G g')]) ++
            [.placed [C] k g g'] ++
            (if hasMember G rest g then [] else [.removed [] g])
        else [.modified [C] k p old new]
      | none => []
    | .modified l k p old new => [.modified (C :: l) k p old new]
    | .placed l k a b => [.placed (C :: l) k a b]

/-! ## `filter` at the root -/

/-- Walk up `n` parents from node `(l, k)`, to the key of its ancestor `n`
levels up. -/
def Tree.walk (T : Tree) : Nat → Level → Key → Option Key
  | 0, _, k => some k
  | n + 1, l, k => (T.get (l, k)).bind fun m => m.parent.bind fun q => T.walk n l.dropLast q

/-- A node is visible when its root ancestor passes the predicate. -/
def visible (P : Props → Bool) (T : Tree) (id : Id) : Bool :=
  match T.walk id.1.length id.1 id.2 with
  | some r => (T.get ([], r)).any (P ·.props)
  | none => false

/-- `filter(P)` at the root: the root rows that pass `P`, with their subtrees. -/
def filter.F (P : Props → Bool) (T : Tree) : Tree :=
  T.filter fun e => visible P T e.1

/-- Whether node `y` is `x` or below it. -/
def inSubtree (T : Tree) (x y : Id) : Bool :=
  x.1.length ≤ y.1.length && y.1.take x.1.length == x.1 &&
    T.walk (y.1.length - x.1.length) y.1 y.2 == some x.2

/-- Add `x` and its subtree, parents first, with their current values. -/
def admit (T : Tree) (x : Id) : List Event :=
  ((T.filter (inSubtree T x ·.1)).mergeSort fun a b => a.1.1.length ≤ b.1.1.length).map
    fun e => .added e.1.1 e.1.2 e.2.parent e.2.props

/-- Remove `x` and its subtree, children first. -/
def evict (T : Tree) (x : Id) : List Event :=
  ((T.filter (inSubtree T x ·.1)).mergeSort fun a b => b.1.1.length ≤ a.1.1.length).map
    fun e => .removed e.1.1 e.1.2

/-- A row's arrival or departure passes through when it is visible. When a
predicate property of a root row changes, or a row moves, its visibility may
change: if it becomes visible, add it and its subtree with their current values;
if it becomes hidden, remove its subtree, children first. The change itself is
then not forwarded, because the added rows already carry it.

`deps` is the caller's list of the properties `P` reads (`mutableProperties` in
TypeScript). The step is correct when `P` ignores every other property. -/
def filterStep (P : Props → Bool) (deps : List String) : Step where
  handle T e :=
    match T.apply e with
    | none => []
    | some T' =>
      let change (x : Id) : List Event :=
        match visible P T x, visible P T' x with
        | true, true => [e]
        | false, true => admit T' x
        | true, false => evict T x
        | false, false => []
      match e with
      | .added l k _ _ => if visible P T' (l, k) then [e] else []
      | .removed l k => if visible P T (l, k) then [e] else []
      | .modified l k p _ _ =>
        if l = [] ∧ p ∈ deps then change (l, k)
        else if visible P T (l, k) then [e] else []
      | .placed l k _ _ => change (l, k)

end JinagaSpec.Cascade
