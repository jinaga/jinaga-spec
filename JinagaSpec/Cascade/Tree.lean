/-!
# Cascade: the output tree and its events

`@jinaga/cascade-core` maintains a tree of keyed arrays as rows arrive and leave.
Each pipeline step listens to the events of the step before it and emits events
of its own. This file defines the tree and what each event does to it.

A node is identified by its level, the path of array names from the root, and
its key. A key is unique within its level. A node's parent is its *placement*:
a value that `added` sets and `placed` changes. Descendants are addressed by
their own identity, so when a node moves, its subtree moves with it.

`apply` is the protocol every step must keep. It refuses:

- adding a node that exists, or whose parent does not;
- removing a node that does not exist, or that still has children;
- a change whose `old` value is not the current one, or equals the new one;
- a move whose `old` parent is not the current one, equals the new one, or
  whose new parent does not exist.

Requiring `old` to be current forbids delivering a change twice. Refusing a
change from a value to itself forbids no-op events.
-/
namespace JinagaSpec.Cascade

noncomputable section

abbrev Level := List String

/-- A property's value: a number, or an object. An object is a copy of a node's
props, which `pickBy*` and `enrich` write onto another node; a later step sees
it as one value and cannot reach inside it. -/
inductive Val where
  | int (n : Int)
  | obj (props : String → Option Val)

/-- Values compare by extension: two objects are equal when their props are.

The TypeScript groups by `JSON.stringify` of the grouping values, which keeps an
object's properties in insertion order, so `groupBy` on a copied object puts
`{a: 1, b: 2}` and `{b: 2, a: 1}` in different groups. Insertion order is how an
object was built, not something that varies in the domain, so the model does not
represent it; the TypeScript agrees with the model when a grouping value is a
number or an object built in one order. -/
noncomputable instance : DecidableEq Val := fun a b => Classical.propDecidable (a = b)

instance (n : Nat) : OfNat Val n := ⟨.int n⟩

/-- A value as a number. An object counts 0, as the TypeScript's
`toFiniteNumber` counts anything that is not a finite number. -/
def Val.num : Val → Int
  | int n => n
  | obj _ => 0

/-- A value's number, if it is one. -/
def Val.toInt? : Val → Option Int
  | int n => some n
  | obj _ => none

abbrev Props := String → Option Val

/-- A key. A root row has a `row` key. A child fed through `collection()` has a
`child` key: its parent's key and its own natural key, so it is unique within
its level even when its natural key is not. A root-level `groupBy` derives a
group's key from its grouping values, so two groups share a key exactly when
they share their values. -/
inductive Key where
  | row (n : Nat)
  | child (parent : Key) (k : Nat)
  | group (values : List (Option Val))

noncomputable instance : DecidableEq Key := fun a b => Classical.propDecidable (a = b)

abbrev Id := Level × Key

structure Node where
  parent : Option Key
  props : Props

abbrev Tree := List (Id × Node)

def Tree.get (T : Tree) (id : Id) : Option Node :=
  (T.find? (·.1 == id)).map (·.2)

/-- Whether a node at level `l` may have parent `p`: a root node has none, any
other node has a parent that exists at the level above. -/
def Tree.parentOk (T : Tree) (l : Level) : Option Key → Bool
  | none => l.isEmpty
  | some q => !l.isEmpty && (T.get (l.dropLast, q)).isSome

/-- Whether node `(l, k)` has a child. -/
def Tree.hasChild (T : Tree) (l : Level) (k : Key) : Bool :=
  T.any fun (id, n) => !id.1.isEmpty && id.1.dropLast == l && n.parent == some k

def Props.set (ps : Props) (p : String) (v : Option Val) : Props :=
  fun q => if q = p then v else ps q

inductive Event where
  | added (l : Level) (k : Key) (parent : Option Key) (props : Props)
  | removed (l : Level) (k : Key)
  | modified (l : Level) (k : Key) (p : String) (old new : Option Val)
  | placed (l : Level) (k : Key) (old new : Key)

/-- Replace the node at `id`. -/
def Tree.update (T : Tree) (id : Id) (f : Node → Node) : Tree :=
  T.map fun e => if e.1 == id then (e.1, f e.2) else e

def Tree.apply (T : Tree) : Event → Option Tree
  | .added l k p ps =>
    if (T.get (l, k)).isNone && T.parentOk l p then some (((l, k), ⟨p, ps⟩) :: T) else none
  | .removed l k =>
    if (T.get (l, k)).isSome && !T.hasChild l k then some (T.filter (·.1 != (l, k))) else none
  | .modified l k p old new =>
    match T.get (l, k) with
    | some n => if n.props p == old && old != new
        then some (T.update (l, k) fun n => { n with props := n.props.set p new }) else none
    | none => none
  | .placed l k a b =>
    match T.get (l, k) with
    | some n => if n.parent == some a && a != b && T.parentOk l (some b)
        then some (T.update (l, k) fun n => { n with parent := some b }) else none
    | none => none

def Tree.applyAll (T : Tree) : List Event → Option Tree
  | [] => some T
  | e :: es => (T.apply e).bind (·.applyAll es)

/-- A tree is well formed when its ids are distinct and every node's parent
exists. `apply` keeps it so. -/
structure Tree.WF (T : Tree) : Prop where
  nodup : (T.map (·.1)).Nodup
  parents : ∀ id n, T.get id = some n → T.parentOk id.1 n.parent = true

/-- Two trees hold the same nodes. The order of a tree's list means nothing. -/
def Tree.Equiv (T U : Tree) : Prop := ∀ id, T.get id = U.get id

end

end JinagaSpec.Cascade
