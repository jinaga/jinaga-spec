import JinagaSpec.Cascade.Json

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

abbrev Level := List String

/-- A property's value: JSON (`Json.lean`). An object, such as the copy of a
node's props that `pickBy*` and `enrich` write onto another node, is a map from
names to values; a later step sees it as one value and cannot reach inside it.
The model builds every map through `CMap`, so the values it builds are canonical
(`Json.Canonical`): two of them are equal when they hold the same JSON, whatever
order they were built in. A caller's values are assumed canonical, as they are
when the input reads them as JSON. Under that contract, objects that differ only
in the order of their properties are the same value, and so group together;
the TypeScript groups by `JSON.stringify`, which keeps insertion order
(jinaga/jinaga-cascade-core#41). -/
abbrev Val := Json

instance (n : Nat) : OfNat Json n := ⟨.int n⟩

/-- A value as a number. Anything else counts 0. The TypeScript converts a
value with `Number()`, so there a numeric string counts its number; the vectors
add and subtract only numbers (`check`). -/
def Val.num : Val → Int
  | .int n => n
  | _ => 0

/-- A value's number, if it is one. -/
def Val.toInt? : Val → Option Int
  | .int n => some n
  | _ => none

/-- A node's props: a finite map from names to values, read as a function. -/
abbrev Props := CMap String Val

instance : CoeFun Props (fun _ => String → Option Val) := ⟨CMap.get⟩

theorem Props.ext {ps qs : Props} (h : ∀ p, ps p = qs p) : ps = qs := CMap.ext h

/-- A key is a value, as in the TypeScript, where keys are strings. A root row
has a `row` key. A child fed through `collection()` has a `child` key: its
parent's key and its own natural key, so it is unique within its level even
when its natural key is not. A root-level `groupBy` derives a group's key from
its grouping values, so two groups share a key exactly when they share their
values. Each form is tagged, so no two forms share a key. -/
abbrev Key := Json

/-- An optional value as a value: `[]` or `[v]`. -/
def Json.ofOption : Option Val → Json
  | none => .list []
  | some v => .list [v]

def Key.row (n : Nat) : Key := .list [.str "row", .int n]
def Key.child (parent : Key) (k : Nat) : Key := .list [.str "child", parent, .int k]
def Key.group (values : List (Option Val)) : Key := .list (.str "group" :: values.map Json.ofOption)

theorem Json.ofOption_inj {a b : Option Val} (h : Json.ofOption a = Json.ofOption b) : a = b := by
  cases a <;> cases b <;> simp_all [Json.ofOption]

theorem Key.row_inj {n m : Nat} : Key.row n = Key.row m ↔ n = m := by
  simp [Key.row, Int.ofNat_inj]

theorem Key.child_inj {p q : Key} {n m : Nat} : Key.child p n = Key.child q m ↔ p = q ∧ n = m := by
  simp [Key.child, Int.ofNat_inj]

theorem map_ofOption_inj : ∀ {vs ws : List (Option Val)},
    vs.map Json.ofOption = ws.map Json.ofOption → vs = ws
  | [], [], _ => rfl
  | v :: vs, w :: ws, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Json.ofOption_inj h.1, map_ofOption_inj h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem Key.group_inj {vs ws : List (Option Val)} : Key.group vs = Key.group ws ↔ vs = ws := by
  simp only [Key.group, Json.list.injEq, List.cons.injEq, true_and]
  constructor
  · exact map_ofOption_inj
  · intro h; rw [h]

@[simp] theorem Key.row_ne_child (n : Nat) (p : Key) (k : Nat) : Key.row n ≠ Key.child p k := by
  simp [Key.row, Key.child]
@[simp] theorem Key.row_ne_group (n : Nat) (vs : List (Option Val)) : Key.row n ≠ Key.group vs := by
  simp [Key.row, Key.group]
@[simp] theorem Key.child_ne_group (p : Key) (k : Nat) (vs : List (Option Val)) :
    Key.child p k ≠ Key.group vs := by
  simp [Key.child, Key.group]
@[simp] theorem Key.child_ne_row (p : Key) (k n : Nat) : Key.child p k ≠ Key.row n :=
  fun h => Key.row_ne_child n p k h.symm
@[simp] theorem Key.group_ne_row (vs : List (Option Val)) (n : Nat) : Key.group vs ≠ Key.row n :=
  fun h => Key.row_ne_group n vs h.symm
@[simp] theorem Key.group_ne_child (vs : List (Option Val)) (p : Key) (k : Nat) :
    Key.group vs ≠ Key.child p k :=
  fun h => Key.child_ne_group p k vs h.symm

/-- A group key's values. -/
def Key.groupValues? : Key → Option (List (Option Val))
  | .list (.str "group" :: xs) => xs.mapM fun
    | .list [] => some none
    | .list [v] => some (some v)
    | _ => none
  | _ => none

theorem Key.groupValues?_group (vs : List (Option Val)) : (Key.group vs).groupValues? = some vs := by
  simp only [Key.group, Key.groupValues?]
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases v <;> simp_all [Json.ofOption, List.mapM_cons]

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

def Props.set (ps : Props) (p : String) (v : Option Val) : Props := CMap.set ps p v

@[simp] theorem Props.set_apply (ps : Props) (p q : String) (v : Option Val) :
    (ps.set p v) q = if q = p then v else ps q := CMap.get_set ps p q v

/-- `ps` with the names in `Q` taken from `v`. -/
def Props.override (Q : List String) (v : String → Option Val) (ps : Props) : Props :=
  Q.foldr (fun x m => m.set x (v x)) ps

@[simp] theorem Props.override_apply (Q : List String) (v : String → Option Val) (ps : Props)
    (x : String) : (Props.override Q v ps) x = if x ∈ Q then v x else ps x := by
  induction Q with
  | nil => simp [Props.override]
  | cons q Q ih =>
    simp only [Props.override, List.foldr_cons] at ih ⊢
    rw [Props.set_apply, ih]
    by_cases h : x = q
    · subst h; simp
    · simp [h]

/-- The props `G` takes from `f`, and no others. -/
def Props.ofFn (G : List String) (f : String → Option Val) : Props := CMap.ofFn G f

@[simp] theorem Props.ofFn_apply (G : List String) (f : String → Option Val) (x : String) :
    (Props.ofFn G f) x = if x ∈ G then f x else none := CMap.get_ofFn G f x

/-- A node's props as a value: an object, the map from each name to its value. -/
def Props.toJson (ps : Props) : Val :=
  Json.ofMap (CMap.ofFn (ps.keys.map .str) fun
    | .str p => ps p
    | _ => none)

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

end JinagaSpec.Cascade
