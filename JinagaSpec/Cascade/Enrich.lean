import JinagaSpec.Cascade.Sources
import JinagaSpec.Cascade.Ordered

/-!
# Cascade: `enrich`

`enrich` gives each primary row at level `s` a property `as`: a copy of the
secondary pipeline's root row that matches it, with everything below that row,
or `whenMissing` when none does. A secondary row matches when its collection-key
values `CK` equal the primary row's values for `K`, all of them present
(`primaryJoinFromPrimaryRow`, `secondaryJoinFromSecondaryRow`).

The secondary pipeline's output is a source of its own (`Sources.lean`). The step
is a join: it reads the primary and secondary sources and emits the primary's
events. A primary event is handled as by any step that overwrites a property
with a value computed from its input (`overlayStep`), the secondary held fixed.
A secondary event changes no primary row, only what some rows hold: the step
emits a change for each primary row whose copy differs.

A copy is a value (`Tree.copy`): the row's props, and for each of its arrays, the
map from each child's key to the child's copy. The TypeScript embeds its keyed
arrays in the row; it keeps an array after its last child leaves, where the
copy has an array only while it has children. A secondary whose collection key
is not unique has more than one match; the TypeScript keeps the last one it
saw, and the model gives such a row `whenMissing`.

The TypeScript passes an upstream change to `as` through, where the model's step
hides it, as for the aggregates.
-/
namespace JinagaSpec.Cascade

/-! ## A node and what is below it, as a value -/

/-- The nodes directly below node `(l, k)`, in any of its arrays. -/
def Tree.childrenOf (T : Tree) (l : Level) (k : Key) : Tree :=
  T.filter fun e => e.1.1 ≠ [] ∧ e.1.1.dropLast = l ∧ e.2.parent = some k

/-- The arrays of node `(l, k)` that have a child. -/
def Tree.arraysOf (T : Tree) (l : Level) (k : Key) : List String :=
  dedup ((T.childrenOf l k).filterMap fun e => e.1.1.getLast?)

/-- The keys of node `(l, k)`'s children in array `a`. -/
def Tree.keysIn (T : Tree) (l : Level) (k : Key) (a : String) : List Key :=
  (T.childrenOf l k).filterMap fun e => if e.1.1 = l ++ [a] then some e.1.2 else none

/-- Node `(l, k)`, with props `ps`, and what is below it, as one value: an object
of its props and, for each of its arrays, the map from each child's key to the
child's copy. `n` bounds the depth; `T.length` is enough for any node of `T`. -/
def Tree.copy (T : Tree) : Nat → Level → Key → Props → Val
  | 0, _, _, ps => ps.toJson
  | n + 1, l, k, ps =>
    Json.ofMap (CMap.ofFn (dedup ((ps.keys ++ T.arraysOf l k).map .str)) fun
      | .str a =>
        if a ∈ T.arraysOf l k then
          some (Json.ofMap (CMap.ofFn (T.keysIn l k a) fun ck =>
            (T.get (l ++ [a], ck)).map fun c => T.copy n (l ++ [a]) ck c.props))
        else ps a
      | _ => none)

/-! ## The join -/

/-- The secondary root rows that match primary props `ps`. An empty collection
key matches nothing (`enrich_secondary_collection_key_missing`). -/
def enrich.matches (K CK : List String) (Tq : Tree) (ps : Props) : Tree :=
  if !CK.isEmpty && K.all fun x => (ps x).isSome then
    Tq.filter fun e => e.1.1 = [] ∧ CK.map (e.2.props ·) = K.map (ps ·)
  else []

/-- The element of a one-element list. -/
def onlyOne {α : Type} : List α → Option α
  | [r] => some r
  | _ => none

/-- What primary row `(s, k)` of `T` holds as `as`, against secondary tree `Tq`. -/
def enrich.val (s : Level) (K CK : List String) (w : Option Val) (Tq : Tree) (T : Tree) (k : Key)
    (_ : String) : Option Val :=
  match T.get (s, k) with
  | none => none
  | some n =>
    match onlyOne (enrich.matches K CK Tq n.props) with
    | some r => some (Tq.copy Tq.length [] r.1.2 r.2.props)
    | none => w

/-- `enrich`'s output: the primary tree, each row at `s` holding its value. -/
def enrich.F (p q : Source) (s : Level) (as : String) (K CK : List String) (w : Option Val)
    (F : Forest) : Tree :=
  overlay.F s [as] (enrich.val s K CK w (F q)) (F p)

/-- The changes that take each node at `c` of `T` from values `a` to values `b`. -/
def retarget (c : Level) (Q : List String) (a b : Key → String → Option Val) (T : Tree) : List Event :=
  ((T.filter fun e => e.1.1 = c).map (·.1.2)).flatMap fun k =>
    (dedup Q).filterMap fun x => if a k x = b k x then none else some (.modified c k x (a k x) (b k x))

/-- `enrich(…)`: a primary event as `overlayStep` handles it, the secondary held
fixed; a secondary event as the changes to the primary rows whose values it
changes; any other source's events as nothing. -/
def enrich (p q : Source) (s : Level) (as : String) (K CK : List String) (w : Option Val) : Join where
  handle F e :=
    if e.1 = p then (overlayStep s [as] (enrich.val s K CK w (F q))).handle (F p) e.2
    else if e.1 = q then
      match (F q).apply e.2 with
      | some Tq' => retarget s [as] (enrich.val s K CK w (F q) (F p)) (enrich.val s K CK w Tq' (F p)) (F p)
      | none => []
    else []

end JinagaSpec.Cascade
