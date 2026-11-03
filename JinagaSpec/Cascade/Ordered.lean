import JinagaSpec.Cascade.Sig

/-!
# Cascade: steps over ordered siblings

`cumulativeSum` and `replaceToDelta` give each node at a level `c` values
computed from its siblings, the nodes at `c` with the same parent, taken in an
order. Both are a step that overwrites some properties `Q` of the nodes at `c`
with values computed from the whole input tree (`overlay.F`). The step forwards
each event, hides upstream changes to `Q` at `c`, and then emits a change for
each other node whose computed value changed (`overlayStep`). It is correct
whatever the values are, so long as equivalent trees give the same values.

## The order

Both TypeScript steps sort each parent's items into a total order, so the order
items arrive in never matters. `cumulativeSum` compares its `orderBy` values in
turn, then the keys; `replaceToDelta` compares its `orderBy` values, which must
include the collection key, then the keys. The model takes the comparison as a
parameter `lt` on a node's key and props, and assumes only that it is a strict
total order on nodes with distinct keys (`StrictTotal`). How values compare
(numbers, strings, missing values) is outside the model.

`cumulativeSum`'s values need no assumption about `lt` to ignore list order;
the assumption ties them to the TypeScript's sorted list (`prefix_of_sorted`).
`replaceToDelta`'s predecessor needs it to be well defined: the greatest of the
siblings before a node is unique only under a total order (`latest_perm`), and
it is the node just before in the sorted list (`latest_of_sorted`).

## The TypeScript's suffix

The TypeScript keeps each parent's items in a sorted list and updates only the
items after the one that changed. The model emits a change for every node whose
value differs, which is the same set of events: the values before the change
are the same (`overlayStep` does not need this, and `Cache.lean` is where the
model compares a step to its cache).
-/
namespace JinagaSpec.Cascade

/-- `lt` is a strict total order on nodes with distinct keys. -/
structure StrictTotal (lt : Key × Props → Key × Props → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a.1 ≠ b.1 → lt a b = true ∨ lt b a = true

/-! ## Overwriting properties of one level -/

/-- `ps` with the names in `Q` taken from `v`. -/
def overlay (Q : List String) (v : String → Option Val) (ps : Props) : Props :=
  fun x => if x ∈ Q then v x else ps x

/-- The nodes at level `c` take the values `val T k` for the names in `Q`. -/
def overlay.F (c : Level) (Q : List String) (val : Tree → Key → String → Option Val) (T : Tree) :
    Tree :=
  T.mapProps c fun k ps => overlay Q (val T k) ps

/-- The changes that take the nodes at `c` that were in `T` and are in `T'` from
their values in `T` to their values in `T'`. -/
def resync (c : Level) (Q : List String) (val : Tree → Key → String → Option Val) (T T' : Tree) :
    List Event :=
  ((T'.filter fun e => e.1.1 = c ∧ (T.get e.1).isSome).map (·.1.2)).flatMap fun k =>
    (dedup Q).filterMap fun x =>
      if val T k x = val T' k x then none else some (.modified c k x (val T k x) (val T' k x))

/-- Forward each event: a node added at `c` arrives with its values, and an
upstream change to a name in `Q` at `c` is hidden, because this step defines it.
Then emit a change for each other node at `c` whose value changed. -/
def overlayStep (c : Level) (Q : List String) (val : Tree → Key → String → Option Val) : Step where
  handle T e :=
    match T.apply e with
    | none => []
    | some T' =>
      (match e with
        | .added l k p ps => [.added l k p (if l = c then overlay Q (val T' k) ps else ps)]
        | .modified l k x old new => if l = c ∧ x ∈ Q then [] else [.modified l k x old new]
        | e => [e]) ++
      resync c Q val T T'

/-- What the step declares: the names in `Q` at `c` can change. -/
def overlay.sig (c : Level) (Q : List String) (σ : Sig) : Sig :=
  ⟨fun l x => σ.mutable l x || (l == c && decide (x ∈ Q)), σ.movable⟩

/-! ## Siblings -/

/-- The nodes at level `c` with parent `p`, as keys and props. -/
def siblings (c : Level) (T : Tree) (p : Option Key) : List (Key × Props) :=
  (T.filter fun e => e.1.1 = c ∧ e.2.parent = p).map fun e => (e.1.2, e.2.props)

/-! ## `cumulativeSum` -/

/-- The running total of `x` at node `(c, k)`: the sum of `x` over the node and
its siblings before it, an absent value counting 0. The TypeScript writes it
over `x` (`composeOutputProps`). -/
def cumulativeSum.val (c : Level) (lt : Key × Props → Key × Props → Bool) (T : Tree) (k : Key)
    (x : String) : Option Val :=
  (T.get (c, k)).map fun n =>
    (((siblings c T n.parent).filter fun y => y.1 == k || lt y (k, n.props)).map
      fun y => (y.2 x).getD 0).sum

/-- `cumulativeSum(c, orderBy, P)`. -/
def cumulativeSum.F (c : Level) (lt : Key × Props → Key × Props → Bool) (P : List String) :
    Tree → Tree :=
  overlay.F c P (cumulativeSum.val c lt)

def cumulativeSumStep (c : Level) (lt : Key × Props → Key × Props → Bool) (P : List String) :
    Step :=
  overlayStep c P (cumulativeSum.val c lt)

/-! ## `replaceToDelta` -/

/-- One node into the greatest so far. -/
def latestStep (lt : Key × Props → Key × Props → Bool) (y : Key × Props) :
    Option (Key × Props) → Option (Key × Props)
  | none => some y
  | some a => if lt a y then some y else some a

/-- The greatest of some nodes under `lt`, if there are any. -/
def latest (lt : Key × Props → Key × Props → Bool) : List (Key × Props) → Option (Key × Props) :=
  List.foldr (latestStep lt) none

/-- A node's predecessor: the greatest of its siblings before it. -/
def predecessor (c : Level) (lt : Key × Props → Key × Props → Bool) (T : Tree) (k : Key) (n : Node) :
    Option (Key × Props) :=
  latest lt ((siblings c T n.parent).filter fun y => lt y (k, n.props))

/-- The output names, each paired with the property it is the delta of. -/
abbrev Deltas := List (String × String)

/-- Output `o` of node `(c, k)`, for the pair `(p, o)`: its `p` less its
predecessor's, an absent value counting 0, and the first node's predecessor
counting 0 (`computeDeltaForProperty`). -/
def replaceToDelta.val (c : Level) (lt : Key × Props → Key × Props → Bool) (D : Deltas) (T : Tree)
    (k : Key) (o : String) : Option Val :=
  match D.find? (·.2 = o), T.get (c, k) with
  | some (p, _), some n =>
    some ((n.props p).getD 0 - (((predecessor c lt T k n).bind (·.2 p)).getD 0))
  | _, _ => none

/-- `replaceToDelta(…, orderBy, properties, outputs)` on the events at `c`. -/
def replaceToDelta.F (c : Level) (lt : Key × Props → Key × Props → Bool) (D : Deltas) :
    Tree → Tree :=
  overlay.F c (D.map (·.2)) (replaceToDelta.val c lt D)

def replaceToDeltaStep (c : Level) (lt : Key × Props → Key × Props → Bool) (D : Deltas) : Step :=
  overlayStep c (D.map (·.2)) (replaceToDelta.val c lt D)

end JinagaSpec.Cascade
