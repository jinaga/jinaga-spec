import JinagaSpec.Cascade.Steps

/-!
# Cascade: the input

A caller adds and removes root rows (`pipeline.add`, `pipeline.remove`), and the
children of declared source arrays (`pipeline.collection(...).add`, `.remove`).
A child is named by the natural keys of its ancestors and its own, root first.
A natural key need only be unique among its siblings: the input composes it with
its parent's key (`Key.child`), so it is unique within its level.

The input step turns each operation into events:

- A row is added only when its parent is present. A child that arrives before
  its parent is refused (jinaga/jinaga-cascade-core#31): Jinaga delivers a nested
  collection's rows only after their parent, so an orphan means the caller wired
  the input out of order.
- Removing a row removes its subtree first, children before parents, so no step
  sees a parent leave while it still has children.

`receive` is what the input holds after an operation: the denotation the input
step's events must produce.
-/
namespace JinagaSpec.Cascade

/-- The key of the row named by natural keys `r :: rest`, root first. -/
def nodeKey (r : Nat) (rest : List Nat) : Key := rest.foldl .child (.row r)

/-- What a caller does. A root row has `rest = []`; a child at level `l` has one
natural key in `rest` per segment of `l`. -/
inductive Op where
  | add (l : Level) (r : Nat) (rest : List Nat) (props : Props)
  | remove (l : Level) (r : Nat) (rest : List Nat)

/-- The parent the row named by `r :: rest` would have, if `rest` is not empty. -/
def parentOf (r : Nat) (rest : List Nat) : Option Key :=
  if rest = [] then none else some (nodeKey r rest.dropLast)

/-- An add is accepted when its level matches its key path, and its parent, if
it has one, is present. -/
def accepts (T : Tree) (l : Level) (r : Nat) (rest : List Nat) : Bool :=
  l.length == rest.length && T.parentOk l (parentOf r rest)

/-- What the input holds after an operation. A refused add changes nothing;
removing a row removes its subtree. -/
def Tree.receive (T : Tree) : Op → Tree
  | .add l r rest ps =>
    if accepts T l r rest then ((l, nodeKey r rest), ⟨parentOf r rest, ps⟩) :: T else T
  | .remove l r rest => T.filter fun e => !inSubtree T (l, nodeKey r rest) e.1

/-- The events the input step emits for an operation. -/
def input.handle (T : Tree) : Op → List Event
  | .add l r rest ps =>
    if accepts T l r rest then [.added l (nodeKey r rest) (parentOf r rest) ps] else []
  | .remove l r rest =>
    if (T.get (l, nodeKey r rest)).isSome then evict T (l, nodeKey r rest) else []

/-- The caller's contract: a row is not added twice. Jinaga delivers each row
of a subscription once. -/
def Fresh (T : Tree) : Op → Prop
  | .add l r rest _ => T.get (l, nodeKey r rest) = none
  | .remove .. => True

end JinagaSpec.Cascade
