import JinagaSpec.Cascade.Tree

/-!
# Cascade: the output session

The last step's events reach the output session, which keeps the nested keyed
arrays React renders. A node there sits in the array at its level, under its
ancestors: to reach it, the session needs the key of each ancestor, one per
segment. Events carry only a node's parent, so the session keeps a placement
index, the parent of each node it has queued, and resolves an event's location
through it when the event is queued (`Tree.ancestors`, `locate` in TypeScript).
Running a batch is then a pure function of the arrays.

The arrays are modelled by their *located entries*: each node with its level and
the key path of its ancestors. That is what a nested keyed array is, up to the
order of each array. It keeps what matters here: a node is reached through its
ancestors' keys, a subtree moves with its location, removing a node removes what
is below it, and an operation at a missing location fails.
-/
namespace JinagaSpec.Cascade

/-- The keys of the ancestors of a node at level `l` whose parent is `p`, root
first, read from the parents a tree records. Undefined when an ancestor is
missing. -/
def Tree.ancestorsN (T : Tree) : Nat → Level → Option Key → Option (List Key)
  | 0, _, none => some []
  | 0, _, some _ => none
  | _ + 1, _, none => none
  | n + 1, l, some q =>
    (T.get (l.dropLast, q)).bind fun m => (T.ancestorsN n l.dropLast m.parent).map (· ++ [q])

def Tree.ancestors (T : Tree) (l : Level) (p : Option Key) : Option (List Key) :=
  T.ancestorsN l.length l p

/-- A node as the arrays hold it: in the array at `segmentPath`, under the
ancestors `keyPath`. -/
structure Located where
  segmentPath : Level
  keyPath : List Key
  key : Key
  props : Props

abbrev Arrays := List Located

def Located.id (e : Located) : Id := (e.segmentPath, e.key)

/-- The node an entry holds: its parent is its last ancestor. -/
def Located.node (e : Located) : Node := ⟨e.keyPath.getLast?, e.props⟩

/-- The tree the arrays hold. -/
def Arrays.tree (A : Arrays) : Tree := A.map fun e => (e.id, e.node)

/-- Whether the arrays hold a node at this location. -/
def Arrays.holds (A : Arrays) (l : Level) (kp : List Key) (k : Key) : Bool :=
  A.any fun e => e.segmentPath == l && e.keyPath == kp && e.key == k

/-- Whether the arrays hold the parent of a location: the array a node at
level `l` under `kp` goes in exists. -/
def Arrays.parentHeld (A : Arrays) (l : Level) (kp : List Key) : Bool :=
  match kp.getLast? with
  | none => l.isEmpty
  | some q => !l.isEmpty && A.holds l.dropLast kp.dropLast q

/-- Whether entry `e` is the node at `(l, kp, k)`. -/
def Located.isAt (e : Located) (l : Level) (kp : List Key) (k : Key) : Bool :=
  e.segmentPath == l && e.keyPath == kp && e.key == k

/-- Whether entry `e` is below the node at `(l, kp, k)`. -/
def Located.isBelow (e : Located) (l : Level) (kp : List Key) (k : Key) : Bool :=
  l.isPrefixOf e.segmentPath && (kp ++ [k]).isPrefixOf e.keyPath

/-- Whether entry `e` is the node at `(l, kp, k)` or below it: what goes with
the node when it is removed or moved. -/
def Located.within (e : Located) (l : Level) (kp : List Key) (k : Key) : Bool :=
  e.isAt l kp k || e.isBelow l kp k

def Arrays.addNode (A : Arrays) (l : Level) (kp : List Key) (k : Key) (ps : Props) : Option Arrays :=
  if A.parentHeld l kp then some (⟨l, kp, k, ps⟩ :: A) else none

/-- Removing a node removes what is below it. -/
def Arrays.removeNode (A : Arrays) (l : Level) (kp : List Key) (k : Key) : Option Arrays :=
  if A.parentHeld l kp then some (A.filter fun e => !e.within l kp k) else none

def Arrays.modifyNode (A : Arrays) (l : Level) (kp : List Key) (k : Key) (p : String)
    (v : Option Val) : Option Arrays :=
  if A.holds l kp k then
    some (A.map fun e => if e.isAt l kp k then { e with props := e.props.set p v } else e)
  else none

/-- Moving a node moves what is below it: their key paths change from under
`kp₁` to under `kp₂`. -/
def Arrays.moveNode (A : Arrays) (l : Level) (kp₁ kp₂ : List Key) (k : Key) : Option Arrays :=
  if A.holds l kp₁ k && A.parentHeld l kp₂ then
    some (A.map fun e =>
      if e.within l kp₁ k then { e with keyPath := kp₂ ++ e.keyPath.drop kp₁.length } else e)
  else none

/-- An operation as the session queues it: located, with the key path of the
node's ancestors (`PendingOperation`). -/
inductive Pending where
  | add (l : Level) (kp : List Key) (k : Key) (props : Props)
  | remove (l : Level) (kp : List Key) (k : Key)
  | modify (l : Level) (kp : List Key) (k : Key) (p : String) (v : Option Val)
  | move (l : Level) (kp₁ kp₂ : List Key) (k : Key)

/-- Locate an event through the placement index `I`, the tree whose parents the
index records. Undefined when the index does not know the node or an ancestor:
the session reports the event and drops it. -/
def Tree.locate (I : Tree) : Event → Option Pending
  | .added l k p ps => (I.ancestors l p).map fun kp => .add l kp k ps
  | .removed l k =>
    (I.get (l, k)).bind fun n => (I.ancestors l n.parent).map fun kp => .remove l kp k
  | .modified l k p _ v =>
    (I.get (l, k)).bind fun n => (I.ancestors l n.parent).map fun kp => .modify l kp k p v
  | .placed l k _ b =>
    (I.get (l, k)).bind fun n => (I.ancestors l n.parent).bind fun kp₁ =>
      (I.ancestors l (some b)).map fun kp₂ => .move l kp₁ kp₂ k

/-- Run a located operation on the arrays. Undefined when its location is
missing: the session reports the operation and drops it. -/
def Arrays.run (A : Arrays) : Pending → Option Arrays
  | .add l kp k ps => A.addNode l kp k ps
  | .remove l kp k => A.removeNode l kp k
  | .modify l kp k p v => A.modifyNode l kp k p v
  | .move l kp₁ kp₂ k => A.moveNode l kp₁ kp₂ k

def Arrays.runAll (A : Arrays) : List Pending → Option Arrays
  | [] => some A
  | op :: ops => (A.run op).bind (·.runAll ops)

/-- The arrays hold tree `T`: they are nested, each entry with one ancestor key
per segment and its parent's entry present, and they hold the nodes of `T`.
That each entry then sits where the index locates it is a theorem
(`located`). -/
structure Arrays.Holds (A : Arrays) (T : Tree) : Prop where
  nodup : (A.map (·.id)).Nodup
  nested : ∀ e ∈ A, e.keyPath.length = e.segmentPath.length ∧ A.parentHeld e.segmentPath e.keyPath
  equiv : A.tree.Equiv T

/-! ## The session

The session holds the arrays as of the last flush, the operations queued since,
and the placement index as of the last queued operation. An operation is located
when it is queued. A flush runs the queue on the arrays in one `setState`.

The index records a node's placement before the operation is queued
(`enqueueOperation` runs `recordPlacement` first), because queueing can flush,
and the flush can call back into the session before `enqueueOperation` returns:
a subscriber may react by adding a child of the node it was just told about.

The index is modelled as the tree of queued events: `ancestors` reads only the
parents it records. -/
structure Session where
  arrays : Arrays
  queue : List Pending
  index : Tree

/-- Queue an event: locate it, record its placement, then push it. -/
def Session.enqueue (S : Session) (e : Event) : Option Session :=
  (S.index.locate e).bind fun op =>
    (S.index.apply e).map fun I => { S with queue := S.queue ++ [op], index := I }

def Session.flush (S : Session) : Option Session :=
  (S.arrays.runAll S.queue).map fun A => { S with arrays := A, queue := [] }

/-- The queue holds the events that took the flushed tree to the index, each
located against the index as it was when the event was queued. -/
inductive Replay : Tree → List Pending → Tree → Prop where
  | nil (T : Tree) : Replay T [] T
  | cons {T T₁ I : Tree} {e : Event} {op : Pending} {ops : List Pending} :
      T.apply e = some T₁ → T.locate e = some op → Replay T₁ ops I → Replay T (op :: ops) I

/-- The session invariant: the arrays hold the flushed tree, and the queue
replays it to the index. -/
def Session.Inv (S : Session) : Prop :=
  ∃ T₀, S.arrays.Holds T₀ ∧ Replay T₀ S.queue S.index

end JinagaSpec.Cascade
