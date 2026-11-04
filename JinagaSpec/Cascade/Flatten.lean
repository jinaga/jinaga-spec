import JinagaSpec.Cascade.Sig

/-!
# Cascade: `flatten` at the root

`flatten(P, C, O)` replaces each root row's array `P`, and each `P` item's array
`C`, with one array `O` of flattened rows. A flattened row is a `C` item with
its `P` parent's values, placed under the root row; it keeps the child's key,
which is unique within its level, and what was below the child stays below it.
The parent's other arrays are not kept.

A flattened row takes the parent's values for the names in `I`, the parent's
properties, and the child's values for the rest. The model ignores a child's
value for a name in `I`, so it needs no contract on its input. The TypeScript
agrees with it under two assumptions about the payloads, which the TypeScript
checks only in part:

- `I` lists every property a parent's payload carries. The TypeScript reads the
  inherited names from the parent's descriptor; a payload property the
  descriptor does not declare is inherited on add but never declared mutable,
  so it is not updated after a move.
- No child payload carries a name in `I`. jinaga/jinaga-cascade-core#38 rejects
  a name both descriptors declare, and the types reject every shared name; for
  an undeclared child property in an untyped pipeline, the TypeScript shows the
  child's value where the model shows the parent's.

Both are cases of a descriptor that does not declare every property its
payloads carry.

When a parent's value changes, every one of its flattened rows changes with it.
When a parent moves to another root row, its flattened rows move with it. When a
child moves to another parent, its row moves to the new parent's root row if
that differs, and takes on the new parent's values: the change that
jinaga/jinaga-cascade-core#30 lost.
-/
namespace JinagaSpec.Cascade

/-- A flattened row's values: the parent's for the inherited names `I`, the
child's for the rest. -/
def flattenProps (I : List String) (pp cp : Props) : Props :=
  Props.override I pp cp

/-- Where an input level goes in the output, if anywhere: `P :: C :: rest`
becomes `O :: rest`; a parent, a parent's other arrays and an input array
named `O` are not kept; every other level is unchanged. -/
def flatten.level (P C O : String) : Level → Option Level
  | [] => some []
  | x :: rest =>
    if x = O then none
    else if x = P then
      match rest with
      | y :: rest' => if y = C then some (O :: rest') else none
      | [] => none
    else some (x :: rest)

/-- The input level an output level comes from. -/
def flatten.source (P C O : String) : Level → Option Level
  | [] => some []
  | x :: rest => if x = O then some (P :: C :: rest) else if x = P then none else some (x :: rest)

/-- The parent of a child at `[P, C]`. -/
def flatten.parentOf (P : String) (T : Tree) (n : Node) : Option Node :=
  n.parent.bind fun pk => T.get ([P], pk)

def flatten.F (P C O : String) (I : List String) (T : Tree) : Tree :=
  T.filterMap fun e =>
    (flatten.level P C O e.1.1).bind fun l' =>
      if e.1.1 = [P, C] then
        (flatten.parentOf P T e.2).map fun pn => ((l', e.1.2), ⟨pn.parent, flattenProps I pn.props e.2.props⟩)
      else some ((l', e.1.2), e.2)

/-- The children of parent `k`. -/
def flatten.children (P C : String) (T : Tree) (k : Key) : List Key :=
  (T.filter fun e => e.1.1 = [P, C] ∧ e.2.parent = some k).map (·.1.2)

/-- The changes to a moved child's row: one per inherited name whose value
differs between its old parent and its new one. -/
def flatten.inheritedChanges (O : String) (I : List String) (k : Key) (pa pb : Props) : List Event :=
  (dedup I).filterMap fun x =>
    if pa x = pb x then none else some (.modified [O] k x (pa x) (pb x))

/-- `FlattenStep`. A parent's arrival and departure need nothing: it has no
children then. Its changes to inherited names, and its moves, reach each of its
children's rows. A child's arrival is a row with its parent's values; its
changes to inherited names are hidden. Every other event is relocated, or
dropped with its level. -/
def flattenStep (P C O : String) (I : List String) : Step where
  handle T e :=
    let relocate (l : Level) (ev : Level → Event) : List Event :=
      ((flatten.level P C O l).map ev).toList
    match e with
    | .added l k p ps =>
      if l = [P] then []
      else if l = [P, C] then
        match p.bind fun pk => T.get ([P], pk) with
        | some pn => [.added [O] k pn.parent (flattenProps I pn.props ps)]
        | none => []
      else relocate l fun l' => .added l' k p ps
    | .removed l k =>
      if l = [P] then [] else relocate l fun l' => .removed l' k
    | .modified l k x old new =>
      if l = [P] then
        if x ∈ I then (flatten.children P C T k).map fun c => .modified [O] c x old new else []
      else if l = [P, C] ∧ x ∈ I then []
      else relocate l fun l' => .modified l' k x old new
    | .placed l k a b =>
      if l = [P] then (flatten.children P C T k).map fun c => .placed [O] c a b
      else if l = [P, C] then
        match T.get ([P], a), T.get ([P], b) with
        | some pa, some pb =>
          (match pa.parent, pb.parent with
            | some ga, some gb => if ga = gb then [] else [.placed [O] k ga gb]
            | _, _ => []) ++
          flatten.inheritedChanges O I k pa.props pb.props
        | _, _ => []
      else relocate l fun l' => .placed l' k a b

/-- What `flatten` declares can change (its descriptor transform). A flattened
row moves when its parent or its child can. An inherited value changes when the
parent's can, or when the child can move to another parent; the child's own
values change when they could before. Every other kept level declares what its
input level did. This matches the TypeScript transform when `I` is the parent
descriptor's names and that descriptor is complete (see the header). -/
def flatten.sig (P C O : String) (I : List String) (σ : Sig) : Sig where
  mutable l x :=
    match flatten.source P C O l with
    | none => false
    | some s =>
      if s = [P, C] then (if x ∈ I then σ.mutable [P] x || σ.movable [P, C] else σ.mutable [P, C] x)
      else σ.mutable s x
  movable l :=
    match flatten.source P C O l with
    | none => false
    | some s => if s = [P, C] then σ.movable [P] || σ.movable [P, C] else σ.movable s

end JinagaSpec.Cascade
