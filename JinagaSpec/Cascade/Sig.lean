import JinagaSpec.Cascade.Steps

/-!
# Cascade: what can change after add

A step's type descriptor says, for each level, which properties of its nodes can
change after they are added (`mutableProperties`), and whether its nodes can move
to another parent (`mutablePlacement`). The output session and the steps
downstream subscribe only to what it declares: a change it does not declare is
never heard, and the output keeps a stale value (jinaga/jinaga-cascade-core#30).

A signature is that part of a descriptor. A step *keeps* a signature `σ` as `σ'`
when every event it emits for an event `σ` declares is one `σ'` declares. So a
pipeline whose steps keep their signatures emits only events its descriptor
declares, and a consumer that subscribes to the descriptor misses nothing.

Each `….sig` here is the step's descriptor transform in TypeScript, restricted to
these two fields. Declaring more than a step emits is allowed: a subscription
that never fires costs nothing.
-/
namespace JinagaSpec.Cascade

noncomputable section

structure Sig where
  /-- Whether property `p` of a node at level `l` can change after it is added. -/
  mutable : Level → String → Bool
  /-- Whether a node at level `l` can move to another parent. -/
  movable : Level → Bool

/-- Whether signature `σ` declares an event. Adding and removing nodes needs no
declaration. -/
def Event.Declared (σ : Sig) : Event → Prop
  | .modified l _ p _ _ => σ.mutable l p = true
  | .placed l _ _ _ => σ.movable l = true
  | _ => True

/-- Whether a consumer that subscribes to what `σ` declares hears an event. The
output session registers `onModified` for each level's mutable properties, and
`onAdded`, `onRemoved` and `onPlaced` for every level. -/
def Sig.hears (σ : Sig) : Event → Bool
  | .modified l _ p _ _ => σ.mutable l p
  | _ => true

/-- Step `S` keeps `σ` as `σ'`: for an event its input accepts and `σ` declares,
every event it emits is declared by `σ'`. -/
def Keeps (S : Step) (σ σ' : Sig) : Prop :=
  ∀ T e, (T.apply e).isSome → e.Declared σ → ∀ e' ∈ S.handle T e, e'.Declared σ'

/-- The input's signature. A caller only adds and removes rows: a source value
never changes and a source row never moves. -/
def Sig.input : Sig := ⟨fun _ _ => false, fun _ => false⟩

/-- `dropProperty` removes the property from its level's mutable properties. -/
def dropProperty.sig (s : Level) (q : String) (σ : Sig) : Sig :=
  ⟨fun l p => σ.mutable l p && !(l == s && p == q), σ.movable⟩

/-- `defineProperty` declares its property mutable when the caller lists the
properties it reads. -/
def defineProperty.sig (s : Level) (q : String) (deps : List String) (σ : Sig) : Sig :=
  ⟨fun l p => σ.mutable l p || (l == s && p == q && !deps.isEmpty), σ.movable⟩

/-- An aggregate over the children at `c` is a mutable property of their parents
(`appendAggregateAt`). -/
def aggregate.sig (c : Level) (q : String) (σ : Sig) : Sig :=
  ⟨fun l p => σ.mutable l p || (l == c.dropLast && p == q), σ.movable⟩

/-- `groupBy` at the root. A group holds only its grouping values, which never
change, and never moves. A row keeps its other mutable properties, and moves to
another group when a grouping value can change. Every level below moves one
level down unchanged. -/
def groupBy.sig (G : List String) (C : String) (σ : Sig) : Sig where
  mutable
    | [], _ => false
    | c :: l, p => c == C && σ.mutable l p && !(l.isEmpty && p ∈ G)
  movable
    | [] => false
    | [c] => c == C && G.any (σ.mutable [])
    | c :: l => c == C && σ.movable l

/-- `filter` declares what its input declares. -/
def filterStep.sig (σ : Sig) : Sig := σ

end

end JinagaSpec.Cascade
