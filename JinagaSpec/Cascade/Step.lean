import JinagaSpec.Cascade.Tree

/-!
# Cascade: steps and pipelines

A step has a *denotation*, `F : Tree → Tree`: what its output is for a given
input tree. A step's implementation reacts to one input event at a time. It
reads the input tree before the event, and emits events for its output.

A step is correct for `F` when, for every well-formed input tree `T` and every
event `e` that `apply` accepts, its events take `F T` to a tree equivalent to `F T'`, where `T'` is
`T` after `e`. That forbids emitting a stale value, losing a subtree, and
emitting an event `apply` refuses: a duplicated change, a no-op, removing a
parent before its children.

The implementation here reads the whole input tree. A TypeScript step keeps a
smaller cache instead (an aggregate per parent, the members of each group).
`Cache.lean` models those caches and proves that they emit the same events.
-/
namespace JinagaSpec.Cascade

structure Step where
  /-- The events to emit for input event `e` arriving at input tree `T`. -/
  handle : Tree → Event → List Event

/-- `F` maps well-formed trees to well-formed trees, and equivalent trees to
equivalent trees. -/
structure Denotation (F : Tree → Tree) : Prop where
  wf : ∀ T : Tree, T.WF → (F T).WF
  equiv : ∀ T U : Tree, T.WF → U.WF → T.Equiv U → (F T).Equiv (F U)

def Correct (S : Step) (F : Tree → Tree) : Prop :=
  ∀ (T : Tree) e T', T.WF → T.apply e = some T' →
    ∃ U, (F T).applyAll (S.handle T e) = some U ∧ U.Equiv (F T')

/-- Run a step over a sequence of input events from input tree `T`. It stops
at the first event `apply` refuses. -/
def run (S : Step) : Tree → List Event → List Event
  | _, [] => []
  | T, e :: es =>
    match T.apply e with
    | some T' => S.handle T e ++ run S T' es
    | none => []

/-- Two steps in sequence. The second runs over the first's events, starting
at the first's output tree. -/
def Step.andThen (S₁ S₂ : Step) (F₁ : Tree → Tree) : Step where
  handle T e := run S₂ (F₁ T) (S₁.handle T e)

end JinagaSpec.Cascade
