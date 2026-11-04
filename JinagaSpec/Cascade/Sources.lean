import JinagaSpec.Cascade.Step

/-!
# Cascade: named sources

A pipeline can read more than one input. The TypeScript names them (`sources`),
and `enrich` reads another pipeline's output as one. The model gives each source
its own tree: a node is addressed by its source, its level and its key, and an
event names the source it happens in. Each source's tree is an ordinary `Tree`,
so a single-source step and its proofs apply to it unchanged.

Each source runs its own pipeline (`liftD`): the step for that source sees only
its tree. A *join* reads every source and emits the events of one tree; `enrich`
is one. Events from different sources interleave in one stream, so the order
theorems cover interleaving as they cover any other order of arrival.
-/
namespace JinagaSpec.Cascade

abbrev Source := String

/-- One tree per source. -/
abbrev Forest := Source → Tree

/-- An event in a named source. -/
abbrev SEvent := Source × Event

/-- `F` with source `s`'s tree replaced. -/
def Forest.set (F : Forest) (s : Source) (T : Tree) : Forest :=
  fun s' => if s' = s then T else F s'

def Forest.apply (F : Forest) (e : SEvent) : Option Forest :=
  ((F e.1).apply e.2).map (F.set e.1)

def Forest.applyAll (F : Forest) : List SEvent → Option Forest
  | [] => some F
  | e :: es => (F.apply e).bind (·.applyAll es)

def Forest.WF (F : Forest) : Prop := ∀ s, (F s).WF

/-- Two forests hold the same nodes in every source. -/
def Forest.Equiv (F G : Forest) : Prop := ∀ s, (F s).Equiv (G s)

/-! ## Each source's own pipeline -/

/-- Run each source's step on its own tree. -/
def Step.lift (P : Source → Step) : Forest → SEvent → List SEvent :=
  fun F e => ((P e.1).handle (F e.1) e.2).map (e.1, ·)

/-- Each source's denotation, on its own tree. -/
def liftD (D : Source → Tree → Tree) (F : Forest) : Forest := fun s => D s (F s)

/-! ## Joins -/

/-- A step that reads every source and emits the events of one tree. -/
structure Join where
  handle : Forest → SEvent → List Event

/-- A join is correct for `G` when its events take `G F` to `G F'` for every
event that takes the sources from `F` to `F'`. -/
def JCorrect (J : Join) (G : Forest → Tree) : Prop :=
  ∀ (F : Forest) e F', F.WF → F.apply e = some F' →
    ∃ U, (G F).applyAll (J.handle F e) = some U ∧ U.Equiv (G F')

/-- `G` takes well-formed sources to a well-formed tree, and equivalent sources
to equivalent trees. -/
structure JDenotation (G : Forest → Tree) : Prop where
  wf : ∀ F : Forest, F.WF → (G F).WF
  equiv : ∀ F H : Forest, F.WF → H.WF → F.Equiv H → (G F).Equiv (G H)

/-- Run a join over a sequence of source events. -/
def Join.run (J : Join) : Forest → List SEvent → List Event
  | _, [] => []
  | F, e :: es =>
    match F.apply e with
    | some F' => J.handle F e ++ J.run F' es
    | none => []

/-- Each source's pipeline, then a join over their outputs. -/
def Join.after (J : Join) (P : Source → Step) (D : Source → Tree → Tree) : Join where
  handle F e := J.run (liftD D F) (Step.lift P F e)

/-- A join, then a step over its output. -/
def Join.andThen (J : Join) (S : Step) (G : Forest → Tree) : Join where
  handle F e := Cascade.run S (G F) (J.handle F e)

end JinagaSpec.Cascade
