import JinagaSpec.Cascade.Steps

/-!
# Cascade: the steps' caches

A step in `Steps.lean` reads its whole input tree. A TypeScript step cannot: it
keeps a smaller cache, updates it as events arrive, and reads only the cache.
`groupBy` keeps each row's grouping values and each group's size; an aggregate
keeps each item's parent and values, and each parent's count and total;
`defineProperty` keeps each node's values and its computed one.

`Cached` is a step that reads only its cache. It *implements* a tree step when
some relation `R` between caches and trees holds of the empty cache and the
empty tree, and, whenever `R c T` holds and `T` accepts an event, the cached step
emits exactly what the tree step emits, and its new cache is related to the new
tree. Then the two steps emit the same events for any input the protocol
accepts (`implements_run`), so every theorem about the tree step holds of the
cached one.

The caches here are written to be read next to the TypeScript, as maps from keys
to values, and refresh what the TypeScript refreshes: an aggregate's snapshot of
a child only for the aggregated property, `defineProperty`'s only for the
properties the caller lists. `filter` is not here: its TypeScript cache is the
complete state of every node at or below its scope, which is the tree itself.

What is proved is that each cache implements the model's step. Two differences
between the model's steps and the TypeScript's are outside it. A TypeScript step
notifies its own listener before passing an event on, so it emits a derived
change before the event that caused it (`defineProperty`'s new value before the
dependency's change, an aggregate's before the child's event); the model emits
them the other way round. The two events are at different nodes or properties,
so either order should take the output to the same tree; that swap is not proved
here. And a step that defines a
property hides that property's upstream value and changes; the TypeScript
aggregate passes them through, which only matters when an upstream step already
defines a property of the same name.
-/
namespace JinagaSpec.Cascade

noncomputable section

/-- A step that reads only its own cache. -/
structure Cached (C : Type) where
  init : C
  handle : C → Event → C × List Event

/-- Run a cached step over a sequence of events. It checks nothing: it relies
on the protocol. -/
def Cached.run {C : Type} (K : Cached C) : C → List Event → List Event
  | _, [] => []
  | c, e :: es => (K.handle c e).2 ++ K.run (K.handle c e).1 es

/-- Cached step `K` implements tree step `S`, with `R c T` saying that cache `c`
describes input tree `T`. -/
structure Implements {C : Type} (K : Cached C) (S : Step) (R : C → Tree → Prop) : Prop where
  init : R K.init []
  step : ∀ c T e T', R c T → T.WF → T.apply e = some T' →
    (K.handle c e).2 = S.handle T e ∧ R (K.handle c e).1 T'

/-- A map from keys, as the TypeScript's `Map`. -/
def Map.set {α : Type} (m : Key → α) (k : Key) (v : α) : Key → α :=
  fun k' => if k' = k then v else m k'

/-! ## `groupBy` at the root -/

/-- A row's grouping values, as `pickGroupingValues` keeps them. -/
def pick (G : List String) (ps : Props) : Props := fun q => if q ∈ G then ps q else none

/-- `trackedItems` (the grouping values of each root row) and `groupSizes`. -/
structure GroupCache where
  rows : Key → Option Props
  sizes : Key → Nat

/-- `GroupByStep`: the group of a row is its grouping values; a group is added
with its first member and removed with its last, which the sizes tell. -/
def groupBy.cached (G : List String) (C : String) : Cached GroupCache where
  init := ⟨fun _ => none, fun _ => 0⟩
  handle c e := match e with
    | .added [] k _ ps =>
      let vs := pick G ps
      let g := groupKey G vs
      (⟨Map.set c.rows k (some vs), Map.set c.sizes g (c.sizes g + 1)⟩,
        (if 0 < c.sizes g then [] else [.added [] g none (groupProps G g)]) ++
          [.added [C] k (some g) (omitProps G ps)])
    | .added l k p ps => (c, [.added (C :: l) k p ps])
    | .removed [] k =>
      match c.rows k with
      | some vs =>
        let g := groupKey G vs
        let s := c.sizes g - 1
        (⟨Map.set c.rows k none, Map.set c.sizes g s⟩,
          .removed [C] k :: (if 0 < s then [] else [.removed [] g]))
      | none => (c, [])
    | .removed l k => (c, [.removed (C :: l) k])
    | .modified [] k p old new =>
      match c.rows k with
      | some vs =>
        if p ∈ G then
          let vs' := vs.set p new
          let g := groupKey G vs
          let g' := groupKey G vs'
          -- The sizes without this row.
          let rest := fun x => c.sizes x - (if x = g then 1 else 0)
          (⟨Map.set c.rows k (some vs'), fun x => rest x + (if x = g' then 1 else 0)⟩,
            (if 0 < rest g' then [] else [.added [] g' none (groupProps G g')]) ++
              [.placed [C] k g g'] ++
              (if 0 < rest g then [] else [.removed [] g]))
        else (c, [.modified [C] k p old new])
      | none => (c, [])
    | .modified l k p old new => (c, [.modified (C :: l) k p old new])
    | .placed l k a b => (c, [.placed (C :: l) k a b])

/-- Whether entry `e` is a root row of group `g`: what `hasMember` looks for. -/
def isMember (G : List String) (g : Key) (e : Id × Node) : Bool :=
  e.1.1.isEmpty && groupKey G e.2.props == g

/-- The cache describes the tree: each root row's grouping values, and each
group's number of root rows. -/
structure GroupCache.Describes (G : List String) (c : GroupCache) (T : Tree) : Prop where
  rows : ∀ k, c.rows k = (T.get ([], k)).map (pick G ·.props)
  sizes : ∀ g, c.sizes g = T.countP (isMember G g)

/-- Apply changes to values, last first. A cache that tracks only some
properties knows a node's values up to changes to the others. -/
def Props.setAll (ps : Props) (changes : List (String × Option Val)) : Props :=
  changes.foldr (fun x ps => ps.set x.1 x.2) ps

/-! ## `sum` and `count` -/

/-- `CommutativeAggregateStep`'s cache: each child's parent and a snapshot of
its values (`items`), and each parent's number of contributing children
(`contributorCounts`) and their total (`aggregateValues`). The snapshot is
refreshed only for the tracked properties: the aggregated one, when it is
mutable. -/
structure AggCache where
  items : Key → Option (Key × Props)
  count : Key → Nat
  total : Key → Int

/-- A parent's aggregate: absent while no child contributes. -/
def AggCache.value (a : AggCache) (r : Key) : Option Val :=
  if a.count r = 0 then none else some (.int (a.total r))

/-- Take a child's contribution from parent `r`. -/
def AggCache.withdraw (contributes : Props → Bool) (w : Props → Int) (a : AggCache) (r : Key)
    (ps : Props) : AggCache :=
  if contributes ps then
    { a with count := Map.set a.count r (a.count r - 1), total := Map.set a.total r (a.total r - w ps) }
  else a

/-- Give a child's contribution to parent `r`. -/
def AggCache.deposit (contributes : Props → Bool) (w : Props → Int) (a : AggCache) (r : Key)
    (ps : Props) : AggCache :=
  if contributes ps then
    { a with count := Map.set a.count r (a.count r + 1), total := Map.set a.total r (a.total r + w ps) }
  else a

/-- `CommutativeAggregateStep`: each child's contribution moves with it; a parent
whose aggregate changed is told so. A change to an untracked property is not
seen. -/
def aggregate.cached (c : Level) (q : String) (contributes : Props → Bool) (w : Props → Int)
    (tracked : List String) : Cached AggCache where
  init := ⟨fun _ => none, fun _ => 0, fun _ => 0⟩
  handle a e :=
    let touch (a' : AggCache) (r : Key) : List Event :=
      if a.value r = a'.value r then [] else [.modified c.dropLast r q (a.value r) (a'.value r)]
    let withdraw := AggCache.withdraw contributes w
    let deposit := AggCache.deposit contributes w
    match e with
    | .added l k p ps =>
      if l = c.dropLast then (a, [.added l k p (ps.set q (a.value k))])
      else if l = c then
        match p with
        | some r =>
          let a' := { deposit a r ps with items := Map.set a.items k (some (r, ps)) }
          (a', .added l k p ps :: touch a' r)
        | none => (a, [.added l k p ps])
      else (a, [.added l k p ps])
    | .removed l k =>
      if l = c then
        match a.items k with
        | some (r, ps) =>
          let a' := { withdraw a r ps with items := Map.set a.items k none }
          (a', .removed l k :: touch a' r)
        | none => (a, [.removed l k])
      else (a, [.removed l k])
    | .modified l k p old new =>
      if l = c.dropLast ∧ p = q then (a, [])
      else if l = c then
        match a.items k with
        | some (r, ps) =>
          if p ∈ tracked then
            let ps' := ps.set p new
            let a' := { deposit (withdraw a r ps) r ps' with items := Map.set a.items k (some (r, ps')) }
            (a', .modified l k p old new :: touch a' r)
          else (a, [.modified l k p old new])
        | none => (a, [.modified l k p old new])
      else (a, [.modified l k p old new])
    | .placed l k x y =>
      if l = c then
        match a.items k with
        | some (r, ps) =>
          let a' := { deposit (withdraw a r ps) y ps with items := Map.set a.items k (some (y, ps)) }
          (a', .placed l k x y :: (touch a' x ++ touch a' y))
        | none => (a, [.placed l k x y])
      else (a, [.placed l k x y])

/-- The cache describes the tree: each child's parent, with a snapshot of its
values that differs from them only by changes to untracked properties, and each
parent's contributing children's number and total. -/
structure AggCache.Describes (c : Level) (contributes : Props → Bool) (w : Props → Int)
    (tracked : List String) (a : AggCache) (T : Tree) : Prop where
  absent : ∀ k, ((T.get (c, k)).bind (·.parent)) = none → a.items k = none
  present : ∀ k n r, T.get (c, k) = some n → n.parent = some r → ∃ known changes,
    a.items k = some (r, known) ∧ (∀ x ∈ changes, x.1 ∉ tracked) ∧ n.props = known.setAll changes
  count : ∀ r, a.count r = (contributors c contributes T r).length
  total : ∀ r, a.total r = ((contributors c contributes T r).map (w ·.2.props)).sum

/-! ## `defineProperty` -/

/-- `DefinePropertyStep`'s `itemStates`: each node's values as the step knows
them (its values when added, with changes to the properties the caller lists),
and its computed value. -/
structure DefineCache where
  items : Key → Option (Props × Option Val)

/-- `DefinePropertyStep`: a node arrives with its computed value. A change to a
listed property recomputes it from the values the step knows, and is reported if
the value changed. -/
def defineProperty.cached (s : Level) (q : String) (f : Props → Option Val) (deps : List String) :
    Cached DefineCache where
  init := ⟨fun _ => none⟩
  handle d e := match e with
    | .added l k p ps =>
      if l = s then
        let v := f ps
        (⟨Map.set d.items k (some (ps, v))⟩, [.added l k p (ps.set q v)])
      else (d, [.added l k p ps])
    | .removed l k =>
      if l = s then (⟨Map.set d.items k none⟩, [.removed l k]) else (d, [.removed l k])
    | .modified l k p old new =>
      if l = s then
        if p = q then (d, []) else
        match d.items k with
        | some (known, v) =>
          if p ∈ deps then
            let known' := known.set p new
            let v' := f known'
            (⟨Map.set d.items k (some (known', v'))⟩,
              .modified l k p old new :: (if v ≠ v' then [.modified l k q v v'] else []))
          else (d, [.modified l k p old new])
        | none => (d, [])
      else (d, [.modified l k p old new])
    | .placed l k a b => (d, [.placed l k a b])

/-- The cache describes the tree: each node at `s` is cached with its computed
value, and its current values are the known ones with changes to unlisted
properties only. -/
structure DefineCache.Describes (s : Level) (f : Props → Option Val) (deps : List String)
    (d : DefineCache) (T : Tree) : Prop where
  absent : ∀ k, T.get (s, k) = none → d.items k = none
  present : ∀ k n, T.get (s, k) = some n → ∃ known changes,
    d.items k = some (known, f n.props) ∧ (∀ x ∈ changes, x.1 ∉ deps) ∧
      n.props = known.setAll changes

end

end JinagaSpec.Cascade
