import JinagaSpec.Cascade.Steps

/-!
# Cascade: a step within a scope

`@jinaga/cascade-core` scopes a step below the root with `.in(a)`: the step
then works on each root row's array `a` as if that array were a pipeline of its
own. `groupBy` groups each row's items apart from every other row's, `filter`
hides items of `a` with their subtrees, and `flatten` merges two levels below
`a`.

`within a o S` is root step `S` run that way. Each root row `p` is an *anchor*.
Its *view* is the subtree in its array `a`, moved to the root: level `a :: l`
becomes `l`, and the items of `a` lose their parent. The step's denotation runs
on each view, and its output goes back under the anchor in array `o`, which is
`a` unless the step renames the array, as `groupBy(G, o)` does. Each key the
denotation gives is tagged with the anchor's (`Key.tag`), so the keys of
different anchors' outputs differ, as a nested group's key in the TypeScript
includes its parent's.

An event below `a` is an event of its anchor's view. A move of a node to a
parent under another anchor takes its subtree out of one view and into the
other: the step removes it from the first, deepest nodes first, and adds it to
the second, shallowest first. Any other event passes through, except one below
`o` when `o` is not `a`: the output's `o` is the step's.

A deeper scope, `.in(a, b)`, is one `within` inside another.
-/
namespace JinagaSpec.Cascade

/-- The key of the root row node `id` is under. -/
def Tree.rootOf (T : Tree) (id : Id) : Option Key := T.walk id.1.length id.1 id.2

/-- Key `k` under anchor `p`. -/
def Key.tag (p k : Key) : Key := .list [.str "in", p, k]

/-- The root rows' keys. -/
def Tree.roots (T : Tree) : List Key := (T.filter (·.1.1 = [])).map (·.1.2)

namespace within

/-- A node at level `_ :: l`, as its view holds it: with no parent at the top. -/
def viewNode (l : Level) (n : Node) : Node := ⟨if l = [] then none else n.parent, n.props⟩

/-- A node below array `a`, as its view holds it: one level up, and with no
parent at the top. -/
def viewEntry : Id × Node → Id × Node
  | ((_ :: l, k), n) => ((l, k), viewNode l n)
  | e => e

/-- Whether node `id` is below array `a` of anchor `p`. -/
def under (a : String) (T : Tree) (p : Key) (id : Id) : Bool :=
  id.1.head? == some a && T.rootOf id == some p

/-- Anchor `p`'s view: its subtree in array `a`, at the root. -/
def view (a : String) (T : Tree) (p : Key) : Tree :=
  (T.filter (under a T p ·.1)).map viewEntry

/-- A view's node at level `l`, back under anchor `p`. -/
def embedNode (p : Key) (l : Level) (n : Node) : Node :=
  ⟨if l = [] then some p else n.parent.map (Key.tag p), n.props⟩

/-- A view's node, back under anchor `p` in array `o`. -/
def embedEntry (o : String) (p : Key) : Id × Node → Id × Node
  | ((l, k), n) => ((o :: l, Key.tag p k), embedNode p l n)

def embed (o : String) (p : Key) (U : Tree) : Tree := U.map (embedEntry o p)

/-- A view's event, back under anchor `p` in array `o`. -/
def embedEvent (o : String) (p : Key) : Event → Event
  | .added l k q ps => .added (o :: l) (Key.tag p k) (if l = [] then some p else q.map (Key.tag p)) ps
  | .removed l k => .removed (o :: l) (Key.tag p k)
  | .modified l k x u v => .modified (o :: l) (Key.tag p k) x u v
  | .placed l k x y => .placed (o :: l) (Key.tag p k) (Key.tag p x) (Key.tag p y)

/-- Whether `id` is outside the scope and outside the output's array `o`. -/
def outside (a o : String) (id : Id) : Bool := id.1.head? != some a && id.1.head? != some o

/-- `F` within array `a`, its output in array `o`. -/
def F (a o : String) (F : Tree → Tree) (T : Tree) : Tree :=
  T.filter (outside a o ·.1) ++ T.roots.flatMap fun p => embed o p (F (view a T p))

/-- An event below array `a`, as its view sees it. -/
def viewEvent : Event → Event
  | .added l k q ps => .added l.tail k (if l.tail = [] then none else q) ps
  | .removed l k => .removed l.tail k
  | .modified l k x u v => .modified l.tail k x u v
  | .placed l k x y => .placed l.tail k x y

/-- Step `S`'s events for the events `es` below array `a` of anchor `p`, back
under the anchor. -/
def lift (a o : String) (S : Step) (T : Tree) (p : Key) (es : List Event) : List Event :=
  (run S (view a T p) (es.map viewEvent)).map (embedEvent o p)

end within

/-- The level an event is at. -/
def Event.level : Event → Level
  | .added l .. | .removed l .. | .modified l .. | .placed l .. => l

/-- `S` within array `a`, its output in array `o`. -/
def within (a o : String) (S : Step) : Step where
  handle T e :=
    let lift := within.lift a o S T
    if e.level.head? == some a then
      match e with
      | .added l _ q _ =>
        match q.bind fun r => T.rootOf (l.dropLast, r) with
        | some p => lift p [e]
        | none => []
      | .removed l k | .modified l k .. =>
        match T.rootOf (l, k) with
        | some p => lift p [e]
        | none => []
      | .placed l k _ y =>
        match T.rootOf (l, k), T.rootOf (l.dropLast, y) with
        | some p, some p' =>
          if p = p' then lift p [e]
          else lift p (evict T (l, k)) ++
            lift p' (admit (T.update (l, k) fun n => { n with parent := some y }) (l, k))
        | _, _ => []
    else if e.level.head? == some o then [] else [e]

end JinagaSpec.Cascade
