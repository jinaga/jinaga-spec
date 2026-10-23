import JinagaSpec.Semantics

/-!
# Inverting a specification

`invertSpecification`, ported from jinaga.js `src/specification/inverse.ts` (at
`4ebbb27`) to be read side by side with it. An *inverse* answers: when a fact of
this type arrives, which results of the original specification might it have
added or removed? It is a specification whose given is the new fact.

This port follows the TypeScript as it is today, including its known defect at
`inverse.ts:505` (jinaga/jinaga.js#338: a nested inverse keeps its enclosing
existential condition). `lake exe check-inverse` measures it before anything is
proved about it.

Differences from the TypeScript, each forced by the language rather than chosen:

* **Identity.** The TypeScript removes a condition or a match by object
  identity. Here they are removed by structural equality. The two differ only
  when one match list holds two structurally equal conditions.
* **Failure.** Where the TypeScript throws, this returns `.error`.
* **The loop in `shakeTree` is bounded.** The TypeScript loop that moves a match
  with no path condition to the bottom stops when it returns to the match it
  started from, and throws. Rotating a list's suffix of length `k` returns to
  its first element after exactly `k` rotations, so `settle` is given `k` as
  its bound: it is total by structural recursion, and `Proofs/Inverse.lean`
  shows the bound is never what stops it.
* **Dead code.** `simplifyMatch` checks, after simplifying an existential
  condition's matches, whether any of them still expects a successor of the
  given. None can: `simplifyMatch` already returned `null` for any match with
  such a condition. That check is omitted.
* **Not ported.** Inverses of nested specifications in a projection
  (`invertProjection`), because this language's projections hold no
  specifications. Deduplication, because results are compared as sets.
-/
namespace JinagaSpec

deriving instance BEq for Condition, Match

instance : Inhabited Match := ⟨.mk { name := "", type := "" } []⟩

/-- Why a specification cannot be inverted. -/
inductive InverseError where
  | labelNotFound (label : Name)
  /-- `shakeTree` came back to the match it started from: these labels have no
  path condition joining them to the rest. -/
  | notConnected (types : List Name)
  /-- `UnionFind.ts`: the labels fall into more than one group. -/
  | disconnected
  /-- `settle` ran out of rotations. Never happens (`settle_bound`). -/
  | boundReached
deriving Repr, DecidableEq

def InverseError.message : InverseError → String
  | .labelNotFound l => s!"Label {l} not found"
  | .notConnected types => s!"The labels with types {types} are not connected to the rest of the graph"
  | .disconnected => "Disconnected specification detected"
  | .boundReached => "shakeTree: rotation bound reached"

inductive Operation where
  | add
  | remove
deriving Repr, DecidableEq

/-- When a fact of `given`'s type arrives: bind `given` to it, check `given`'s
conditions, run `matchList`, and report each result as `operation`. -/
structure Inverse where
  given : Match
  matchList : List Match
  operation : Operation

def Condition.isPath : Condition → Bool
  | .path _ => true
  | .existential .. => false

def Match.hasPath (m : Match) : Bool := m.conditions.any (·.isPath)

def findMatch (ms : List Match) (label : Name) : Except InverseError Match :=
  match ms.find? (·.unknown.name == label) with
  | some m => .ok m
  | none => .error (.labelNotFound label)

/-- Replace the first match with this name, as the TypeScript replaces the
match `findMatch` found. -/
def updateFirst (name : Name) (f : Match → Match) : List Match → List Match
  | [] => []
  | m :: rest => if m.unknown.name == name then f m :: rest else m :: updateFirst name f rest

def invertAndMovePathCondition (ms : List Match) (label : Name) (pc : PathCondition) :
    Except InverseError (List Match) := do
  let m ← findMatch ms label
  let _ ← findMatch ms pc.labelRight
  let inverted : PathCondition :=
    { rolesLeft := pc.rolesRight, labelRight := m.unknown.name, rolesRight := pc.rolesLeft }
  let ms := updateFirst label (fun x => .mk x.unknown (x.conditions.erase (.path pc))) ms
  return updateFirst pc.labelRight (fun x => .mk x.unknown (.path inverted :: x.conditions)) ms

/-- Move every path condition that joins the match at `i` from a later match
onto the match at `i`, inverted. -/
def pullTags (ms : List Match) (i : Nat) : Except InverseError (List Match) :=
  let name := (ms.getD i default).unknown.name
  (List.range' (i + 1) (ms.length - (i + 1))).foldlM (fun ms j =>
    let tagged := ms.getD j default
    tagged.conditions.foldlM (fun ms c =>
      match c with
      | .path pc => if pc.labelRight == name then invertAndMovePathCondition ms tagged.unknown.name pc else pure ms
      | .existential .. => pure ms) ms) ms

/-- Move the match at `i` to the bottom. -/
def rotateAt (ms : List Match) (i : Nat) : List Match :=
  ms.take i ++ ms.drop (i + 1) ++ (ms.drop i).take 1

/-- While the match at `i` has no path condition: give it the path conditions
that join it, move it to the bottom, and look at the match that takes its
place. `bound` is how many rotations remain before the suffix returns to
`first`. -/
def settle (ms : List Match) (i : Nat) (first : Name) : (bound : Nat) → Except InverseError (List Match)
  | 0 => .error .boundReached
  | bound + 1 =>
    if (ms.getD i default).hasPath then .ok ms else do
      let ms ← pullTags ms i
      let ms := rotateAt ms i
      if (ms.getD i default).unknown.name == first then
        .error (.notConnected ((ms.drop i).map (·.unknown.type)))
      else settle ms i first bound

/-- Put `label`'s match first, move its path conditions onto the matches they
join, and move every match left without a path condition down. -/
def shakeTree (ms : List Match) (label : Name) : Except InverseError (List Match) := do
  let m ← findMatch ms label
  let ms := m :: ms.erase m
  let ms ← m.conditions.foldlM (fun ms c =>
    match c with
    | .path pc => invertAndMovePathCondition ms label pc
    | .existential .. => pure ms) ms
  (List.range' 1 (ms.length - 1)).foldlM (fun ms i =>
    settle ms i (ms.getD i default).unknown.name (ms.length - i)) ms

/-! ## Simplifying: the new fact has no successors -/

/-- `unknown->roles = given`: a successor of the given. -/
def expectsSuccessor (given : Name) : Condition → Bool
  | .path pc => pc.labelRight == given && pc.rolesRight.isEmpty && !pc.rolesLeft.isEmpty
  | .existential .. => false

mutual
  /-- `none` when the matches cannot be satisfied with `given` bound to a fact
  that has no successors. -/
  def simplifyMatches (given : Name) : List Match → Option (List Match)
    | [] => some []
    | m :: rest => do
      let m' ← simplifyMatch given m
      let rest' ← simplifyMatches given rest
      pure (m' :: rest')

  def simplifyMatch (given : Name) : Match → Option Match
    | .mk u cs => (Match.mk u) <$> simplifyConditions given cs

  def simplifyConditions (given : Name) : List Condition → Option (List Condition)
    | [] => some []
    | c :: cs =>
      if expectsSuccessor given c then none else
      match c with
      | .path pc => (.path pc :: ·) <$> simplifyConditions given cs
      | .existential e ms =>
        match simplifyMatches given ms with
        | none => if e then none else simplifyConditions given cs
        | some ms' => (.existential e ms' :: ·) <$> simplifyConditions given cs
end

/-! ## Relocating existential conditions to where their labels are bound -/

mutual
  /-- Labels the matches name but do not bind. `inner` holds the labels bound
  around them, including their own unknowns. -/
  def freeInMatches (inner : List Name) : List Match → List Name
    | [] => []
    | .mk _ cs :: rest => freeInConditions inner cs ++ freeInMatches inner rest

  def freeInConditions (inner : List Name) : List Condition → List Name
    | [] => []
    | .path pc :: cs =>
      (if inner.contains pc.labelRight then [] else [pc.labelRight]) ++ freeInConditions inner cs
    | .existential _ ms :: cs =>
      freeInMatches (inner ++ ms.map (·.unknown.name)) ms ++ freeInConditions inner cs
end

/-- The index of the last match that binds `name`. -/
def bindingIndex (ms : List Match) (name : Name) : Option Nat :=
  (ms.zip (List.range ms.length)).foldl
    (fun acc (m, i) => if m.unknown.name == name then some i else acc) none

/-- Where a condition on the match at `i` belongs: an existential condition
moves to the last match that binds a label it names; anything else stays. -/
def relocationTarget (ms : List Match) (i : Nat) : Condition → Nat
  | .path _ => i
  | .existential _ inner =>
    ((freeInMatches (inner.map (·.unknown.name)) inner).filterMap (bindingIndex ms)).foldl max i

def relocateConditions (ms : List Match) : List Match :=
  let final := (List.range ms.length).foldl (fun byIndex i =>
    let here := byIndex.getD i []
    here.foldl (fun acc c =>
      let t := relocationTarget ms i c
      if t > i then acc.set t (acc.getD t [] ++ [c]) else acc)
      (byIndex.set i (here.filter fun c => relocationTarget ms i c ≤ i)))
    (ms.map (·.conditions))
  (ms.zip final).map fun (m, cs) => .mk m.unknown cs

/-! ## Inverting -/

def inferOperation : Operation → Bool → Operation
  | op, true => op
  | .add, false => .remove
  | .remove, false => .add

def removeCondition (ms : List Match) (c : Condition) : List Match :=
  ms.map fun m => if m.conditions.contains c then .mk m.unknown (m.conditions.filter (· != c)) else m

/-- The inverse whose given is the first of `ordered`. The given keeps only its
existential conditions. -/
def mkInverse (op : Operation) : List Match → List Inverse
  | [] => []
  | m :: rest => [{ given := .mk m.unknown (m.conditions.filter (!·.isPath)), matchList := rest, operation := op }]

/-- Shake, simplify and relocate for `label`; nothing if unsatisfiable. -/
def inverseAt (op : Operation) (ms : List Match) (label : Name) : List Inverse :=
  match simplifyMatches label ms with
  | none => []
  | some simplified => mkInverse op (relocateConditions simplified)

mutual
  /-- `invertExistentialConditions`: an inverse for each match inside each
  existential condition, with the operation that condition's polarity gives. -/
  def invertConditions (outer : List Match) (op : Operation) : List Condition → Except InverseError (List Inverse)
    | [] => pure []
    | .path _ :: cs => invertConditions outer op cs
    | .existential e inner :: cs => do
      let here ← invertInner (.existential e inner) (inferOperation op e) (outer ++ inner) inner
      let rest ← invertConditions outer op cs
      pure (here ++ rest)

  def invertInner (condition : Condition) (op : Operation) (acc : List Match) :
      List Match → Except InverseError (List Inverse)
    | [] => pure []
    | .mk u cs :: rest => do
      let acc ← shakeTree acc u.name
      let here ← match simplifyMatches u.name (removeCondition acc condition) with
        | none => pure []
        | some simplified => do
          -- `inverse.ts:505`: the recursion is given `acc`, which still holds
          -- `condition` (jinaga/jinaga.js#338).
          let nested ← invertConditions acc op cs
          pure (mkInverse op (relocateConditions simplified) ++ nested)
      let more ← invertInner condition op acc rest
      pure (here ++ more)
end

/-- `invertMatches`: an "add" inverse for each label, and the inverses of the
existential conditions on its match. Each label's shake starts from the last. -/
def invertLabels : List Match → List Label → Except InverseError (List Inverse)
  | _, [] => pure []
  | ms, l :: ls => do
    let ms ← shakeTree ms l.name
    let existential ← invertConditions ms .add ((ms.head?.map (·.conditions)).getD [])
    let more ← invertLabels ms ls
    pure (inverseAt .add ms l.name ++ existential ++ more)

/-! ## The connectivity check that runs first (`UnionFind.ts`) -/

mutual
  def referencedInMatches : List Match → List Name
    | [] => []
    | .mk _ cs :: rest => referencedInConditions cs ++ referencedInMatches rest

  def referencedInConditions : List Condition → List Name
    | [] => []
    | .path pc :: cs => pc.labelRight :: referencedInConditions cs
    | .existential _ ms :: cs => referencedInMatches ms ++ referencedInConditions cs
end

mutual
  /-- Every label, and every pair the connectivity check joins. -/
  def connectionsInMatches : List Match → List Name × List (Name × Name)
    | [] => ([], [])
    | .mk u cs :: rest =>
      let (l1, e1) := connectionsInConditions u.name cs
      let (l2, e2) := connectionsInMatches rest
      (u.name :: l1 ++ l2, e1 ++ e2)

  def connectionsInConditions (u : Name) : List Condition → List Name × List (Name × Name)
    | [] => ([], [])
    | .path pc :: cs =>
      let (l, e) := connectionsInConditions u cs
      (pc.labelRight :: l, (u, pc.labelRight) :: e)
    | .existential _ ms :: cs =>
      let (l1, e1) := connectionsInMatches ms
      let referenced := referencedInMatches ms
      let (l2, e2) := connectionsInConditions u cs
      (l1 ++ referenced ++ l2, e1 ++ referenced.map (u, ·) ++ e2)
end

/-- Every label is joined to every other, through path conditions or through
labels an existential condition names. -/
def isConnected (s : Specification) : Bool :=
  let (labels, edges) := connectionsInMatches s.matchList
  let labels := (s.given.map (·.name) ++ labels).eraseDups
  match labels with
  | [] => true
  | first :: _ =>
    let step (reached : List Name) : List Name :=
      (reached ++ edges.filterMap fun (a, b) =>
        if reached.contains a then some b else if reached.contains b then some a else none).eraseDups
    let reached := (List.range labels.length).foldl (fun r _ => step r) [first]
    labels.all reached.contains

/-- Every inverse of a specification, or why it cannot be inverted. -/
def invertSpecification (s : Specification) : Except InverseError (List Inverse) := do
  unless isConnected s do throw .disconnected
  let ms := s.given.map (fun l => Match.mk l []) ++ s.matchList
  let inverses ← invertLabels ms (s.given ++ s.matchList.map (·.unknown))
  -- `createSelfInverse`: re-read the whole specification when its one given arrives.
  let selfInverse := match s.given with
    | [g0] => [{ given := .mk g0 [], matchList := s.matchList, operation := .add }]
    | _ => []
  pure (inverses ++ selfInverse)

/-! ## What an inverse finds -/

/-- The results an inverse reports when `f` arrives in `g`, for a subscription
whose givens are bound by `env`: run the inverse from `f`, keep the solutions
that agree with the subscription's givens, and project them as the original
specification does. -/
def Inverse.fire (ι : Inverse) (s : Specification) (g : Graph) (env : Env) (f : Fact) :
    List (List (Option FactId)) :=
  let e0 : Env := Env.bind (fun _ => none) ι.given.unknown.name f.id
  if f.type == ι.given.unknown.type && allHold g e0 ι.given.unknown.name ι.given.conditions then
    ((evalMatches g e0 ι.matchList).filter fun σ => s.given.all fun l => σ l.name == env l.name).map
      fun σ => s.projection.labels.map σ
  else []

end JinagaSpec
