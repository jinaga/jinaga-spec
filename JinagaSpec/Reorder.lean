import JinagaSpec.Candidates

/-!
# Layer 4: start each inverse at the new fact

An inverse from `Candidates.lean` keeps the original specification's order, so
reading it starts at the subscription's givens: a pin inside an existential
condition is checked once per row of the collection. This rewrites each
inverse so that reading starts at the new fact and walks to its row:

1. **Flatten the path.** Each existential condition the path passes through is
   `exists` and holds the pin. Its matches become ordinary matches, right after
   the match that held it. The specification's own projection names only its
   top-level labels, so the results do not change. A lifted label is renamed
   (`liftLabel`): the parser scopes an existential condition's labels to the
   condition, so a later match may reuse the name (jinaga/jinaga.js#343).
2. **Order from the new fact.** Bind first whatever path conditions reach from
   `__f`, then the givens, then whatever reaches from those. Each match leads
   with the path condition that reached it, reversed if it was written on the
   other match (a path condition says two walks meet, which is symmetric).
   Every other condition moves to the first match at which every label it
   names is bound.

Because the subscription's givens are bound, every match of a specification
that names its givens is reached, so nothing is refused (contrast
jinaga/jinaga.js#141, whose inverses must reach every given from the new fact).
-/
namespace JinagaSpec

/-! ## Flattening the path -/

mutual
  def pinnedMatches : List Match → Bool
    | [] => false
    | .mk _ cs :: rest => pinnedConditions cs || pinnedMatches rest

  def pinnedConditions : List Condition → Bool
    | [] => false
    | c :: cs => pinnedCondition c || pinnedConditions cs

  /-- The condition is the pin, or an existential condition the path passes through. -/
  def pinnedCondition : Condition → Bool
    | .path pc => pc == { rolesLeft := [], labelRight := pinLabel, rolesRight := [] }
    | .existential _ ms => pinnedMatches ms
end

/-- What a lifted label is renamed to. Reserved, so it cannot collide with a
label the specification declares, and distinct from `pinLabel`. -/
def liftLabel (n : Name) : Name := "__l" ++ n

def renameLabel (names : List Name) (n : Name) : Name := if names.contains n then liftLabel n else n

mutual
  /-- Rename `names`, wherever they are declared or named. -/
  def renameMatches (names : List Name) : List Match → List Match
    | [] => []
    | .mk u cs :: rest =>
      .mk { u with name := renameLabel names u.name } (renameConditions names cs) :: renameMatches names rest

  def renameConditions (names : List Name) : List Condition → List Condition
    | [] => []
    | c :: cs => renameCondition names c :: renameConditions names cs

  def renameCondition (names : List Name) : Condition → Condition
    | .path pc => .path { pc with labelRight := renameLabel names pc.labelRight }
    | .existential e ms => .existential e (renameMatches names ms)
end

mutual
  /-- Lift the matches of every existential condition that holds the pin into
  the list, after the match that held it, renamed so that no later label of the
  same name captures them. -/
  def flattenMatches : List Match → List Match
    | [] => []
    | .mk u cs :: rest =>
      let (keep, lifted) := flattenConditions cs
      .mk u keep :: lifted ++ flattenMatches rest

  def flattenConditions : List Condition → List Condition × List Match
    | [] => ([], [])
    | c :: cs =>
      let (keep, lifted) := flattenConditions cs
      match c with
      | .existential true ms =>
        if pinnedMatches ms then (keep, renameMatches (ms.map (·.unknown.name)) (flattenMatches ms) ++ lifted)
        else (c :: keep, lifted)
      | c => (c :: keep, lifted)
end

/-! ## Ordering from the new fact -/

/-- A path condition written on `home`. -/
abbrev Edge := Name × PathCondition

/-- The edge, written on the other end: `r->R = u->L` instead of `u->L = r->R`. -/
def Edge.reverse : Edge → Edge
  | (u, pc) => (pc.labelRight, { rolesLeft := pc.rolesRight, labelRight := u, rolesRight := pc.rolesLeft })

/-- Every label an existential condition names from outside itself. -/
def Condition.freeLabels : Condition → List Name
  | .path pc => [pc.labelRight]
  | .existential _ ms => freeInMatches (ms.map (·.unknown.name)) ms

/-- What is left to place: matches not yet bound, edges not yet attached, and
existential conditions not yet attached. -/
structure Pending where
  labels : List Label
  edges : List Edge
  filters : List Condition

/-- An edge that reaches `u` from a label in `reach`, written on `u`. -/
def reaching (reach : List Name) (u : Name) (e : Edge) : Option Edge :=
  if e.1 == u && reach.contains e.2.labelRight then some e
  else if e.2.labelRight == u && reach.contains e.1 then some e.reverse
  else none

/-- Bind `u`, leading with `lead`, and attach every edge and filter whose
labels are now all bound. -/
def place (bound : List Name) (p : Pending) (u : Label) (lead : Edge) : Pending × Match :=
  let bound := u.name :: bound
  let ready (e : Edge) := bound.contains e.1 && bound.contains e.2.labelRight
  let edges := p.edges.erase lead
  let attached := edges.filter ready
  let filters := p.filters.filter fun c => c.freeLabels.all bound.contains
  let conditions := (lead :: attached.map fun e => if e.1 == u.name then e else e.reverse).map (.path ·.2)
  ({ labels := p.labels.erase u, edges := edges.filter (!ready ·),
     filters := p.filters.filter fun c => !c.freeLabels.all bound.contains },
   .mk u (conditions ++ filters))

/-- Place the first pending match that an edge reaches from `reach`; `none`
when none does. Everything in `bound` is bound, whether or not it reaches. -/
def step (reach bound : List Name) (p : Pending) : Option (Label × Pending × Match) :=
  p.labels.findSome? fun u => (p.edges.findSome? (reaching reach u.name)).map fun lead =>
    (u, place bound p u lead)

/-- Place matches while any is reached, at most `n` of them. -/
def grow (reach bound : List Name) (p : Pending) : Nat → List Name × Pending × List Match
  | 0 => (bound, p, [])
  | n + 1 =>
    match step reach bound p with
    | none => (bound, p, [])
    | some (u, p', m) =>
      let (bound', p'', ms) := grow (u.name :: reach) (u.name :: bound) p' n
      (bound', p'', m :: ms)

/-- Reorder a flat list of matches: first what the new fact reaches, then what
the givens reach. The givens are bound throughout. -/
def orderFromPin (givens : List Name) (ms : List Match) : Option (List Match) :=
  let p : Pending := {
    labels := ms.map (·.unknown),
    edges := ms.flatMap fun m => m.conditions.filterMap fun
      | .path pc => some (m.unknown.name, pc)
      | .existential .. => none,
    filters := ms.flatMap fun m => m.conditions.filter (!·.isPath) }
  let (bound, p, fromPin) := grow [pinLabel] (pinLabel :: givens) p ms.length
  let (_, p, fromGivens) := grow bound bound p ms.length
  if p.labels.isEmpty && p.edges.isEmpty && p.filters.isEmpty then some (fromPin ++ fromGivens) else none

/-- An inverse, reordered to start at the new fact. -/
def reorder (i : Specification) : Option Specification :=
  let givens := (i.given.map (·.name)).filter (· != pinLabel)
  (orderFromPin givens (flattenMatches i.matchList)).map fun ms => { i with matchList := ms }

end JinagaSpec
