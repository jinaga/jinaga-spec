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
   top-level labels, so the results do not change, provided no lifted label
   has the name of another (the parser lets a later match reuse a name an
   existential condition declared: jinaga/jinaga.js#343).
2. **Order from the new fact.** Bind first whatever path conditions reach from
   `__f`, then the givens, then whatever reaches from those. Each match leads
   with the path condition that reached it, reversed if it was written on the
   other match (a path condition says two walks meet, which is symmetric).
   Every other condition moves to the first match at which every label it
   names is bound.

Because the subscription's givens are bound, every match of a specification
that names its givens is reached, so nothing is refused (contrast
jinaga/jinaga.js#141, whose inverses must reach every given from the new fact).

**The result is checked, not trusted.** `arranges` checks that the reordered
matches bind the same unknowns, once each, carry the same conditions (each
possibly reversed or moved), and bind every label before it is used.
`reorderOrSelf` keeps the original inverse when the check fails, so it is
correct whatever `orderFromPin` does (`Proofs/Reorder.lean`); how often it
falls back is measured by `check-inverse`.
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

mutual
  /-- Lift the matches of every existential condition that holds the pin into
  the list, after the match that held it. -/
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
        if pinnedMatches ms then (keep, flattenMatches ms ++ lifted)
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

/-- An edge that reaches `u` from a label in `reach`: the edge as it is
pending, and as it is written on `u`. -/
def reaching (reach : List Name) (u : Name) (e : Edge) : Option (Edge × Edge) :=
  if e.1 == u && reach.contains e.2.labelRight then some (e, e)
  else if e.2.labelRight == u && reach.contains e.1 then some (e, e.reverse)
  else none

/-- Bind `u`, leading with `lead` (pending as `lead.1`, written as `lead.2`),
and attach every edge and filter whose labels are now all bound. -/
def place (bound : List Name) (p : Pending) (u : Label) (lead : Edge × Edge) : Pending × Match :=
  let bound := u.name :: bound
  let ready (e : Edge) := bound.contains e.1 && bound.contains e.2.labelRight
  let edges := p.edges.erase lead.1
  let attached := edges.filter ready
  let filters := p.filters.filter fun c => c.freeLabels.all bound.contains
  let conditions := (lead.2 :: attached.map fun e => if e.1 == u.name then e else e.reverse).map (.path ·.2)
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

/-! ## Checking the result -/

mutual
  /-- `ScopedMatches`, decided: every path condition names a label in scope. -/
  def isScopedMatches : List Name → List Match → Bool
    | _, [] => true
    | scope, .mk u cs :: rest =>
      isScopedConditions (u.name :: scope) scope cs && isScopedMatches (u.name :: scope) rest

  def isScopedConditions (inner outer : List Name) : List Condition → Bool
    | [] => true
    | c :: cs => isScopedCondition inner outer c && isScopedConditions inner outer cs

  def isScopedCondition (inner outer : List Name) : Condition → Bool
    | .path pc => outer.contains pc.labelRight
    | .existential _ ms => isScopedMatches inner ms
end

/-- The same condition: as written, or a path condition reversed onto its
other end, or an existential condition moved to another match (an existential
condition does not read the match it is written on). -/
def sameConstraint : Name × Condition → Name × Condition → Bool
  | (u1, .path pc), (u2, .path pc2) =>
    (u1 == u2 && pc == pc2) || (u2 == pc.labelRight && Edge.reverse (u1, pc) == (u2, pc2))
  | (_, c1), (_, c2) => c1 == c2

def constraints (ms : List Match) : List (Name × Condition) :=
  ms.flatMap fun m => m.conditions.map (m.unknown.name, ·)

/-- Binds each unknown once, none of them in `scope`, and names only labels
already bound. -/
def bindsOnce (scope : List Name) (ms : List Match) : Bool :=
  let names := ms.map (·.unknown.name)
  (names.Nodup : Bool) && names.all (!scope.contains ·) && isScopedMatches scope ms

/-- Every condition of `ms1` is a condition of `ms2`. -/
def covers (ms1 ms2 : List Match) : Bool :=
  (constraints ms1).all fun c => (constraints ms2).any (sameConstraint c ·)

/-- `ms2` is an arrangement of `ms1`, starting from `scope`: the same unknowns,
each bound once, and the same conditions, each possibly reversed or moved. -/
def arranges (scope : List Name) (ms1 ms2 : List Match) : Bool :=
  bindsOnce scope ms1 && bindsOnce scope ms2 &&
    (ms1.map (·.unknown)).all (ms2.map (·.unknown)).contains &&
    (ms2.map (·.unknown)).all (ms1.map (·.unknown)).contains &&
    covers ms1 ms2 && covers ms2 ms1

/-- An inverse, reordered to start at the new fact. -/
def reorder (i : Specification) : Option Specification :=
  let givens := (i.given.map (·.name)).filter (· != pinLabel)
  (orderFromPin givens (flattenMatches i.matchList)).map fun ms => { i with matchList := ms }

/-- The reordered inverse, if it checks. -/
def reorderChecked (i : Specification) : Option Specification :=
  let scope := pinLabel :: (i.given.map (·.name)).filter (· != pinLabel)
  (reorder i).filter fun r =>
    isScopedMatches scope i.matchList && arranges scope (flattenMatches i.matchList) r.matchList &&
      i.projection.labels.all fun l => scope.contains l || (i.matchList.map (·.unknown.name)).contains l

/-- The reordered inverse when it checks, and otherwise the inverse itself. -/
def reorderOrSelf (i : Specification) : Specification := (reorderChecked i).getD i

/-! ## The whole algorithm -/

/-- The results `f` might have changed, when it arrives in `old` and the graph
is now `new`: each inverse, reordered to start at `f`, read on `new`. If `f`
is one of the subscription's own givens, it was not stored before, so the
replica read nothing then, and every result it reads now is a candidate
(jinaga.js's `givenCandidateInverse`). -/
def factCandidates (s : Specification) (env : Env) (new : Graph) (f : Fact) : List Row :=
  if s.given.any (env ·.name == some f.id) then
    s.read new env
  else
    ((inverses s).map reorderOrSelf).flatMap (·.evaluate new (pinEnv s env f))

/-- The results a batch `B` might have changed: each fact's candidates, every
one read on `g ++ B`, the graph that holds the whole batch. -/
def candidates (s : Specification) (env : Env) (g : Graph) (B : List Fact) : List Row :=
  B.flatMap (factCandidates s env (g ++ B))

end JinagaSpec
