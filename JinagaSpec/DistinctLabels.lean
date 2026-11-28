import JinagaSpec.Feeds

/-!
# Renaming reused labels

`withDistinctLabels`, ported from jinaga.js `src/specification/distinct-labels.ts`
(jinaga/jinaga.js#430, as published in jinaga 6.17.2) to be read side by side
with it.

Lexical scope lets two declarations share a name when neither is in scope of
the other: sibling existential conditions, or a condition and a later match or
child specification (`WellFormed`). `buildFeeds` joins a descendant's positive
conditions into one level, where both are in scope, and the SQL a feed becomes
names its labels by name. So the feed theorems assume `DistinctLabels` of every
descendant, and this renaming establishes it (`Proofs/DistinctLabels.lean`):

* Walking each descendant in declaration order, a match that declares a name
  already declared in that descendant (a given included) takes the first of
  `name2`, `name3`, … that appears nowhere in the specification and that the
  walk has not already made, and every reference to it within its scope
  follows.
* A new name never begins with the reserved prefix: a repeated `__` name first
  loses its leading underscores (`freshBase`).
* Givens keep their names, because a caller's start facts are found by them.
* Sibling child specifications are separate descendants, so they may keep a
  shared label: each starts from what its parent declared.

Differences from the TypeScript, each forced by the language rather than
chosen:

* **State is threaded.** The TypeScript mutates two sets. Here `taken` is
  threaded through the whole walk, and `declared` through one descendant,
  restarting at each child specification from its parent's.
* **`taken` gains every declared name**, not only the names `freshName`
  makes. A name declared as itself is already in the TypeScript's `taken`,
  which starts with every label the specification declares, so the two sets
  have the same members.
* **The search is bounded.** The TypeScript tries `name2`, `name3`, … until
  one is free. Of the first `taken.length + 1` candidates one must be, since
  they are distinct, so `freshName` tries only those (`freshName_fresh`).
* **No `renamed` flag.** The TypeScript returns the specification itself when
  nothing was renamed. Renaming nothing returns an equal specification
  (`withDistinctLabels_eq_self`).
* **Givens carry no conditions** in `Specification`, so their conditions'
  labels are not collected. `reduceGivenConditions` moves them into the
  matches first.

Written in the portable subset: inductive types, total functions, structural
recursion and lists. A scope is a function from a name, as written, to the
name it now has, as an `Env` is.
-/
namespace JinagaSpec

/-- The stem of a new name: the name, or, for a reserved one, the name without
its leading underscores (`label` if nothing is left). -/
def freshBase (name : Name) : Name :=
  if isReserved name then
    let base := String.ofList (name.toList.dropWhile (· == '_'))
    if base.isEmpty then "label" else base
  else name

/-- The candidates for a new name: `base2`, `base3`, …, one more than there
are names taken, so that one of them is free. -/
def freshCandidates (taken : List Name) (name : Name) : List Name :=
  (List.range (taken.length + 1)).map fun i => freshBase name ++ toString (i + 2)

/-- The first candidate not taken. -/
def freshName (taken : List Name) (name : Name) : Name :=
  ((freshCandidates taken name).find? (!taken.contains ·)).getD (freshBase name)

/-- The walk's state: every name the specification declares or the walk has
made (`taken`), and every name declared so far in this descendant, its givens
included (`declared`). -/
structure RenameState where
  taken : List Name
  declared : List Name

/-- Declare `name`: as itself if this descendant has not declared it, or else
as a new name. -/
def RenameState.declare (st : RenameState) (name : Name) : RenameState × Name :=
  let name' := if st.declared.contains name then freshName st.taken name else name
  ({ taken := name' :: st.taken, declared := name' :: st.declared }, name')

/-- The scope `ρ`, with `old` now named `new`. -/
def renameTo (ρ : Name → Name) (old new : Name) : Name → Name :=
  fun n => if n = old then new else ρ n

mutual
  /-- Rename the matches in scope `ρ`. Returns the state, the matches, and the
  scope after them. -/
  def renameMatches (ρ : Name → Name) (st : RenameState) :
      List Match → RenameState × List Match × (Name → Name)
    | [] => (st, [], ρ)
    | .mk u cs :: rest =>
      let (st1, name) := st.declare u.name
      let inner := renameTo ρ u.name name
      let (st2, cs') := renameConditions inner ρ st1 cs
      let (st3, rest', ρ') := renameMatches inner st2 rest
      (st3, .mk { u with name } cs' :: rest', ρ')

  /-- `inner` is the scope of existential conditions, `outer` of path
  conditions. -/
  def renameConditions (inner outer : Name → Name) (st : RenameState) :
      List Condition → RenameState × List Condition
    | [] => (st, [])
    | c :: cs =>
      let (st1, c') := renameCondition inner outer st c
      let (st2, cs') := renameConditions inner outer st1 cs
      (st2, c' :: cs')

  def renameCondition (inner outer : Name → Name) (st : RenameState) :
      Condition → RenameState × Condition
    | .path pc => (st, .path { pc with labelRight := outer pc.labelRight })
    | .existential e ms =>
      let (st1, ms', _) := renameMatches inner st ms
      (st1, .existential e ms')
end

mutual
  /-- Rename a projection in scope `ρ`, after a descendant that declared
  `declared`. Each child specification begins a descendant of its own, from
  `declared`. Only `taken` goes on from one child to the next. -/
  def renameProjection (ρ : Name → Name) (declared : List Name) (taken : List Name) :
      Projection → List Name × Projection
    | .fact label => (taken, .fact (ρ label))
    | .composite cs =>
      let (taken', cs') := renameComponents ρ declared taken cs
      (taken', .composite cs')

  def renameComponents (ρ : Name → Name) (declared : List Name) (taken : List Name) :
      List Component → List Name × List Component
    | [] => (taken, [])
    | c :: cs =>
      let (taken1, c') := renameComponent ρ declared taken c
      let (taken2, cs') := renameComponents ρ declared taken1 cs
      (taken2, c' :: cs')

  def renameComponent (ρ : Name → Name) (declared : List Name) (taken : List Name) :
      Component → List Name × Component
    | .fact name label => (taken, .fact name (ρ label))
    | .specification name ms p =>
      let (st, ms', ρ') := renameMatches ρ { taken, declared } ms
      let (taken', p') := renameProjection ρ' st.declared st.taken p
      (taken', .specification name ms' p')
end

/-- Every label the specification declares, anywhere, and its givens. -/
def Specification.labelsOf (s : Specification) : List Name :=
  s.given.map (·.name) ++ s.descendants.flatMap fun d => declaredMatches d.matchList

/-- The specification with its repeated declarations renamed, so that each of
its descendants declares every label once. -/
def withDistinctLabels (s : Specification) : Specification :=
  let givens := s.given.map (·.name)
  let (st, ms, ρ) := renameMatches id { taken := s.labelsOf, declared := givens } s.matchList
  let (_, p) := renameProjection ρ st.declared st.taken s.projection
  { s with matchList := ms, projection := p }

end JinagaSpec
