import JinagaSpec.Split
import JinagaSpec.Proofs.Scoped

/-!
# Splitting a specification, reaching into existential conditions

`splitBeforeFirstSuccessor`. The graph can run a *head* of predecessor walks. A
*tail* needs the store. The split cuts at the first match the graph cannot run,
which is the *pivot*, and reaches into the tail's existential conditions, at
any depth, not only the pivot's own top level, hoisting into the head every
path condition that walks predecessors of a label already in scope at the
pivot, wherever doing so is sound.

Formulation D of jinaga/jinaga.js#231 is a rule whose tail's existential
condition walks predecessors of the given: the given is used after the first
successor join, so `tailReadsGiven` refuses it (`Store.lean`) unless that walk
is hoisted into the head.

Not every such condition can be hoisted soundly. Under a positive existential,
an existential over a union is the union of the existentials, and the head's
enumeration of split labels is a union, so hoisting agrees. Under a negative
existential this can fail when the walk is multi-valued: the split evaluates
the negative existential once per value the walk could take, and excludes the
pivot's solution if *any* of them witnesses it, where the original evaluates it
once, against the whole set (`docs/findings.md`). The split only hoists a
condition at positive polarity: *not enclosed by any negative existential*,
however deep. Polarity is not simply the parity of the enclosing negations
(`docs/findings.md` records a second counterexample, found by the randomized
check, where two nested negative existentials cancel by parity but still
disagree, because a condition in the outer one and a condition in the inner
one share a multi-valued label): once a walk is beneath one negative
existential, it stays ineligible beneath everything nested inside it, however
many further negations follow.

Written in the same portable subset as `Split.lean`: inductive types, total
pure functions, structural recursion, and lists. No tactics, no dependent type.
-/
namespace JinagaSpec

mutual
  /-- Walk a list of matches at polarity `pos`, hoisting every eligible path
  condition. Returns the next free split-label index, the head matches the
  hoisted conditions produce, and the rewritten matches. -/
  def hoistMatches (scope : List Name) : Nat → Bool → List Match → Nat × List Match × List Match
    | i, _, [] => (i, [], [])
    | i, pos, .mk u cs :: rest =>
      let (i1, headCs, cs') := hoistConditions scope i pos cs
      let (i2, headRest, rest') := hoistMatches scope i1 pos rest
      (i2, headCs ++ headRest, .mk u cs' :: rest')

  def hoistConditions (scope : List Name) : Nat → Bool → List Condition → Nat × List Match × List Condition
    | i, _, [] => (i, [], [])
    | i, pos, c :: cs =>
      let (i1, headC, c') := hoistCondition scope i pos c
      let (i2, headCs, cs') := hoistConditions scope i1 pos cs
      (i2, headC ++ headCs, c' :: cs')

  /-- A path condition is hoisted when it walks predecessors (`rolesRight` is
  non-empty) of a label already in scope at the pivot, and it sits at positive
  polarity. Polarity is monotone: a negative existential makes its matches
  negative regardless of the polarity outside it, and once negative, nothing
  nested inside recovers positive polarity, however many further existentials
  (positive or negative) it passes through. -/
  def hoistCondition (scope : List Name) : Nat → Bool → Condition → Nat × List Match × Condition
    | i, pos, .path pc =>
      match pos, pc.rolesRight.getLast?, scope.contains pc.labelRight with
      | true, some last, true =>
        (i + 1,
         [.mk { name := splitLabel i, type := last.predecessorType }
             [.path { rolesLeft := [], labelRight := pc.labelRight, rolesRight := pc.rolesRight }]],
         .path { rolesLeft := pc.rolesLeft, labelRight := splitLabel i, rolesRight := [] })
      | _, _, _ => (i, [], .path pc)
    | i, pos, .existential e ms =>
      let (i1, headMs, ms') := hoistMatches scope i (pos && e) ms
      (i1, headMs, .existential e ms')
end

/-- Split at a pivot, hoisting every eligible path condition in the tail, not
only the pivot's own. The tail's givens and the head's projection are derived
the same way regardless of how the tail's matches were produced. -/
def hoistAt (s : Specification) (before : List Match) (pivot : Match) (after : List Match) : Split :=
  let scope := scopeAt s before
  let (_, headExtra, tailMatches) := hoistMatches scope 0 true (pivot :: after)
  let headMatches := before ++ headExtra
  let tailGiven := tailGivenAt s headMatches tailMatches
  { head := { given := s.given, matchList := headMatches,
              projection := .composite (tailGiven.map fun l => { name := l.name, label := l.name }) },
    tail := some { given := tailGiven, matchList := tailMatches, projection := s.projection } }

def splitBeforeFirstSuccessor (s : Specification) : Split :=
  match s.matchList.span matchIsDeterministic with
  | (_, []) => { head := s, tail := none }
  | (before, pivot :: after) => hoistAt s before pivot after

end JinagaSpec
