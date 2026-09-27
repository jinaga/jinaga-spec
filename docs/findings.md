# What the spike found

Each item says how it was established. Items marked *open* are questions the
spike raised and did not answer.

## The theorem needs its hypotheses

`split_correct` assumes `WellFormed`: labels are in scope, no match shadows a
label already in scope, and the projection names givens or top-level unknowns.
Two experiments show these are necessary, not just convenient.

- **Shadowing.** `lake exe check 1 duplicates` lets the random generator reuse
  label names. The split then disagrees with the whole specification in 630 of
  30,000 checks. With unique names it disagrees in none, across seven seeds.
- **A pivot that joins itself.** `splitPaths_correct` was first stated without
  saying that a pivot's path condition never names the pivot's own unknown. An
  agent proving it found the statement false, with a one-fact counterexample
  that I reproduced (the original condition holds, the split's head has no
  solution). The original reads the pivot bound to a fact. The head runs before
  it is bound. The scope rule excludes this shape, and the proof now takes the
  exclusion as a lemma (`pivot_paths_ne`). The parser agrees: it looks up a
  path's joined label among the labels already in scope, which do not include the
  match's own unknown, so a self-join is rejected with "The label ... has not been
  defined".

These are traced, and the consequences written up, in `contracts.md`. In short:
the parser enforces scoping and no-shadowing, but **not** that the projection
names a defined label. A specification with an undefined projection label
parses, passes `validateSpecification`, and is split into a tail that projects
that label. `validateSpecification` checks only that each match is rooted. The
DSL builder scopes labels by construction, which was not verified.

The theorem's no-shadowing rule is lexical, so two sibling existential conditions
may declare the same name. The parser agrees: it discards a nested match's
labels when the condition ends.

## Results are equal as sets

The split enumerates the head's split labels before the pivot, so it visits
solutions in a different order, and with multi-valued predecessor roles it can
find one solution by more than one route. The theorem says the same results, not
the same list. Authorization asks only whether the user is among them, so sets
suffice. Anything that counts or orders results would need a stronger statement.

## The evaluator seeds one given; the theorem does not

`AuthorizationRuleSpecification` runs the head with `head.given[0]` only. The
theorem evaluates from an environment binding every given. For a rule with one
given (every authorization rule today) they are the same. The vectors
`given-only-an-existential-uses` and `pivot-joins-a-second-given` are specifications
whose head has two givens, which is the case #308 flagged in its notes. Whether
to seed every given is a decision for the evaluator, not the split.

## The three pull requests, as vectors

Run against #308, #309 and #311, the vectors pass 7, 9, 12, then 17 of 17, and
each one flips in the layer whose issue names it. The first version of one
vector (`given-only-the-tail-uses`) failed at #308 and #309 for a reason unrelated
to #297: its pivot had two path conditions, which is #231's shape. It tangled two
mechanisms in one case. It is now two vectors. A vector should exercise one thing.

## Smaller observations

- `describeSpecification` sorts a composite projection's components in place
  (`description.ts`, `projection.components.sort`). Describing a specification
  can reorder its projection. It does not change results, but a printer that
  mutates its input is a trap. The TypeScript runner compares structure before
  it prints, to stay clear of it.
- The split's naming differs in shape from the Lean: TypeScript allocates the
  split labels up front and indexes into the list, and the Lean threads the
  taken names through the walk. They produce the same names. The Lean form avoids
  an unreachable "ran out of names" case. Refactoring the TypeScript to match
  would make the port read one to one.
- `labelsInCondition` collects the labels of an existential condition's nested
  matches without subtracting the labels those matches declare. It is safe
  because `referencedLabels` then filters against labels that unshadowing keeps
  distinct from the nested ones, and because split labels avoid every declared
  label (`declaredLabels` walks nested matches). That reasoning is spread across
  three functions and one hypothesis. The proof makes it explicit.

## Where the proof effort went

| file | lines | what it proves |
|---|---|---|
| `Locality.lean` | 84 | Evaluating matches depends only on the labels they use. |
| `SplitPaths.lean` | 264 | Splitting the pivot's path conditions preserves them. |
| `Derivation.lean` | 386 | The tail's givens, derived as free labels, are closed. |
| `Main.lean` | 202 | The pivot step, and the theorem. |
| `Basic.lean`, `Scoped.lean` | 252 | Helper facts, and the definitions of well-formedness. |

The derivation of the tail's givens is the largest piece by some distance. The
idea is small (a tail runs from the labels it uses but does not define), but
stating "the labels it uses" through `allLabels`, `used`, `defined` and the split
labels takes real bookkeeping. That may be a sign that the derivation can be
expressed more directly. This is an observation about proof size, not a
recommendation.

## Not covered

Conditions on givens, `field`/`hash`/`time` projections, and nested
specification projections are not modelled. `buildFeeds`, skeleton canonicity
and distribution soundness are not started.
