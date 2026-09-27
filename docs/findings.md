# What the spike found

Each item says how it was established. Items marked *open* are questions the
spike raised and did not answer.

## The theorem needs its hypotheses

`split_correct` assumes `WellFormed`: labels are in scope, every declared label
is new and not reserved, and the projection names declared labels. Two
experiments show these are necessary, not just convenient.

- **Shadowing.** `lake exe check 1 duplicates` lets the random generator reuse
  label names. The split then disagrees with the whole specification in about 630
  of 30,000 checks. With well-formed specifications it disagrees in none, across
  many seeds.
- **A pivot that joins itself.** `splitPaths_correct` was first stated without
  saying that a pivot's path condition never names the pivot's own unknown. An
  agent proving it found the statement false, with a one-fact counterexample
  that I reproduced (the original condition holds, the split's head has no
  solution). The original reads the pivot bound to a fact. The head runs before
  it is bound. The scope rule excludes this shape, and the proof takes the
  exclusion as a lemma (`pivot_paths_ne`). The parser agrees: it looks up a
  path's joined label among the labels already in scope, which do not include the
  match's own unknown.

The parser enforces scoping and no-shadowing, but **not** that the projection
names a defined label. A specification with an undefined projection label parses,
passes `validateSpecification`, and is split into a tail that projects that
label. The traced consequences are in `contracts.md`; the fix is to check at the
boundary, which `jinaga.js` now does.

Scope is lexical, so two sibling existential conditions may declare the same
name. The parser agrees: it discards a nested match's labels when the condition
ends.

## Reserving a namespace beats enumerating declarations

The split needs labels that nothing declares. The first design found them by
searching every place a label can be declared. That enumeration was already
wrong twice: `jinaga.js` missed a given's existential conditions until a review
caught it, and the .NET version searches only top-level names, so a label inside
an existential condition can collide.

The redesign removes the search. A label that begins with `__` is reserved: the
boundary rejects a specification that declares one, and the split names the fact
its head walks to for the `i`th path condition `__s<i>`. A collision is then
impossible however many declaration sites the language grows. The check gained
one conjunct, and the proof lost a pigeonhole argument and every
"declared anywhere" lemma.

## What the definitions no longer need

Working from the theorem, each piece of special-case code was asked whether the
theorem needs it. Four went.

| removed | why it was unnecessary |
|---|---|
| The search for a fresh label, and the four functions that enumerate declared labels. | Reserved labels. |
| `head: undefined` when the pivot is the first match and walks no predecessor. | A head with no matches is a head. The split is total, and the theorem has one case fewer. |
| The derivation of the head's givens. | The head is given every given. |
| "Labels used but not defined" as the tail's givens. | The tail is given the labels in scope at the pivot that it uses. With no label declared twice, nothing needs subtracting, and a nested specification's own labels are harmless in the used set. |

In `jinaga.js`, the split went from 226 lines to 91, and `src` shrank by 131
lines net (76 added, 207 removed). In the spec, `Split.lean` went from 179 lines
to 131, and the executable check from 74 lines to 50 (one traversal instead of
two).

The removal of `head: undefined` is a behavior change. A rule whose first match
seeks successors of the given used to throw `AuthorizationRuleError` on every
write. It now evaluates, and admits nobody on a live write for the same reason
the `Link` rule in `jinaga.js#297` does: the given is the fact under
authorization, which is not yet in the store. When the given is readable, as in
`getAuthorizedPopulation`, it names the owner. Whether such a rule should be
refused when it is written is a separate question from whether the split is
defined for it.

## Results are equal as sets

The split enumerates the head's split labels before the pivot, so it visits
solutions in a different order, and with multi-valued predecessor roles it can
find one solution by more than one route. The theorem says the same results, not
the same list. Authorization asks only whether the user is among them, so sets
suffice. Anything that counts or orders results would need a stronger statement.

## A vector should exercise one thing

The first version of one vector failed against the earlier layers of the three
stacked pull requests for a reason unrelated to the issue it was written for: its
pivot had two path conditions, which is a different issue's shape. It tangled two
mechanisms in one case, and is now two vectors.

## Smaller observations

- `describeSpecification` sorts a composite projection's components in place
  (`description.ts`, `projection.components.sort`). Describing a specification
  reorders it. Reproduced, and filed against `jinaga.js`.
- `specificationIsNotDeterministic` widened when it was derived from
  `matchIsDeterministic`, and nothing reads it now. Filed against `jinaga.js`.
- A vector-freshness check in `scripts/verify.sh` could not fail (`diff ... &&
  echo` does not trip `set -e`). It now does, and the check is shown to fail on a
  corrupted vector.

## The store is a graph with the given retyped, not a second semantics

`Split.evaluate` runs the head and the tail over the *same* graph, so it cannot
see either consequence of a rule running before its own fact is saved: that the
fact is absent from the store, and that it must still be reachable by walking
predecessors from it. Modelling this with a second, store-shaped semantics
would have meant re-proving locality and the pivot step against it. Instead
`Graph.authGraph store f := store ++ [{ f with type := batchType }]` reuses
`Split.evaluate` and `split_correct` unchanged: it is one call of `evaluate` on
one graph, just built to make the two consequences true by construction.

The reserved batch type is the whole trick. `Graph.step` looks a start fact up
by id, so a walk that starts at `f` (because some label is already bound to it)
still reaches its predecessors — the graph must hold `f` for that. But
`evalMatches` filters every candidate by type before it ever binds one, and no
ordinary type is the batch type, so `f` can never be *bound* to a fresh
unknown — the graph must hide `f` from that. Retyping the one fact gets both
for free: present to a walk that already knows where it starts, invisible to a
scan that does not.

`store_denies` and `store_correct` (`JinagaSpec/Proofs/Store.lean`) show
`tailReadsGiven` is exactly the boundary. The harder direction,
`store_correct`, needed one more fact that was not free: a walk of at least one
step, whether it starts at `f` or at a fact already in the store, never lands
outside a closed store. Without it, `f` could in principle be reached by a
walk two hops from the given, `authGraph`'s retyping would not stop that, and
a split label bound to `f` would leak into a tail given that the store cannot
resolve. The empirical check (`checkStoreSpec` in `Check.lean`) agreed on every
graph across three seeds before the proof was attempted, and the mutation
check (dropping the absent-given rule from `evaluateStore`) is caught on a
genuine but small minority of `tailReadsGiven` specifications — most such
walks fail on their own once the given is retyped, and the guard's real work is
catching the rule's given passed straight through to the tail's projection.

## Hoisting: polarity is not parity

Formulation D of #231 is fixed by hoisting a tail condition that walks
predecessors of the given, inside a *positive* existential, into the head
(`JinagaSpec/Hoist.lean`). The first version of the rule toggled polarity on
every existential, positive or negative, on the theory that two negative
existentials cancel: an existential over a union is the union of the
existentials (positive case), and negating that twice returns a union again.

`lake exe check` disproves this at one level of nesting deeper than the
single-negation counterexample already known. With a given `p1` whose role `x`
is multi-valued (`{20, 21}`), two candidates for an outer match `e1` (`e1A`,
`e1B`), and two candidates for a doubly-nested match `e2` (`e2A` witnessing
`e1A` only at the value `20`, `e2B` witnessing `e1B` only at `21`), the whole
specification's pivot `s1` has a solution: *for every* `e1` candidate, *some*
value of `x` rescues it (`∀e1 ∃x`). Naive-parity hoisting computes the
opposite quantifier order: it picks *one* value of `x` for the whole head and
unions the tail's evaluation over that one value afterward (`∃x ∀e1`), which
is strictly stronger and is empty here, because no single value rescues both
`e1A` and `e1B` at once. The bug needs two matches at the *same* nesting depth
each satisfiable only by a *different* value the hoisted condition could take,
which needs depth two to set up — one match to vary over, one to be hoisted
out of a second, nested negation — so it does not show up at the depth the
single-negation counterexample already exercises.

The fix makes polarity monotone instead of alternating: a negative
existential's matches are negative regardless of the polarity outside them,
and nothing nested inside a negative existential ever recovers positive
polarity, however many further existentials, positive or negative, it passes
through. `hoistConditionNaiveParity` (the disproved rule) is kept as a
permanent mutation check alongside `hoistConditionNoPolarity` (the original,
single-negation one): across ten random seeds, the naive-parity mutant
disagreed on 0–2 of 3,480 checks per seed (rarer than the single-negation
mutant's failures, because it needs the deeper shape above), and the fixed
`hoist` disagreed on none, over the same specifications and the two
handcrafted counterexamples. This is the same shape of finding as the
shadowing experiment above: a plausible-sounding rule, refuted by the
randomized check before it reached a proof.

## Hoisting: the general proof, and why it did not need `splitPaths`' numbering

`hoist_correct` is now proved for every well-formed specification, with no
hypothesis beyond `WellFormed s` — the same shape as `split_correct`. An
earlier pass at this proof (recorded in an earlier revision of this file)
tried to reduce `hoist_correct` to `split_correct` by showing the two
algorithms compute the same split, up to `splitPaths`' numbering. That attempt
stalled on a real obstacle: `hoist`'s split-label counter only advances when a
condition is actually hoisted, while `splitPaths`' advances once per top-level
path condition regardless, so the two numberings only coincide when every one
of the pivot's own top-level conditions is eligible — not the general case,
and not formulation D, where the eligible condition is *not* at the pivot's
own top level at all.

The proof that landed does not go through `splitPaths` or `splitBeforeFirstSuccessor`
at all. It generalizes the two lemmas underneath `split_correct` directly, to
the whole tree instead of the pivot's own flat condition list:

- `Locality.lean`'s environment-agreement argument (two environments agreeing
  on a scope give solutions agreeing on that scope, plus what the matches
  declare) generalizes to `hoistMatches`/`hoistConditions`/`hoistCondition`'s
  own recursion, carrying the same agreement through however many nested
  existentials.
- `SplitPaths.lean`'s swap (a hoisted path condition, and the head match that
  witnesses it, say the same thing) generalizes to a condition at any depth,
  using the *same* commutation argument at every level: a hoisted label is
  bound in the head, so it is existentially quantified outside every
  quantifier of the tail; existentials commute with existentials, so pulling
  the walk out through positive existentials preserves meaning, and a
  negative existential is a universal an existential cannot be pulled through
  — exactly the boundary `hoistCondition`'s monotone polarity already draws
  (`Hoisting: polarity is not parity`, above).

The two combine into one mutual induction
(`hoistMatches_correct`/`hoistConditions_correct`/`hoistCondition_correct`,
`Proofs/Hoist.lean`) mirroring `hoistMatches`/`hoistConditions`/`hoistCondition`'s
own recursive structure: at each step, hoisting a match list is a genuine
transformation (not just "a different but agreeing environment", the way
`evalMatches_agree` treats it), so the induction is stated as a full `↔` over
an explicit projection `(L, r)` — mirroring `pivot_step`'s own top-level
shape — rather than the one-directional "original implies hoisted" form a
first attempt reaches for; degenerating `L` to `[]` is what lets a nested
existential's own emptiness check reuse the very same theorem, rather than
needing a second, weaker lemma just for that case. `hoist_step` and
`hoist_correct` then assemble exactly as `pivot_step` and `split_correct` do,
using a generalized `tail_scoped` (`hoist_tail_scoped`) built on
`hoistMatches_scoped` in place of `splitPaths_names`.

The store boundary theorems carry over the same way: `store_denies_hoist` and
`store_correct_hoist` (`Proofs/Store.lean`) are `store_denies`/`store_correct`
with `hoist` in place of `splitBeforeFirstSuccessor`, reusing every
graph-agnostic lemma (`walk_authGraph_eq`, `ordinary_binds_store`,
`evalMatches_authGraph_agree`, `safeAt_before`) unchanged, and replacing only
the two facts that were `splitPaths`-shaped: `given_notin_headMatchList` (now
`given_notin_headMatchList_hoist`, using `hoistMatches_reserved` instead of
`splitPaths_names`) and `splitPaths_head_binds_store` (now
`hoistMatches_head_binds_store`, the same one-step-of-the-walk argument,
generalized to `hoistMatches`'s recursion the same way `hoist_step` generalizes
`pivot_step`). `OrdinaryTypes` survives hoisting outright
(`hoistMatches_ordinaryTypes`): hoisting only ever rewrites conditions, never
a match's own unknown or its type.

All sixteen named cases, and thousands of random specifications, pass the
randomized check, and now also the proof.

## Where the proof effort went

| file | what it proves |
|---|---|
| `Locality.lean` | Evaluating matches depends only on the labels they use. |
| `SplitPaths.lean` | Splitting the pivot's path conditions preserves them. |
| `Derivation.lean` | The tail's givens, derived as used labels in scope, are closed; every label a well-formed, scoped list of matches uses is ordinary. |
| `Main.lean` | The pivot step, and the theorem. |
| `WellFormedCheck.lean` | The executable check decides `WellFormed`. |
| `Basic.lean`, `Scoped.lean` | Helper facts, and the definitions of well-formedness. |
| `Proofs/Store.lean` | `authGraph`'s retyping keeps the given out of every candidate list and every walk of at least one step; `store_denies`/`store_correct` and their `hoist` counterparts. |
| `Proofs/Hoist.lean` | `hoist` agrees with the reference semantics, for every well-formed specification, at any nesting depth. |

The redesign changed the proofs less than it changed the definitions. The
derivation of the tail's givens fell from 386 lines to 344, and no longer needs
the tail's own labels to be disjoint from its givens. `SplitPaths.lean` grew from
264 lines to 285, because the labels are now numbered by position and the
induction carries the index. The proofs lost the fresh-name search and its
pigeonhole argument, and every lemma about labels "declared anywhere". The
definitions, which a port must read, are where the reduction shows: 417 lines
became 350, with the check included.

## Not covered

Conditions on givens, `field`/`hash`/`time` projections, and nested
specification projections are not modelled. `buildFeeds`, skeleton canonicity
and distribution soundness are not started.
