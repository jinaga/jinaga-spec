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

## Hoisting becomes the split

The spec once had two algorithms: `splitBeforeFirstSuccessor`, confined to the
pivot's own path conditions, and `hoist`, reaching any depth, kept and proved
separately (`hoist_correct`, `store_denies_hoist`, `store_correct_hoist`) once
the general proof above landed. `jinaga.js` ports `hoist` as its own
`splitBeforeFirstSuccessor` (jinaga/jinaga.js#325), so the spec had one
algorithm and two names for it. Adopting `hoist` as *the* split collapses that:
`hoist` is renamed `splitBeforeFirstSuccessor`, and `hoist_correct`,
`store_denies_hoist`, `store_correct_hoist` are renamed `split_correct`,
`store_denies`, `store_correct`. The narrower, pivot-only split
(`splitPaths`, `splitAt`, `tailMatchesAt`, `pivot_step`, `tail_scoped`, and the
theorems stated only for them) is deleted, along with `pathsOf`/`existentialsOf`
and everything that existed only to separate a match's path conditions from
its existential ones for that split's benefit; `hoistMatches`/`hoistConditions`/
`hoistCondition` keep their names, since they still do the same hoisting
regardless of what the outer driver is called.

This changes what the split does, not just what it is called: formulation D of
jinaga/jinaga.js#231 is admitted (`tailReadsGiven` is `false` for it), because
the walk to the parent's workspace now moves out of its enclosing positive
existential and into the head. And a split label's number no longer counts the
pivot's own top-level path conditions; it counts the walks actually hoisted, at
any depth, in the order `hoistMatches`/`hoistConditions`/`hoistCondition`
visits them — the same reason the general proof above did not need
`splitPaths`' numbering to begin with.

## Maintaining a result needs only covering candidates

`maintain_correct` (jinaga/jinaga-spec#6) takes no hypothesis about the
specification or the facts: a held set re-checked on candidates that cover each
step's change equals `evaluate` after every insertion. `lake exe check` runs it
over about 6,850 random batches of one to three facts per seed (seeds 1–3) with
no failure, and a mutant that drops one changed row from the candidates is
caught on every specification whose sample graphs had a change.

`evaluate_perm` does need one hypothesis: an id names at most one fact
(`Graph.IdsUnique`). Two facts with the same id and different content resolve
differently depending on which comes first. Content addressing gives this. The
theorem is stated more generally as `evaluate_congr`, for graphs holding the
same facts with any repetition, because a replica that receives a fact twice
holds it twice, and #9's `converge` needs exactly that.

## Inversion, measured before anything is proved about it

`JinagaSpec/Inverse.lean` ports `invertSpecification` from jinaga.js at
`4ebbb27`, including its known defect at `inverse.ts:505`.
`ports/typescript/inverse-diff.ts` checks that the port's inverses equal
jinaga.js's, as text, on 400 random specifications per seed. They agree on
every one across five seeds, refusals included, about 1,000 inverses per seed.
`lake exe check-inverse` then measures them against law L4 (every result gained
is reported by an "add" inverse, every result lost by a "remove" inverse) on
random graphs and a fresh fact.

**jinaga.js's inverses miss changes, from one cause.** Per seed of about 1,500
specifications, a few lost results go unreported, and occasionally a gained
one. Every miss inspected has the same cause: an inverse evaluates, on the new
graph, a condition that held only on the old one. That happens at every level of
the chain from the result down to the fact whose solution was *lost*.

- `exists { notExists }` (jinaga/jinaga.js#338): retiring the only current
  mirror loses the account, but the inverse requires the mirror's `notExists`
  on the new graph, where it is false.
- Two sibling `notExists` conditions that one fact falsifies together. Each
  inverse removes its own condition and keeps the other, which the same fact
  has just falsified. This is new. It is reproduced in jinaga.js itself: `watch`
  reports the row added and never removed, while a query returns nothing.
- At depth 3 it shows as a missed *gain*: `notExists { notExists { exists } }`.
  The new fact makes the innermost `exists` true, which removes the middle
  solution, which adds the result. The inverse's operation is "add", but the
  middle level lost its solution, and its `notExists` is false on the new graph.

**#338's proposed fix is not enough.** It keeps the enclosing conditions as
written for "add" and negates them for "remove", decided by the inverse's final
operation. Built directly from the specification and measured the same way, it
still misses a few results per seed, and it misses the sibling case. Which
conditions an inverse may keep depends on the direction of each level, not on
the final operation.

**The coarse rule misses nothing.** At each level of the chain that *lost* its
solution, drop that level's existential conditions; at each level that gained,
keep them, except the condition the chain passes through. Path conditions are
kept everywhere: a lost solution never binds the new fact, and a walk from any
other fact is the same on the old graph and the new. It missed no change across
eight seeds, about 12,000 specifications. Its candidates are a superset, which a
re-checking stream (#6) does not mind. This is the rule `candidates_complete`
will be proved for.

**Soundness, for a stream that trusts its inverses.** jinaga.js's "remove"
inverses report about 16 results per seed that the graph still has (#338's
second symptom). No "add" reports a result the graph lacks. A re-checking
stream needs neither.

**`shakeTree` refuses well-formed specifications.** About 8% of random
well-formed specifications (126 of 1,516 on seed 1) pass the connectivity check
and are then refused by `shakeTree` as "not connected to the rest of the graph".
In each one a given is joined only from inside an existential condition. The
connectivity check counts that join and `shakeTree` does not. One of the named
cases is refused this way: `(p1: Post, p2: Jinaga.User)` with
`!E { u3: Ban [u3->user = p2] }`, so jinaga.js cannot subscribe to it.
jinaga/jinaga.js#141 is the open proposal to handle it. (The other refusals,
about 250 per seed, are disconnected specifications from the generator, which
jinaga.js is right to refuse.)

**The loop that once ran forever cannot.** `shakeTree_bound`
(`Proofs/Inverse.lean`): the loop that moves a match without a path condition to
the bottom (jinaga/jinaga.js#132) returns to its first match within the length
of the suffix it rotates, for every input, so it runs at most that many times.
What it does on return is refuse, which is the refusal above.
`relocateConditions` visits each match once and moves conditions only forward.

**Smaller observations.** `simplifyMatch` checks whether a simplified
existential condition still expects a successor of the given; none can, so the
branch is dead. The mutant that re-notifies a fact already in the store is
caught on only about 1% of specifications: it shows only when a skipped
successor condition matters on a small random graph.

## The proven inverse

`candidates_complete` (`Proofs/Candidates.lean`): for a well-formed
specification and a fresh fact, the results of `inverses s`, evaluated on the
new graph, include every result the fact adds or removes. `stream_correct`
composes it with `maintain_correct`: a stream that re-checks those candidates
after each insertion holds exactly the specification's results on the
replica's graph. Both depend only on the standard axioms. Both now hold for
a batch of facts, of which a single fact is the case `[f]` (next section).

What the proof needed, and did not:

- **Freshness is two facts, not three.** `f`'s id is new to the graph, and no
  fact of the graph points to it. Nothing about `f`'s own predecessors is used.
  This is the only place the graph matters (`Proofs/Fresh.lean`).
- **`WellFormed` is used once, for the reserved label.** Each inverse is given
  the subscription's givens and `f` under `__f`, and the proof needs no label of
  the specification to be `__f`. The scoping and naming rules that the split
  needed for its own reasons are otherwise unused.
- **No operation.** The inverses do not say "add" or "remove". They only have to
  be complete, because the stream re-checks every candidate (#6). This removes
  the polarity bookkeeping that #338's defect lived in.
- **Reordering is for speed, and it checks itself.** An inverse as built keeps
  the original specification's nesting and order. That is enough for
  correctness, but read from the givens a pin inside an existential condition
  is checked once per row of the collection. `reorderOrSelf` (`Reorder.lean`)
  flattens the existential conditions the path passes through and orders the
  matches from `__f`. It then checks its own result (`arranges`): the same
  unknowns, each bound once, the same conditions (each possibly reversed or
  moved), every label bound before use. If the check fails, it keeps the
  inverse as it was. `reorderOrSelf_correct` holds with no hypothesis, because
  the proof is about the check, not the search that produced the order: a list
  of matches is a conjunction, so any well-scoped arrangement of the same
  conditions has the same solutions. On random specifications every reordered
  inverse starts at the new fact and every match is reached by a path
  condition from something bound, and the results never change.
- **Known givens make jinaga/jinaga.js#141 go away.** The reordering binds the
  givens throughout, so a given joined only through an existential condition
  is never a problem. jinaga.js refuses those specifications only because its
  inverses must reach every given from the new fact alone.

## A label reused after an existential condition captures it

The parser scopes an existential condition's labels to the condition, so a
later match may declare the same name. jinaga.js's inverse concatenates the
outer and inner matches and looks labels up by name. The later match comes
first in that list, so it captures the lookup, and the inverse misses changes
(jinaga/jinaga.js#343, reproduced in jinaga.js itself). `check-inverse`
generates such names. With them, jinaga.js's inverses also report results that
are not there.

`candidates` is immune, because an inverse keeps its nesting. The reordering
is not: flattening would bind the two labels in one list. Rather than rename,
which would need its own proof, the self-check rejects the flattened list when
a name repeats, and the inverse is kept unordered: correct, and as slow as an
unordered inverse. With reused names in the generator, about 6% of inverses
fall back; without them, none do. Renaming lifted labels is a possible later
improvement.

`check-inverse` measures `candidates` itself, not a copy of the rule: it misses
no change.

## A batch is read on the graph that holds it all (#11)

A replica saves a batch, then notifies each saved fact against the graph that
holds the whole batch (`ObservableSource.notify` in jinaga.js). So a fact's
inverses are read on `g ++ B`, never on `g ++ pre ++ [f]`, and within the
batch a fact may already have successors. The question was whether reading
there still finds every change, and if not, what a stream may conclude.

**Every change is a candidate (question 1).** `lake exe check-inverse` draws,
for each of about 1,500 specifications per seed, 40 graphs and a batch of one
to four fresh facts, each pointing into the graph or at facts of the batch made
before it, listed in a random order. It compares the net change, from `g` to
`g ++ B`, with `candidates s env g B`, every fact's inverses read on `g ++ B`:

| seed | batches | with facts naming each other | results changed | missed by `candidates` | changed with no candidate | mutant "read each fact alone" misses |
|---|---|---|---|---|---|---|
| 1 | 60,640 | 21,212 | 3,063 | 0 | 0 | 140 |
| 2 | 60,640 | 20,812 | 3,044 | 0 | 0 | 167 |
| 3 | 60,640 | 20,881 | 3,454 | 0 | 0 | 162 |
| 4 | 60,640 | 21,074 | 2,501 | 0 | 0 | 136 |
| 5 | 60,640 | 20,993 | 2,561 | 0 | 0 | 114 |
| 6 | 60,640 | 21,064 | 3,200 | 0 | 0 | 158 |
| 7 | 60,640 | 21,205 | 3,216 | 0 | 0 | 152 |
| 8 | 60,640 | 20,896 | 3,478 | 0 | 0 | 208 |

So there is no counterexample to record. Question 2's weaker shapes are not
needed: triggering follows from coverage, and no change to the inverses is
needed. The mutant reads each fact's inverses on `g` and that fact alone. It
misses changes on every seed, so the check would see a read on the wrong
graph. `batch-exists-together` is the smallest such case: an account and its
mirror arrive together, and neither fact's inverses find the account on a
graph without the other.

**The proof is the single-fact proof, read for a batch.** The walk from a
changed result down to a new fact never needed `f` to be the last fact. It
stops at the *first* fact of `B` it meets. Above that point every bound fact is
old, so the walks the proof compares start outside `B`, and those are the same
on `g` and `g ++ B`. The proof also learns which fact to pin only when it
reaches it. So it reads each level with the pin unbound, and binds it on the
way back up, which is sound because the specification never mentions `__f`
(`AgreeOff`). That lemma group is the only new reasoning; the rest of
`Proofs/Candidates.lean` changed `[f]` to `B`.

**The hypothesis is weaker than the issue proposed.** `Fresh g B` asks only
that no fact of `g` has the id of a fact of `B`, or points to one. It says
nothing about order within the batch: no topological order is needed. That
matters because jinaga.js discards the batch's order (jinaga/jinaga.js#248).
The issue's hypothesis, fresh in some topological order, implies it.

**What a stream may conclude.** Three theorems, each depending only on the
standard axioms:

- `candidates_complete`: for a well-formed specification and a fresh batch,
  `candidates s env g B` includes every result the batch adds or removes. If a
  fact of the batch is one of the subscription's givens, that fact's candidates
  are every result old and new, as before. (Superseded: a stream now
  maintains what a replica reads, and that fact's candidates are every
  result read on the new graph. See the next section.)
- `notify_correct`: from a held set equal to the result on `g`, re-checking
  each fact's candidates in turn, each read on `g ++ B`, leaves exactly the
  result on `g ++ B`. This is the shape jinaga/jinaga.js#336 and #345 need.
  The re-checks commute (`recheck_each`): they all read one graph, so the
  notifications may run in any order.
- `stream_correct`: over a sequence of batches, each fresh when it arrives,
  the stream holds exactly the specification's results.

A row gained and lost within one batch (`batch-current-value`: two revisions
arrive together, and the one between is current only inside the batch) may be
a candidate, and the re-check drops it. Nothing proven covers a second batch
saved while the first one's notifications are still reading. Those reads see
more than `g ++ B`, which is a question about the store, not about inverses.

**Vectors.** `vectors/inverse/` gains two named batch vectors and six random
ones (`random-batch-<n>`, three facts each, at least one naming another). A
batch vector carries `batch` in place of `fact`, and the existing vectors are
unchanged (`vectors/README.md`). jinaga.js's `MemoryStore`, reading the proven
inverses given each fact of the batch on a store that holds it all, finds
exactly the vectors' candidates on all 30.

## A replica reads nothing until its givens arrive

`evaluate` binds a given to its id whether or not the graph holds that fact.
jinaga.js's `SpecificationRunner.read` returns nothing while any given is
missing. The two disagree before a given arrives, and only then: a
specification whose only conditions on a missing user are `notExists` has
results under `evaluate` and none for a replica (`given-arrives-under-not-exists`).

`Specification.read` is the replica's reading: `evaluate` when every given is a
fact of `g` of its declared type, and nothing otherwise. A stream maintains
`read`. `evaluate` stays the reference semantics underneath, so the split, the
store and the inverses are unchanged.

`Covers`, `recheck` and `maintainStep` now take the result as a function of the
graph, and `maintain_correct` holds for any such function: its proof never
looked inside `evaluate`. `candidates_complete`, `notify_correct` and
`stream_correct` are restated for `(s.read · env)`, under the same hypotheses.

When a given arrives in a fresh batch, `Fresh` says the graph did not hold it,
so the old read is empty, and every result read on the new graph is a
candidate. That is all `factCandidates` reads for it now, which is jinaga.js's
`givenCandidateInverse`, so jinaga.js's stream is the proven one in this case
too. When no given arrives, each given is stored after the batch exactly when
it was before (`has_append_outside`): either both reads are empty, or both are
`evaluate` and the inverses cover the change as before.

This is also the semantics a condition on a given needs. jinaga.js reduces such
a condition to a match bound to the given, which binds only a stored fact, so
the reduction agrees with `read`, not with `evaluate`.

## Conditions on a given reduce to a match

jinaga.js lets a given carry existential conditions; a replica reads nothing
while one fails. `ConditionedSpecification` (`GivenConditions.lean`) is that
shape, and its `read` is `Specification.read` behind the conditions.

`reduceGivenConditions x c` moves every condition onto one new first match,
`x: T [x = g, ...]`, bound to the first given with a condition. An existential
condition does not read the match it is written on, so one match serves every
given's conditions, where jinaga.js used one per given, each needing its own
label. The match has one solution when the conditions hold and none when they
do not, and only while the given is stored, which is why this follows the
previous section: against `evaluate`, the reduction would need a hypothesis
that the given is present; against `read`, it needs none.

`read_reduceGivenConditions` assumes only that the reduction is well-formed and
that `x` is not a label the specification names. Both are checkable: a port
runs `isWellFormed` on the reduction it builds, and the label rule (the first
of `given`, `given2`, ... not named anywhere) is checked by the vector
generator, not proved, since the theorem holds for any unused label. The proof
reuses `scopedMatches_shrink` to drop `x` from the scope of what never names
it, `allHold_agree` for the conditions, and `exists_projection_iff` for the
rows. `candidates_complete_given` and `stream_correct_given` follow by
rewriting with it.

jinaga.js labelled the match `__g<i>`, which `WellFormed` rejects, because the
proofs reserve `__` names. The label is now an ordinary one the specification
does not use, so jinaga.js's reduction must change to match: two vectors,
`given-condition-lost` and `given-condition-gained`, pin it.
`check-inverse` adds a random condition to a random given in a third of its
batches; `candidates` of the reduction misses nothing, and a mutant that
drops the condition is caught.

## Exact inverses

`candidates` is complete, and a stream decides each candidate by reading the
specification again (`recheck`). That second read is what a replicator pushing
changes to a client would rather not pay. `changes` (`Exact.lean`) makes the
inverses themselves exact, so each reports adds or removes from one read.

**The rule.** The inverses split by direction (`inversesFor`). An add inverse
(gained direction) is conjoined, match by match, with the original top-level
matches (`conj`): every original condition is re-attached to its match. A
remove inverse (lost direction) comes in one variant per top-level match `j`
and existential condition `d` on it: the inverse conjoined with the original
unknowns, no conditions, except `d` flipped on match `j` (`removeTests`). A
specification with no top-level existential condition has no remove inverses,
and needs none: a top-level row can be lost only when one of them flips, since
path conditions do not change on a fresh batch.

**Why one test at the top suffices.** The tests say nothing about the old
graph. An add need only be in the new result, and a remove only absent from
it: adding a row the set already holds, or removing one it lacks, changes
nothing. So "sound on the new graph" (`adds_sound`, `removes_sound`) plus
complete (`changes_complete`) is exact (`exact_correct`), and a row cannot be
both added and removed, so the order of the two does not matter. That is also
why the levels below the top may stay relaxed: whatever an inverse's nested
levels admit, the top-level test decides the row on the new graph. The
counterexamples in "Inversion, measured" are each caught by this rule:
`exists { notExists }` with a second current mirror (the remove test, no
current mirror, fails), sibling `notExists` (the remove test for either holds),
and Restore with a second freeze (the re-attached `notExists`, no unrestored
freeze, fails).

The proof turned on one lemma: two lists of matches over the same unknowns,
each bound once, read as one have exactly the solutions they share
(`mem_evalMatches_conj`). Both bind the same unknown to a fact of the same
type, and the finished solution says which, because nothing rebinds it. The
soundness theorems need no `Fresh`: they are statements about the new graph
alone. Completeness reuses the walk of `inverses_complete` (`gainedMatches`,
`lostMatches`), restated to keep the direction, and one new walk: a solution
the batch removes fails, on the new graph, an existential condition of one of
its top-level matches (`lost_test`).

**The limit: `ProjectsUnknowns`.** The remove test is per solution. When the
projection leaves out a top-level unknown, two solutions can project to one
row, and one of them failing does not remove the row.
`projection-drops-unknown` is the case: tasks with an open assignment,
projecting only the task. Of two open assignments, one is completed; the task
stays, but the remove inverse reports it. Exactness for rows there would need
the remove test to be `notExists` over a renamed copy of the whole original
match list, joined to the projected labels, which needs label renaming and a
lemma for it. Maintaining products, where the projection is every top-level
unknown, and deriving rows with counts, is the alternative. Neither is done.

**Measured** (`check-inverse`, seed 1). On 30,341 batches over the random
specifications and the named cases, each with the projection widened to every
top-level unknown where it was not already (25,723 of them): 3,640 rows gained
and 98 lost, 6,289 adds and 2,133 removes. No add is absent from the new
result, no remove is present in it, no change is missed, and applying the
changes to the old result gives the new one on every batch. Without the
widening, 470 removes report a row the new result still has, which is why the
hypothesis is needed. Both mutants are caught: add inverses without the
re-attached conditions report rows the new result lacks (Restore shapes,
including `not-exists-not-exists-second-freeze`), and remove inverses without
the flipped test report rows it still has. Random graphs rarely build the
second shape, which `exists-not-exists-second-mirror` supplies.

Re-attaching every original condition, path conditions included, duplicates
the inverse's own path conditions, which costs nothing in meaning and keeps
the proof to one lemma. It does not make reordering fall back more often:
217 of 5,068 add inverses keep their order, the same 217 as the plain
inverses, and 401 of 2,440 remove inverses (16%), against 228 of 1,349 plain
lost-direction inverses (17%). So the alternative, attaching only the
existential conditions, is not worth its extra lemma.

## Cascade: identity and placement

`@jinaga/cascade-core` maintains a tree of keyed arrays, and each pipeline step
turns input events into output events. jinaga/jinaga-cascade-core#29 found a
pipeline whose output depended on the order rows arrived. Generalizing it turned
up the same fault in several steps: a step that moved or admitted a row re-sent
it as new, carrying only the values it had when it first arrived, and left its
subtree behind. The fix in jinaga/jinaga-cascade-core#32 addresses a node by its
level and key, makes its parent a changeable value, and adds a `placed` event.
This model was written to prove that design.

`Tree.apply` states the protocol, and each refusal corresponds to a bug the
review of #32 found. Requiring a change's `old` value to be current forbids the
double count `filter` produced when it forwarded the change that admitted a row.
Requiring `old ≠ new` forbids no-op events. Refusing to remove a node with
children forced the `filter` and `flatten` fixes, and the input step's removal of
children before their parent.

Proving the steps turned up two things the TypeScript still does differently:

- **An aggregate after its last contributor leaves.** The denotation gives a
  parent with no contributing children no aggregate, however many it had before.
  The TypeScript leaves the last value it computed (`0` for `sum`), so a parent
  that lost its children and one that never had any differ. That depends on
  history, which `order_independent` forbids.
- **No-op events.** `sum` emits a change when a child contributes `0`, and
  `pickBy*` emits on every update to a picked row, even when nothing changed.
  `apply` refuses both.

Two steps are correct only under a contract on the caller's function:
`defineProperty` and `filter` re-evaluate only when a property the caller lists
changes, so the function must read no other property. In TypeScript that list is
`mutableProperties`.

The proofs split along the steps. `andThen_correct` needs nothing about the
steps beyond their own theorems, so `tiers_correct`, a five-step pipeline, has a
one-term proof. The hardest step was `filter`: when a row's visibility changes,
the step adds its subtree parents first or removes it children first, and the
proof rests on two generic lemmas about adding and removing a list of nodes in
depth order (`addAll`, `removeAll`) and one about what a change at one node
does (`Local`, `local_update`).

## Cascade: the input

A caller of `@jinaga/cascade-core` adds root rows, and the children of declared
source arrays, named by their ancestors' natural keys. Two questions about that
input were open after the first cascade step.

**Can a child arrive before its parent?** Not through Jinaga:
`jinaga.js`'s observer delivers a nested collection's rows only from inside their
parent's `onAdded`, and holds early children until then. So an orphan means the
input was wired out of order. The input refuses it with a diagnostic
(jinaga/jinaga-cascade-core#33) rather than holding it: a second buffer would
duplicate the observer's, and would hide the wiring mistake.

**Are composed keys unique?** Yes. `nodeKey_inj` shows a row's key determines
its natural keys, so a natural key need only be unique among its siblings.

With those, `input_correct` needs no hypothesis about order: the input's events
are always accepted. Its one contract is that a row is not added twice, which
Jinaga's observer also guarantees. The proof reuses `removeAll` and the subtree
lemmas from `filter`: removing a row is evicting its subtree.

## Cascade: the output session

The last step's events reach the output session, which turns them into the
nested keyed arrays a React component renders. An event names a node and its
parent; to reach the node in nested arrays, the session needs every ancestor's
key. So it keeps a placement index, the parent of each node it has queued, and
locates an event when it queues it. Two things must hold.

**The arrays follow the tree.** The model represents the arrays by their
located entries: a node, its level, and its ancestors' keys. That is a nested
keyed array up to the order of each array, and keeps what can go wrong: an
operation at a missing location fails, removing a node removes what is nested
in it, and moving a node moves its subtree, whose key paths change from under
the old parent to under the new one. The invariant is only that the arrays are
nested, each entry's parent entry present, and hold the tree's nodes. That each
entry sits where the index locates it is then a theorem (`located`), and
`session_apply` follows event by event, with each proof local to the entries an
operation touches.

**The index is current whenever a flush can run.** Queueing an operation can
flush, and `setState` can call back into the session before the queueing
returns: a subscriber reacts to a row by adding its child. The session's
invariant is that the arrays hold the flushed tree and the queue, each operation
located against the index as it was then, replays it to the index. Queueing and
flushing keep it (`inv_enqueue`, `inv_flush`), and under it no operation is ever
dropped at a flush. It holds at the callback only because the TypeScript records
the placement before it pushes the operation. `record_before_push` is the
counterexample to the other order: the callback's child finds no parent.

Not modelled: the recursive array code itself (`updateArrayAt`), the order of
items within an array, and the epoch and dispose checks.

## Cascade: what can change after add

A consumer of a step's events subscribes to what the step's descriptor declares:
the output session registers `onModified` only for each level's mutable
properties. A change the descriptor does not declare is never heard.
jinaga/jinaga-cascade-core#30 was such a case: `flatten` emitted changes to a
flattened row's inherited values after a move, but declared none of them, so
the output kept the old parent's values. Fixing it showed two more facts the
descriptor had to carry. Whether a level's nodes can move is a value of its own
(`mutablePlacement`), and each level's mutable properties belong to that level:
a list shared by every level let a `sum` miss `replaceToDelta`'s outputs, and
let a property at one level change what another of the same name declared.

The model's signature is that part of a descriptor: a mutable flag per level and
property, and a movable flag per level. Each step's `….sig` mirrors its
TypeScript descriptor transform, and `…_keeps` proves that for every event its
input declares, the step emits only events its output declares. The proofs are
per event and need no invariant: the step's own events show what it can emit.
`groupBy` is the one that turns a change into a move, which is why
`movable [C]` holds exactly when a grouping value is mutable. Declaring more
than a step emits is allowed.

`ops_heard` is the property the output relies on: for anything a caller does, a
subscriber to the pipeline's descriptor hears every event. The TypeScript
checks the moves half of this by test: every `onPlaced` a pipeline emits is at
a level its descriptor declares movable.
## Cascade: the steps' caches

A step in the model reads its whole input tree; a TypeScript step reads only the
cache it keeps. For `groupBy`, an aggregate and `defineProperty`, the cache is
modelled as the TypeScript keeps it, and the cached step implements the model's
step: when the cache describes the input tree and the tree accepts an event, the
cached step emits exactly the step's events, and its new cache describes the
new tree.

The descriptions say what each cache must hold. `groupBy`'s holds each root
row's grouping values and each group's number of root rows; deciding whether a
group is created or removed reads only the size. An aggregate's holds each
child's parent and values, and each parent's number of contributing children
and their total, so a parent with no contributors has no aggregate, as the model
requires. `defineProperty`'s is the interesting one: the TypeScript records a
node's values when it is added, and afterwards only changes to the properties
the caller lists. Its view of a node is out of date for every other property.
The description says how: the current values are the known ones with some
changes to unlisted properties. That is harmless under the contract the step's
correctness already needs, that its function reads only the listed properties,
and the proof uses exactly that.

The aggregate's cache is stale in the same way: the TypeScript refreshes a
child's snapshot only for the aggregated property, so its description, too,
allows changes to untracked properties, under the contract that what a child
contributes reads only the tracked one.

`filter` is not modelled: its TypeScript cache is the complete state of every
node at or below its scope, which is the tree.

Two differences between the model's steps and the TypeScript's are outside this
refinement. A TypeScript step's own listener runs before the step passes an
event on, so it emits a derived change before its cause; the two are at
different nodes or properties, so either order should reach the same tree, but
that is not proved here. And the
TypeScript aggregate passes through an upstream value of its own property, which
the model's step hides; that matters only when two steps define a property of
the same name.

## Cascade: `flatten`

`flatten` is the step where jinaga/jinaga-cascade-core#30 was found: a child
that moved to another parent kept its old parent's values, because the output
did not listen for them. Modelling it raised the question of what a flattened
row shows when its parent and child share a name. TypeScript answered it two
ways at once: the child's value won on add only if the child had one, while the
parent's later changes were ignored whenever the child declared the name. An
aggregate declares its property before it has a value, so the rows depended on
arrival order. jinaga/jinaga-cascade-core#38 makes a shared name an error, at the
type level and, for declared names, at run time.

The model takes the parent's names `I` as a parameter: a row shows the parent's
values for those and the child's for the rest. It ignores a child's value for a
name in `I`, so it needs no contract on its input. The TypeScript agrees with it
when two things hold of the payloads. `I` must list every property a parent's
payload carries: the TypeScript reads the inherited names from the parent's
descriptor, so an undeclared parent property is inherited on add but never
declared mutable, and is not updated after a move. And no child payload may
carry a name in `I`: #38 rejects names both descriptors declare, and the types
reject every shared name, but an undeclared child property in an untyped
pipeline shows the child's value. Both are the same gap: a descriptor that does
not declare every property its payloads carry. The proof reads the output through `get`: each output level comes
from one input level, and a row from a child and its parent. The frame lemmas
say an event changes the output only at its image; the work is in the events
that reach many rows, a parent's change or move, and a child's move, which
changes its row's parent and then each inherited value that differs.

`flatten_keeps` checks the descriptor rule #34 introduced, `mutablePlacement`
and inherited mutability, against the step.

## Cascade: steps over ordered siblings

`cumulativeSum` and `replaceToDelta` are the steps whose output depends on an
order. Both TypeScript steps keep each parent's items in a sorted list and
update the items after the one that changed. Both sort by their `orderBy`
values and break ties on the key. The model takes the comparison as a parameter
and assumes that it is a strict total order on nodes with distinct keys. The
TypeScript does not guarantee that: the key makes the comparison total, but both
comparators compare two numbers as numbers and anything else as strings, which
is not transitive (`2 < 10`, `10 < "11"`, `"11" < 2`). With mixed `orderBy`
types, the sorted list depends on the order items arrived in. The proofs apply
when the values make the comparison transitive, such as values of one type.

The two steps turned out to be one. Each overwrites some properties of one
level with values computed from the whole input tree: a running total over the
node and the siblings before it, or the difference between a node's value and
its predecessor's. A step that forwards each event, hides upstream changes to
those properties, and then emits a change for every node whose value differs is
correct whatever the values are (`overlay_correct`), so the order matters only
to the values. A running total ignores the order of the tree's list without any
assumption. A predecessor, the greatest of the siblings before a node, needs a
total order to be unique, and with one it ignores the list's order
(`latest_perm`). The bridge to the TypeScript is the sorted list: a running
total is the sum over the node's prefix of it (`cumulativeSum_val_sorted`), and
a predecessor is the node just before it (`predecessor_sorted`). These are
correspondences of values, not of events. The model emits one change for each
node whose value differs. When an `orderBy` change moves an item, the TypeScript
updates the items after its old place and then those after its new one, so an
item after both changes and changes back: moving `A` between `B` and `C`, with
values 1, 2 and 3, emits `C`: 6 → 5, then 5 → 6. The output ends with the
model's values, but a subscriber sees the transient one.

`pickByMin` and `pickByMax` raised the question of what a property holds when it
holds a node. Abstractly, the step adds one thing per parent, which child is
picked; the object the TypeScript writes is the picked child's props, which the
tree already holds. That suggested references between nodes. But a later step
can remove the node a reference points at: `flatten` removes the parents' level,
and a pick on a root row among its parents would then point at nothing, where
the TypeScript's copy survives. A step cannot reach inside an object, so
downstream the copy is the step's output, not a cache of it. A pick is a copy
of the picked child's props (`Props.toJson`). The reference is the TypeScript's cache, its heap and `lastEmitted`. The
pick is the same step as the running total, one level up: correct for any values
(`pickBy_correct`), independent of the list's order under a strict total order
(`pickBy_denotation`), and the top of the TypeScript's heap (`picked_sorted`).
The TypeScript updates the copy only on the picked child's declared mutable
properties, so the copy is current when the child's descriptor is complete; the
model, which hears every change, does not see that gap. And objects are equal in
the model when their props are, where the TypeScript groups by `JSON.stringify`,
which keeps an object's insertion order: grouping by a copy separates
`{a: 1, b: 2}` from `{b: 2, a: 1}`. The order is how the object was built, not a
value, so the model does not represent it.

What a value is took two attempts. Objects were first functions from names to
values, like props. `enrich` copies a secondary row with its nested arrays, and
a keyed array would be a function from keys; but a group's key holds its
grouping values, so a value would contain functions from keys that contain
values. That is Cantor's paradox: no model has it, and Lean rejects it. The
TypeScript never meets it, because everything in it is finite and its keys are
strings. So everything in the model is finite too. A value is `Json`: an
integer, a string, a list, or a map. A map is kept sorted by key with no key
repeated (`CMap`), so maps with the same entries are the same list, whatever
order they were built in. Props are such a map from names to values. A key is
a value, tagged by its form (a row, a child, a group), as the TypeScript's keys
are strings. Keys are ordered through an injective encoding into lists of
integers (`Json.enc_inj`). Equality is structural and decidable, so the model is
computable and its examples are checked by evaluation. `Json.map` holds a plain
list, so canonical form (`Json.Canonical`) is a condition rather than a type: the
model builds its maps through `CMap`, and a caller's values are assumed
canonical, as they are when the input reads them as JSON.

`cumulativeSum`'s descriptor transform is the identity: the TypeScript requires
each summed property to be mutable already, and under that requirement the
step emits only what its input declares (`cumulativeSum_keeps`).
`replaceToDelta` declares its outputs mutable at the events' level
(`replaceToDelta_keeps`).

## Cascade: `enrich`

`enrich` is the step that reads two pipelines. The model first considered a step
with two inputs, which would have needed its own composition theorems and its
own proof that the inputs' events can interleave in any order. Instead each
source has its own tree, and an event names its source (`Sources.lean`). The
existing trees, steps and proofs are untouched: a source's pipeline is an
ordinary step run on its own tree (`lift_correct`). `enrich` is a join, a step
that reads every source and emits one tree's events. Events from both sources
arrive in one stream, so the order theorem for joins covers interleaving as the
single-source one covers arrival order.

A primary row holds a copy of the secondary root row whose collection-key values
equal its key values. The copy carries the row's nested arrays, keyed by their
children's keys, which is what made the model's values finite: see the `pickBy*`
section. A primary event is handled by the overlay step with the secondary held
fixed, so its proof is `overlay_correct`. A secondary event changes no primary
row, only what some rows hold, and the step emits a change for each row whose
copy differs (`retarget_correct`). The denotation compares copies of equivalent
secondaries, which are equal because every map in a copy is built from keys
whose membership, not order, decides it (`copy_congr`).

Three differences from the TypeScript are recorded rather than modelled. It keeps
an empty array in a copy after the array's last child leaves, where the model's
copy has an array only while it has children; a secondary whose collection key
is not unique leaves the TypeScript with the last match it saw, where the model
gives `whenMissing`; and the TypeScript passes an upstream change to the enriched
property through, where the model hides it, as for the aggregates.

## Cascade: a step below the root

The model's steps were written for the root scope. Rather than give each of
`groupBy`, `filter` and `flatten` a scope and prove it again, a step below the
root is the root step run on each root row's subtree as a tree of its own
(`Within.lean`). One theorem, `within_correct`, carries any root step's proof
there, so the root proofs are untouched and the nested ones are one line each.

Three things make the lift faithful. A view's keys are the input's, but the
keys a step makes, such as group keys, could coincide across rows, so each key
of the output is tagged with its row's: the TypeScript composes a nested group's
key with its parent's for the same reason. A move between rows is not an event
of any one view: the step removes the node's subtree from the old row's view and
adds it to the new one's, the same lists `filter` already uses (`evict`,
`admit`). And the step's output array can differ from its input's, as
`groupBy(G, o)` replaces array `a` with `o`.

The output keeps an item's key tagged where the TypeScript keeps it plain. The
vectors never compare keys, so the difference is not observable in them. No
cascade-core runtime test scoped a `flatten` before these vectors; they pass.

## Feeds: what a replica needs to converge

A replica reads a specification's feeds page by page, loads what they name with
its predecessors, and runs the specification on what it holds. Eventual
consistency is the claim that once every feed's page comes back empty, it reads
what the replicator reads. It splits into two parts, and both are proved.

**Paging loses nothing** (`Cursor.lean`, `Proofs/Cursor.lean`). A tuple's
position is its fact ids, largest first, compared lexicographically, as
jinaga-server's `sort(array[...], 'desc')`. `Caught` (every tuple at or before
the bookmark has been delivered) holds from the start, after every page, and
after every batch the replicator saves, and an empty page then means every
tuple is delivered. Two tuples at one position hold the same facts, so a
`LIMIT` that cuts between them loses nothing. The growth step rests on two
things. `feed_antitone`: a feed has path conditions, and negative conditions
over path conditions only (`buildFeeds_feedShape`), so a tuple that appears
after a batch binds a fact of the batch. And
`IdsIncrease`: that fact's id is larger than every id the replica's bookmark
names. jinaga-server assigns `fact_id` from a sequence before commit, and its
saves take no lock, so two saves can commit out of id order and a bookmark can
pass a fact that commits later. That is jinaga/jinaga-server#203, reproduced
there against replicator 3.8.0, and #207.

**The feeds cover the specification** (`feeds_cover`, `Proofs/Cover.lean`). A
replica holding the givens, every fact the feeds deliver, their predecessors,
and any other facts of the graph reads what the replicator reads.
`feed_converges` puts the two together. This is #9's `relevance_complete`, in
the form the stream already uses: the replica is `g`, and the rest of the
replicator's graph is a fresh batch `B` to it, since a replica saves each fact
with its predecessors.

### The feeds, from the requirements

`buildFeeds` is chapter 12's ordinary, excluding and restoring feeds. It was
reached by stating what a feed must do and removing every rule the statement
does not force. There are three requirements, and each is a theorem:

1. **Consistency** (`feeds_cover`), above.
2. **Append-only** (`buildFeeds_feedShape`, `feed_antitone`). A bookmark can
   only move forward, so a tuple must never appear behind one. A feed has path
   conditions and negative conditions over path conditions only. A fact that
   arrives can then remove a feed's tuple, but never add one that binds only
   older facts.
3. **Deferral** (`feeds_defer`). A new client is not sent the details of an
   entity whose exclusion nothing has cancelled. In chapter 12's terms, the
   properties of a deleted entity are withheld until the delete is restored.
   Restorable deletes are the common case.

The walk follows a level's matches, each with its positive conditions joined
in. At each negative condition, every feed so far does three things:

- it **emits an excluding feed**: itself, then the condition's level, and stops;
- it **goes on filtered** by the condition's level; and
- it **goes on restored**: through the condition's level, then the level of one
  of that level's own negative conditions, walked the same way.

Each rule is forced, and the check has a mutant for each, caught on 43 to 127 of
613 specifications over seeds 1 and 2. Deferral forces the excluding feed to stop. Consistency then
forces both the filter and the restore. The filter is the negative condition's
level, path conditions only, so append-only holds. A restoring feed must drop
the restored fact's other negative conditions; it is restored when any one
fails. That rule is `jinaga.js`'s first bug below. Nothing forces a filter
inside an excluding feed: what it would filter out, a restoring feed delivers
anyway. So there is none.

`feeds_defer` states deferral exactly as the walk delivers it. Take any feed
that binds a label after a match `m`, and any tuple of it. Then every negative
condition of `m` is *passed* at a context the tuple extends: either the
condition has no witness, or some witness has a fact of one of its own negative
conditions. A stronger statement, that a feed is withheld while every witness
stands, is false four levels deep. A restore that is revoked twice, one
revocation undone, has a canceller whose own exclusion has been cancelled. The
vector `restore-revoked-and-unrevoked` shows it.

**No feeds can do better** (`exact_deferral_impossible`,
`Proofs/Contested.lean`). The theorem quantifies over any list of feeds, each
any specification, with any nesting of conditions. A feed delivers the facts
its matches bind, at the specification's givens (`Specification.tuples`); its
projection, and any child specification in it, deliver nothing. The theorem
holds two requirements fixed, each stated as the conclusion of the theorem
that proves it of `buildFeeds`:

- `Consistent s Fs` is `feeds_cover`'s conclusion, under its hypotheses on the
  graphs: a replica that holds the givens and what the feeds deliver reads what
  the replicator reads.
- `AppendOnly f` is `feed_antitone`'s conclusion, for a batch whose ids are
  larger than the graph's (`IdsIncrease`): a tuple found after it, none of
  whose facts is in it, was found before. That is exactly what paging by
  bookmark needs of a feed (`caught_grow`, `feed_grow`).

`FeedShape` is not assumed. It is how `buildFeeds` meets append-only, not the
requirement itself. So the class is every feed set a replicator could page.
`buildFeeds` is in it (`buildFeeds_consistent`, `buildFeeds_appendOnly`), on
the counterexample too (`contested_feasible`), so the hypotheses can be met.

The specification is `contested`: an event's names, unless its delete stands;
a delete stands unless restored, a restore unless revoked, a revoke unless
unrevoked. The graphs are `graph N U ++ [name]`: the event, its one delete, a
restore, `N` revokes of the restore, an unrevoke of each revoke in `U`, and
the event's name. The conclusion names one with a revoke not unrevoked, on
which the event reads no result, so its one delete stands, and the feeds
deliver the name. That refutes "withheld while every witness stands", and so
also "withheld while excluded". The proof is a count:

1. Take `N` revokes of the restore, more than all the feeds have matches. With
   every revoke unrevoked, the delete is cancelled and the name is a result.
   A replica holding everything but the name would read nothing, so
   consistency forces some feed's tuple to deliver it.
2. Take away the last unrevoke, which has the largest id. The delete stands
   and the event is excluded. The unrevoke is a batch with larger ids than the
   graph, so append-only says the tuple was there before it arrived, unless it
   binds that unrevoke. If no such tuple binds it, the name is delivered while
   the event is excluded.
3. A specification sees ids only for equality, so renaming them renames the
   tuples (`tuples_rename`, `Proofs/Rename.lean`). Swapping any revoke and its
   unrevoke with the last keeps the graph, so the tuple binds every one of the
   `N` unrevokes. A tuple binds one fact per match, and no feed has `N`
   matches.

So `feeds_defer`'s weaker form is the most a feed design can promise for a
contested exclusion, not a limitation of this walk. Exact deferral is possible
only by giving up append-only, so that a tuple could appear behind a bookmark
and be missed, or consistency. The vector
`restore-revoked-and-both-unrevoked` is the other side of the count: the name,
delivered through an unrevoke once every revocation is undone.

The same count works two levels deep, for chapter 12's restorable deletes: an
event deleted `N` times, each delete restored, then one restore taken away.
There the witnesses are the deletes, so it refutes only "withheld while
excluded", which at two levels `feeds_defer` does not claim: "withheld while
every witness stands" is what it says there. It takes four levels to refute
that. The two-level case is not separately proved.

`check-feeds` tries three feed sets on the theorem's graphs, `N` from 1 to 3:

| Feeds | consistent | append-only | exact |
| --- | --- | --- | --- |
| `buildFeeds` | yes | yes | no |
| `buildFeeds` without the restoring feed through an unrevoke, plus a feed of the unrevokes | no | yes | yes |
| the same, plus a feed of the name filtered by the restore's whole condition | yes | no | yes |

The second withholds the name once every revocation is undone. The third
defers exactly with a nested negative condition, and a tuple of it appears,
binding no new fact, when the last unrevoke arrives. The check fails if any
feed set is all three. The proof is about 400 lines, and renaming ids
(`Proofs/Rename.lean`, which holds for any specification) about 95 more. The
count is about 60 lines, and swapping two revokes about 70. The rest
evaluates `contested` on a graph with a variable number of revokes, one level
at a time (`zs_iff` to `ds_iff`).

The cost is measured on chapter 12's case: 50 events of 10 names each, 30
deleted, and 10 of those restored. A new client downloads 391 of the graph's
591 facts. Levels, which had no excluding or restoring feeds, would send all
591.

### How consistency is proved

The proof has three parts, and only the last mentions a feed.

- **Normal form** (`nf`). A level has a solution exactly when its path
  conditions, positive conditions joined in, have one at which each of its
  negative conditions has none. This reuses `flatten_correct`
  (`Proofs/Reorder.lean`) with every positive condition lifted.
- **Two semantic inductions.** (A) `semA`: a context valid on the replicator,
  held by the replica, all of whose valid cancellers are delivered (`PD`), is
  valid on the replica. (B) `semB`: a context invalid on the replicator, whose
  first failing condition's valid witnesses and their evidence are delivered
  (`EvD`), is invalid on the replica. Both induct on the specification's size.
- **The walk delivers both.** `pd_level` shows the restoring feeds deliver
  every valid canceller. A restoring feed through the witness reaches the
  canceller's level. From there, the rest of the walk lands in a feed, because
  every condition after it can be passed (`walk_level`, `walk_neg`).
  `evd_level` shows the excluding feed at the first failing condition delivers
  its witnesses. Every earlier condition holds, so the walk reaches that
  condition filtered. Landing is threaded through a continuation property,
  `KDone`, since a feed's tail is the rest of the specification. A label budget
  (`Within`, `Hygiene`) keeps every label bound once along the way.

A feed that `traversesSuccessors` drops walks only to predecessors of what it
starts from. Its tuples bind facts the replica already holds
(`feeds_settled`, using `levelFeeds_rooted` and `dropped_settled`). The theorem
needs `WellFormed`, `DistinctLabels` (joining a positive condition binds nothing
twice) and `RootedMatches` (every match has a path condition, which `jinaga.js`
requires). `buildFeeds_nodup` gives `feed_grow` its other hypothesis.

### What `jinaga.js` gets wrong

Checking consistency against a port of `jinaga.js`'s `buildFeeds` found two
defects:

- **A restoring feed asks too much of the fact it restores.** An excluded fact
  is cancelled when any one of its negative conditions fails. `jinaga.js`'s
  restoring branch for one of them keeps the other conditions its excluding feed
  attached. A delete that is both restored and undone is then restored by no
  feed, and the event's name reaches the replica through none
  (`not-exists-cancelled-twice`, `not-exists-cancelled-by-second`;
  jinaga/jinaga.js#427). jinaga/jinaga.js#368 fixed the conditions waiting at the even level, which a
  restoring branch does need; the same rule reached the odd level too.
- **A positive condition inside a negative one replaces it.**
  `buildExistentialCondition` builds the inner positive condition from its own
  matches, doubled, and assigns it over the outer one. The main feed of
  `!E { d: Delete [..., E { a: Approval [a->delete = d] }] }` becomes
  `E { a, a }`, which names `d` without binding it. jinaga.js's own
  `MemoryStore` throws reading it, and so does jinaga-server's `sqlFromFeed`
  (`exists-inside-not-exists`; jinaga/jinaga.js#425).

`ports/typescript/feed-builder.ts` corrects both and drops the filter inside
the excluding feed. It matches every vector and sends no fact the vector's
feeds withhold. Before the fixes below, `jinaga.js` missed a result on four of
the 20 vectors.

Both are fixed in `jinaga.js`: jinaga/jinaga.js#429 (from #425) joins a positive
condition into its negative condition's level, and #432 (from #427) restores an
excluded fact through each of its cancellers with none of the others attached.
Fixing the first exposed a third case of the same rule, a canceller reached
through a positive condition on the excluded fact
(`d [ E { y [ !E { z } ] } !E { u } ]`), which #432 covers too. `jinaga.js`'s
feeds now cover all 20 vectors.

### Levels, and why they were set aside

Before the requirements were written down, a simpler algorithm, *levels*, was
proved consistent. It had one feed per level, positive conditions joined, path
conditions only, and no filter at all. It was six lines against the machine's
22. It met consistency and append-only, but it sends every deleted entity's
details to every new client, so it fails deferral. The lemmas its proof needed
survive in `Proofs/Flat.lean`. Its measurements on `check-feeds`' seed 1 are
kept for comparison, from before the check generated child specifications.
Levels made 1,641 feeds and delivered 8,934 facts. The corrected filtered
machine made 2,377 feeds and delivered 9,865. The present algorithm made 2,373
feeds and delivered 9,593.

A specification that reuses a name an existential condition declared, which
`WellFormed` allows, can give a level two matches with the same label. The
semantics shadows, but the SQL a feed becomes names its labels by name.
`DistinctLabels` excludes it.

## Feeds: child specifications

Chapter 12 builds a projection's feeds recursively. First come the feeds of the
specification without its projection. Then each *positive* one, ordinary or
restoring, is extended with the feeds of each child specification, and those
with the feeds of their own children. `jinaga.js`'s `addProjections` does the
same at the terminal of every even-parity feed. Here it is one continuation,
`projectionFeeds`. `buildFeeds` hands each feed that completes the
specification, filtered or restored, to it. An excluding feed stops before, so
it carries no child's facts. On chapter 12's Entity List (`child-of-excluded`)
this makes the eleven feeds the book counts: three for servers, four for names
and four for rates.

### A child specification is a specification

The proofs did not need a second walk. A child specification's matches go on
from its parent's, so each one *is* a specification: the same givens, the
parent's matches followed by its own, at every depth
(`Specification.descendants`, built from `Projection.paths`). The feeds of a
specification are exactly the flat feeds of its descendants (`mem_buildFeeds`).
The proof is a lemma about continuations: a walk whose continuation hands a
partial to any of several continuations makes the feeds of any of those walks
(`levelFeeds_mem_iff`). Every requirement is then the PR #42 theorem applied to
each descendant (`Proofs/Children.lean`). The flat theorems are renamed
`flatFeeds_*` and keep their proofs:

| Requirement | Theorem | From |
|---|---|---|
| Consistency | `feeds_cover` | `flatFeeds_cover` of each descendant, and `reads_congr` |
| Append-only | `buildFeeds_feedShape`, `buildFeeds_nodup` | `flatFeeds_feedShape`, `flatFeeds_nodup` |
| Deferral | `feeds_defer` | `flatFeeds_defer`, and `levelFeeds_within` |
| Convergence | `feed_converges` | `feeds_cover` |

The hypotheses are the flat ones for each descendant: `WellFormed`,
`DistinctLabels` and `RootedMatches`. `DistinctLabels` of each descendant
forbids a label repeated along a path to a child specification. Sibling child
specifications may share one, since no feed binds both. Chapter 12's names and
rates both declare `next`, and the Entity List vector keeps that.

### What a replica reads, at every depth

A result now holds each child specification's results (`Result`). They are
compared as sets at every depth. `Projection.ReadsAt` says a result is read
from one solution σ when σ projects to its row and, for each child
specification, each listed result is read from some solution of the child's
matches from σ, and each such solution has some listed result read from it.
`Projection.Reads` reads a result from some solution of the matches.
`feeds_cover` concludes `∀ r, s.Reads g env r ↔ s.Reads (g ++ B) env r`.

A replica that holds the givens reads a result from every solution, at any
depth (`reads_of_solution`). The result is `Projection.resultsAt`: one result
per solution of each child, as `SpecificationRunner.read` builds it.
`Specification.readsOf` lists one per solution, and it is complete:
`s.Reads g env r ↔ ∃ r' ∈ s.readsOf g env, r.SetEq r'` (`reads_iff_readsOf`),
where `Result.SetEq` is equality as sets at every depth. That rests on
uniqueness: a result read from σ is `SetEq` to `resultsAt`'s
(`setEq_resultsAt`). `readsOf` is what `check-feeds`, `check-content` and the
feed vectors' `nestedResults` compute, so they test the definition, not a
stand-in. They compare lists with `sameResults`, through `Result.key`, which
is meant to identify results up to `SetEq`; that is not proved.

The first definition (jinaga/jinaga-spec#53) said each child's list holds,
as a set, exactly the child's results from the solution: `r ∈ cs ↔ Reads r`.
A list with duplicates has the same members, so a document with one comment
had infinitely many results (`[c]`, `[c, c]`, …), and no finite list held them
all. Two levels down, every solution was dropped and `Reads` was empty, so
`feeds_cover`'s iff held between two empty sets: it said nothing about the
child results it was meant to cover. The proofs went through all the same,
since their content is that the solutions agree along every path. The test
library's `readsOf` built one list per solution, as intended, and nothing
connected it to `Reads`, so no check noticed. `twoDeep_reads` is that
counterexample, now read as `.mk [] [[.mk [] [[.mk [some 3] []]]]]`.
A lemma that every solution has a result, now `reads_of_solution`, would have
caught it.

The flat proof had shown that the replica's and the replicator's solutions
agree on the unknowns. Two solutions from the same environment that agree on
the unknowns are the same environment (`evalMatches_frame`). So
`flatFeeds_cover` now says the replica finds *exactly* the replicator's
solutions, and it no longer needs the givens to be held. A child's results are
evaluated from its parent's solution. Equal solutions of every descendant's
matches therefore give equal results at every depth (`reads_congr`, with
`prefix_iff`). That step does not mention a feed.

### Deferral, restated

The first statement of `feeds_defer` for child specifications kept PR #42's
form: a feed that binds a label after a top-level match `m` passes `m`'s
negative conditions. It was proved, and then the check's new mutant broke it:
an excluding feed extended with the child specifications. That feed binds no
later top-level match, only the child's, so the statement said nothing about
it. Yet it sends a terminated server's names to a new client.

The theorem now says where each feed comes from. Every feed is a feed of one
of the specification's descendants and binds only that descendant's labels.
For each of the descendant's matches `m`, it carries `m`'s details, the later
matches and its child specifications', only where `m`'s negative conditions
pass. With sibling child specifications that share a label, naming the
descendant is what makes "the details" mean the right facts. `check-feeds`
checks it in that form.

### What the check and the vectors show

A third of `check-feeds`' specifications have child specifications, two deep at
most, with negative conditions of their own (`genChildSpec`). Four new mutants
are each caught:

- no child specification feeds;
- a restoring feed that does not go on to them;
- child feeds that drop the parent's filters; and
- an excluding feed that goes on to them.

They are caught on 6 to 66 of 613 specifications over seeds 1 and 2. The
restoring mutant needs a restore that delivers a child's result. That is rarer,
and it is caught on 6 and 9.

There are six new vectors: `child-of-excluded`, `grandchild`,
`child-uses-a-given` and three `random-children-*` (two since jinaga-spec#55,
which drops one). A vector with child
specifications carries `expected.nestedResults`. `feed-builder.ts` passes all
19. On every child vector, `jinaga.js`'s `buildFeeds` covers the results and
sends no fact the vector's feeds withhold. Its misses are still PR #42's four.

### Where `jinaga.js` and `jinaga-server` diverge

- **The book's own Entity List repeats a label, and jinaga-server cannot serve
  its feeds.** As printed in chapter 12, `listOfServers` names both the
  `ServerRehired` inside the server's negative condition and the `ServerRate`
  of the rates child `sr`. `jinaga.js` accepts it, and its restoring feed
  extended with rates declares `sr` twice. `MemoryStore` shadows the first and
  reads it. jinaga-server's `QueryDescriptionBuilder` takes the second `sr` for
  the first's fact. Building the SQL for both of those feeds throws
  `Type mismatch: Rate is compared to Rehired`: that was run through
  `sqlFromFeed` with jinaga 6.16.1, not against a database. So a replica
  subscribed through jinaga-server would get no rates for a rehired server.
  `feed-builder.ts` rejects the specification instead (`DistinctLabels`).
  The vector renames the rate `rt`.
  `jinaga.js` now renames instead (jinaga/jinaga.js#430, from #426): before
  building feeds, a declaration that repeats a name earlier in its descendant
  takes the first unused `name2`, `name3`, …, so its feeds meet
  `DistinctLabels`. The two differ on this input, and that renaming preserves
  results is not proved here.
- **A child feed that joins the givens through separate chains has no SQL.**
  In `random-children-1` as it was (it is no longer generated, since
  `isConnectedDeep` refuses it: jinaga-spec#55), the parent reaches the given `p2`. The child reaches
  only `p1`, and a grandchild's positive condition connects the two.
  `detectDisconnectedSpecification` accepts the specification. But the child's
  first feeds are a product of two chains, and jinaga-server's `generateJoins`
  throws `Neither predecessor nor successor fact has been written` for them.
  It does so for jinaga.js's feeds and for the vector's alike. The cause is
  wider than child feeds: a top-level specification whose two givens each have
  their own chain fails the same way (jinaga/jinaga-server#233).
- **`assertWellFormed` does not look inside a child specification.**
  `wellFormedErrors` checks scope only for the top-level matches, and
  `projectedLabels` skips specification components. A child specification
  that joins an undefined label, redeclares its parent's label, or projects a
  label it does not declare passes, and only the text parser catches it. The
  theorems need each descendant `WellFormed`, which `isWellFormedDeep` decides
  (`isWellFormedDeep_iff`). The vectors `child-redeclares-a-given` and
  `child-joins-an-undefined-label` show it. jinaga/jinaga.js#431 (from #428)
  fixed it, and `run-vectors.ts` now requires jinaga.js to agree on them.
- **jinaga.js's parser refuses an existential condition that does not join its
  own unknown.** `WellFormed` puts a condition's matches in scope of the givens,
  the earlier matches and the enclosing unknown, and does not require them to
  join the unknown. `random-2`, as it was before it was dropped for an unused
  given (jinaga-spec#45), had such a condition, `!E { e1717 }` on
  `e1716`, which joins only the given `p1`. `wellFormedErrors` accepts it, and
  jinaga.js's feeds and `MemoryStore` handle it, but `SpecificationParser`
  throws `The existential condition must be based on the unknown`, so
  `describeSpecification`'s text for it cannot be read back
  (jinaga/jinaga.js#434).
- **jinaga.js orders composite components by locale, not by code point.**
  `describeSpecification` sorts them with `localeCompare`
  (`src/specification/description.ts:69`). `Describe.lean` sorts by
  `String ≤`, and jinaga.net by `StringComparer.Ordinal`. The components
  `username`, `userName`, `Zone` and `alpha` print as
  `alpha username userName Zone` in jinaga.js and as
  `Zone alpha userName username` here. So the same specification gets
  different text, and a different hash, depending on which replica describes
  it (jinaga/jinaga.js#438).

Review found two places that read a projection's labels and missed a child's.
`Projection.labels` names only the facts a projection projects. The split's
`tailGivenAt` used it, so a given only a child specification joins was not
given to the tail. jinaga.js's `labelsInProjection` includes it (vector
`given-only-a-child-uses`). `ConditionedSpecification.labels` used it too, so
the label for conditions on a given could be one a child declares: `given`
where jinaga.js picks `given2`. Both now use one helper, `Projection.allLabels`,
which names every label a child specification declares or joins, at any depth.
The TypeScript reference's `reduceGivenConditions` had the same gap and now
mirrors it.

No issue was found for any of the three.

## Feeds: no feed is a product (jinaga-spec#55)

`buildFeeds` keeps each descendant's matches in written order, and emits a
feed wherever a negative condition or a child specification cuts them. A cut
can fall between two chains that only a later match joins, and the feed is
then a product of the two, which jinaga-server cannot answer
(jinaga/jinaga-server#233). Such a specification is refused, and
`buildFeeds` is unchanged.

### Why not reorder

jinaga-spec#55 first asked for `buildFeeds` to order each descendant's matches
so that every feed is connected, keeping the feeds that cover and defer, with
no feed delivering a fact today's feeds do not. Those requirements contradict
each other:

- **N**, `(p1: R, p2: A) { u: A [u->a = p2, !E { e: E [e->r = p1] }] } => u`.
  The excluding feed is `{ u: A [u->a = p2]  e: E [e->r = p1] }`. It has one
  match for each given and nothing joins them, and no order of its single
  top-level match connects it. `isConnected` accepts N, since it joins the
  labels a condition names to the match it is written on.
- **J!**, `(p1: R, p2: A) { u: A [u->a = p2]  c: A [c->r = p1, !E { e: E [e->c = c] }]  x: B [x->c = c, x->u = u] } => x`.
  No set of feeds is connected, covers, defers and widens nothing. The feed
  that delivers `e` binds `c`. If it binds `x` too, it sends `x`, a detail of
  `c`, while `c` is excluded, which deferral forbids. If it binds `u`
  without `x`, it is a product. If it binds neither, it is `{c, e}`, which
  delivers on graphs where today's feeds deliver nothing. Ordering `u, x, c`
  delivers `x` while `c` is deleted, and ordering from `p1` widens.

So option (A) was chosen: refuse. The requirement to reorder is moot. Nothing
is ordered, so no theorem says that ordering never fails, and `feeds_cover`
and `feeds_defer` hold as they are, with no new hypothesis.

### The check

`ConnectedDescendants s` (`Connected.lean`), decided by `isConnectedDeep`
(`isConnectedDeep_iff`), holds when:

1. each descendant, as a feed (its matches, with the givens they use), passes
   `isConnected`; and
2. every feed `buildFeeds` emits is joined (`isJoined`): its path conditions
   alone, its negative conditions' filters dropped (`Match.paths`), join its
   matches and the givens they use, and it passes `isConnected`.

(As #55 first landed, a clause between these asked that every given be used
by some descendant, jinaga-spec#45's rule. jinaga-spec#60 dropped it; see
below.)

Clause 2 is what says no feed is a product. It is stated over the emitted
feeds, not over the prefixes where `buildFeeds` cuts, because those prefixes
are the feeds. An excluding feed is the written prefix followed by the
condition's matches, which hold only path conditions, so they are joined to
the rest by their own path conditions. A filtered feed keeps the condition as
a filter on its last match (`addLast`), and `isConnected` counts every label a
filter names as joined to that match. So `isConnected` alone accepts B,
`(p1: R, p2: A) { u: U [u->r = p1]  x: X [x->a = p2, !E { e: E [e->u = u, e->x = x] }] } => x`,
whose filtered feed `{ u, x [!E { e }] }` joins `u` and `x` only through the
filter. `isJoined` checks the feed with its filters dropped, which refuses B.

Two choices in `isJoined` are forced by vectors:

- **A given that only a filter names need not be joined by path conditions.**
  The feed with its filters dropped takes only the givens its path conditions
  use (`asFeed`). `two-givens`, the unread messages of a user in a channel,
  has the filtered feed `(p1: User, p2: Channel) { m [m->channel = p2, !E { rd [rd->message = m, rd->user = p1] }] }`.
  `p1` is a parameter of the filter, not a factor of a product. Keeping the
  feed's own givens refuses it, and it is a named feed vector.
- **The feed must pass `isConnected` too.** With its filters dropped, nothing
  checks that a filter's matches are joined to the feed.
  `negative-condition-joined-only-inside-its-own` has the filter `!E { e }`,
  whose `e` only its own negative condition `!F { f [f->e = e, f->u = u] }`
  joins to `u`. The filter keeps `e` without that condition, so the filter is
  joined to nothing. Its excluding feed walks no successor and is dropped, and
  its descendant passes `isConnected`, so only this conjunct refuses it.

| theorem | statement | hypotheses | reads |
|---|---|---|---|
| `isConnectedDeep_iff` | the check decides `ConnectedDescendants` | none | both clauses |
| `isConnected_asFeed` | `isConnected (asFeed s.given s.matchList) = isConnected s` | none | nothing beyond the definitions |

So clause 1, at the specification itself, is exactly `isConnected`, and
`ConnectedDescendants s → isConnected s` holds. Nothing else is proved about
the check, and the rest is refusal policy:

- **Clause 2 is a definition.** `isJoined` is what "not a product" means here,
  and no theorem derives it from anything else. An earlier
  `buildFeeds_connected` concluded, from all of `ConnectedDescendants`, that
  every feed passes `isConnected`, with the feed's givens
  `usedGivens s.given f.matchList`. It read only this clause, which stated it,
  and the second conjunct held by `rfl` for every specification, so it was
  dropped. "Every feed passes `isConnected`" is now half of clause 2.
- **Clause 1 at a child specification** has no theorem behind it. It refuses P
  (`child-joins-two-chains-only-in-a-grandchild`) through clause 2 too, and
  `two-chains-of-predecessors`, which has no feeds, only through clause 1 at
  the top level.

The earlier `isConnected_of_connectedDescendants` assumed all of
`ConnectedDescendants` and read only clause 1 at the specification itself; it
is now `isConnected_asFeed`.

The check is strictly stricter than `isConnected`: `isConnected` accepts N, J!
and B, and the check refuses them. `child-uses-a-given` (chapter 12, Unused
Givens), whose user only the comment feed uses, passes both. (Superseded:
before jinaga-spec#60, `isConnected` counted every given and refused
`child-uses-a-given`, so the two were incomparable, and `isConnected_asFeed`
needed the hypothesis that the top-level matches use every given.)

### Mutants

Each mutant of the check (`connectedMutants`, `CheckGen.lean`) is caught by a
well-formedness vector, and on the random and named specifications of
`check-feeds`, where `connectedBreaks` counts what each gets wrong:

| mutant | gets wrong | caught on (seeds 1, 2) |
|---|---|---|
| `isConnected` alone, as the inverse checks it | accepts a product feed (N, J!, B) | 66, 79 |
| descendants only, no feed checked (#55's first statement) | accepts a product feed (N, J!, B) | 62, 78 |
| feeds by `isConnected`, which a filter joins | accepts a product feed (B) | 9, 12 |
| feeds by their path conditions only | accepts a feed `isConnected` refuses (`negative-condition-joined-only-inside-its-own`) | 1, 1 (the named vector only) |
| feeds only, no descendant checked | accepts a specification `isConnected` refuses (`two-chains-of-predecessors`, which has no feeds) | 2, 1 |
| every given used, the rule of jinaga/jinaga-spec#45 | refuses an unused given (`unused-given`, jinaga-spec#60) | 55, 53 |

The real check refuses 73 and 86 of 600 random specifications on the two
seeds. It breaks none of the four statements on any of them, but two are its
own clauses, the third is `isConnected_asFeed`, and the fourth says it has no
clause about unused givens, so that zero only checks that `connectedWith {}`
and `connectedBreaks` agree with `isConnectedDeep`. What the table shows is
that each mutant is caught.

The negative vectors are `child-joins-two-chains-only-in-a-grandchild` (P),
`negative-condition-before-the-join` (J!),
`negative-condition-joins-another-given` (N),
`negative-condition-joins-two-chains` (B),
`negative-condition-joined-only-inside-its-own` and
`two-chains-of-predecessors`. Every named feed vector passes the check and
keeps its feeds, byte for byte, with `isJoined` in place of `isConnected`.
`existential-joins-a-sibling-conditions-match`, which is not well formed,
states `connected: false`: its second filter names `e1`, which is out of scope
there, and with the filters dropped nothing joins it. Of the random feed
vectors, `random-children-1` (P's shape) fails the check and is no longer
generated; the later ones move up a number, with the same contents.
`random-2` (an unused given) was dropped too, and is generated again since
jinaga-spec#60. One split vector, `given-only-an-existential-uses`, is N's
shape. `isConnected` accepts it, and the check refuses it. It stays, since the
split does not assume the check.

### jinaga.js

From jinaga-spec#55: jinaga.js's `buildFeeds` on `3e18b4b` emits P's middle
feed, `{ u: A [u->a = p2]  c: A [c->r = p1] }`, and its own
`detectDisconnectedSpecification` refuses that feed. `isConnected` alone, the
rule jinaga/jinaga.js#436 puts in the parser, accepts N and J!. This session
had no jinaga.js or jinaga-server checkout, so neither was confirmed with the
`jinaga-conformance` runners, and no issue is drafted.

## Unused givens are allowed (jinaga-spec#60)

Decided 2026-11-23: a given no match uses must not cause refusal anywhere.
This replaces jinaga-spec#45's rule, the former clause 2 of `ConnectedDescendants` above,
which no theorem needed, and the part of `isConnected` that seeded every given
into its reachability set. The shapes it admits are `(p1: R) { } => p1`,
`(p1: R, p2: A) { } => p2` and `unused-given`,
`(p1: R, p2: A) { u: A [u->r = p1] } => u`. None is a product: a feed takes
only the givens its matches use (`asFeed`).

- **`ConnectedDescendants`** has two clauses: each descendant, as a feed, passes
  `isConnected`, and each feed is joined. `isConnectedDeep_iff` is restated for
  them, with the same one-line proof.
- **`isConnected`** (`Inverse.lean`) counts only the givens the matches use
  (`usedGivens`, moved to `Syntax.lean` so that `Inverse.lean` can read it).
  `isConnected_asFeed` loses its hypothesis that the top-level matches use
  every given: `isConnected (asFeed s.given s.matchList) = isConnected s` for
  every specification, since `usedGivens` is idempotent. So clause 1, at the
  specification itself, is exactly `isConnected`, and `ConnectedDescendants s
  → isConnected s` now holds; `child-uses-a-given` is no longer a
  counterexample, because `isConnected` no longer counts the user.
- **`invertSpecification`** gives an unused given no inverse. That inverse would
  bind the given to the new fact `f` and keep only the solutions that agree
  with the subscription's givens, so it reports a result only when `f` is that
  given. No match reads the given, so no other fact can change a result
  through it, and the given's own arrival changes what `read` returns
  whatever the matches say: the self-inverse and `factCandidates`' full
  re-read handle that. Nor could `shakeTree` build it: nothing joins the
  given to the matches, so it throws `notConnected`. The self-inverse still
  counts every given. This is a documented fact, not a theorem: nothing about
  `invertSpecification` is proved (it is the port measured by `check-inverse`),
  and the proved inverses (`inverses`, `candidates`) never consulted
  `isConnected`, so no theorem changed. `Inverse.fire` now starts an unused
  given, and only an unused one, from the subscription's binding, so a
  projection that names it reads it. A used given still starts unbound, so an
  inverse that fails to bind one still finds nothing and is still measured.

What the checks show (seed 1 of `check-inverse`): 1341 specifications
inverted and 176 refused, against 1144 and 373 before. The 197 newly accepted
all have an unused given, since on a specification whose matches use every
given both `isConnected` and `invertSpecification` are unchanged. Before
`Inverse.fire` read the unused givens' bindings, 278 gained results were
missed; the first projected the unused given `p2`, which no inverse binds.
After, one is (the tallies are the same whether `fire` pre-binds every given
or only the unused ones), and it is not about unused givens: the same
specification with the unused given removed misses it too. It reuses the label
`e2605` inside an existential condition and at the top level, the
`findMatch` capture of jinaga/jinaga.js#343. The random inverse vectors are
still filtered to specifications whose matches use every given, because
jinaga.js's `invertSpecification` counts every given and refuses the rest; the
named vectors `unused-given`, `no-matches` and `no-matches-two-givens` show
the new shapes, and their candidates are what a store reads (the given's
arrival is a full re-read).

In `CheckGen.lean`, the mutant "no given coverage" becomes "every given used,
the rule of jinaga/jinaga-spec#45", which refuses an unused given; the fourth
of `connectedBreaks` counts a check refusing an otherwise connected
specification with an unused given (caught on 55 and 53 of the random and
named specifications on seeds 1 and 2). The real check refuses 73 and 86 of
600 random specifications, against 125 and 136 before.

Vectors: `well-formed/unused-given` now states `connected: true`, and
`no-matches` and `no-matches-two-givens` are new, both connected.
`path-joins-an-undefined-label` (not well formed) now states `connected: true`
too: its only connectivity fault was its unused given `p1`. Every other
well-formedness vector keeps its verdict. Of the feed vectors, the random
seed now admits `(p1: R, p2: A) { u1: B [...] } => u1` with `p2` unused as
`random-2` (it was `random-2` at `77aa47d`), and the former `random-2` moves
to `random-3`.

jinaga.js's `detectDisconnectedSpecification` (`UnionFind.ts`) and
`invertSpecification` still seed every given, so they refuse these shapes.
`run-vectors.ts` holds jinaga.js to `connected` on every well-formed vector
and reports `unused-given` and `no-matches-two-givens`, named in
`jinagaRefusesUnusedGiven`, as known rather than failing on them;
`run-feed-vectors.ts` names the feed vector `random-2` in `jinagaMisses` and
counts a `buildFeeds` that throws as covering nothing, since jinaga.js's may
refuse it. Each is pending jinaga.js following (jinaga/jinaga.js#436, #437). `inverse-diff.ts`, which
compares the port of `invertSpecification` with jinaga.js's line for line,
counts a specification jinaga.js refuses as disconnected for an unused given
instead of failing on it, since that difference is chosen. Not confirmed with the
`jinaga-conformance` runners (no jinaga.js checkout in this session), and no
issue is drafted.

## Content storage: SEC-1 to SEC-5

The content store of "Distribution-Based Content Storage: Functional
Requirements" (Nov 20, 2026) is modelled in `Content.lean`. A replicator holds
the fact store and objects by content key; `write` stores an upload, `read`
serves one, and a history is a list of saves (each a batch) and uploads
(`Replicator.run`).
A `Policy` supplies what a fact's fields hold, the hash, the declared
constraints, the authorization rules and the distribution rules, and every
theorem holds for every policy.

| | theorem | statement |
|---|---|---|
| SEC-1 | `read_authorized` | a read returns an object only to an authenticated user whom the distribution rules let run the proof, and whose proof yields the content fact |
| SEC-2 | `read_integrity` | after any history, a read returns only bytes whose hash is the content fact's content hash |
| SEC-3 | `stored_authorized` | every stored object was uploaded, those bytes, for that key, by a user the authorization rules let create the fact at the moment the upload was accepted |
| SEC-4 | `read_isolated` | a read keyed by `F` depends on the object under `F` alone |
| | `yields_iff_reads` | a proof yields a fact exactly when some result a replica reads (`Specification.Reads`) names it, at some depth of child specifications |
| SEC-5 | `read_noninterference`, `write_noninterference` | to a reader the rules do not admit, or a writer they refuse, the answer does not depend on which objects are stored |
| | `read_admitted`, `write_accepted` | an admitted reader with a bound proof gets the object, or 404 `not_uploaded`; an authorized upload of matching bytes within the constraints is stored, or answered 200 if the key already holds one |
| RR-4 | `confirms_eq_yields` | the check `read` runs, `Proof.confirms` (bind the content fact as a result and look for a solution), is `Proof.yields` for every proof whose specification's descendants are well formed |
| RR-1 | `read_badRequest`, `Proof.bound_iff` | an authenticated read is 400 exactly when the proof is not `Proof.Bound`: a fact for every given, and every descendant well formed, which `Proof.bound` decides |
| | `Replicator.save_fresh`, `Replicator.run_closed` | a save stores the whole batch, and only if it is fresh, or nothing; after any history the store holds every predecessor of each fact it holds |

SEC-1 to SEC-5 only say when the replicator may serve or store. A handler that
never serves, or answers 403 where RR-7 wants 404, meets all five. The last
row pins down the success path. The vectors pin down every response.

Decisions the statements forced:

- **`read` does not hash again.** SEC-2 holds of every reachable state because
  `write` verified the bytes and the fact store only grows, so a key's fact
  never changes (`stored_authorized`, `store_grows`). Purging (ST-4) is not
  modelled. With purging, SEC-2 holds only if a purge removes the key's
  mapping along with its fact.
- **SEC-3 names the bytes.** "Some upload for `F` by an authorized user" is
  met by the shortcut "I already have this hash" (ST-3): the writer is
  authorized to create the fact they minted. The statement must say the stored
  object is the one that upload carried.
- **SEC-4 is what rules out the spoof.** Looking an object up by content hash
  breaks neither SEC-1 (the reader is admitted for `F`) nor SEC-2 (the hash
  matches). Only key isolation catches it.
- **SEC-5 covers uploads too.** Answering a repeat upload (RW-8) before
  checking the writer tells a refused writer which keys hold an object, and no
  theorem about `read` notices. So `write` checks the writer as soon as the
  fact is found, before the content-bearing check (RW-3) and before any
  object is consulted. Only a missing fact (RW-2) is answered first, because
  there is no fact to authorize; that answer reveals only the fact store,
  which the writer named.
- **"Yields" is any projected fact, at any depth.** A proof yields `F` when
  some result names it, at any position: a reader the rules admit may see
  everything the specification returns. A child specification counts: its
  results under a solution of its parent are the results of the descendant
  whose matches go on from the parent's (`Specification.descendants`, as for
  feeds), so `Proof.yields` asks whether any descendant's rows name `F`, and
  `Proof.bound` checks `isWellFormedDeep`. A first draft read the top level
  only. That is safe, since it only refuses more, but it refused the recorded
  proof (CR-1) of a document a client reached through a nested query
  (Copilot's review of jinaga/jinaga-spec#51). No security theorem notices
  that mutant; `read_admitted` does. `yields_iff_reads` proves that `Proof.yields`
  means the nested reading: some result a replica reads
  (`Specification.Reads`) names the fact at some depth (`Result.Names`). On
  the way, `yields_iff` says the givens are held and a solution of the
  matches, then of a child specification's matches from it and so on down,
  projects the fact (`Projection.Names`), and `Projection.names_iff_reads`
  that this is the same as some result read naming it. `check-content` also
  compares it with `Specification.readsOf` on every read.
- **A given absent from the store is 403, not 400.** RR-1's 400 is for a proof
  with the wrong number of givens or an ill-formed specification. A missing
  given makes `read` empty (`Specification.read`), so the proof yields nothing.
- **A save checks freshness and closure, and nothing else.** `save` takes a
  batch and stores it only if it is fresh (`isFresh`, `isFresh_iff`: `Fresh`)
  and closed (`isClosed`: every predecessor its facts name is in the store or
  the batch), so the cache theorems below need no hypothesis on the history
  (`Replicator.save_fresh`). Closure makes the store closed under
  predecessors after any history (`Replicator.run_closed`), and on a closed
  store a batch with the facts the store already holds dropped is fresh
  (`Closed.fresh_new`): what a real replicator saves. Without the closure
  check the store need not be closed: `save [Member -> group 1]` and then
  `save [Group 1]` stores the membership and then refuses the group for good,
  since the stored membership names it. Otherwise any batch is stored, so
  SEC-1 to SEC-5 hold against every store. The fact store's own
  authorization, and RW-2's combined fact-and-object request, are not
  modelled. The vector `batch-not-fresh` is a batch that repeats a stored
  fact, and `batch-not-closed` a membership saved before its group; neither
  is stored.

**Confirming yields by binding the result (RR-4).** RR-4 asks the replicator
to confirm that the proof yields the content fact, preferably by binding the
fact as the result and checking that a match exists, rather than running the
whole query. Its open question was whether that is cheap enough with the
current inverse algorithm or needs an algorithm of its own. It needs none: the
check is the inverse machinery with the pin at the content fact.
`Proof.confirms` (`Content.lean`) takes each descendant of the specification
(each child specification, with its parent's matches before its own), with
every given held, and each label it projects:

- a label that is a given is bound already, so the given must be the content
  fact, and the matches must have a solution;
- a label that is an unknown is pinned: its match gains `l = __f`, keeping its
  own conditions, existential ones included (`pinUnknown`, the first clause of
  `touchMatches true`), with `__f` bound to the content fact. The pinned
  specification (`Specification.pinResult`) is reordered by `reorderOrSelf`,
  so the read starts at the content fact and walks to the givens, and the
  check asks only whether it has a solution.

`confirms_eq_yields` proves this is `Proof.yields` for every proof whose
descendants are well formed. The proof reads three consequences of
`WellFormed`: a descendant's top-level unknowns are distinct
(`WellNamedMatches.nodup`), none is `__f` (`WellFormed.not_pin`), and no
condition names `__f` (`WellFormed.pin_unused`), so pinning changes nothing
but the one label. `evalMatches_pinUnknown` is the core: pinning `l`'s match
keeps exactly the solutions that bind `l` to the fact. Reordering is
`reorderOrSelf_correct`, already proved for the inverses, and needs no
hypothesis. The projection clause of `WellFormed` is not read: a projected
label that is neither a given nor an unknown is unbound, and names nothing.

When `reorderChecked` refuses, `reorderOrSelf` keeps the pinned specification
in written order. That is still correct, but no cheaper than a full read for
that label: it starts at the givens. It refuses when some match is reached by
no path condition from the pin or the givens, as in a product
(`(g: Group) { d: Document [d->group: Group = g], e: Other } => d`, pinning
`d`). On the random well-formed specifications of `check-content` it never
refuses: 0 of 4289 pinned specifications on seed 1, and 0 of 4316 on seed 2.

`read` runs `Proof.confirms`, not `Proof.yields`, and SEC-1 and
`read_admitted` are still stated against `Proof.yields` (through
`Policy.admits`), so they now say the check is right, not only that the
handler calls it. `Replicator.read_bound` is the step: with a bound proof,
`read` asks what `Policy.admits` asks.

**Every hypothesis on the proof is checked at RR-1.** The proof is
attacker-supplied, so whatever a theorem assumes of it must be refused when
false. The only hypothesis on the proof any content theorem assumes is
`confirms_eq_yields`'s, every descendant well formed. `Proof.bound` checks it
(`isWellFormedDeep`) and RR-1's given count, and `Proof.bound_iff` proves it
decides `Proof.Bound`, their conjunction; `read_badRequest` proves `read`
answers 400 exactly when the proof is not bound. Connectivity
(`ConnectedDescendants`) is not checked: no content theorem uses it, and a
disconnected proof is only read in written order (above).

**Conditions on a given are refused at RR-1.** Lean's `Specification` has no
conditions on its givens, so no content theorem covers a proof that has them.
jinaga.js's specification type has them, and evaluates them. The TypeScript
store first accepted them and ignored them, so it served
`(d: Document [!E { a: Archived [a->doc: Document = d] }]) { } => d` for an
archived `d`, and a rule proof's given conditions were ignored the same way.
Its `bound` now refuses a specification with conditions on any given
(`hasGivenConditions`; a child specification shares its parent's givens),
which answers a reader's proof 400 and makes a rule proof with them authorize
nothing, as an unbound rule proof already does. The Lean generator cannot
express such a proof, so `run-content-vectors.ts` checks both on two
port-only cases. A later extension could accept them by reducing them to a
match first (`reduceGivenConditions`, proved to keep what a replica reads by
`read_reduceGivenConditions`). The TypeScript store
calls the deep `isWellFormed` of `ports/typescript/well-formed.ts` instead of
taking a well-formedness check from its harness. The vectors
`ill-formed-child-specification` (a child declares its parent's unknown again,
so the descendant's unknowns are not distinct), `reserved-label` (the
specification declares `__f`) and `unbound-given` (too few givens, and too
many) expect 400.

**Distribution rules are specifications (RR-3).** `Policy.distribution`
gives, for a specification and its givens, one clause per feed, each the rule
proofs that may authorize that feed: a rule `share(feed).with(users)` is the
proof that runs `users` from the feed's givens. Which rule matches which feed
is fixed by the model, so `distribution` reads no store.
`Policy.distributes u s gs g` asks every clause for a bound rule proof that
`Proof.confirms` on `g` names `u` (on a bound proof that is `Proof.yields`,
`confirms_eq_yields`, which `admits_stable` reads); a rule proof that is not
bound counts for nothing, so the policy needs no well-formedness hypothesis. The engine is the same as the
reader's proof's (RR-3), and so are its inverses, which is what lets a save
invalidate a cached decision (below). The named cases use membership:
`(g: Group) { m: Member [ m->group: Group = g, !E { r: Removal [ r->member:
Member = m, !E { s: Restore [ s->removal: Removal = r ] } ] } ] u: Jinaga.User
[ u = m->user: Jinaga.User ] } => u` (`ContentCases.membersOf`), and
`check-content` the same rule over its random graphs.

**The obligation on distribution rules.** SEC-1 says the replicator asks the
distribution engine and checks yields, and nothing more. A proof that names
the content fact as its own given, `(d: Document) { } => d` with `d := F`, is
well formed and yields `F` on every store that holds `F` (the vector
`content-fact-as-given`). For that proof, yields is vacuous and SEC-1 is only
as strong as the engine's verdict. With no clauses, `Policy.distributes` is
`true`, the empty conjunction: that is precisely the obligation. The engine
must not authorize a specification merely because it has no feeds to check;
`distribution` must give every specification at least one clause, as the
feeds endpoint gives every specification at least one feed. `check-content`
uses the empty conjunction on purpose, to test the handler's yields check
with rules that admit everyone.

`check-content` runs each statement as written on 2000 random histories per
seed, with a policy in which a content hash is one of three values. Besides
SEC-1 to SEC-5 and `read_admitted`, it checks RR-1 (`read_badRequest`) and
`confirms_eq_yields`, which it tests on the handler: for a bound proof, the
handler's admission with distribution rules that admit everyone must be
`Proof.yields`. It also checks `Proof.confirms` against `Proof.yields` on
every bound read, and that a save stores only a fresh batch
(`Replicator.save_fresh`) and keeps the store closed
(`Replicator.run_closed`). The real handlers break none (they are proved). The
counts are in the handlers' table below, from the same run as the cache's.

What each new statement rules out: `confirms_eq_yields` every mutant of the
check (a check that ignores children or binds fewer labels refuses an
admitted reader, which `read_admitted` also sees; one that drops the pinned
match's conditions or skips the givens serves a reader whose proof yields
nothing, which SEC-1 also sees for the dropped conditions on both seeds, and
for the skipped givens on seed 1 but not seed 2); `read_badRequest` a 400 check that misses an
ill-formed child specification, which `confirms_eq_yields` does not cover;
`Replicator.save_fresh` a save that stores a batch that is not fresh, and
`Replicator.run_closed` one that stores a batch naming a predecessor it does
not hold. On the random histories each of the last two is caught by its own
statement alone: the answers they change break none of the others.

One history in three has child specifications (`genChildSpec`). One proof in
eight binds a given to the key read, whatever its type, so that a given the
store does not hold as one is tried, and each history reads one proof whose
child specification declares its parent's unknowns again. Random
specifications rarely yield a document, so only 48 of 82000 random reads are
served on seed 1 (61 on seed 2), and the success path is thin there. The vectors
cover it: `vectors/content/` holds twenty-eight named histories on one
documents-in-groups model, among them the documents read as a child
specification, a proof projecting both a given and an unknown, a pinned match
with an existential condition, a given the store does not hold, and (for the
cache, below) a revocation, a restore, a given arriving, a batch whose facts
change a result only together, a batch that is not fresh, and one that is
not closed. Each is checked to catch the mutants it names, and together they
catch all fifteen of the handlers' and all six of the cache's.
`ports/typescript/content-store.ts` is a reference port that passes them,
computing yields with the port of `Proof.confirms`
(`ports/typescript/content-proof.ts`), which the harness also checks against
each vector's `yields`.

### The content hash (jinaga-spec#64)

`Policy.hash` stays abstract, and no theorem changes. But a client hashes a
blob when it stages it (CW-1), a replicator while it streams the upload
(RW-5), and a client again on arrival (CR-7), so the libraries must agree
byte for byte. The content hash is defined (`vectors/README.md`) as the fact
hash's digest and encoding applied to the object's raw bytes, with no
serialization: standard, padded base64 of SHA-512.

The fact hash is read from jinaga.js 6.17.0 as published on npm (`npm pack
jinaga`): `computeObjectHash` (`src/fact/hash.ts`, lines 53 to 59) hashes the
canonical string with `computeStringHash` (`src/util/encoding.ts`, lines 5 to
10), which takes the string's UTF-8 (`@stablelib/utf8`), its SHA-512
(`@stablelib/sha512` 1.0.1) and `encode` of `@stablelib/base64` 1.0.1, the
standard alphabet with `=` padding. `npm run content-hash` checks the vectors
against those primitives when `JINAGA_JS` names a checkout; it passed against
that package with its dependencies installed. jinaga.net's fact hash is
unverified: no checkout was available.

The content hash has no prefix or other domain separation from fact hashes,
and needs none. Nothing is looked up by content hash: an object is stored and
read under its content key, a `FactId` (ST-1). A read depends on the fact
store and, among objects, only on the one under that key (`read_isolated`,
SEC-4: two replicators with the same store and the same object under the key
answer alike). A content hash can equal a fact's hash without any collision:
upload a fact's canonical string and the two are equal by construction. The
argument therefore rests on SEC-4 and ST-1, not on collision resistance:
since no read path takes a hash as a key, equal strings cannot be confused.
A prefix added for safety would only break agreement with the libraries that
hash the bytes as they are.

`computeStringHash` itself is not the content hash: it takes a string, and
bytes that are not valid UTF-8 do not survive decoding. The runner checks
that `computeStringHash` of `not-utf8`'s lossily decoded text differs from its
content hash.

### Revocation and the proof cache: SEC-7 and NF-2

NF-2 lets the replicator cache proof results per user, specification and
givens, and asks that any saved fact that could change a result invalidate the
entry. SEC-7 asks that once a proof stops yielding the fact, or the user loses
distribution rights, no later read with that proof returns the object.

**SEC-7 as written is false of Jinaga.** A revocation is a negative
existential condition (a `Removal` of a membership), and a later fact can undo
it (a `Restore` of the removal), so a user can lose rights and then regain
them, and a proof can stop yielding a fact and then yield it again. The vector
`membership-restored` is that history: SEC-7 as written forbids its last
answer, which SEC-1 requires. What must hold is SEC-1 at the moment of every
read, including one answered from the cache.

`ContentCache.lean` models the cache: a list of entries `(user, proof, key,
admitted)`. A read with no token, or with a proof that is not bound, is
answered as `Replicator.read` answers it; otherwise the decision comes from
the cache, or is computed as `read` computes it (`Proof.confirms`) and cached.
Saving a fresh batch `B` onto `g` drops an entry when `B` may change the
reader's proof's yields of the key, or some rule proof's yields of the user
(`Policy.invalidates`). "May change `q.yields · k`" is `Proof.mayChange`: some
descendant `d` of `q.spec` has a row of `candidates d (d.bindGivens q.givens) g
B` (`Reorder.lean`) containing `k`. Reads change the state, so a history
(`Request`) holds reads as well as events.

| theorem | statement |
|---|---|
| `isFresh_iff` | the freshness check `save` runs decides `Fresh`, the hypothesis of `candidates_complete` |
| `Replicator.save_fresh` | a save stores the whole batch, and only if it is fresh, or nothing |
| `yields_stable` | for a bound proof and a fresh batch that `mayChange` does not flag, `yields` is unchanged |
| `admits_stable` | for an entry with a bound proof that the save does not invalidate, `Policy.admits` is unchanged |
| `cache_valid` | after any history, every cache entry's proof is bound and its decision is `Policy.admits` on the current store |
| `cached_read` | after any history, the cached replicator answers every read exactly as `Replicator.read` does on the state the same saves and uploads produce |
| `cached_read_authorized` | SEC-7, pointwise: a read answered with an object, from the cache or not, is by an authenticated user whom the rules admit on the store at that moment, and whose proof yields the fact there |

`yields_stable` is `candidates_complete` read for one fact: whether a proof
yields `k` depends only on which rows naming `k` it reads, and every row a
fresh batch adds or removes is a candidate, so if no candidate names `k`,
neither does any change. No theorem has a hypothesis on the history: `save`
checks freshness. `candidates` is used rather than the exact `changes`
(`Exact.lean`), which would invalidate less but needs `ProjectsUnknowns`.

`check-content` runs `cached_read` as written on its random histories:
memberships of random users in the facts of the first given's type (or of a
predecessor of it, so that a given can arrive after the rule's group), half of
them removed and half the removals restored, saved with the graph in batches
of one to four, one batch in ten repeating a stored fact and one in ten
preceded by a later fact saved alone before a predecessor it names, with a few
proofs read again and again through the history. Each cache mutant
invalidates too little, in one way, and must be caught by `cached_read` and
by a named vector. Every count in this section is from one run of
`check-content` at the commit that adds `Replicator.run_closed`, on seeds 1
and 2 (`verify.sh` runs both):

| cache mutant | caught on (seed 1, seed 2) | named vector | what `cached_read` rules out |
|---|---|---|---|
| invalidate only on a fact of the content fact's type | 47, 30 | `membership-revoked` | a cache keyed to the content's own facts misses a `Removal`, which the rule reads |
| ignore a given arriving in the batch | 2, 2 | `given-arrives` | a given was not stored, so nothing was read; when it arrives every result is new, and no inverse need find it |
| read each fact of a batch alone | 2, 2 | `batch-arrives-together` | facts that change a result only together (a group, its document and a membership): each fact's inverses must read the whole batch (jinaga/jinaga-spec#11) |
| never invalidate on a revocation (gained-direction inverses only) | 16, 12 | `membership-revoked` | the SEC-7 scenario: a removal under a negative existential condition is a loss, which only the other direction's inverses find |
| keep the entries the rules refused | 115, 106 | `membership-restored` | a restore turns a refusal into an admission, so refusals must be dropped too |
| invalidate on the reader's proof only, never the rules | 43, 31 | `membership-revoked` | a reader who loses distribution rights, with the proof still yielding the fact |

The arrival and batch mutants are rare on random histories (2 of 2000 each on
both seeds): a given usually arrives before anything that could admit a
reader, and a result that needs two facts of one batch needs a reader already
admitted. The named vectors catch each one directly.

An earlier draft listed a seventh cache mutant, "store a batch without
checking it is fresh", as a test of `candidates_complete`'s hypothesis. It
was not one: it was caught because the stored facts diverged from the
uncached replicator's, and an uncached replicator that skips `isFresh`
diverges on the same vector. It is now a handler mutant, caught by the
statement it breaks, `Replicator.save_fresh`.

The handlers' mutants, from the same run:

| mutant | caught on (seed 1, seed 2) | by |
|---|---|---|
| no yields check | 2000, 2000 | SEC-1, SEC-5, `confirms_eq_yields` |
| the check ignores child specifications | 17, 18 | `confirms_eq_yields`, `read_admitted` |
| the check binds only the first projected label | 53, 47 | `confirms_eq_yields`, `read_admitted` |
| the check drops the pinned match's own conditions | 691, 683 | SEC-1, SEC-5, `confirms_eq_yields` |
| the check skips the givens being held | 16, 13 | SEC-1, SEC-5, `confirms_eq_yields` (seed 2: `confirms_eq_yields` alone) |
| RR-1 checks only the top-level specification | 1837, 1782 | RR-1 |
| no distribution check | 62, 59 | SEC-1, SEC-5 |
| store bytes without hashing them | 625, 642 | SEC-2, SEC-3 |
| authorize the fact's presence, not the writer (RW-4) | 642, 644 | SEC-3, SEC-5 |
| map a key to stored bytes of the same hash (ST-3) | 36, 34 | SEC-3 |
| look an object up by its content hash (ST-1) | 23, 21 | SEC-4, `read_admitted` |
| answer 404 before checking the proof (RR-5) | 1153, 1127 | SEC-5 |
| answer a repeat upload before checking the writer (RW-8) | 144, 143 | SEC-5 |
| store a batch without checking it is fresh | 512, 591 | `Replicator.save_fresh` |
| store a batch that names a predecessor not stored | 820, 860 | `Replicator.run_closed` |

Seed 1 saves 560 batches that are not fresh and 1299 that are not closed
(seed 2: 653 and 1454): a batch the replicator refuses drops its new facts,
so later batches that name them are not closed either.

The TypeScript port `ports/typescript/content-cache.ts` caches and
invalidates in the same way, with `candidateInverses` from
`inverse-candidates.ts`, and passes every content vector, as does the
uncached `content-store.ts`.

Not covered: the reactive hold (RR-6, SEC-6), purging (ST-4), chunked
uploads, notifications and the batch status endpoint (RR-10, RR-11), and the
client (SEC-8). A cache with a bound on its size, or entries that expire, only
drops more, so `cached_read` covers it.

## Where the proof effort went

| file | what it proves |
|---|---|
| `Locality.lean` | Evaluating matches depends only on the labels they use. |
| `SplitPaths.lean` | A step, and a walk of at least one step, land on a fact of a known type. |
| `Derivation.lean` | The tail's givens, derived as used labels in scope, are closed; every label a well-formed, scoped list of matches uses is ordinary. |
| `Main.lean` | Two environments agreeing on a scope give the same projected results. |
| `WellFormedCheck.lean` | The executable check decides `WellFormed`. |
| `Basic.lean`, `Scoped.lean` | Helper facts, and the definitions of well-formedness. |
| `Proofs/Store.lean` | `authGraph`'s retyping keeps the given out of every candidate list and every walk of at least one step; `store_denies`/`store_correct`. |
| `Proofs/Hoist.lean` | The split agrees with the reference semantics, for every well-formed specification, at any nesting depth. |
| `Proofs/Maintain.lean` | A held set re-checked on covering candidates equals the result; re-checking in turn on one graph is re-checking at once; graphs holding the same facts give the same results. |
| `Proofs/Inverse.lean` | `shakeTree`'s rotation loop always stops within the length of the suffix it rotates. |
| `Proofs/Fresh.lean` | A fresh batch changes no walk that starts outside it. |
| `Proofs/Candidates.lean` | Every result a fresh batch changes is a result of one of the inverses, given one of the batch's facts. |
| `Proofs/Reorder.lean` | Matches are a conjunction, so a checked arrangement has the same solutions; flattening an `exists` keeps them. |
| `Proofs/Exact.lean` | Two match lists over the same unknowns read as one are a conjunction; the exact inverses are sound on the new graph and complete, so a stream that applies their changes is exact. |
| `Proofs/Stream.lean` | The candidates cover every change a replica reads, a replica that notifies each fact of a batch is exact, and a re-checking stream is exact. |
| `Proofs/GivenConditions.lean` | Reducing conditions on a given to a match keeps what a replica reads, so the stream of a conditioned specification is exact. |
| `Cascade/CMap.lean`, `Json.lean` | Sorted maps with the same lookups are equal; the encoding of JSON values is injective, so it orders and compares them. |
| `Proofs/Cascade/Tree.lean`, `Step.lean` | `apply` keeps a tree well formed and takes equivalent trees to equivalent trees; correct steps compose, and a pipeline's output depends only on its input. |
| `Proofs/Cascade/MapProps.lean` | `dropProperty` and `defineProperty`, which change the props of one level. |
| `Proofs/Cascade/Aggregate.lean` | The aggregates (`sum`, `count`, `min`, `max`, `average`): forwarding each event and changing the aggregate of each affected parent. Correctness holds for any function of the contributing children's values; the denotation needs it to ignore their order. |
| `Proofs/Cascade/GroupBy.lean` | `groupBy` at the root, including the move that #29 broke. |
| `Proofs/Cascade/Filter.lean` | `filter` at the root: visibility is local to a subtree, and admitting or evicting it is exact. |
| `Proofs/Cascade/Input.lean` | Composed keys are unique; the input's events are always accepted and take it to what it received; pipelines are correct and order independent over what a caller does. |
| `Proofs/Cascade/Session.lean` | Nested arrays that hold a tree hold each node where the placement index locates it; located events keep them holding the tree; queueing and flushing keep the session's invariant, and recording a placement after the push would drop a child. |
| `Proofs/Cascade/Sig.lean` | Each step emits only what its descriptor declares can change or move; keeping a signature composes, so a subscriber to a pipeline's descriptor hears every event. |
| `Proofs/Cascade/Cache.lean` | The TypeScript caches of `groupBy`, the aggregates and `defineProperty` emit exactly the model's events, so the steps as written are correct. |
| `Proofs/Cascade/Flatten.lean` | `flatten` at the root is correct: parents' changes and moves reach their rows, and a moved child takes on its new parent's values; it emits only what its descriptor declares. |
| `Proofs/Cascade/Ordered.lean` | A step that overwrites properties with values computed from the input is correct for any values; `cumulativeSum`, `replaceToDelta` and `pickBy*` are instances, their values ignore list order under a strict total order, and they match the TypeScript's sorted list or heap. |
| `Proofs/Cascade/Sources.lean` | Each source's correct pipeline, run on its own tree, is correct for the sources; a correct join composes with what comes before and after it, and its output does not depend on how the sources' events interleave. |
| `Proofs/Cascade/Enrich.lean` | `enrich` is correct for any event in either source, and its copies depend only on what the secondary holds. |
| `Proofs/Cascade/Pipeline.lean` | A five-step pipeline is correct and independent of arrival order, from the steps' theorems alone. |
| `Proofs/Feeds.lean` | A feed has only path conditions, so a tuple new to a feed binds a new fact. |
| `Proofs/Cursor.lean` | Paging by bookmark keeps a replica caught up from the first page to an empty one while the graph grows. |
| `Proofs/Cover.lean` | A flat level, then any level, agrees on a replica holding what its feeds deliver; every flat feed is scoped and binds each label once; a replica holding what the flat feeds deliver finds the replicator's solutions. |
| `Proofs/Content.lean` | The content store's read and write meet SEC-1 to SEC-5 for every policy, after any history of saves and uploads; an admitted reader is served and an authorized upload stored. |
| `Proofs/ContentCache.lean` | A cache of read decisions that drops an entry on every fresh batch whose inverse candidates name its key or user never changes an answer, so SEC-1 holds at every read (SEC-7, pointwise). |
| `Proofs/Children.lean` | The feeds of a specification are the flat feeds of its descendants; so each requirement holds with child specifications, the replica reads their results at every depth, and a replica that has paged every feed converges. |

The redesign changed the proofs less than it changed the definitions. The
derivation of the tail's givens fell from 386 lines to 344, and no longer needs
the tail's own labels to be disjoint from its givens. `SplitPaths.lean` grew from
264 lines to 285, because the labels are now numbered by position and the
induction carries the index. The proofs lost the fresh-name search and its
pigeonhole argument, and every lemma about labels "declared anywhere". The
definitions, which a port must read, are where the reduction shows: 417 lines
became 350, with the check included.

## Not covered

`field`/`hash`/`time` projections are not modelled. Child specifications in a
projection are read, with their results, only by feeds (`Specification.Reads`).
`evaluate`, which the split, the store and the inverses are proved against,
reads a projection's rows; a child specification adds none. What those
algorithms do take from a child specification is its labels. The split's tail
is given the labels a child joins (`tailGivenAt`), and the label for conditions
on a given avoids every label a child names (`givenConditionsLabel`), both
through `Projection.allLabels`. Their theorems do not mention a child's
results: the inverses of a child specification (`invertProjection`) are not
ported. In the cascade model: `groupBy`,
`filter` and `flatten` below the root; and the caches of the steps other than
`groupBy`, the aggregates and `defineProperty`. Conditions on givens are modelled for the inverse algorithm and
the stream, not for the split. Skeleton canonicity (feed hashes), the stream
session's wake-ups (liveness), and distribution soundness are not started.
