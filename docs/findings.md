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
| `Proofs/Stream.lean` | The candidates cover every change a replica reads, a replica that notifies each fact of a batch is exact, and a re-checking stream is exact. |
| `Proofs/GivenConditions.lean` | Reducing conditions on a given to a match keeps what a replica reads, so the stream of a conditioned specification is exact. |

The redesign changed the proofs less than it changed the definitions. The
derivation of the tail's givens fell from 386 lines to 344, and no longer needs
the tail's own labels to be disjoint from its givens. `SplitPaths.lean` grew from
264 lines to 285, because the labels are now numbered by position and the
induction carries the index. The proofs lost the fresh-name search and its
pigeonhole argument, and every lemma about labels "declared anywhere". The
definitions, which a port must read, are where the reduction shows: 417 lines
became 350, with the check included.

## Not covered

`field`/`hash`/`time` projections and nested specification projections are
not modelled. Conditions on givens are modelled for the inverse algorithm and
the stream, not for the split. `buildFeeds`, skeleton canonicity
and distribution soundness are not started.
