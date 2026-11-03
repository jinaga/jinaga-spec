# jinaga-spec

A formal specification of Jinaga's specification language and the algorithms
that transform it, with machine-checked proofs that they are correct, and
conformance vectors that any implementation can run.

Two algorithms are covered end to end:

- **The split** (`splitBeforeFirstSuccessor`), which cuts an authorization rule
  into a head that runs on the in-memory graph and a tail that runs on the store.
  `split_correct` proves it keeps the rule's meaning.
- **The inverse algorithm** (`candidates`), which says which results of a
  subscription a batch of new facts might have changed. `stream_correct` proves
  that a stream which re-checks those candidates after every batch holds exactly
  the specification's results. Its exact variant (`changes`) strengthens each
  inverse so that it reports adds and removes with no re-check, and
  `exact_stream_correct` proves a stream that applies them exact, when the
  projection names every top-level unknown.

**Status.** It began as a spike to find out whether this approach keeps the
definitions readable, the proofs tractable, and the ports checkable. It does,
and the libraries now port from it:

- **`jinaga.js`** runs the proven inverse algorithm
  (`src/specification/inverse-candidates.ts`) and refuses ill-formed
  specifications where they enter.
- **`jinaga.net`** has ported both (`InverseCandidates.cs`,
  `WellFormedSpecification.cs`), and runs a pinned copy of the vectors in its
  tests.

## What is here

| | |
|---|---|
| `JinagaSpec/Syntax.lean`, `Semantics.lean`, `Split.lean` | The definitions: the language, what it means over a fact graph (`evaluate`, and `read`, what a replica reads), and the shared plumbing a split's result evaluates through. Written to be read next to the TypeScript. |
| `JinagaSpec/WellFormed.lean` | `isWellFormed`: an executable check of the preconditions every theorem assumes, proved to agree with `WellFormed`. |
| `JinagaSpec/Hoist.lean` | `splitBeforeFirstSuccessor`: the split. Reaches into existential conditions at any depth, hoisting a predecessor walk into the head wherever doing so is sound. |
| `JinagaSpec/Store.lean` | The graph a rule runs on while its fact is under authorization, and the boundary `tailReadsGiven` decides. |
| `JinagaSpec/Candidates.lean`, `Reorder.lean` | `candidates`: the inverses of a specification, each reordered to start at the new fact. |
| `JinagaSpec/Exact.lean` | `changes`: the exact inverses, which report adds and removes from one read each, and a stream that applies them. |
| `JinagaSpec/Maintain.lean` | A stream that re-checks candidates after each batch. |
| `JinagaSpec/GivenConditions.lean` | Conditions on a given, and their reduction to a match. |
| `JinagaSpec/Inverse.lean` | A port of `jinaga.js`'s earlier `invertSpecification`, kept to measure what the proven algorithm replaced. |
| `JinagaSpec/Proofs/` | The proofs. `Hoist.lean` and `Store.lean` for the split, `Stream.lean`, `Exact.lean` and `GivenConditions.lean` for the inverse algorithm. |
| `JinagaSpec/Cascade/` | A model of `@jinaga/cascade-core`'s incremental pipeline: the output tree and the protocol its events keep (`Tree.lean`), steps and their composition (`Step.lean`), the steps themselves (`Steps.lean`), the input (`Input.lean`), the output session (`Session.lean`), and the steps' caches (`Cache.lean`). |
| `JinagaSpec/Proofs/Cascade/` | The proofs that those steps are correct, that correct steps compose, and that a pipeline's output does not depend on the order its rows arrive. |
| `JinagaSpec/Cases.lean`, `InverseCases.lean`, `Vectors.lean` | Named cases, and the program that writes the vectors from the definitions. |
| `vectors/` | The generated conformance vectors: `split/`, `well-formed/` and `inverse/`. Any port can read them; `vectors/README.md` gives the format. |
| `ports/typescript/` | Runs the vectors against `jinaga.js`, holds reference implementations of `isWellFormed` and of the inverse algorithm, and audits `jinaga.js`'s parser. |
| `Check.lean`, `CheckInverse.lean` | Randomized tests of the theorems, with mutation checks. They run before a proof exists, and keep earning their place after. |
| `docs/findings.md` | What each step turned up, in order. Read it after the theorems. |
| `docs/contracts.md` | What the split expects, who must provide it, and how to check a sequence of steps. |

## Try it

```
scripts/verify.sh
```

That builds and checks the proofs, confirms that every theorem rests only on the
standard axioms, confirms the vectors are current, runs the randomized checks,
and runs the TypeScript ports if it finds `../jinaga.js` (or `JINAGA_JS`). CI
runs everything but the TypeScript step, which depends on a `jinaga.js`
checkout. It needs [`elan`](https://github.com/leanprover/elan); the
toolchain is pinned in `lean-toolchain`, and there is no other Lean dependency
(no Mathlib).

## The split

An authorization rule is a specification. To evaluate one, `jinaga.js` cuts it
at its first match that the in-memory graph cannot run. The *head* before the
cut walks predecessors on the graph, reaching into the tail's existential
conditions, at any depth, not only the pivot's own top level, for every
predecessor walk of a label already in scope, hoisting it into the head
wherever doing so is sound. The *tail* after it runs against the store, once
per head result, seeded with only the facts the tail is given.

```lean
theorem split_correct (s : Specification) (hwf : WellFormed s) (g : Graph) (env : Env)
    (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluate g env ↔ r ∈ s.evaluate g env
```

For every well-formed specification, every graph, and every assignment of the
givens, the split and the whole specification return the same results. It
depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

`WellFormed` is what a library checks once, where a specification enters (`docs/contracts.md`):

1. **Scoped.** Every label a path condition names is in scope: a given, an
   earlier match, or, inside an existential condition, the enclosing unknown.
2. **Well-named.** Every declared label is new, not already in scope, and ordinary,
   not reserved: a label that begins with `__` belongs to the split.
3. **Projected.** The projection names only givens and top-level unknowns.

The theorem is about sets of results. It does not claim the split returns them
in the same order or with the same multiplicity, which authorization does not
need (it asks whether any result is the user).

`split_correct` runs the head and the tail on the same graph. A rule does not:
it runs while its fact is being authorized, before that fact is saved, so the
store the tail runs on does not have it. `JinagaSpec/Store.lean` models this —
`Split.evaluateStore` is the runner's behaviour, and `tailReadsGiven` is the
model's name for exactly the shape that denies everyone — and two theorems say
the boundary is exact:

```lean
theorem store_denies (hwf : WellFormed s) (hg : s.given = [g0]) (hord : OrdinaryTypes s)
    (hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (splitBeforeFirstSuccessor s) g0.name = true) :
    (splitBeforeFirstSuccessor s).evaluateStore store f env = []

theorem store_correct (hwf : WellFormed s) (hg : s.given = [g0]) (hord : OrdinaryTypes s)
    (hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (splitBeforeFirstSuccessor s) g0.name = false) (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluateStore store f env ↔
      r ∈ s.evaluate (Graph.authGraph store f) env
```

A rule with one given, whose tail reads that given, admits nobody
(`store_denies`). One that does not means, on the store, exactly what the whole
specification means on the graph that holds the given (`store_correct`). See
`docs/findings.md` for the retyping trick both proofs lean on.

`jinaga.js` refuses this shape where a rule is written:
`AuthorizationRuleSpecification`'s constructor throws `AuthorizationRuleError`
when the tail is given the rule's own given
([jinaga/jinaga.js#324](https://github.com/jinaga/jinaga.js/pull/324)). The
TypeScript port checks that it throws exactly when `tailReadsGiven` is true of
the split it runs.

Reaching into existential conditions at any depth, rather than only the
pivot's own top level, is what admits formulation D of jinaga/jinaga.js#231,
which a split confined to the pivot's own path conditions leaves with a tail
that reads the given. Not every such condition can be hoisted soundly — only
one at *positive* polarity, not enclosed by any negative existential, however
deep — and `split_correct` proves the split sound regardless, for every
well-formed specification, with no hypothesis beyond `WellFormed s`. Where
hoisting stops being sound, and the argument the proof turns on, are in
`docs/findings.md` — including an unsoundness the randomized check found in an
earlier version of the rule, one level of nesting deeper than the first
counterexample.

## The inverse algorithm and the stream

A subscription holds the results of a specification and updates them as facts
arrive. A replica saves facts in batches. For each fact of a batch, `candidates`
builds one inverse per way that fact can change a result, and reads each one,
starting at the fact, on the graph that holds the whole batch. The inverses
carry no "add" or "remove": they find *candidates*, and the stream keeps or
drops each candidate by reading the specification.

```lean
theorem stream_correct (s : Specification) (hwf : WellFormed s) (env : Env) :
    ∀ (bs : List (List Fact)) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ s.read g env) →
      (∀ pre B post, bs = pre ++ B :: post → Fresh (g ++ pre.flatten) B) →
      ∀ r, r ∈ (bs.foldl (maintainStep (s.read · env) (candidates s env)) (g, held)).2 ↔
        r ∈ s.read (g ++ bs.flatten) env
```

Start from a held set equal to the result. After each batch, re-check its
candidates. The held set is then exactly the result, for every well-formed
specification, provided each batch is *fresh*: no stored fact has the id of a
fact in the batch, or names one as a predecessor. The facts within a batch may
name each other, in any order. The theorem rests on three results:

- `candidates_complete`: every result a batch adds or removes is a candidate.
- `maintain_correct`: re-checking covering candidates keeps the held set exact.
- `notify_correct`: notifying each fact of the batch in turn, in any order, is
  the same as re-checking all of them at once.

The result is `read`, what a replica reads: nothing until every given is a fact
it holds, then `evaluate`. When a given itself arrives in a batch, every result
read afterwards is a candidate. jinaga.js's `givenCandidateInverse` does exactly
this.

### Exact inverses

The re-check costs a second read per candidate. `changes` (`Exact.lean`) makes
the inverses themselves exact. An inverse for gained results re-attaches the
specification's top-level conditions, so every row it finds is in the new
result. An inverse for lost results comes in one variant per top-level
existential condition, flipped, so every solution it finds fails the
specification on the new graph. Neither says anything about the old graph:
adding a row the set holds, or removing one it lacks, changes nothing.

```lean
theorem exact_stream_correct (s : Specification) (hwf : WellFormed s) (hpu : ProjectsUnknowns s)
    (env : Env) :
    ∀ (bs : List (List Fact)) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ s.read g env) →
      (∀ pre B post, bs = pre ++ B :: post → Fresh (g ++ pre.flatten) B) →
      ∀ r, r ∈ (bs.foldl (exactStep s env) (g, held)).2 ↔ r ∈ s.read (g ++ bs.flatten) env
```

The remove test is per solution, so it is exact for rows only when a row
determines its solution: when the projection names every top-level unknown
(`ProjectsUnknowns`). It rests on `adds_sound` and `removes_sound` (sound on
the new graph, with no freshness needed) and `changes_complete`.

A given may carry existential conditions, as in jinaga.js. `reduceGivenConditions`
moves them onto one new first match, `read_reduceGivenConditions` proves that
the reduced specification reads the same results, and `stream_correct_given`
carries the stream theorem over to it.

## Cascade pipelines

`@jinaga/cascade-core` maintains a tree of keyed arrays as rows arrive and
leave. Each pipeline step reacts to one input event at a time and emits events
for its output. jinaga/jinaga-cascade-core#29 showed the output could depend on
the order rows arrived: `groupBy` moved a row by removing it and adding it again
with the values it had at its first add.

The model addresses a node by its level and its key, and makes its parent a
value that changes (`placed`). `Tree.apply` is the protocol: it refuses adding
a node that exists or whose parent does not, removing a node that still has
children, a change whose old value is stale or equals the new one, and a move
to a missing parent.

A step is correct for a denotation `F` when its events take `F T` to `F T'`
for every event that takes the input from `T` to `T'`:

```lean
def Correct (S : Step) (F : Tree → Tree) : Prop :=
  ∀ (T : Tree) e T', T.WF → T.apply e = some T' →
    ∃ U, (F T).applyAll (S.handle T e) = some U ∧ U.Equiv (F T')

theorem andThen_correct (h₁ : Correct S₁ F₁) (hF₁ : Denotation F₁)
    (h₂ : Correct S₂ F₂) (hF₂ : Denotation F₂) : Correct (S₁.andThen S₂ F₁) (F₂ ∘ F₁)

theorem order_independent (hS : Correct S F) (hF : Denotation F) {T T₁ T₂ : Tree}
    {es₁ es₂ : List Event} (hT : T.WF)
    (h₁ : T.applyAll es₁ = some T₁) (h₂ : T.applyAll es₂ = some T₂) (h : T₁.Equiv T₂) :
    ∃ U₁ U₂, (F T).applyAll (run S T es₁) = some U₁ ∧ (F T).applyAll (run S T es₂) = some U₂ ∧
      U₁.Equiv U₂
```

Proved correct: `dropProperty`, `defineProperty` (when its function reads only
the properties the caller lists), `sum` and `count` (`aggregate_correct`, for any
contribution and weight), `groupBy` at the root (`groupBy_correct`, where a
regroup is one `placed` event), and `filter` at the root (`filter_correct`,
which adds or removes a whole subtree when a row's visibility changes, and never
forwards the change that caused it). `tiers_correct` composes five of them into
the pipeline that reproduced #29 without `enrich`.

The input (`Input.lean`) turns what a caller does into events. A child's key
is its parent's key and its own natural key (`nodeKey_inj`: composed keys are
unique). A child whose parent is not present is refused (`orphan_refused`,
jinaga/jinaga-cascade-core#31), and removing a row removes its subtree, children
first. `input_correct` proves the input's events are always accepted and take it
to exactly what it received; `ops_correct` and `ops_order_independent` carry the
pipeline theorems from events to operations, under one contract: a row is not
added twice.

The output session (`Session.lean`) keeps the nested keyed arrays React renders.
Events name only a node's parent, so the session keeps a placement index and
locates each event when it queues it; a flush runs the queue in one `setState`.
The arrays are modelled by their located entries: each node with its level and
its ancestors' keys, which is a nested keyed array up to the order of each
array. Nested arrays that hold a tree hold each node where the index locates it
(`located`), so an accepted event, located and run, leaves arrays that hold the
new tree (`session_apply`). Queueing and flushing keep the session's invariant,
and a flush drops no operation (`inv_enqueue`, `inv_flush`). The index records a
placement before the operation is pushed, because the push can flush and the
flush can call back: `record_before_push` shows a child queued from that
callback is dropped if the placement is recorded after.

A step here reads its whole input tree. A TypeScript step keeps a smaller cache
and reads only that. `Cache.lean` models the caches of `groupBy` (each row's
grouping values, each group's size), the aggregates (each child's parent and
values, each parent's count and total) and `defineProperty` (the values it
knows, and its computed value). Each implements its step (`…_implements`): from
a cache that describes the input, it emits exactly the step's events, and its
new cache describes the new input. So over any input the protocol accepts the
cached step emits what the step emits (`implements_run`), and is correct
(`…_cached_correct`). Like the TypeScript, an aggregate refreshes its snapshot
of a child only for the aggregated property, and `defineProperty` only for the
properties the caller lists; each needs the contract that what it computes reads
only those. The order in which a TypeScript step notifies listeners, which puts
a derived change before its cause, is not modelled: the two events touch different
nodes or properties, but that either order reaches the same tree is not proved.

## Reading the definitions

`Split.lean` and `Hoist.lean` are in a deliberately **portable subset**:
inductive types, total pure functions, structural recursion, and lists. No
tactics, no dependent types. A port should read line for line. Names match
TypeScript, with these exceptions:

| Lean | TypeScript |
|---|---|
| `matchList` (`matches` is reserved) | `matches` |
| `Match.mk unknown conditions` | `{ unknown, conditions }` |
| `Condition.existential «exists» matchList` | `ExistentialCondition` |
| `Env` | `ReferencesByName` |
| `evalMatches` | `FactGraph.executeMatches` |
| `Split.evaluate` | the head-then-tail evaluation in `AuthorizationRuleSpecification` |
| `Env.restrictTo names` | `startReferences(tuple, tail)` |
| `tailGivenAt` | `referencedLabels(tailMatches, inScope, projection)` |
| `splitLabel` | `splitLabel(i)` |
| `WellFormed` | what `SpecificationParser` and `validateSpecification` enforce |
| `Graph.authGraph` | the in-memory write batch, with the fact under authorization added |
| `Split.evaluateStore` | `AuthorizationRuleSpecification.isAuthorized`/`getAuthorizedPopulation`, running the tail on the store |
| `tailReadsGiven` | the check in `AuthorizationRuleSpecification`'s constructor that throws `AuthorizationRuleError` (jinaga/jinaga.js#324) |
| `splitBeforeFirstSuccessor` | `splitBeforeFirstSuccessor` (jinaga/jinaga.js#325) |
| `hoistMatches`, `hoistCondition` | `hoistMatches`, `hoistCondition`; jinaga.js numbers split labels by the length of the accumulator it builds up, where Lean threads an explicit `i : Nat` index |


## Conformance vectors

There are three kinds, all generated from the definitions (`vectors/README.md`):

- `split/`: a specification, the split the oracle computes, and both in
  Jinaga's text form.
- `well-formed/`: a specification, and whether it is well-formed.
- `inverse/`: a specification, a graph, a subscription's givens, and a fresh
  fact or batch. Each vector gives the rows gained and lost, the inverses and
  their reorderings, the candidates they find, and, where the projection names
  every top-level unknown, the exact inverses' adds and removes.

The inverse vectors are named cases plus fixed random seeds. `lake exe vectors`
refuses to write a set that leaves out any shape in its coverage list, which
includes nested and multi-match existential conditions, batches, a given
arriving, and a condition on a given.

`jinaga.js` passes every split and well-formedness vector. It passes the
inverse vectors except the two with a condition on a given, which wait on the
new label rule (jinaga/jinaga.js#371). `jinaga.net` runs a copy of the vectors
pinned at `07d5788`, from before the vectors for a given arriving and for
conditions on a given.

## What is modelled, and what is not

Modelled: path conditions, positive and negative existential conditions at any
depth, multi-valued predecessor roles, fact and composite projections, several
givens, batches of facts, and a given that is not yet stored.

Conditions on givens are modelled for the inverse algorithm and the stream
(`GivenConditions.lean`), not for the split: the split's handling of a given's
conditions (`declaredLabelsInGivens`, added in the review of #311) has no
counterpart here.

Not yet: `field`/`hash`/`time` projections, and nested specification
projections. `jinaga.js` and `jinaga.net` observe a nested collection by
flattening it into a specification of its own, which is outside the proof.
See `docs/findings.md`.

## The limit of the guarantee

The proof covers the model in `JinagaSpec/`. The TypeScript is a separate
artifact. What connects them is the conformance corpus and a reading of the two
side by side. The randomized check and the mutation check make a divergence
harder to hide, but they are not a proof about the TypeScript.

## Next

1. `jinaga.js` adopts the proven reduction of conditions on a given
   (jinaga/jinaga.js#371). `jinaga.net` re-pins its vectors and ports a
   replica's `read`, the given-arrival candidates, and that reduction.
2. A stream whose reads see later batches: prove it exact, or show that batches
   must be serialized (#13).
3. Conditions on givens in the split, the remaining projections, and nested
   collections.
4. Feeds: prove that they carry every relevant fact and that replicas converge
   (#9). Then `buildFeeds`, skeleton canonicity, and distribution soundness.
5. Cascade: the remaining steps (`min`,
   `max`, `average`, `pickBy*`, `flatten`, `enrich`, `cumulativeSum`,
   `replaceToDelta`), nested scopes, and conformance vectors and mutants that
   bind the model to `@jinaga/cascade-core`.

## License

MIT. See `LICENSE`.
