# Contracts between algorithms

An algorithm is correct only for the inputs it expects. `split_correct` is a
theorem about **well-formed** specifications. This document says what the split
expects, who is responsible for providing it, and how a library can make the
expectation true by construction. Where a postcondition is proved, it says
where. Where it is not, it says so, and the obligation stays with whoever
composes the steps.

## The split's contract

**Precondition** (`WellFormed`, `JinagaSpec/Proofs/Scoped.lean`; executable as
`isWellFormed`, `JinagaSpec/WellFormed.lean`):

1. **Scoped.** Every label a path condition names is in scope: a given, an
   earlier match, or, inside an existential condition, the enclosing unknown.
   In particular, a match never joins its own unknown.
2. **Well-named.** Every declared label is new, not already in scope (scope is
   lexical, so sibling existential conditions may reuse a name), and ordinary,
   not reserved. A label that begins with `__` is reserved for the split.
3. **Projected.** The projection names only givens and top-level unknowns.

**Postconditions.**

| | Status |
|---|---|
| The split returns the same results as the whole specification (as sets). | Proved: `split_correct`. |
| The split is total. It has a head, possibly with no matches, and a tail only when a match seeks successors. | By construction: `Split.head` is not optional. |
| The tail's path conditions and projection name only the tail's givens or labels the tail declares earlier. | Proved: `tail_scoped`. |
| Every split label is reserved, so it differs from every label the specification declares. | Proved: `splitPaths_names`, `isReserved_splitLabel`. |
| The head is deterministic (the graph can run it). | True by construction, **not proved**. |
| The head and tail are themselves `WellFormed`, so they can be split or transformed again. | **Not stated, not proved.** |
| A rule whose tail is not given the fact under authorization means the same on the store as the specification means. | Proved: `store_correct`. |
| A rule whose tail is given it admits nobody. | Proved: `store_denies`. |

The last two matter only if a head or tail is fed to another algorithm that
assumes well-formedness. Nothing does today.

## Make it true by construction

A precondition that every caller must remember is a precondition that will be
forgotten. Two moves remove the need to remember it.

1. **Check once, at the boundary where a specification enters.** `isWellFormed`
   decides the precondition exactly (`isWellFormed_iff`), so a specification that
   passes is split correctly (`split_correct_of_check`), and one the theorem
   covers is never rejected.
2. **Give the checked value a type.** A function that relies on the
   precondition takes the type that only the check can make. The compiler then
   enforces the precondition for every caller, and no internal function checks it
   again.

`jinaga.js` does both in pull requests
[#308](https://github.com/jinaga/jinaga.js/pull/308) and
[#311](https://github.com/jinaga/jinaga.js/pull/311):
`assertWellFormed` runs the check and returns a `WellFormedSpecification`, which
`splitBeforeFirstSuccessor` takes, and `AuthorizationRuleSpecification` calls it
once in its constructor. A test with `@ts-expect-error` shows the compiler
rejecting a specification that has not been checked.

The rule-level conditions of an authorization rule belong at the same boundary:
one given, and a projection of a single fact. The split does not need them, but
the evaluator does: it seeds the head from `head.given[0]`, which seeds every
given exactly when there is one. Checked once in the constructor, the evaluator
does not check them per call.

A third rule-level condition used to belong at the same boundary: the tail
must not be given the rule's own given, because a rule runs while its fact is
being authorized, before that fact is saved, so the store the tail runs on
does not have it (`JinagaSpec/Store.lean`, `docs/findings.md`).
`tailReadsGiven` decides this from the split alone, and `store_denies`/
`store_correct` say it is exact: true means the rule admits nobody, false
means the store means what the graph means.

`jinaga.js` no longer checks this at construction. Pull request
[#308](https://github.com/jinaga/jinaga.js/pull/308), which removed the
tail's old single-given restriction so a tail can be given the head's own
projected labels as well as the rule's given, also dropped the upfront
`AuthorizationRuleError` this condition used to raise: a rule shaped this way
now constructs and runs, and is refused with `Forbidden` only because the
store cannot read a fact that has not been saved yet — `store_denies`'s own
mechanism, reached at runtime rather than guarded against in advance.
`jinaga.js`'s own test for this shape
(`test/authorization/authorizationSplitTailSpec.ts`) documents that the
decision is still the wrong one for formulation D (jinaga/jinaga.js#231): the
write should be admitted, and wiring `hoist` in place of the split
(`hoist_correct`, below) is what would let it read a predecessor walk of the
given instead of the given itself, tracked as jinaga/jinaga.js#297.

## `hoist`'s contract

`hoist` (`JinagaSpec/Hoist.lean`) is an alternative to
`splitBeforeFirstSuccessor` that reaches into the tail's existential
conditions, at any depth, for a predecessor walk of a label already in scope,
and hoists it into the head wherever doing so is sound. Its precondition is
exactly the split's (`WellFormed`, above) — no reduced scope, no extra
condition.

**Postconditions.**

| | Status |
|---|---|
| `hoist` returns the same results as the whole specification (as sets). | Proved: `hoist_correct`. |
| A rule whose tail is not given the fact under authorization means the same on the store as the specification means, with `hoist` in place of the split. | Proved: `store_correct_hoist`. |
| A rule whose tail is given it admits nobody, with `hoist` in place of the split. | Proved: `store_denies_hoist`. |

`hoist` is not yet wired into `jinaga.js`'s constructor; see the previous
section and `docs/findings.md` for the commutation argument the general proof
turns on.

## Who can hand the split a specification

Traced in `jinaga.js` and the local `jinaga.net` checkout:

- **`splitBeforeFirstSuccessor` has one caller in `jinaga.js`**, the class
  `AuthorizationRuleSpecification` (`src/authorization/authorizationRules.ts`).
  `jinaga.net` has the same shape (`Authorization/AuthorizationRuleSpecification.cs`).
  The other local checkouts do not call it.
- **The class is not exported,** but the function is, so any package can call it.
  With the type above, a caller must obtain a `WellFormedSpecification` from
  `assertWellFormed` first.
- **The class is built in three places:** the model builder, the
  predecessor-selector builder, and the parser (`AuthorizationRules.loadFromDescription`).
  All three reach the constructor, so the check there covers each of them, and
  any future producer, without relying on any of them.

## Which producer establishes which condition

| | Scoped | Well-named | Projected |
|---|---|---|---|
| **Parser** | Enforced: a path's joined label must be in `labels`, which excludes the match's own unknown. | Enforced for *new* (`parseMatch`: "has already been used"). Scope is lexical. **Not enforced** for reserved. | **Not enforced.** `parseProjection` and `parseComponent` never look a label up. |
| **Model builder** | By construction, unverified. | By construction, unverified. | By construction, unverified. |
| **`validateSpecification`** | Not checked. | Not checked. | Not checked. |
| **`assertWellFormed`** | Checked. | Checked. | Checked. |

`npm run audit` in `ports/typescript` runs the parser and `validateSpecification`
over the well-formedness vectors. Six ill-formed vectors pass both: the three
projection violations and the three reserved-label violations. The check at the
boundary rejects them.

## Other algorithms that produce or transform specifications

These are exported from `jinaga.js` and are not modelled here:
`alphaTransform`, `intersectSpecificationWithDistribution`, `reduceSpecification`,
`buildFeeds`, and the inverse-specification builders. **None feeds the split in
the current code.** If any ever does, it must preserve `WellFormed`, and today
there is no statement, and no proof, that it does. For each, the obligation is
one of: a proof here, or a test in the implementation that its output is
well-formed for well-formed input.

## Checking a sequence of steps

For a pipeline `s0 → f1 → ... → fn → split`, the split's precondition holds if

1. the producer of `s0` establishes `WellFormed s0`,
2. each `fi` preserves it: `WellFormed x → WellFormed (fi x)`, and
3. so `WellFormed (fn (... (f1 s0)))` holds when the split runs.

A cell that is not proved is a runtime obligation, and the type above turns it
into one the compiler tracks: the pipeline must end in `assertWellFormed`.

| step | establishes or preserves | how it is known |
|---|---|---|
| producer | Scoped, Well-named, Projected | proved / enforced in code / **unverified** |
| `f1` | ... | ... |

## What is not covered

Conditions on givens, and the labels declared inside nested specification
projections, are not modelled, and the check ignores them. The reserved-label
rule makes the second harmless for the split's own labels: no declaration site,
modelled or not, can collide with a name it may not use.

## Remaining work

1. **`jinaga.net`:** the same check at the same boundary, and the split
   simplified to match. Filed as issues.
2. **State `WellFormed` postconditions** for the algorithms above, and prove them
   or test them.
3. **Prove the split's own output well-formed**, so a head or tail can be passed
   on.
4. **Model conditions on givens and the remaining projections.**
