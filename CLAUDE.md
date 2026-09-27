# Working conventions for jinaga-spec

## Simplicity applies to the theorem *and* the proof

Prefer the simplest theorem that is still true and useful: minimal hypotheses,
the narrowest scope that still covers the motivating case, a hypothesis named
for what it means rather than a conjunction of ad hoc conditions. This project
already does this — `store_denies`/`store_correct` take only the hypotheses
their proofs actually use, and `hoist_correct` holds for every well-formed
specification, with no hypothesis beyond `WellFormed s`, because that turned
out to be the narrowest scope that was actually true: an earlier version
(`hoist_correct_reduced`, since deleted) covered only specifications where
`hoist`'s split-label numbering happened to match `splitPaths`', and was
replaced rather than kept once the general argument was found — a narrower
theorem earns its keep only while it is genuinely simpler to prove, not
merely because it was proved first.

The same preference applies to the *proof*, not only the statement. Measure
proof simplicity in lines of code / information complexity — "does it
compile" is not the bar. Concretely:

- Getting a proof green by iterating against the compiler is fine and
  expected. Treat the first green version as a draft. Once it compiles, do a
  pass to cut what the final proof doesn't need: `show`/`unfold`/`simp only`
  chains left over from discovering how a term reduces, intermediate `have`s
  that turned out to only be used once and inline cleanly, a hypothesis
  threaded through that the proof never reads.
- A small structural fact restated in two files (a `flatMap` congruence
  lemma, a `List.span` decomposition) belongs in one shared, non-private
  lemma in whichever file both already import — not copied.
- A family of near-identical recursive definitions that differ by one rule
  (three mutual definitions hand-copied per variant, changing one line each
  time) should be one definition parameterized over the part that varies,
  the way `Check.lean`'s `mutants : List (String × (Split → Split))` already
  parameterizes split-mutants over a transform instead of writing one
  function per mutant. Exception: don't push that parameter into the
  production algorithm the mutants are tested against, if doing so would
  make the production definition itself harder to read as a standalone,
  portable spec — keep the mutant family generic in the test file, not in the
  spec.
- Prefer fewer, more general lemmas assembled directly over many narrow ones
  glued together with tactics, when the general one is not meaningfully
  harder to prove.
- When two true theorems are both available, prefer the one whose proof is
  shorter, even at a small cost to generality — this is why
  `hoistMatches_agree`/`hoistConditions_agree`/`hoistCondition_agree`
  (`Proofs/Hoist.lean`) are separate, non-recursive corollaries built from
  `evalMatches_frame` and each function's own `_reserved` fact, rather than
  folded into `hoistMatches_correct`'s own conclusion: bundling the
  environment-agreement result into the main mutual induction would need it
  threaded through every recursive call, where stating it separately needs
  only that a hoisted head match's own name is reserved.

When asked to simplify existing proofs, look first for: (1) lemmas restating
the same fact in more than one file, (2) hand-duplicated recursive
definitions that a single higher-order parameter would collapse, (3) tactic
scaffolding from an earlier, less certain draft of the same step.
