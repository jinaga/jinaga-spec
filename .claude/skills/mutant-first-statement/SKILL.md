---
name: mutant-first-statement
description: "Write the plausible wrong algorithms as mutants before stating a requirement as a jinaga-spec theorem, and check that the statement rules each one out. Use when turning a requirement (consistency, deferral, append-only, convergence) into a theorem, when restating an existing theorem for a wider scope such as child specifications, or when a proof goes through suspiciously easily."
---

# Mutants before the statement

A theorem can be true of the algorithm and still too weak to say what the
requirement means. The first child-specification version of `feeds_defer` kept
PR #42's wording, proved, and let through the mutant "an excluding feed goes
on to child specifications" — the exact bug deferral exists to prevent. It had
to be restated and proved again. Mutants are cheap; a second proof is not.

## Steps

1. **List the wrong algorithms** a reasonable implementer might write. Each
   should break the requirement in one way. Sources:
   - real bugs in jinaga.js or jinaga-server (`docs/findings.md`);
   - each rule of the algorithm, dropped or inverted (no filters, no restoring
     feeds, excluding feeds don't stop);
   - each rule applied in the wrong scope (child feeds without the parent's
     filters, excluding feeds going on to children);
   - designs the user rejected (feeds: "levels", which breaks deferral).

2. **Add them to the check file**, not the spec: a field on the `Mutant`
   structure and an entry in `mutants : List (String × Mutant)` in
   `CheckFeeds.lean` (or `Check.lean`/`CheckInverse.lean`), keeping one
   parameterized definition as `CLAUDE.md` requires.

3. **Write the statement**, then, for each mutant, say in one line which part
   of the statement it violates. If you can't point to one, the statement is
   too weak — strengthen it before proving.

4. **Make the randomized check test the statement as written**, not a
   paraphrase of it: the same quantifiers and the same scope (per descendant,
   not top level only). Run it:

   ```bash
   lake build check-feeds && lake exe check-feeds 1 && lake exe check-feeds 2
   ```

   Every mutant must be caught on some specifications, and the real algorithm
   on none. A mutant caught on zero means the generator doesn't produce the
   input that exposes it (extend `CheckGen.lean`) or the statement doesn't
   cover it (back to step 3).

5. **If the strongest form fails a vector**, weaken it to the strongest form
   that holds, record the counterexample vector, and write the weaker form's
   meaning in `docs/findings.md` (as with "withheld while every witness
   stands", which fails four levels deep).

6. **Only now prove it.** Record the mutant counts in `docs/findings.md`.
