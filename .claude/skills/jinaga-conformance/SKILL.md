---
name: jinaga-conformance
description: "Compare jinaga-spec's Lean definitions and TypeScript ports against jinaga.js and jinaga-server on vectors or ad-hoc specifications: well-formedness, disconnection, buildFeeds, and jinaga-server's SQL for each feed. Use when checking whether jinaga.js or jinaga-server agrees with the spec on a new kind of input, reproducing a reviewer's counterexample, or confirming a divergence before recording it in docs/findings.md — instead of writing one-off scripts in the scratchpad."
---

# Conformance against jinaga.js and jinaga-server

## The runners that already exist

`scripts/verify.sh` runs these. Run one directly while iterating, from
`ports/typescript`:

| What | Command |
|---|---|
| Split and well-formedness vectors vs jinaga.js | `JINAGA_JS=../../../jinaga.js npm run --silent vectors` |
| Feed vectors vs jinaga.js `buildFeeds` (misses reported) | `JINAGA_JS=../../../jinaga.js npm run --silent feeds` |
| Feed vectors vs the port (must all pass) | `JINAGA_JS=../../../jinaga.js PORT=./feed-builder.ts npm run --silent feeds` |
| Inverse vectors vs jinaga.js / the reference | `npm run --silent inverse`, `PORT=./inverse-candidates.ts npm run --silent inverse` |
| Cascade vectors | `npm run --silent cascade` |
| Lean oracle vs jinaga.js on random specifications | `lake exe check-inverse dump <file> 1`, then `npx tsx inverse-diff.ts <file>` |

## The probe, for everything else

`scripts/probe.mts` (in this skill) runs a specification through jinaga.js and
jinaga-server. Its input is a vector directory, one vector file, or a
`.jinaga` file of specification text:

```bash
cd ports/typescript
P=../../.claude/skills/jinaga-conformance/scripts/probe.mts
npx tsx $P wellformed ../../vectors/well-formed     # validateSpecification + wellFormedErrors
npx tsx $P disconnected ../../vectors/feeds         # detectDisconnectedSpecification
npx tsx $P feeds my-spec.jinaga                     # jinaga.js buildFeeds, as text
npx tsx $P sql ../../vectors/feeds                  # jinaga-server SQL for the vectors' feeds
FEEDS=jinaga npx tsx $P sql ../../vectors/feeds     # ...for jinaga.js's own feeds
```

`JINAGA_JS` and `JINAGA_SERVER` default to sibling checkouts. The probe exits 1 when it reports any problem, and a `.jinaga` file must hold one specification and nothing after it. The `sql`
check runs jinaga-server's SQL builder only. It doesn't run a database, so a
query that builds may still return wrong rows. Say so when you report it.

Put a reviewer's counterexample in a `.jinaga` file in the scratchpad and
probe it, rather than writing a new script. If you need a check the probe
lacks, add a case to `probe.mts` so the next run has it.

## Reporting a divergence

For each disagreement, record in `docs/findings.md`:
- the input (vector name or specification text);
- what jinaga.js or jinaga-server does, with exact error text;
- what the spec does, and the theorem that says why.

Note the jinaga.js version (`node_modules/jinaga/package.json` in
jinaga-server, or `git -C ../jinaga.js log -1 --oneline`). If the divergence
should be filed, use the `file-divergence` skill.
