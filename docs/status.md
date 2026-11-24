# Status and standing decisions

What a new session (local or cloud) needs to know that the code and
`docs/findings.md` don't say. Facts about open work carry the date they were
last checked; check the issue before acting on one.

## Standing decisions

- **Feeds must defer.** A new client skips the details of a deleted entity, and
  restorable deletes are common. The "levels" algorithm (no filters) was proved
  consistent and rejected for violating deferral: don't propose it again.
- **Port the proved algorithm; don't patch empirically.** Implementation bugs
  in jinaga.js and jinaga.net are fixed by porting the algorithm proved here
  (as with the inverse, where jinaga.js#338's proposed patch proved
  insufficient).
- **Ask which requirements are non-negotiable before simplifying one away.**
- **The fact_id commit-order problem is jinaga-server#203 and #207.** Don't
  file it again.
- **Proof simplicity** is in `CLAUDE.md`.
- **Unused givens are allowed** (jinaga-spec#60, decided 2026-11-23). A given
  no match uses causes no refusal: not in `isConnectedDeep`, `isConnected` or
  `invertSpecification`.
- **A disconnected feed is refused, not reordered** (jinaga-spec#55, option
  (A)). `buildFeeds` keeps written order, and `feed-builder.ts` refuses a
  specification `isConnectedDeep` refuses. Reordering cannot connect, cover,
  defer and not widen all at once (N and J!, `docs/findings.md`).

## Open work (checked 2026-11-22)

- jinaga-spec#45: superseded by jinaga-spec#60 (2026-11-24). Unused givens
  are allowed: `ConnectedDescendants` (`Connected.lean`) no longer asks that
  every given be used, and `isConnected` counts only the givens the matches
  use. The random feed vectors are filtered for `isConnectedDeep`, so
  `random-children-1` (a product, P's shape) is still not generated, but
  `random-2` (an unused given) is again. `isConnectedDeep_iff` proves the
  check decides `ConnectedDescendants`, whose feed clause asks that each feed
  be joined (`isJoined`). `isConnected_asFeed`, with no hypothesis now, makes
  the descendant clause at the specification itself exactly `isConnected`.
  jinaga.js still refuses an unused given (`docs/findings.md`).
- jinaga-spec#18: the given-conditions label rule's wording in
  `vectors/README.md` and `GivenConditions.lean`, and a regression check; the
  code was fixed in `287ef39`.
- jinaga-spec#13: exactness when a batch's reads see later batches.
- jinaga-spec#20: purge and purge compliance.
- jinaga-server#233: both SQL builders seed `FROM` with only the first edge's
  given.
- jinaga.net: its vectors are pinned to an older jinaga-spec commit and need
  a re-pin, then a port of `read`, given arrival and `reduceGivenConditions`
  (last checked 2026-10-27).

## Cloud sessions

The repository runs in Claude Code on the web. `scripts/cloud-setup.sh`
installs elan, the pinned toolchain and the port's npm packages. It runs from
the SessionStart hook in `.claude/settings.json`. Paste the snippet in its
header comment into the environment's setup script so that the install is
snapshotted. Things that differ from a local session:

- The default network allowlist covers GitHub and npm but not Lean. elan
  reads the release index from `release.lean-lang.org` and downloads the
  toolchain from `releases.lean-lang.org`. Allow both in the environment's
  allowed domains (Limited network access), or `*.lean-lang.org`. Without
  them, elan fails with "Could not resolve host: ...lean-lang.org".
- `verify.sh`'s TypeScript and cascade steps, and the `jinaga-conformance`
  probes, need jinaga.js, jinaga-cascade-core and jinaga-server checkouts. A
  session reaches only the repositories attached to it, so attach them and set
  `JINAGA_JS`, `CASCADE_CORE` and `JINAGA_SERVER` if they are not siblings.
  Otherwise those steps are skipped.
- `gh issue` and `gh pr` fail: the GitHub proxy blocks GraphQL. Use
  `gh api` REST endpoints instead (the `file-divergence` skill shows how).
- User-level memory, skills and MCP servers don't load; only this
  repository's `CLAUDE.md`, `.claude/` and this file do.
