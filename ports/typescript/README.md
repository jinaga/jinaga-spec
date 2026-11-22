# TypeScript port

Runs the conformance vectors against the split in a `jinaga.js` checkout:
`splitBeforeFirstSuccessor` (jinaga/jinaga.js#325), each split vector's own
`expected` envelope.

```
npm ci
JINAGA_JS=/path/to/jinaga.js npm run vectors
```

`JINAGA_JS` defaults to `../../../jinaga.js`. The runner imports the source
directly, so it tests whatever is on disk there. Point it at a worktree of an
earlier commit to see which vectors that commit fails.

It changes nothing in `jinaga.js`.

## Cascade vectors

```
CASCADE_CORE=/path/to/jinaga-cascade-core npm run cascade
```

Builds each `vectors/cascade/` pipeline through `@jinaga/cascade-core`'s builder,
performs its operations in each of its orders, and compares the output with the
vector's, up to the order of each array. `CASCADE_CORE` defaults to
`../../../jinaga-cascade-core`.

## Feed vectors

```
JINAGA_JS=/path/to/jinaga.js npm run feeds
JINAGA_JS=/path/to/jinaga.js PORT=./feed-builder.ts npm run feeds
```

Reads each `vectors/feeds/` vector's feeds with jinaga.js's `MemoryStore`, as
the replicator serves them, and checks they deliver the vector's facts. Then
checks a `buildFeeds` three ways: its feeds equal the vector's; a replica
holding what they deliver reads the vector's results, child specifications'
at every depth; and they deliver no fact
the vector's feeds withhold, which is deferral. `feed-builder.ts` is the
reference implementation, and must pass all three. Against jinaga.js's own
`buildFeeds`, a replica of its feeds must read the vector's results, except on
the vectors the runner names in `jinagaMisses` (none at present). Its feeds
differ from the vector's, so the other two are reported.

## Content vectors

```
npm run content
PORT=./my-content-store.ts npm run content
```

Runs each `vectors/content/` history against `content-store.ts`, the
reference port of `JinagaSpec/Content.lean`, or against the `ContentStore`
class that `PORT` exports. The harness builds each vector's policy from its
data. It takes `yields` from the vector, because computing it needs a
specification engine. Every response and the objects stored at the end must
equal the vector's. Needs no jinaga.js checkout.

