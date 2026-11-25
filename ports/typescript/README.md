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

The same command holds each well-formedness vector to its `expected` envelope:
`expected.wellFormed` against the reference and jinaga.js's `wellFormedErrors`,
and `expected.connected` against the reference's `isConnectedDeep` and, on a
well-formed vector, jinaga.js's `detectDisconnectedSpecification`. jinaga.js
connects a vector when that call does not throw. The runner names, in `jinagaRefusesUnusedGiven`, the
vectors jinaga.js is known to refuse because a given is unused
(`unused-given`, `no-matches-two-givens`; jinaga/jinaga-spec#60): they are
reported, not failed, until jinaga.js follows.

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
reference implementation, and must pass all three. It refuses a specification
that `well-formed.ts`'s `isConnectedDeep` refuses, and `npm run vectors` holds
that check to each well-formedness vector's `expected.connected`. Against jinaga.js's own
`buildFeeds`, a replica of its feeds must read the vector's results, except on
the vectors the runner names in `jinagaMisses`: only `random-2`, whose given
`p2` no match uses, which jinaga/jinaga-spec#60 allows and jinaga.js's
`buildFeeds` may refuse. A `buildFeeds` that throws covers nothing. Its feeds
differ from the vector's, so the other two are reported.

## Content vectors

```
npm run content
PORT=./my-content-store.ts npm run content
```

Runs each `vectors/content/` history against `content-store.ts`, the
reference port of `JinagaSpec/Content.lean`, or against the `ContentStore`
class that `PORT` exports. The harness builds each vector's policy from its
data. The store checks each proof itself: the given count, no conditions on a
given (`hasGivenConditions`: Lean's `Specification` has none, so no theorem
covers them), and the deep `isWellFormed` of `well-formed.ts` (RR-1), then `confirms` in
`content-proof.ts`, the port of `Proof.confirms` (RR-4), which binds the
content fact as a result, pins it with `reorderInverse`'s `__f` and looks for
a solution, with a port of the naive evaluator. The harness checks `confirms`
against each bound read's `yields`. The distribution rules are the vector's
`rule`, a specification the store runs with the proof's givens and checks with
the same `confirms` (`Policy.distributes`); a rule proof that is not bound
authorizes nothing. A save is a batch, stored only if it is fresh (`isFresh`)
and closed (`isClosed`: every predecessor it names is in the store or the
batch); the harness checks both against each save's `fresh` and `closed`.
Every response and the objects stored at the end must equal the vector's.
Two port-only cases, which the Lean generator cannot express, check that a
reader's proof with conditions on a given is refused with 400 and a rule
proof with them authorizes nothing.

Each history runs a second time against `content-cache.ts`, the port of
`JinagaSpec/ContentCache.lean` (or the `CachedContentStore` that `CACHE_PORT`
exports), which caches each read's decision per user, proof and key, and drops
an entry when a fresh batch's inverse candidates (`buildInverses` of
`inverse-candidates.ts`, each reordered by `reorderInverse`, read on the store with the whole batch, and every
result when a given arrives) name the key for the reader's proof, or the user
for a rule proof. A cache never changes an answer (`cached_read`), so it must
give the same responses. Needs no jinaga.js checkout.


## Content-hash vectors

```
npm run content-hash
JINAGA_JS=/path/to/jinaga.js npm run content-hash
```

Hashes each `vectors/content-hash/` object with Node's crypto, one shot and in
chunks of 1, 3, 64, 1000 and 65536 bytes, and compares each with the vector's
hash. With a jinaga.js checkout it also hashes the bytes with the primitives
its fact hash uses (`@stablelib/sha512`, then `@stablelib/base64`'s `encode`,
resolved from `src/util/encoding.ts`), and checks that `computeStringHash` of
the decoded text gives the same hash exactly when the bytes are valid UTF-8.
Without one, that check is skipped.
