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

