// The content store with a cache of read decisions (NF-2), ported line for
// line from JinagaSpec/ContentCache.lean.
//
// A decision is cached per user, proof (specification and givens) and content
// key. Saving a fresh batch drops every entry whose decision it may change: for
// the reader's proof and the key, or for some distribution rule proof and the
// user, some specification or child specification has an inverse candidate
// (`candidates`, JinagaSpec/Reorder.lean; ./inverse-candidates.ts) that names
// that fact (`Proof.mayChange`, `Policy.invalidates`). A revocation is a
// negative existential condition, and a restore one nested in it, so both are
// found.
//
// Proved: after any history of saves, uploads and reads, the cached store
// answers every read as the uncached one does (`cached_read`), so every read,
// cached or not, satisfies SEC-1 at that moment (`cached_read_authorized`).
// The proof needs each batch to be fresh, which `save` checks (`accepts`).

import { ContentStore, accepts } from "./content-store.ts";
import type { Fact, FactId, Proof, User } from "./content-store.ts";
import { bind, bindGivens, evalMatches, has } from "./content-proof.ts";
import type { Env, Graph } from "./content-proof.ts";
import { buildInverses, pinLabel, reorderInverse } from "./inverse-candidates.ts";
import { descendants, projectedLabels } from "./well-formed.ts";
import type { Specification } from "./well-formed.ts";

type Row = (FactId | undefined)[];

/** The rows the specification reads (`Specification.evaluate`). */
const evaluate = (s: Specification, g: Graph, env: Env): Row[] =>
    evalMatches(g, env, s.matches).map(e => projectedLabels(s.projection).map(l => e.get(l)));

/** Nothing until every given is held (`Specification.read`). */
const read = (s: Specification, g: Graph, env: Env): Row[] =>
    s.given.every(l => has(g, env, l.label)) ? evaluate(s, g, env) : [];

/** The givens' bindings, and the new fact as `__f` (`pinEnv`). */
function pinEnv(s: Specification, env: Env, f: Fact): Env {
    const restricted: Env = new Map([...env].filter(([n]) => s.given.some(l => l.label.name === n)));
    return bind(restricted, pinLabel, f.id);
}

/**
 * The results a batch might have changed (`candidates`): for each fact, every
 * result if it is one of the givens (it was not stored, so nothing was read),
 * and otherwise each inverse reordered to start at it; all read on the store
 * that holds the whole batch.
 */
function candidates(s: Specification, env: Env, g: Graph, batch: Fact[]): Row[] {
    const now = [...g, ...batch];
    const inverses = buildInverses(s as any).map(reorderInverse);
    return batch.flatMap(f => s.given.some(l => env.get(l.label.name) === f.id)
        ? read(s, now, env)
        : inverses.flatMap(i => evaluate(i as any, now, pinEnv(s, env, f))));
}

/** Saving the batch may change whether the proof yields `k` (`Proof.mayChange`). */
const mayChange = (p: Proof, g: Graph, batch: Fact[], k: FactId): boolean =>
    descendants(p.specification).some(d =>
        candidates(d, bindGivens(d, p.givens), g, batch).some(row => row.includes(k)));

interface Entry { user: User; proof: Proof; key: FactId; admitted: boolean }

const keyOf = (user: User, key: FactId, proof: Proof): string =>
    JSON.stringify([user, key, proof.specification, proof.givens]);

export class CachedContentStore extends ContentStore {
    readonly cache = new Map<string, Entry>();

    /** The decision `read` would compute: cached, or computed and cached (`Cached.admits`). */
    protected admits(user: User, key: FactId, proof: Proof): boolean {
        const k = keyOf(user, key, proof);
        const cached = this.cache.get(k);
        if (cached !== undefined) return cached.admitted;
        const admitted = super.admits(user, key, proof);
        this.cache.set(k, { user, proof, key, admitted });
        return admitted;
    }

    /** May the batch change the entry's decision? (`Policy.invalidates`) */
    private invalidates(batch: Fact[], e: Entry): boolean {
        return mayChange(e.proof, this.store, batch, e.key) ||
            this.policy.distribution(e.proof.specification, e.proof.givens)
                .some(clause => clause.some(q => mayChange(q, this.store, batch, e.user)));
    }

    /** A batch the store accepts drops every entry it may invalidate, then is stored (`Cached.step`). */
    save(batch: Fact[]) {
        if (accepts(this.store, batch)) {
            for (const [k, e] of [...this.cache]) if (this.invalidates(batch, e)) this.cache.delete(k);
        }
        super.save(batch);
    }
}
