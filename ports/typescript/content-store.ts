// A reference port of the content store in JinagaSpec/Content.lean: the
// replicator's write and read endpoints, over a policy the caller supplies.
// It is a template for a replicator's implementation, and what
// run-content-vectors.ts runs the content vectors against. The proved
// properties are SEC-1 to SEC-5 (JinagaSpec/Proofs/Content.lean).
//
// A read checks its proof itself: the givens' count and `isWellFormed`
// (./well-formed.ts, every child specification included) for RR-1
// (`Proof.bound`, `read_badRequest`), then `confirms` (./content-proof.ts),
// proved to be `Proof.yields` on every proof that passes (`confirms_eq_yields`).
// RR-1 also refuses a proof with conditions on a given (`hasGivenConditions`):
// Lean's `Specification` has none, so no theorem covers one, and jinaga.js
// evaluates them, so ignoring them would serve a reader they exclude.
//
// The distribution rules are proofs too (`Policy.distribution`): a user may run
// a specification when every feed has a bound rule proof that names them
// (`Policy.distributes`), checked with the same `confirms`; a rule proof with
// conditions on a given is not bound, so it authorizes nothing. A save is a
// batch, stored only if it is fresh (`isFresh`, JinagaSpec/Content.lean), which
// the cache's invalidation needs (./content-cache.ts), and names no
// predecessor outside the store and the batch (`isClosed`), so the store holds
// every predecessor of each fact it holds (`Replicator.run_closed`).

import { confirms } from "./content-proof.ts";
import { isWellFormed } from "./well-formed.ts";
import type { Specification } from "./well-formed.ts";

export type FactId = number;
export type User = number;

export interface Fact {
    id: FactId;
    type: string;
    predecessors: { role: string; id: FactId }[];
}

export interface Proof {
    specification: any;
    givens: FactId[];
}

export interface Policy {
    /** The hash of an object's bytes. */
    hash(bytes: string): string;
    /** The fact's content hash field, or undefined if its type is not content-bearing (MD-1). */
    contentHash(fact: Fact): string | undefined;
    /** The object meets the declared constraints (MD-2). */
    fits(fact: Fact, bytes: string): boolean;
    /** The authorization rules let the user create the fact (RW-4). */
    mayCreate(user: User, store: Fact[], fact: Fact): boolean;
    /**
     * The distribution rules for the specification with these givens (RR-3): one
     * clause per feed, each the rule proofs that may authorize it. Reads no store.
     */
    distribution(specification: any, givens: FactId[]): Proof[][];
}

export type Code =
    | "ok" | "stored" | "already_stored" | "bad_request" | "unauthenticated"
    | "forbidden" | "not_uploaded" | "fact_missing" | "too_large" | "unprocessable";

export interface Response { status: number; code: Code; bytes?: string }

const status: Record<Code, number> = {
    ok: 200, stored: 201, already_stored: 200, bad_request: 400, unauthenticated: 401,
    forbidden: 403, not_uploaded: 404, fact_missing: 404, too_large: 413, unprocessable: 422
};
const respond = (code: Code, bytes?: string): Response =>
    bytes === undefined ? { status: status[code], code } : { status: status[code], code, bytes };

/**
 * Some given carries conditions. A child specification has its parent's givens
 * (`descendants`, ./well-formed.ts), so this covers every depth.
 */
export const hasGivenConditions = (specification: Specification): boolean =>
    specification.given.some(g => (g.conditions ?? []).length > 0);

/**
 * Every given is bound, no given carries conditions, and every descendant is
 * well formed (RR-1, `Proof.bound`). Lean's `Specification` cannot express
 * conditions on a given, so `bound` refuses them rather than ignore them; a
 * later extension could reduce them to a match instead (`reduceGivenConditions`,
 * proved to keep what a replica reads by `read_reduceGivenConditions`).
 */
export const bound = (proof: Proof): boolean =>
    proof.givens.length === proof.specification.given.length && !hasGivenConditions(proof.specification) &&
    isWellFormed(proof.specification);

/** No stored fact has the id of a fact of the batch, or names one as a predecessor (`isFresh`). */
export const isFresh = (store: Fact[], batch: Fact[]): boolean =>
    batch.every(b => store.every(x => x.id !== b.id && x.predecessors.every(p => p.id !== b.id)));

/** Every predecessor a fact of the batch names is in the store or the batch (`isClosed`). */
export const isClosed = (store: Fact[], batch: Fact[]): boolean =>
    batch.every(b => b.predecessors.every(p => [...store, ...batch].some(x => x.id === p.id)));

/** A save stores the batch only if it is fresh and closed (`Graph.accepts`). */
export const accepts = (store: Fact[], batch: Fact[]): boolean => isFresh(store, batch) && isClosed(store, batch);

export class ContentStore {
    readonly store: Fact[] = [];
    /** Objects by content key, never by content hash (ST-1). */
    readonly objects = new Map<FactId, string>();

    constructor(protected readonly policy: Policy) {}

    /** Store the batch if it is fresh and closed; otherwise leave the store as it is. */
    save(batch: Fact[]) {
        if (accepts(this.store, batch)) this.store.push(...batch);
    }

    /** Every clause has a bound rule proof whose results name the user (`Policy.distributes`). */
    distributes(user: User, specification: any, givens: FactId[]): boolean {
        return this.policy.distribution(specification, givens).every(clause =>
            clause.some(q => bound(q) && confirms(q.specification, q.givens, this.store, user)));
    }

    /** The rules let the user read `key` with the bound proof: what `read` asks. */
    protected admits(user: User, key: FactId, proof: Proof): boolean {
        return this.distributes(user, proof.specification, proof.givens) &&
            confirms(proof.specification, proof.givens, this.store, key);
    }

    /** `PUT /content/{key}`. */
    write(user: User | null, key: FactId, bytes: string): Response {
        const P = this.policy;
        if (user === null) return respond("unauthenticated");
        const fact = this.store.find(f => f.id === key);
        if (fact === undefined) return respond("fact_missing");
        // The writer is checked before anything about the fact or its object is answered.
        if (!P.mayCreate(user, this.store, fact)) return respond("forbidden");
        const hash = P.contentHash(fact);
        if (hash === undefined) return respond("unprocessable");
        if (P.hash(bytes) !== hash) return respond("unprocessable");
        if (!P.fits(fact, bytes)) return respond("too_large");
        if (this.objects.has(key)) return respond("already_stored");
        this.objects.set(key, bytes);
        return respond("stored");
    }

    /** `POST /content/{key}/read`. */
    read(user: User | null, key: FactId, proof: Proof): Response {
        if (user === null) return respond("unauthenticated");
        if (!bound(proof)) return respond("bad_request");
        // Checked before the object is looked up, so the answer to a reader the
        // rules do not admit does not depend on what is stored (RR-5).
        if (!this.admits(user, key, proof)) return respond("forbidden");
        const bytes = this.objects.get(key);
        return bytes === undefined ? respond("not_uploaded") : respond("ok", bytes);
    }
}
