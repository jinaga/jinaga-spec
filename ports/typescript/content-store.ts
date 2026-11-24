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

import { confirms } from "./content-proof.ts";
import { isWellFormed } from "./well-formed.ts";

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
    /** The distribution rules let the user run the specification with these givens (RR-3). */
    distributes(user: User, specification: any, givens: FactId[], store: Fact[]): boolean;
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

export class ContentStore {
    readonly store: Fact[] = [];
    /** Objects by content key, never by content hash (ST-1). */
    readonly objects = new Map<FactId, string>();

    constructor(private readonly policy: Policy) {}

    save(fact: Fact) {
        this.store.push(fact);
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
        const P = this.policy;
        if (user === null) return respond("unauthenticated");
        if (proof.givens.length !== proof.specification.given.length || !isWellFormed(proof.specification))
            return respond("bad_request");
        // Checked before the object is looked up, so the answer to a reader the
        // rules do not admit does not depend on what is stored (RR-5).
        if (!(P.distributes(user, proof.specification, proof.givens, this.store) &&
            confirms(proof.specification, proof.givens, this.store, key)))
            return respond("forbidden");
        const bytes = this.objects.get(key);
        return bytes === undefined ? respond("not_uploaded") : respond("ok", bytes);
    }
}
