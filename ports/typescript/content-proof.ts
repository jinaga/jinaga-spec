// The replicator's check that a read's proof yields the content fact (RR-4),
// ported line for line from JinagaSpec/Content.lean (`Proof.confirms`), with
// the naive evaluator it reads with (`evalMatches`, JinagaSpec/Semantics.lean).
//
// For each specification and child specification of the proof, with every
// given held, and each label it projects: bind the label to the content fact
// and look for a solution. A label that is a given is bound already, so the
// given must be the fact. A label that is an unknown is pinned to the fact
// (`l = __f`, keeping its match's own conditions) and the matches are reordered
// to start at the pin (`reorderInverse`, ./inverse-candidates.ts), so the read
// walks from the content fact to the givens.
//
// Proved equal to `Proof.yields`, whether some result of the specification
// names the fact, for every proof whose specification and child specifications
// are well formed (`confirms_eq_yields`), which `read` checks first
// (`bound`, ./content-store.ts). `bound` also refuses conditions on a given,
// which `confirms`, like Lean's `Specification`, does not read.

import { pinLabel, reorderInverse } from "./inverse-candidates.ts";
import { descendants, projectedLabels } from "./well-formed.ts";
import type { Condition, Label, Match, PathCondition, Specification } from "./well-formed.ts";
import type { Fact, FactId } from "./content-store.ts";

export type Graph = Fact[];
export type Env = Map<string, FactId>;

/* ---------------- The semantics (JinagaSpec/Semantics.lean) ---------------- */

const factOf = (g: Graph, id: FactId): Fact | undefined => g.find(f => f.id === id);

/** The facts a fact points to by one role, of the role's declared type. */
function step(g: Graph, role: { name: string; predecessorType: string }, id: FactId): FactId[] {
    const fact = factOf(g, id);
    if (fact === undefined) return [];
    return fact.predecessors.filter(p => p.role === role.name).map(p => p.id)
        .filter(p => factOf(g, p)?.type === role.predecessorType);
}

function walk(g: Graph, start: FactId, roles: { name: string; predecessorType: string }[]): FactId[] {
    if (roles.length === 0) return [start];
    const [role, ...rest] = roles;
    return step(g, role, start).flatMap(p => walk(g, p, rest));
}

export const bind = (env: Env, name: string, id: FactId): Env => new Map(env).set(name, id);

function holdsPath(g: Graph, env: Env, unknown: string, c: PathCondition): boolean {
    const u = env.get(unknown), r = env.get(c.labelRight);
    if (u === undefined || r === undefined) return false;
    const right = walk(g, r, c.rolesRight);
    return walk(g, u, c.rolesLeft).some(a => right.includes(a));
}

/** Every way to bind the unknowns of the matches, in order, so that each match's conditions hold. */
export function evalMatches(g: Graph, env: Env, ms: Match[]): Env[] {
    if (ms.length === 0) return [env];
    const [{ unknown, conditions }, ...rest] = ms;
    return g.filter(f => f.type === unknown.type).flatMap(f => {
        const env2 = bind(env, unknown.name, f.id);
        return allHold(g, env2, unknown.name, conditions) ? evalMatches(g, env2, rest) : [];
    });
}

const allHold = (g: Graph, env: Env, unknown: string, cs: Condition[]): boolean =>
    cs.every(c => holds(g, env, unknown, c));

const holds = (g: Graph, env: Env, unknown: string, c: Condition): boolean =>
    c.type === "path" ? holdsPath(g, env, unknown, c) : c.exists === (evalMatches(g, env, c.matches).length > 0);

/** The label is bound to a fact of `g` of the label's type. */
export function has(g: Graph, env: Env, l: Label): boolean {
    const id = env.get(l.name);
    return id !== undefined && factOf(g, id)?.type === l.type;
}

/** Bind the givens, in order, to the facts a caller supplies. */
export function bindGivens(s: Specification, facts: FactId[]): Env {
    const env: Env = new Map();
    s.given.forEach((g, i) => { if (i < facts.length && !env.has(g.label.name)) env.set(g.label.name, facts[i]); });
    return env;
}

/* ---------------- The check (JinagaSpec/Content.lean) ---------------- */

const pinCondition: PathCondition = { type: "path", rolesLeft: [], labelRight: pinLabel, rolesRight: [] };

/** `ms`, with the match whose unknown is `l` pinned to the new fact; it keeps its own conditions. */
const pinUnknown = (l: string, ms: Match[]): Match[] =>
    ms.map(m => m.unknown.name === l ? { unknown: m.unknown, conditions: [pinCondition, ...m.conditions] } : m);

/** `d`, with the unknown `u` pinned to the new fact, given as `pinLabel`, and projected. */
const pinResult = (d: Specification, u: Label): Specification => ({
    given: [...d.given, { label: { name: pinLabel, type: u.type }, conditions: [] }],
    matches: pinUnknown(u.name, d.matches),
    projection: { type: "fact", label: u.name }
});

/** Some solution of `d`'s matches from `env` binds the label `l` to `key`. */
function bindsResult(d: Specification, g: Graph, env: Env, key: FactId, l: string): boolean {
    const m = d.matches.find(m => m.unknown.name === l);
    if (m !== undefined) {
        const reordered = reorderInverse(pinResult(d, m.unknown) as any);
        return evalMatches(g, bind(env, pinLabel, key), reordered.matches).length > 0;
    }
    return env.get(l) === key && evalMatches(g, env, d.matches).length > 0;
}

/**
 * Some descendant of the proof's specification, with every given held, has a
 * projected label that some solution binds to `key` (`Proof.confirms`).
 */
export function confirms(specification: Specification, givens: FactId[], g: Graph, key: FactId): boolean {
    return descendants(specification).some(d => {
        const env = bindGivens(d, givens);
        return d.given.every(l => has(g, env, l.label)) && projectedLabels(d.projection).some(l => bindsResult(d, g, env, key, l));
    });
}
