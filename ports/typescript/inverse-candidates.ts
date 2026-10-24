// Reference TypeScript implementation of jinaga-spec's proven inverse
// algorithm, `candidates` (JinagaSpec/Candidates.lean, JinagaSpec/Reorder.lean).
//
// It is written against jinaga.js's `Specification` JSON shape, and is what
// jinaga/jinaga.js#338 ports into `src/specification/inverse-candidates.ts`.
// `npm run inverse` with PORT=./inverse-candidates.ts checks it against the
// vectors, exactly as it checks the port in jinaga.js.
//
// Proven (jinaga/jinaga-spec#7): for a well-formed specification and a fresh
// fact (no stored fact has its hash, none names it as a predecessor), every row
// whose membership changes when the fact is saved is found by one of
// `candidateInverses(specification)`, read with the subscription's givens and
// the new fact (`candidates_complete`), and a stream that re-checks those
// candidates holds exactly the result (`stream_correct`).

type Role = { name: string, predecessorType: string };
type Label = { name: string, type: string };
type PathCondition = { type: "path", rolesLeft: Role[], labelRight: string, rolesRight: Role[] };
type ExistentialCondition = { type: "existential", exists: boolean, matches: Match[] };
type Condition = PathCondition | ExistentialCondition;
type Match = { unknown: Label, conditions: Condition[] };
type Given = { label: Label, conditions: ExistentialCondition[] };
type Specification = { given: Given[], matches: Match[], projection: any };

/** The label an inverse gives the new fact. Reserved, so no specification declares it. */
export const pinLabel = "__f";

const pinCondition: PathCondition = { type: "path", rolesLeft: [], labelRight: pinLabel, rolesRight: [] };

/** Structural equality: never object identity. */
function deepEqual(a: unknown, b: unknown): boolean {
    if (a === b) return true;
    if (typeof a !== "object" || typeof b !== "object" || a === null || b === null) return false;
    if (Array.isArray(a) !== Array.isArray(b)) return false;
    const ka = Object.keys(a as object), kb = Object.keys(b as object);
    return ka.length === kb.length && ka.every(k => deepEqual((a as any)[k], (b as any)[k]));
}

function removeFirst<T>(list: T[], item: T): T[] {
    const i = list.findIndex(x => deepEqual(x, item));
    return i < 0 ? list : [...list.slice(0, i), ...list.slice(i + 1)];
}

const isPath = (c: Condition): c is PathCondition => c.type === "path";

/* ---------------- Step 1: one inverse per way the new fact can touch a row ---------------- */

type Touch<T> = { pinned: Label, value: T };

/** A level that lost its solution keeps only its path conditions, in order. */
function relax(gained: boolean, conditions: Condition[]): Condition[] {
    return gained ? conditions : conditions.filter(isPath);
}

function relaxMatches(gained: boolean, matches: Match[]): Match[] {
    return gained ? matches : matches.map(m => ({ unknown: m.unknown, conditions: relax(false, m.conditions) }));
}

/** Every way the new fact can change a solution of `matches`, in direction `gained`. */
function touchMatches(gained: boolean, matches: Match[]): Touch<Match[]>[] {
    if (matches.length === 0) return [];
    const [m, ...rest] = matches;
    const out: Touch<Match[]>[] = [];
    // Pin this unknown. Only a gained solution can contain the new fact.
    if (gained) {
        out.push({ pinned: m.unknown, value: [{ unknown: m.unknown, conditions: [pinCondition, ...m.conditions] }, ...rest] });
    }
    // Through one of this match's conditions; the matches after it relax.
    for (const t of touchConditions(gained, m.conditions)) {
        out.push({ pinned: t.pinned, value: [{ unknown: m.unknown, conditions: t.value }, ...relaxMatches(gained, rest)] });
    }
    // In the matches after it; this match relaxes.
    for (const t of touchMatches(gained, rest)) {
        out.push({ pinned: t.pinned, value: [{ unknown: m.unknown, conditions: relax(gained, m.conditions) }, ...t.value] });
    }
    return out;
}

/** Through exactly one condition; the others relax. */
function touchConditions(gained: boolean, conditions: Condition[]): Touch<Condition[]>[] {
    if (conditions.length === 0) return [];
    const [c, ...cs] = conditions;
    const out: Touch<Condition[]>[] = [];
    for (const t of touchCondition(gained, c)) {
        out.push({ pinned: t.pinned, value: [t.value, ...relax(gained, cs)] });
    }
    for (const t of touchConditions(gained, cs)) {
        out.push({ pinned: t.pinned, value: [...relax(gained, [c]), ...t.value] });
    }
    return out;
}

/** Into an existential condition, which becomes `exists: true`. Inside a notExists, a gain is a loss. */
function touchCondition(gained: boolean, c: Condition): Touch<Condition>[] {
    if (isPath(c)) return [];
    return touchMatches(gained === c.exists, c.matches)
        .map(t => ({ pinned: t.pinned, value: { type: "existential", exists: true, matches: t.value } as ExistentialCondition }));
}

/** Step 1: every inverse, given the subscription's givens and the new fact as `__f`. */
export function buildInverses(s: Specification): Specification[] {
    return [...touchMatches(true, s.matches), ...touchMatches(false, s.matches)].map(t => ({
        given: [...s.given, { label: { name: pinLabel, type: t.pinned.type }, conditions: [] }],
        matches: t.value,
        projection: s.projection
    }));
}

/* ---------------- Step 2: start each inverse at the new fact, and check it ---------------- */

const isPin = (c: Condition) =>
    isPath(c) && c.rolesLeft.length === 0 && c.labelRight === pinLabel && c.rolesRight.length === 0;
const pinnedMatches = (ms: Match[]): boolean => ms.some(m => m.conditions.some(pinnedCondition));
const pinnedCondition = (c: Condition): boolean => isPath(c) ? isPin(c) : pinnedMatches(c.matches);

/** Lift the matches of every `exists` condition that holds the pin, right after the match that held it. */
function flattenMatches(ms: Match[]): Match[] {
    return ms.flatMap(m => {
        const keep: Condition[] = [];
        const lifted: Match[] = [];
        for (const c of m.conditions) {
            if (!isPath(c) && c.exists && pinnedMatches(c.matches)) lifted.push(...flattenMatches(c.matches));
            else keep.push(c);
        }
        return [{ unknown: m.unknown, conditions: keep }, ...lifted];
    });
}

/** A path condition and the match it is written on. */
type Edge = { home: string, condition: PathCondition };

/** `r->R = u->L` instead of `u->L = r->R`. */
const reverse = (e: Edge): Edge => ({
    home: e.condition.labelRight,
    condition: { type: "path", rolesLeft: e.condition.rolesRight, labelRight: e.home, rolesRight: e.condition.rolesLeft }
});

/** Labels the matches name but do not bind; `inner` holds the labels bound around them. */
function freeInMatches(inner: string[], ms: Match[]): string[] {
    return ms.flatMap(m => freeInConditions(inner, m.conditions));
}

function freeInConditions(inner: string[], cs: Condition[]): string[] {
    return cs.flatMap(c => isPath(c)
        ? (inner.includes(c.labelRight) ? [] : [c.labelRight])
        : freeInMatches([...inner, ...c.matches.map(m => m.unknown.name)], c.matches));
}

const freeLabels = (c: Condition): string[] =>
    isPath(c) ? [c.labelRight] : freeInMatches(c.matches.map(m => m.unknown.name), c.matches);

/** First what the new fact reaches, then what the givens reach; `null` if anything is left. */
function orderFromPin(givens: string[], ms: Match[]): Match[] | null {
    let labels: Label[] = ms.map(m => m.unknown);
    let edges: Edge[] = ms.flatMap(m => m.conditions.filter(isPath).map(c => ({ home: m.unknown.name, condition: c })));
    let filters: Condition[] = ms.flatMap(m => m.conditions.filter(c => !isPath(c)));

    const reaching = (reach: string[], u: string, e: Edge): [Edge, Edge] | null =>
        e.home === u && reach.includes(e.condition.labelRight) ? [e, e] :
        e.condition.labelRight === u && reach.includes(e.home) ? [e, reverse(e)] : null;

    function grow(reach: string[], bound: string[]): { bound: string[], placed: Match[] } {
        const placed: Match[] = [];
        for (let n = ms.length; n > 0; n--) {
            let found: { u: Label, lead: [Edge, Edge] } | null = null;
            for (const u of labels) {
                for (const e of edges) {
                    const lead = reaching(reach, u.name, e);
                    if (lead) { found = { u, lead }; break; }
                }
                if (found) break;
            }
            if (!found) break;
            const { u, lead } = found;
            bound = [u.name, ...bound];
            reach = [u.name, ...reach];
            const ready = (e: Edge) => bound.includes(e.home) && bound.includes(e.condition.labelRight);
            const isReady = (c: Condition) => freeLabels(c).every(l => bound.includes(l));
            edges = removeFirst(edges, lead[0]);
            const attached = edges.filter(ready);
            const attachedFilters = filters.filter(isReady);
            edges = edges.filter(e => !ready(e));
            filters = filters.filter(c => !isReady(c));
            labels = removeFirst(labels, u);
            placed.push({
                unknown: u,
                conditions: [
                    lead[1].condition,
                    ...attached.map(e => (e.home === u.name ? e : reverse(e)).condition),
                    ...attachedFilters
                ]
            });
        }
        return { bound, placed };
    }

    const fromPin = grow([pinLabel], [pinLabel, ...givens]);
    const fromGivens = grow(fromPin.bound, fromPin.bound);
    return labels.length === 0 && edges.length === 0 && filters.length === 0
        ? [...fromPin.placed, ...fromGivens.placed] : null;
}

/** Every path condition names a label in scope; a match's unknown is in scope for its existential conditions. */
function isScoped(scope: string[], ms: Match[]): boolean {
    for (const m of ms) {
        const inner = [m.unknown.name, ...scope];
        for (const c of m.conditions) {
            if (isPath(c) ? !scope.includes(c.labelRight) : !isScoped(inner, c.matches)) return false;
        }
        scope = inner;
    }
    return true;
}

function bindsOnce(scope: string[], ms: Match[]): boolean {
    const names = ms.map(m => m.unknown.name);
    return new Set(names).size === names.length && names.every(n => !scope.includes(n)) && isScoped(scope, ms);
}

/** As written; a path condition reversed onto its other end; an existential condition on any match. */
function sameConstraint([u1, c1]: [string, Condition], [u2, c2]: [string, Condition]): boolean {
    if (isPath(c1) && isPath(c2)) {
        return (u1 === u2 && deepEqual(c1, c2)) ||
            (u2 === c1.labelRight && deepEqual(reverse({ home: u1, condition: c1 }), { home: u2, condition: c2 }));
    }
    return deepEqual(c1, c2);
}

const constraints = (ms: Match[]) => ms.flatMap(m => m.conditions.map(c => [m.unknown.name, c] as [string, Condition]));
const covers = (a: Match[], b: Match[]) => constraints(a).every(x => constraints(b).some(y => sameConstraint(x, y)));

/** `b` is an arrangement of `a`: the same unknowns, each bound once, and the same conditions. */
function arranges(scope: string[], a: Match[], b: Match[]): boolean {
    return bindsOnce(scope, a) && bindsOnce(scope, b) &&
        a.every(m => b.some(n => deepEqual(m.unknown, n.unknown))) &&
        b.every(m => a.some(n => deepEqual(m.unknown, n.unknown))) &&
        covers(a, b) && covers(b, a);
}

/** Every label the projection reads from this level. */
function projectionLabels(projection: any): string[] {
    switch (projection.type) {
        case "fact": case "field": case "hash": return [projection.label];
        case "composite": return projection.components.flatMap((c: any) =>
            c.type === "specification" ? freeInMatches(c.matches.map((m: Match) => m.unknown.name), c.matches) : [c.label]);
        default: return [];
    }
}

/** Step 2: the inverse reordered to start at the new fact if the result checks, and otherwise the inverse itself. */
export function reorderInverse(inverse: Specification): Specification {
    const givens = inverse.given.map(g => g.label.name).filter(n => n !== pinLabel);
    const scope = [pinLabel, ...givens];
    const flat = flattenMatches(inverse.matches);
    const ordered = orderFromPin(givens, flat);
    const ok = ordered !== null && isScoped(scope, inverse.matches) && arranges(scope, flat, ordered) &&
        projectionLabels(inverse.projection).every(l => scope.includes(l) || inverse.matches.some(m => m.unknown.name === l));
    return ok ? { ...inverse, matches: ordered! } : inverse;
}

/** The whole algorithm's inverses. Read each with `[...subscriptionGivens, newFact]`; every resulting row is a candidate. */
export function candidateInverses(specification: Specification): Specification[] {
    return buildInverses(specification).map(reorderInverse);
}
