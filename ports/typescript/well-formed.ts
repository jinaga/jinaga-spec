// A reference implementation of `isWellFormed`, mirroring JinagaSpec/WellFormed.lean
// line for line. It depends on no other package, so it can be lifted as it
// stands. Its types are structural: they match `Specification` in
// `src/specification/specification.ts` in jinaga.js.
//
// It checks the preconditions of `splitBeforeFirstSuccessor`:
//   scoped      every label a path condition names is in scope
//   well-named  every declared label is new (not already in scope) and ordinary
//               (not reserved for the split: it does not begin with `__`)
//   projected   the projection names only givens and top-level unknowns
//
// A child specification in the projection is checked as a specification of its
// own: the parent's givens, and the parent's matches followed by its own
// (`isWellFormedDeep`, `Specification.descendants`). Not modelled yet, and
// ignored here: conditions on givens.
//
// `isConnectedDeep` (JinagaSpec/Connected.lean) is the check `buildFeeds`
// needs besides: every descendant, as a feed, is connected, and every feed is
// joined, so no feed is a product of two chains (jinaga/jinaga-spec#55). A
// given no match uses is allowed (jinaga/jinaga-spec#60). It reads the feeds from
// ./feed-builder.ts, which is the one dependency of this file.

import { asFeed, feedsOf, paths } from "./feed-builder.ts";

export interface Label { name: string; type: string }
export interface Role { name: string; predecessorType: string }
export interface PathCondition { type: "path"; rolesLeft: Role[]; labelRight: string; rolesRight: Role[] }
export interface ExistentialCondition { type: "existential"; exists: boolean; matches: Match[] }
export type Condition = PathCondition | ExistentialCondition;
export interface Match { unknown: Label; conditions: Condition[] }
export type Component =
    | { type: "specification"; matches: Match[]; projection: Projection }
    | { type: "fact" | "field" | "hash" | "time"; label: string };
export type Projection =
    | { type: "composite"; components: Component[] }
    | { type: "fact" | "field" | "hash" | "time"; label: string };
export interface Specification {
    /** jinaga.js's givens carry conditions; Lean's `Specification` has none (see `bound`, ./content-store.ts). */
    given: { label: Label; conditions?: unknown[] }[];
    matches: Match[];
    projection: Projection;
}

const isReserved = (name: string) => name.startsWith("__");

// `scope` holds the labels a match may join. A match adds its unknown to the
// scope of the matches after it, and of its own existential conditions. Scope
// is lexical: the labels a nested match declares do not outlive its condition,
// so sibling existential conditions may reuse a name.
function isWellFormedMatches(scope: string[], matches: Match[]): boolean {
    for (const match of matches) {
        const name = match.unknown.name;
        const inner = [name, ...scope];
        if (scope.includes(name) || isReserved(name) ||
            !match.conditions.every(c => isWellFormedCondition(inner, scope, c))) {
            return false;
        }
        scope = inner;
    }
    return true;
}

// `inner` is the scope of existential conditions, `outer` of path conditions.
function isWellFormedCondition(inner: string[], outer: string[], condition: Condition): boolean {
    return condition.type === "path"
        ? outer.includes(condition.labelRight)
        : isWellFormedMatches(inner, condition.matches);
}

/** The labels whose facts a projection names; a child specification names its own (`Projection.labels`). */
export function projectedLabels(projection: Projection): string[] {
    return projection.type === "composite"
        ? projection.components.flatMap(c => c.type === "specification" ? [] : [c.label])
        : [projection.label];
}

function isWellFormedNode(specification: Specification): boolean {
    const givens = specification.given.map(g => g.label.name);
    const unknowns = specification.matches.map(m => m.unknown.name);
    return givens.every(name => !isReserved(name)) &&
        isWellFormedMatches(givens, specification.matches) &&
        projectedLabels(specification.projection).every(label => givens.includes(label) || unknowns.includes(label));
}

/**
 * A specification and its child specifications at every depth, each as a
 * specification: the same givens, and the parent's matches followed by its own.
 */
export function descendants(specification: Specification): Specification[] {
    const children = specification.projection.type === "composite" ? specification.projection.components : [];
    return [specification, ...children.flatMap(c => c.type !== "specification" ? [] :
        descendants({ given: specification.given, matches: [...specification.matches, ...c.matches], projection: c.projection }))];
}

/** A specification and each child specification of its projection, at every depth, are well formed. */
export function isWellFormed(specification: Specification): boolean {
    return descendants(specification).every(isWellFormedNode);
}

// The connectivity check `invertSpecification` runs (`isConnected`,
// JinagaSpec/Inverse.lean, after jinaga.js's UnionFind.ts). A path condition
// joins its match's unknown to the label it names. An existential condition
// joins its match's unknown to every label its path conditions name. Only the
// givens the matches use are labels, as for a feed (`usedGivens`); UnionFind.ts
// counts every given, and so refuses an unused one (jinaga/jinaga-spec#60).

function referenced(matches: Match[]): string[] {
    return matches.flatMap(m => m.conditions.flatMap(c => c.type === "path" ? [c.labelRight] : referenced(c.matches)));
}

/** Every label, and every pair the connectivity check joins. */
function connections(matches: Match[]): { labels: string[]; edges: [string, string][] } {
    const labels: string[] = [];
    const edges: [string, string][] = [];
    for (const m of matches) {
        const u = m.unknown.name;
        labels.push(u);
        for (const c of m.conditions) {
            if (c.type === "path") {
                labels.push(c.labelRight);
                edges.push([u, c.labelRight]);
            } else {
                const inner = connections(c.matches);
                const names = referenced(c.matches);
                labels.push(...inner.labels, ...names);
                edges.push(...inner.edges, ...names.map(n => [u, n] as [string, string]));
            }
        }
    }
    return { labels, edges };
}

/** Every label is joined to every other, through path conditions or through labels an existential condition names. */
export function isConnected(specification: Specification): boolean {
    const { labels: matchLabels, edges } = connections(specification.matches);
    const given = usedGivens(specification.given, specification.matches);
    const labels = [...new Set([...given.map(g => g.label.name), ...matchLabels])];
    if (labels.length === 0) return true;
    let reached = [labels[0]];
    for (let i = 0; i < labels.length; i++) {
        reached = [...new Set([...reached, ...edges.flatMap(([a, b]) =>
            reached.includes(a) ? [b] : reached.includes(b) ? [a] : [])])];
    }
    return labels.every(l => reached.includes(l));
}

/** Labels the matches name but do not bind. `inner` holds the labels bound around them. */
function freeIn(inner: string[], matches: Match[]): string[] {
    return matches.flatMap(m => m.conditions.flatMap(c => c.type === "path"
        ? (inner.includes(c.labelRight) ? [] : [c.labelRight])
        : freeIn([...inner, ...c.matches.map(n => n.unknown.name)], c.matches)));
}

/** The givens the matches name, in their path conditions or their filters, in the specification's order (`usedGivens`). */
export function usedGivens<G extends { label: Label }>(given: G[], matches: Match[]): G[] {
    const free = freeIn([], matches);
    return given.filter(g => free.includes(g.label.name));
}

/**
 * A feed is joined when its path conditions alone, its negative conditions'
 * filters dropped, join its matches and the givens it uses, so it is not a
 * product; and it passes `isConnected`, so each filter's matches are joined to
 * it (`isJoined`).
 */
const isJoined = (f: Specification): boolean =>
    isConnected(f) && isConnected(asFeed(f.given, f.matches.map(paths)));

/**
 * Every descendant, as a feed, is connected, and every feed `buildFeeds`
 * emits is joined (`ConnectedDescendants`).
 */
export function isConnectedDeep(specification: Specification): boolean {
    return descendants(specification).every(d => isConnected(asFeed(d.given, d.matches))) &&
        feedsOf(specification as any).every(isJoined);
}
