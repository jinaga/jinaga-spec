// A reference implementation of `buildFeeds` (JinagaSpec/Feeds.lean), in the
// shape of jinaga.js's `Specification`, written to be ported into jinaga.js's
// src/specification/feed-builder.ts.
//
//   PORT=./feed-builder.ts npm run --silent feeds
//
// These are chapter 12's ordinary, excluding and restoring feeds, derived from
// its requirements: a replica reads what the replicator reads; tuples are never
// inserted behind a bookmark, so a feed has one level of negative condition; and
// a new client is not sent the details of an entity whose exclusion nothing has
// cancelled.
//
// Walk a level's matches, each joined with its positive conditions. At each
// negative condition, every feed so far
//   - emits an excluding feed: itself, then the condition's level, and stops;
//   - goes on filtered by the condition's level; and
//   - goes on restored: through the condition's level, then the level of one of
//     that level's own negative conditions, walked the same way.
//
// A feed that completes the specification, filtered or restored, then goes on
// to each child specification of the projection, walked the same way after it.
// An excluding feed stops before, so a child's facts are deferred with the rest
// of an excluded entity's details.
//
// It differs from jinaga.js's buildFeeds in three places, each a vector:
//   - a restoring feed drops the negative conditions of the fact it restores
//     (`not-exists-cancelled-twice`, `not-exists-cancelled-by-second`);
//   - a positive condition inside a negative one joins its level
//     (`exists-inside-not-exists`); and
//   - an excluding feed is not filtered, since what it would filter out a
//     restoring feed delivers anyway.

// It refuses a specification that is not well formed (`isWellFormedDeep`), or
// one of whose feeds or child specifications is not connected
// (`isConnectedDeep`): the hypotheses of the theorems. A specification that
// repeats a label is renamed first (`withDistinctLabels`, ./distinct-labels.ts),
// so the feeds are those of the renamed specification.

import { withDistinctLabels } from "./distinct-labels.ts";
import { isConnectedDeep, isWellFormed, usedGivens } from "./well-formed.ts";

type Label = { name: string; type: string };
type Role = { name: string; predecessorType: string };
type PathCondition = { type: "path"; rolesLeft: Role[]; labelRight: string; rolesRight: Role[] };
type ExistentialCondition = { type: "existential"; exists: boolean; matches: Match[] };
type Condition = PathCondition | ExistentialCondition;
type Match = { unknown: Label; conditions: Condition[] };
type Given = { label: Label; conditions: unknown[] };
type Component = { type: "specification"; name: string; matches: Match[]; projection: Projection } |
    { type: "fact" | "field" | "hash" | "time"; name: string; label: string };
type Projection = { type: "composite"; components: Component[] } | { type: "fact" | "field" | "hash" | "time"; label: string };
type Specification = { given: Given[]; matches: Match[]; projection: Projection };
type Continuation = (feed: Match[]) => Match[][];

const isPath = (c: Condition): c is PathCondition => c.type === "path";
const negatives = (m: Match): Match[][] =>
    m.conditions.flatMap(c => c.type === "existential" && !c.exists ? [c.matches] : []);

/**
 * Join every positive condition's matches into the level, right after the
 * match that holds it. What remains on each match is its path conditions and
 * its negative conditions.
 */
function flatten(matches: Match[]): Match[] {
    return matches.flatMap(m => [
        { unknown: m.unknown, conditions: m.conditions.filter(c => isPath(c) || !c.exists) },
        ...flatten(m.conditions.flatMap(c => c.type === "existential" && c.exists ? c.matches : []))
    ]);
}

export const paths = (m: Match): Match => ({ unknown: m.unknown, conditions: m.conditions.filter(isPath) });

/** A negative condition's level: its matches, positives joined, path conditions only. */
const level = (matches: Match[]): Match[] => flatten(matches).map(paths);

/** The negative conditions of a level, with its positive conditions joined. */
const negativesOf = (matches: Match[]): Match[][] => flatten(matches).flatMap(negatives);

/**
 * Add a condition to the last match of the feed. Every label a filter names is
 * bound by then.
 */
function addLast(condition: Condition, feed: Match[]): Match[] {
    return feed.map((m, i) => i === feed.length - 1 ? { ...m, conditions: [...m.conditions, condition] } : m);
}

/** The feeds of a level after the partial feed `P`; completed feeds go to `k`. */
function levelFeeds(k: Continuation, P: Match[], matches: Match[]): Match[][] {
    if (matches.length === 0) return k(P);
    const [m, ...rest] = matches;
    return negFeeds(Q => levelFeeds(k, Q, rest), [...P, ...level([m])], negativesOf([m]));
}

/** The feeds of the partial feed `Q` with the negative conditions `negs` to walk. */
function negFeeds(k: Continuation, Q: Match[], negs: Match[][]): Match[][] {
    if (negs.length === 0) return k(Q);
    const [ns, ...rest] = negs;
    const lvl = level(ns);
    const filter: Condition = { type: "existential", exists: false, matches: lvl };
    return [
        [...Q, ...lvl],
        ...negFeeds(k, addLast(filter, Q), rest),
        ...negativesOf(ns).flatMap(canceller =>
            levelFeeds(Q2 => negFeeds(k, Q2, rest), [...Q, ...lvl], canceller))
    ];
}

/** A feed that walks no successor edge delivers only what a replica already holds. */
const traversesSuccessors = (feed: Specification) =>
    feed.matches.some(m => m.conditions.some(c => isPath(c) && c.rolesLeft.length > 0));

/** A projection's child specifications. */
const children = (projection: Projection): { matches: Match[]; projection: Projection }[] =>
    projection.type === "composite"
        ? projection.components.flatMap(c => c.type === "specification" ? [{ matches: c.matches, projection: c.projection }] : [])
        : [];

/**
 * A positive feed, one that completes its level, then the feeds of each child
 * specification walked after it, each going on to the child's own projection.
 * An excluding feed never reaches here, so it carries no child's facts.
 */
const projectionFeeds = (projection: Projection): Continuation => P =>
    [P, ...children(projection).flatMap(c => levelFeeds(projectionFeeds(c.projection), P, c.matches))];

/** Matches as a feed of `given`: with the givens they use, and no projection. */
export const asFeed = (given: { label: Label }[], matches: Match[]): Specification => ({
    given: usedGivens(given, matches).map(g => ({ label: g.label, conditions: [] })),
    matches,
    projection: { type: "composite", components: [] }
});

/** The feeds of a specification, with no check of its input. */
export function feedsOf(specification: Specification): Specification[] {
    return levelFeeds(projectionFeeds(specification.projection), [], specification.matches)
        .map(matches => asFeed(specification.given, matches))
        .filter(traversesSuccessors);
}

export function buildFeeds(specification: Specification): Specification[] {
    // The theorems assume every descendant is well formed (`isWellFormedDeep`).
    // jinaga.js's assertWellFormed does not look inside a child specification.
    if (!isWellFormed(specification as any))
        throw new Error("The specification is not well formed: a label is out of scope, redeclared, or reserved.");
    // The theorems are about a specification whose givens carry no conditions.
    // Conditions on givens are reduced to a match first (`reduceGivenConditions`),
    // and renamed after (jinaga/jinaga-spec#71).
    if (specification.given.some(g => (g.conditions ?? []).length > 0))
        throw new Error("Reduce the conditions on the givens first (reduceGivenConditions): feeds are built from a specification whose givens have none.");
    // Joining positive conditions into one level would bind a label that two
    // sibling conditions both declare twice, and a child specification's feeds
    // bind its parent's labels too. The theorems assume each descendant
    // declares each label once (`DistinctLabels`, JinagaSpec/Feeds.lean); the
    // renaming establishes it and reads the same (`withDistinctLabels_reads`,
    // jinaga/jinaga-spec#71).
    specification = withDistinctLabels(specification as any) as Specification;
    // No feed is a product of two chains (`ConnectedDescendants`,
    // JinagaSpec/Connected.lean, jinaga/jinaga-spec#55). Checked after renaming:
    // the check reads a label by name, so before it two declarations that share
    // one would count as one label (`two-chains-share-a-name`).
    if (!isConnectedDeep(specification as any))
        throw new Error("The specification is not connected: a feed, or a child specification, joins givens that nothing joins to each other, or a feed is joined only by a negative condition.");
    return feedsOf(specification);
}
