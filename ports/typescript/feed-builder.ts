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
// It differs from jinaga.js's buildFeeds in three places, each a vector:
//   - a restoring feed drops the negative conditions of the fact it restores
//     (`not-exists-cancelled-twice`, `not-exists-cancelled-by-second`);
//   - a positive condition inside a negative one joins its level
//     (`exists-inside-not-exists`); and
//   - an excluding feed is not filtered, since what it would filter out a
//     restoring feed delivers anyway.

type Label = { name: string; type: string };
type Role = { name: string; predecessorType: string };
type PathCondition = { type: "path"; rolesLeft: Role[]; labelRight: string; rolesRight: Role[] };
type ExistentialCondition = { type: "existential"; exists: boolean; matches: Match[] };
type Condition = PathCondition | ExistentialCondition;
type Match = { unknown: Label; conditions: Condition[] };
type Given = { label: Label; conditions: unknown[] };
type Specification = { given: Given[]; matches: Match[]; projection: unknown };
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

const paths = (m: Match): Match => ({ unknown: m.unknown, conditions: m.conditions.filter(isPath) });

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

/** The labels a feed's path conditions name, in its matches or its filters. */
const named = (matches: Match[]): string[] => matches.flatMap(m => m.conditions.flatMap(c =>
    isPath(c) ? [c.labelRight] : named(c.matches)));

export function buildFeeds(specification: Specification): Specification[] {
    return levelFeeds(feed => [feed], [], specification.matches)
        .map(matches => ({
            given: specification.given
                .filter(g => named(matches).includes(g.label.name))
                .map(g => ({ label: g.label, conditions: [] })),
            matches,
            projection: { type: "composite", components: [] }
        }))
        .filter(traversesSuccessors);
}
