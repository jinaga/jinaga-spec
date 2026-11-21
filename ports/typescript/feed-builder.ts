// A reference implementation of `buildFeeds` (JinagaSpec/Feeds.lean), in the
// shape of jinaga.js's `Specification`, written to be ported into jinaga.js's
// src/specification/feed-builder.ts.
//
//   PORT=./feed-builder.ts npm run --silent feeds
//
// A specification's levels are its matches and the matches of each negative
// existential condition, at any depth. Each level is one feed: its matches,
// with every positive condition's matches joined in after the match they
// qualify, keeping only path conditions, after the matches of the levels that
// enclose it. A feed that walks no successor edge is dropped.
//
// It replaces jinaga.js's excluding and restoring feeds. No feed filters by a
// negative condition, so none has to restore what a filter wrongly excluded.

type Label = { name: string; type: string };
type Role = { name: string; predecessorType: string };
type PathCondition = { type: "path"; rolesLeft: Role[]; labelRight: string; rolesRight: Role[] };
type ExistentialCondition = { type: "existential"; exists: boolean; matches: Match[] };
type Condition = PathCondition | ExistentialCondition;
type Match = { unknown: Label; conditions: Condition[] };
type Given = { label: Label; conditions: unknown[] };
type Specification = { given: Given[]; matches: Match[]; projection: unknown };

const isPath = (c: Condition): c is PathCondition => c.type === "path";

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

/** The level's own feed, after `pre`, then the feeds of its negative conditions. */
function levelFeeds(pre: Match[], matches: Match[]): Match[][] {
    const level = flatten(matches);
    const here = [...pre, ...level.map(paths)];
    return [here, ...level.flatMap(m => m.conditions.flatMap(c =>
        c.type === "existential" && !c.exists ? levelFeeds(here, c.matches) : []))];
}

/** A feed that walks no successor edge delivers only what a replica already holds. */
const traversesSuccessors = (feed: Specification) =>
    feed.matches.some(m => m.conditions.some(c => isPath(c) && c.rolesLeft.length > 0));

export function buildFeeds(specification: Specification): Specification[] {
    return levelFeeds([], specification.matches)
        .map(matches => ({
            given: specification.given
                .filter(g => matches.some(m => m.conditions.some(c => isPath(c) && c.labelRight === g.label.name)))
                .map(g => ({ label: g.label, conditions: [] })),
            matches,
            projection: { type: "composite", components: [] }
        }))
        .filter(traversesSuccessors);
}
