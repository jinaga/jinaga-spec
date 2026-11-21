// A reference implementation of `buildFeeds` (JinagaSpec/Feeds.lean), in the
// shape of jinaga.js's `Specification`. It is the algorithm `check-feeds`
// tests and the feed vectors (vectors/feeds/) are generated from, written to
// be ported into jinaga.js's src/specification/feed-builder.ts.
//
//   PORT=./feed-builder.ts npm run --silent feeds
//
// It differs from jinaga.js's `buildFeeds` in three places, each a case in
// vectors/feeds/:
//
// 1. A restoring branch drops the negative conditions its excluding feed
//    attached, and skips the rest of the excluded condition
//    (`not-exists-cancelled-twice`, `not-exists-cancelled-by-second`). The
//    excluded fact is cancelled when any one of its negative conditions fails;
//    a restoring feed shows that one did, and asks nothing more of it.
// 2. A positive condition inside a negative one joins the stripped condition
//    as matches (`exists-inside-not-exists`). jinaga.js replaces the condition
//    with the positive one.
// 3. The remainder is a list of work rather than a continuation chain. That is
//    a matter of presentation: the feeds come out in the same order.

type Label = { name: string; type: string };
type Role = { name: string; predecessorType: string };
type PathCondition = { type: "path"; rolesLeft: Role[]; labelRight: string; rolesRight: Role[] };
type ExistentialCondition = { type: "existential"; exists: boolean; matches: Match[] };
type Condition = PathCondition | ExistentialCondition;
type Match = { unknown: Label; conditions: Condition[] };
type Given = { label: Label; conditions: unknown[] };
type Specification = { given: Given[]; matches: Match[]; projection: unknown };

/** What a feed still has to match. */
type Work =
    | { kind: "matches"; matches: Match[] }
    | { kind: "conditions"; label: string; conditions: Condition[] }
    | { kind: "stop"; parity: number };

const isPath = (c: Condition): c is PathCondition => c.type === "path";

/**
 * The matches of a negative condition as a feed applies it: each match with
 * only its path conditions, followed by the matches of every positive
 * condition inside it, at any depth.
 */
function stripped(matches: Match[]): Match[] {
    return matches.flatMap(m => [
        { unknown: m.unknown, conditions: m.conditions.filter(isPath) },
        ...m.conditions.flatMap(c => c.type === "existential" && c.exists ? stripped(c.matches) : [])
    ]);
}

/** Add each given these conditions name that the feed does not have yet. */
function useGivens(givens: Given[], feed: Given[], conditions: Condition[]): Given[] {
    for (const c of conditions) {
        if (!isPath(c)) continue;
        const given = givens.find(g => g.label.name === c.labelRight);
        if (given && !feed.some(f => f.label.name === given.label.name)) {
            feed = [...feed, { label: given.label, conditions: [] }];
        }
    }
    return feed;
}

function withMatch(givens: Given[], feed: Specification, match: Match): Specification {
    const paths = match.conditions.filter(isPath);
    return {
        ...feed,
        given: useGivens(givens, feed.given, paths),
        matches: [...feed.matches, { unknown: match.unknown, conditions: paths }]
    };
}

/** Attach a negative condition, stripped, to the last match whose unknown is `label`. */
function withCondition(givens: Given[], feed: Specification, label: string, matches: Match[]): Specification {
    const condition: ExistentialCondition = { type: "existential", exists: false, matches: stripped(matches) };
    let index = -1;
    for (let i = feed.matches.length - 1; i >= 0; i--) {
        if (feed.matches[i].unknown.name === label) { index = i; break; }
    }
    return {
        ...feed,
        given: useGivens(givens, feed.given, condition.matches.flatMap(m => m.conditions)),
        matches: feed.matches.map((m, i) => i === index ? { ...m, conditions: [...m.conditions, condition] } : m)
    };
}

/** The feed without the negative conditions attached to its matches from `base` on. */
function unattach(base: number, feed: Specification): Specification {
    return {
        ...feed,
        matches: feed.matches.map((m, i) => i < base ? m : { unknown: m.unknown, conditions: m.conditions.filter(isPath) })
    };
}

/** What follows the end of the excluding branch of parity `parity`. */
function afterStop(parity: number, work: Work[]): Work[] {
    const index = work.findIndex(w => w.kind === "stop" && w.parity === parity);
    return index < 0 ? [] : work.slice(index + 1);
}

/**
 * The feeds that start from `feed`, at nesting depth `parity`, with `work`
 * still to match. In an excluding feed, `base` counts the matches it began
 * with: those before the condition it follows.
 */
function run(givens: Given[], feed: Specification, parity: number, base: number, work: Work[]): Specification[] {
    if (work.length === 0) return [feed];
    const [head, ...rest] = work;
    switch (head.kind) {
        case "stop":
            return head.parity === parity ? [feed] : run(givens, feed, parity, base, rest);
        case "matches": {
            if (head.matches.length === 0) return run(givens, feed, parity, base, rest);
            const [match, ...matches] = head.matches;
            return run(givens, withMatch(givens, feed, match), parity, base, [
                { kind: "conditions", label: match.unknown.name, conditions: match.conditions },
                { kind: "matches", matches },
                ...rest
            ]);
        }
        case "conditions": {
            if (head.conditions.length === 0) return run(givens, feed, parity, base, rest);
            const [condition, ...conditions] = head.conditions;
            const remaining: Work[] = [{ kind: "conditions", label: head.label, conditions }, ...rest];
            if (condition.type === "path") return run(givens, feed, parity, base, remaining);
            if (condition.exists) {
                return run(givens, feed, parity, base, [{ kind: "matches", matches: condition.matches }, ...remaining]);
            }
            // An excluding branch follows the condition's matches and stops at
            // their end. A restoring branch shows that the fact its excluding
            // feed follows is cancelled, which any one of that fact's negative
            // conditions does. So it drops the conditions the excluding feed
            // attached, and skips the rest of the excluded condition.
            const branch = parity % 2 === 0
                ? run(givens, feed, parity + 1, feed.matches.length, [
                    { kind: "matches", matches: condition.matches },
                    { kind: "stop", parity: parity + 1 },
                    ...remaining
                ])
                : run(givens, unattach(base, feed), parity + 1, base, [
                    { kind: "matches", matches: condition.matches },
                    ...afterStop(parity, remaining)
                ]);
            return [...branch, ...run(givens, withCondition(givens, feed, head.label, condition.matches), parity, base, remaining)];
        }
    }
}

/** A feed that walks no successor edge delivers only what a replica already holds. */
function traversesSuccessors(feed: Specification): boolean {
    return feed.matches.some(m => m.conditions.some(c => isPath(c) && c.rolesLeft.length > 0));
}

export function buildFeeds(specification: Specification): Specification[] {
    const empty: Specification = { given: [], matches: [], projection: { type: "composite", components: [] } };
    return run(specification.given, empty, 0, 0, [{ kind: "matches", matches: specification.matches }])
        .filter(traversesSuccessors);
}
