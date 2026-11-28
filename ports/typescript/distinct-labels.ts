// A reference implementation of `withDistinctLabels` (JinagaSpec/DistinctLabels.lean),
// in the shape of jinaga.js's `Specification`.
//
// Lexical scope lets two declarations share a name when neither is in scope of
// the other: sibling existential conditions, or a condition and a later match
// or child specification (`isWellFormed`). `buildFeeds` joins a descendant's
// positive conditions into one level, where both are in scope, so the feed
// theorems assume each descendant declares each label once (`DistinctLabels`).
// This renaming establishes it, and keeps what the specification reads
// (`withDistinctLabels_reads`, Proofs/DistinctLabels.lean):
//
//   - Walking each descendant in declaration order, a match that declares a
//     name already declared in that descendant (a given included) takes the
//     first of `name2`, `name3`, … that appears nowhere in the specification
//     and that the walk has not made, and every reference to it within its
//     scope follows.
//   - A new name never begins with the reserved prefix: a repeated `__` name
//     first loses its leading underscores.
//   - Givens keep their names.
//   - Sibling child specifications are separate descendants, so they may keep
//     a shared label.
//
// A specification with conditions on its givens is renamed after they are
// reduced to a match (`reduceGivenConditions`): their matches then join the
// first level of every descendant.

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

const reserved = (name: string) => name.startsWith("__");

/** Every label a list of matches declares, at any depth. */
const declared = (matches: Match[]): string[] => matches.flatMap(m => [
    m.unknown.name,
    ...m.conditions.flatMap(c => c.type === "existential" ? declared(c.matches) : [])
]);

/** Every label the specification's projection declares, in every child specification. */
const declaredInProjection = (projection: Projection): string[] => projection.type !== "composite" ? [] :
    projection.components.flatMap(c => c.type === "specification"
        ? [...declared(c.matches), ...declaredInProjection(c.projection)] : []);

export function withDistinctLabels(specification: Specification): Specification {
    const givens = specification.given.map(g => g.label.name);
    // Every name the specification declares or the walk has made.
    const taken = new Set<string>([...givens, ...declared(specification.matches), ...declaredInProjection(specification.projection)]);

    function fresh(name: string): string {
        const base = reserved(name) ? (name.replace(/^_+/, "") || "label") : name;
        for (let suffix = 2; ; suffix++) {
            const candidate = `${base}${suffix}`;
            if (!taken.has(candidate)) return candidate;
        }
    }

    // `scope` maps each name in lexical scope to its new name. `declared` holds
    // what this descendant has declared so far, at every depth of condition.
    function renameMatches(matches: Match[], scope: Map<string, string>, declared: Set<string>): { matches: Match[]; scope: Map<string, string> } {
        const renamed = matches.map(match => {
            const name = declared.has(match.unknown.name) ? fresh(match.unknown.name) : match.unknown.name;
            taken.add(name);
            declared.add(name);
            const inner = new Map(scope).set(match.unknown.name, name);
            const conditions = match.conditions.map((condition): Condition => condition.type === "path"
                ? { ...condition, labelRight: scope.get(condition.labelRight) ?? condition.labelRight }
                : { ...condition, matches: renameMatches(condition.matches, inner, declared).matches });
            scope = inner;
            return { ...match, unknown: { ...match.unknown, name }, conditions };
        });
        return { matches: renamed, scope };
    }

    function renameProjection(projection: Projection, scope: Map<string, string>, declared: Set<string>): Projection {
        if (projection.type !== "composite")
            return { ...projection, label: scope.get(projection.label) ?? projection.label };
        return {
            ...projection,
            components: projection.components.map(component => {
                if (component.type !== "specification")
                    return { ...component, label: scope.get(component.label) ?? component.label };
                // Each child begins a descendant of its own, from what its parent declared.
                const childDeclared = new Set(declared);
                const child = renameMatches(component.matches, scope, childDeclared);
                return { ...component, matches: child.matches, projection: renameProjection(component.projection, child.scope, childDeclared) };
            })
        };
    }

    const declaredHere = new Set(givens);
    const top = renameMatches(specification.matches, new Map(givens.map(n => [n, n])), declaredHere);
    return { ...specification, matches: top.matches, projection: renameProjection(specification.projection, top.scope, declaredHere) };
}
