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
// Not modelled yet, and ignored here: conditions on givens, and the labels
// declared inside nested specification projections.

export interface Label { name: string; type: string }
export interface Role { name: string; predecessorType: string }
export interface PathCondition { type: "path"; rolesLeft: Role[]; labelRight: string; rolesRight: Role[] }
export interface ExistentialCondition { type: "existential"; exists: boolean; matches: Match[] }
export type Condition = PathCondition | ExistentialCondition;
export interface Match { unknown: Label; conditions: Condition[] }
export type Component = { type: "specification" } | { type: "fact" | "field" | "hash" | "time"; label: string };
export type Projection =
    | { type: "composite"; components: Component[] }
    | { type: "fact" | "field" | "hash" | "time"; label: string };
export interface Specification {
    given: { label: Label }[];
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

function projectedLabels(projection: Projection): string[] {
    return projection.type === "composite"
        ? projection.components.flatMap(c => c.type === "specification" ? [] : [c.label])
        : [projection.label];
}

export function isWellFormed(specification: Specification): boolean {
    const givens = specification.given.map(g => g.label.name);
    const unknowns = specification.matches.map(m => m.unknown.name);
    return givens.every(name => !isReserved(name)) &&
        isWellFormedMatches(givens, specification.matches) &&
        projectedLabels(specification.projection).every(label => givens.includes(label) || unknowns.includes(label));
}
