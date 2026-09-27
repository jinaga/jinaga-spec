// A reference implementation of `isWellFormed`, mirroring JinagaSpec/WellFormed.lean
// line for line. It depends on no other package, so it can be lifted into
// jinaga.js as it stands. Its types are structural: they match `Specification`
// in `src/specification/specification.ts`.
//
// It checks the preconditions of `splitBeforeFirstSuccessor`:
//   scoped      every label a path condition names is in scope
//   unshadowed  no match declares a label that is already in scope
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

export interface Verdicts {
    scoped: boolean;
    unshadowed: boolean;
    projected: boolean;
    wellFormed: boolean;
}

// A match adds its unknown to the scope of the matches after it, and of its own
// existential conditions. `inner` is the scope of existential conditions and
// `outer` of path conditions.
function isScopedMatches(scope: string[], matches: Match[]): boolean {
    for (const match of matches) {
        const inner = [match.unknown.name, ...scope];
        if (!match.conditions.every(c => isScopedCondition(inner, scope, c))) {
            return false;
        }
        scope = inner;
    }
    return true;
}

function isScopedCondition(inner: string[], outer: string[], condition: Condition): boolean {
    return condition.type === "path"
        ? outer.includes(condition.labelRight)
        : isScopedMatches(inner, condition.matches);
}

// Scope is lexical: the labels a nested match declares do not outlive its
// condition, so sibling existential conditions may reuse a name.
function isUnshadowedMatches(scope: string[], matches: Match[]): boolean {
    for (const match of matches) {
        if (scope.includes(match.unknown.name)) {
            return false;
        }
        const inner = [match.unknown.name, ...scope];
        if (!match.conditions.every(c => isUnshadowedCondition(inner, c))) {
            return false;
        }
        scope = inner;
    }
    return true;
}

function isUnshadowedCondition(inner: string[], condition: Condition): boolean {
    return condition.type === "path" || isUnshadowedMatches(inner, condition.matches);
}

function projectedLabels(projection: Projection): string[] {
    return projection.type === "composite"
        ? projection.components.flatMap(c => c.type === "specification" ? [] : [c.label])
        : [projection.label];
}

export function checkWellFormed(specification: Specification): Verdicts {
    const givens = specification.given.map(g => g.label.name);
    const unknowns = specification.matches.map(m => m.unknown.name);
    const scoped = isScopedMatches(givens, specification.matches);
    const unshadowed = isUnshadowedMatches(givens, specification.matches);
    const projected = projectedLabels(specification.projection)
        .every(label => givens.includes(label) || unknowns.includes(label));
    return { scoped, unshadowed, projected, wellFormed: scoped && unshadowed && projected };
}

export function isWellFormed(specification: Specification): boolean {
    return checkWellFormed(specification).wellFormed;
}
