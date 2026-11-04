// Runs the cascade vectors (vectors/cascade/) against @jinaga/cascade-core.
//
//   CASCADE_CORE=/path/to/jinaga-cascade-core npm run --silent cascade
//
// For each vector, builds its pipeline through cascade-core's public builder,
// performs its operations in each of its orders, and compares the output with
// the vector's expected output. Arrays are compared without regard to order:
// cascade-core's arrays are in arrival order, which the model does not have.
import { deepStrictEqual } from "node:assert";
import { isDeepStrictEqual } from "node:util";
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const cascadeCore = resolve(process.env.CASCADE_CORE ?? join(here, "../../../jinaga-cascade-core"));
const vectorsDir = join(resolve(process.env.VECTORS ?? join(here, "../../vectors")), "cascade");
const { createPipeline, toPipelinePlainOutput } = await import(pathToFileURL(join(cascadeCore, "src/index.ts")).href);

/** A JSON string of a value with its object keys sorted, for ordering. */
const sortedJson = (value: unknown): string => JSON.stringify(value, (_k, v) =>
    v !== null && typeof v === "object" && !Array.isArray(v)
        ? Object.fromEntries(Object.keys(v).sort().map(k => [k, v[k]]))
        : v);

/** The rows of a tree array, in a canonical order. Only the arrays the
descriptor declares are the tree's, in a row or in an object it declares, such
as an enriched copy of a row: their order is arrival order, which the model
does not have, and an empty one is absent, as the model has none. A property's
value, even a list, is compared as it is. */
const rows = (items: unknown[], node: any): unknown[] =>
    items.map(item => row(item, node)).sort((a, b) => {
        const x = sortedJson(a), y = sortedJson(b);
        return x < y ? -1 : x > y ? 1 : 0;
    });

const row = (item: any, node: any): unknown => {
    const arrays = new Map<string, any>(node.arrays.map((a: any) => [a.name, a.type]));
    const objects = new Map<string, any>(node.objects.map((o: any) => [o.name, o.type]));
    return Object.fromEntries(Object.keys(item)
        .filter(k => item[k] !== undefined)
        .filter(k => !(arrays.has(k) && Array.isArray(item[k]) && item[k].length === 0))
        .map(k => [k,
            arrays.has(k) ? rows(item[k], arrays.get(k)) :
            objects.has(k) && item[k] !== null && typeof item[k] === "object" ? row(item[k], objects.get(k)) :
            item[k]]));
};

const sourceArray = (a: any): any => ({
    name: a.name,
    type: { arrays: a.type.arrays.map(sourceArray), collectionKey: [], scalars: a.type.scalars, objects: [] },
});

const predicate = (p: any) => (row: any) => {
    const v = row[p.property];
    switch (p.op) {
        case "gt": return typeof v === "number" && v > p.value;
        case "lt": return typeof v === "number" && v < p.value;
        case "eq": return isDeepStrictEqual(v, p.value);
        default: throw new Error(`unknown predicate ${p.op}`);
    }
};

/** An expression's value on a row: a sum is of two numbers, else undefined. */
const evaluate = (e: any, row: any): unknown => {
    switch (e.op) {
        case "prop": return row[e.property];
        case "lit": return e.value;
        case "add": {
            const a = evaluate(e.left, row), b = evaluate(e.right, row);
            return typeof a === "number" && typeof b === "number" ? a + b : undefined;
        }
        case "cond": return predicate(e.predicate)(row) ? evaluate(e.then, row) : evaluate(e.else, row);
        default: throw new Error(`unknown expression ${e.op}`);
    }
};

/** The vector's pipeline, built through the builder. */
function builderOf(pipeline: any): any {
    let b: any = createPipeline(pipeline.root, pipeline.source.scalars, pipeline.source.arrays.map(sourceArray));
    for (const s of pipeline.steps) {
        switch (s.step) {
            case "groupBy": b = b.groupBy(s.by, s.as); break;
            case "sum": b = b.sum(s.array, s.property, s.as); break;
            case "count": b = b.count(s.array, s.as); break;
            case "min": b = b.min(s.array, s.property, s.as); break;
            case "max": b = b.max(s.array, s.property, s.as); break;
            case "dropProperty": b = b.dropProperty(s.property); break;
            case "flatten": b = b.flatten(s.parent, s.child, s.as); break;
            case "filter": b = b.filter(predicate(s.predicate), [s.predicate.property]); break;
            case "defineProperty": b = b.defineProperty(s.as, (row: any) => evaluate(s.expr, row), s.deps); break;
            case "cumulativeSum": b = b.cumulativeSum(s.array, s.orderBy, s.properties); break;
            case "replaceToDelta": b = b.replaceToDelta(s.entity, s.event, s.orderBy, s.properties, s.outputs); break;
            case "pickByMin": b = b.pickByMin(s.array, s.property, s.as); break;
            case "pickByMax": b = b.pickByMax(s.array, s.property, s.as); break;
            case "enrich": b = b.enrich(s.source, builderOf(s.pipeline), s.primaryKey, s.as, s.whenMissing); break;
            default: throw new Error(`unknown step ${s.step}`);
        }
    }
    return b;
}

/** Perform the operations in one order and read the output. */
function run(v: any, order: number[]): unknown {
    const builder = builderOf(v.pipeline);
    let state: any[] = [];
    const pipeline = builder.build((transform: (s: any[]) => any[]) => { state = transform(state); });
    for (const i of order) {
        const op = v.ops[i];
        const [first, ...rest] = op.keys;
        if (op.source !== undefined) {
            const input = pipeline.sources[op.source];
            if (op.op === "add") input.add(first, op.props); else input.remove(first, op.props);
        } else if (op.path.length === 0) {
            if (op.op === "add") pipeline.add(first, op.props); else pipeline.remove(first, op.props);
        } else {
            const input = pipeline.collection(...op.path);
            const parentKeyPath = [first, ...rest.slice(0, -1)];
            const key = rest[rest.length - 1];
            if (op.op === "add") input.add(parentKeyPath, key, op.props); else input.remove(parentKeyPath, key, op.props);
        }
    }
    pipeline.flush();
    return rows(toPipelinePlainOutput(state, builder.getTypeDescriptor()), builder.getTypeDescriptor());
}

let passed = 0, failed = 0;
for (const file of readdirSync(vectorsDir).filter(f => f.endsWith(".json")).sort()) {
    const v = JSON.parse(readFileSync(join(vectorsDir, file), "utf8"));
    const expected = rows(v.expected, builderOf(v.pipeline).getTypeDescriptor());
    v.orders.forEach((order: number[], n: number) => {
        let actual: unknown;
        try {
            actual = run(v, order);
            deepStrictEqual(actual, expected);
            passed++;
        } catch (e: any) {
            failed++;
            console.log(`FAIL ${v.name}, order ${n}: ${actual === undefined ? e.message : ""}`);
            if (actual !== undefined) {
                console.log(`  expected ${JSON.stringify(expected)}`);
                console.log(`  actual   ${JSON.stringify(actual)}`);
            }
        }
    });
}
console.log(`${passed} cascade vector runs pass, ${failed} fail`);
process.exitCode = failed ? 1 : 0;
