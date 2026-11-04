// Runs the cascade vectors (vectors/cascade/) against @jinaga/cascade-core.
//
//   CASCADE_CORE=/path/to/jinaga-cascade-core npm run --silent cascade
//
// For each vector, builds its pipeline through cascade-core's public builder,
// performs its operations in each of its orders, and compares the output with
// the vector's expected output. Arrays are compared without regard to order:
// cascade-core's arrays are in arrival order, which the model does not have.
import { deepStrictEqual } from "node:assert";
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const cascadeCore = resolve(process.env.CASCADE_CORE ?? join(here, "../../../jinaga-cascade-core"));
const vectorsDir = join(resolve(process.env.VECTORS ?? join(here, "../../vectors")), "cascade");
const { createPipeline, toPipelinePlainOutput } = await import(pathToFileURL(join(cascadeCore, "src/index.ts")).href);

/** A value with object keys sorted and arrays in a canonical order. An empty
array is dropped: the model has no empty arrays, only absent ones. */
const canonical = (value: unknown): unknown => {
    if (Array.isArray(value)) {
        return value.map(canonical).sort((a, b) => {
            const x = JSON.stringify(a), y = JSON.stringify(b);
            return x < y ? -1 : x > y ? 1 : 0;
        });
    }
    if (value !== null && typeof value === "object") {
        return Object.fromEntries(Object.keys(value).sort()
            .filter(k => (value as any)[k] !== undefined)
            .filter(k => !(Array.isArray((value as any)[k]) && (value as any)[k].length === 0))
            .map(k => [k, canonical((value as any)[k])]));
    }
    return value;
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
        case "eq": return JSON.stringify(canonical(v)) === JSON.stringify(canonical(p.value));
        default: throw new Error(`unknown predicate ${p.op}`);
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
        if (op.path.length === 0) {
            if (op.op === "add") pipeline.add(first, op.props); else pipeline.remove(first, op.props);
        } else {
            const input = pipeline.collection(...op.path);
            const parentKeyPath = [first, ...rest.slice(0, -1)];
            const key = rest[rest.length - 1];
            if (op.op === "add") input.add(parentKeyPath, key, op.props); else input.remove(parentKeyPath, key, op.props);
        }
    }
    pipeline.flush();
    return toPipelinePlainOutput(state, builder.getTypeDescriptor());
}

let passed = 0, failed = 0;
for (const file of readdirSync(vectorsDir).filter(f => f.endsWith(".json")).sort()) {
    const v = JSON.parse(readFileSync(join(vectorsDir, file), "utf8"));
    const expected = canonical(v.expected);
    v.orders.forEach((order: number[], n: number) => {
        let actual: unknown;
        try {
            actual = canonical(run(v, order));
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
