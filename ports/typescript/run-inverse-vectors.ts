// Runs the inverse vectors (vectors/inverse/) against jinaga.js.
//
//   JINAGA_JS=/path/to/jinaga.js npm run --silent inverse
//
// Three checks, for each vector:
//
// 1. The proven inverses, read by jinaga.js. Each vector's expected inverses,
//    read by jinaga.js's own MemoryStore from the subscription's givens and the
//    new fact, find exactly the vector's candidates, which include every result
//    gained and lost. This shows that jinaga.js's runner reads these
//    specifications as the reference semantics does. It must pass.
// 2. The port. If jinaga.js has `src/specification/inverse-candidates.ts`
//    (jinaga/jinaga.js#338), its `buildInverses` and `reorderInverse` must
//    produce the vector's inverses, structurally and in order. It must pass
//    once the port exists.
// 3. Today's `invertSpecification`. Reported, not required: whether its "add"
//    inverses report every gained result and its "remove" inverses every lost
//    one. The vectors named after jinaga.js#338 and #343 are expected to miss
//    until the port replaces it.
import { deepStrictEqual } from "node:assert";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const jinagaJs = resolve(process.env.JINAGA_JS ?? join(here, "../../../jinaga.js"));
const vectorsDir = join(resolve(process.env.VECTORS ?? join(here, "../../vectors")), "inverse");
const load = (path: string) => import(pathToFileURL(join(jinagaJs, path)).href);

const { MemoryStore } = await load("src/memory/memory-store.ts");
const { invertSpecification } = await load("src/specification/inverse.ts");
const { Trace } = await load("src/util/trace.ts");
Trace.off();
// PORT names another implementation to check instead, such as this
// directory's reference implementation: PORT=./inverse-candidates.ts.
const portPath = process.env.PORT ? resolve(process.env.PORT) : join(jinagaJs, "src/specification/inverse-candidates.ts");
const port = existsSync(portPath) ? await import(pathToFileURL(portPath).href) : undefined;

const pinLabel = "__f";
type Row = (number | null)[];
const key = (row: Row) => JSON.stringify(row);
const normalize = (value: unknown) => JSON.parse(JSON.stringify(value ?? null));

/** A store holding the vector's graph and its new fact. Fact ids become hashes. */
async function storeOf(v: any) {
    const facts = [...v.graph, v.fact];
    const typeOf = new Map<number, string>(facts.map((f: any) => [f.id, f.type]));
    const ref = (id: number) => ({ type: typeOf.get(id), hash: `h${id}` });
    const store = new MemoryStore();
    await store.save(facts.map((f: any) => {
        const predecessors: any = {};
        for (const p of f.predecessors) (predecessors[p.role] ??= []).push(ref(p.id));
        return { fact: { type: f.type, hash: `h${f.id}`, predecessors, fields: {} }, signatures: [] };
    }));
    return { store, ref };
}

const idOf = (reference: any): number | null => reference ? Number(reference.hash.slice(1)) : null;
const rowOf = (v: any, tuple: any): Row => v.rowLabels.map((l: string) => idOf(tuple[l]));

/** Read an inverse from the subscription's givens and the new fact. */
async function readInverse(v: any, store: any, ref: (id: number) => any, inverse: any): Promise<Row[]> {
    const start = inverse.given.map((g: any) =>
        g.label.name === pinLabel ? ref(v.fact.id) : ref(v.givens[g.label.name]));
    const results = await store.read(start, structuredClone(inverse));
    return results.map((r: any) => rowOf(v, r.tuple));
}

let failed = 0;
let portFailed = 0;
const legacy: string[] = [];
const files = readdirSync(vectorsDir).filter(f => f.endsWith(".json")).sort();
for (const file of files) {
    const v = JSON.parse(readFileSync(join(vectorsDir, file), "utf8"));
    const problems: string[] = [];
    const { store, ref } = await storeOf(v);
    const expected = new Set<string>(v.expected.candidates.map(key));
    const changed: Row[] = [...v.expected.gained, ...v.expected.lost];

    // 1. The proven inverses, read by jinaga.js.
    for (const list of ["inverses", "reordered"]) {
        try {
            const found = new Set<string>();
            for (const { specification } of v.expected[list]) {
                for (const row of await readInverse(v, store, ref, specification)) found.add(key(row));
            }
            const missing = changed.filter(row => !found.has(key(row)));
            if (missing.length > 0) problems.push(`${list}: jinaga.js's reads miss ${JSON.stringify(missing)}`);
            const extra = [...found].filter(k => !expected.has(k));
            const absent = [...expected].filter(k => !found.has(k));
            if (extra.length + absent.length > 0) {
                problems.push(`${list}: jinaga.js's reads differ from the vector's candidates: extra ${extra.join(" ")} absent ${absent.join(" ")}`);
            }
        } catch (e: any) {
            problems.push(`${list}: threw ${e.message}`);
        }
    }

    // 2. The port.
    if (port) {
        try {
            const built = port.buildInverses(structuredClone(v.specification));
            deepStrictEqual(normalize(built), v.expected.inverses.map((i: any) => i.specification));
            deepStrictEqual(normalize(built.map((i: any) => port.reorderInverse(i))),
                v.expected.reordered.map((i: any) => i.specification));
        } catch (e: any) {
            portFailed++;
            problems.push(`port: ${e.message.split("\n").slice(0, 12).join("\n")}`);
        }
    }

    // 3. Today's invertSpecification.
    try {
        const added = new Set<string>();
        const removed = new Set<string>();
        for (const inverse of invertSpecification(structuredClone(v.specification))) {
            const spec = inverse.inverseSpecification;
            if (spec.given[0].label.type !== v.fact.type) continue;
            const results = await store.read([ref(v.fact.id)], structuredClone(spec));
            for (const r of results) {
                // Keep the tuples whose givens are this subscription's.
                if (!Object.entries(v.givens).every(([name, id]) => !(name in r.tuple) || idOf(r.tuple[name]) === id)) continue;
                (inverse.operation === "add" ? added : removed).add(key(rowOf(v, r.tuple)));
            }
        }
        const missedGained = v.expected.gained.filter((row: Row) => !added.has(key(row)));
        const missedLost = v.expected.lost.filter((row: Row) => !removed.has(key(row)));
        if (missedGained.length + missedLost.length > 0) {
            legacy.push(`${v.name}: misses gained ${JSON.stringify(missedGained)} lost ${JSON.stringify(missedLost)}`);
        }
    } catch (e: any) {
        legacy.push(`${v.name}: invertSpecification threw: ${e.message.split("\n")[0]}`);
    }

    if (problems.length === 0) {
        console.log(`  ok    ${v.name}`);
    } else {
        failed++;
        console.log(`  FAIL  ${v.name}   (${v.source})`);
        for (const p of problems) console.log(p.split("\n").map(l => "        " + l).join("\n"));
    }
}
console.log(`\n${files.length - failed} of ${files.length} inverse vectors pass against ${jinagaJs}` +
    (port ? ` (port included, ${portFailed} failing)` : ` (no port at ${portPath} yet)`));
console.log(`today's invertSpecification misses changes on ${legacy.length} of ${files.length}:`);
for (const l of legacy) console.log(`  ${l}`);
if (failed > 0) process.exit(1);
