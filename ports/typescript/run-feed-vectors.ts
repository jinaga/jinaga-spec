// Runs the feed vectors (vectors/feeds/) against jinaga.js.
//
//   JINAGA_JS=/path/to/jinaga.js npm run --silent feeds
//   JINAGA_JS=/path/to/jinaga.js PORT=./feed-builder.ts npm run --silent feeds
//
// For each vector:
//
// 1. The vector's feeds, read by jinaga.js's own MemoryStore (`feed`, as the
//    replicator serves `GET /feeds/{hash}`), deliver the vector's facts. This
//    shows that jinaga.js reads feeds as the reference semantics does. It must
//    pass.
// 2. The implementation under test, `buildFeeds` from jinaga.js's
//    src/specification/feed-builder.ts, or from PORT:
//    a. its feeds equal the vector's, structurally and in order, and
//    b. a replica holding what its feeds deliver, with their predecessors,
//       reads the vector's results, its child specifications' included at
//       every depth (`feeds_cover`), and
//    c. they deliver no fact the vector's feeds do not: a new client is not
//       sent what the specification defers (`feeds_defer`).
//    With PORT all must pass. Against jinaga.js they are reported: 2b fails on
//    the vectors named in `jinagaMisses`, until jinaga.js builds its feeds as
//    feed-builder.ts does.
import { deepStrictEqual } from "node:assert";
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const jinagaJs = resolve(process.env.JINAGA_JS ?? join(here, "../../../jinaga.js"));
const vectorsDir = join(resolve(process.env.VECTORS ?? join(here, "../../vectors")), "feeds");
const load = (path: string) => import(pathToFileURL(join(jinagaJs, path)).href);

const { MemoryStore } = await load("src/memory/memory-store.ts");
const { Trace } = await load("src/util/trace.ts");
Trace.off();
const strict = process.env.PORT !== undefined;
const implementation = strict
    ? await import(pathToFileURL(resolve(process.env.PORT!)).href)
    : await load("src/specification/feed-builder.ts");

/** The vectors jinaga.js's `buildFeeds` is expected to miss a result on. */
const jinagaMisses = new Set(["not-exists-cancelled-twice", "not-exists-cancelled-by-second", "exists-inside-not-exists", "random-2"]);

const normalize = (value: unknown) => JSON.parse(JSON.stringify(value ?? null));
const key = (row: unknown) => JSON.stringify(row);
const sameSet = (a: unknown[], b: unknown[]) => {
    const as = new Set(a.map(key)), bs = new Set(b.map(key));
    return as.size === bs.size && [...as].every(x => bs.has(x));
};

const idOf = (reference: any): number => Number(reference.hash.slice(1));

/** A store holding the given facts of the vector's graph. Fact ids become hashes. */
async function storeOf(v: any, ids: Set<number>) {
    const typeOf = new Map<number, string>(v.graph.map((f: any) => [f.id, f.type]));
    const ref = (id: number) => ({ type: typeOf.get(id), hash: `h${id}` });
    const store = new MemoryStore();
    await store.save(v.graph.filter((f: any) => ids.has(f.id)).map((f: any) => {
        const predecessors: any = {};
        for (const p of f.predecessors) (predecessors[p.role] ??= []).push(ref(p.id));
        return { fact: { type: f.type, hash: `h${f.id}`, predecessors, fields: {} }, signatures: [] };
    }));
    return { store, ref };
}

/** The facts `ids` name, and all their predecessors. */
function closure(v: any, ids: number[]): Set<number> {
    const byId = new Map<number, any>(v.graph.map((f: any) => [f.id, f]));
    const out = new Set<number>();
    const visit = (id: number) => {
        if (out.has(id)) return;
        out.add(id);
        for (const p of byId.get(id)?.predecessors ?? []) visit(p.id);
    };
    ids.forEach(visit);
    return out;
}

/** Every fact the feeds deliver on the vector's graph, read as the replicator reads them. */
async function deliver(v: any, feeds: any[]): Promise<number[]> {
    const { store, ref } = await storeOf(v, new Set(v.graph.map((f: any) => f.id)));
    const ids: number[] = [];
    for (const feed of feeds) {
        const start = feed.given.map((g: any) => ref(v.givens[g.label.name]));
        const { tuples } = await store.feed(structuredClone(feed), start, "");
        for (const t of tuples) ids.push(...t.facts.map(idOf));
    }
    return [...new Set(ids)].sort((a, b) => a - b);
}

/**
 * A result with its child specifications' results, as a key that does not
 * depend on their order or on repeats, at any depth: results are compared as
 * sets (`Projection.Reads`).
 */
function nestedKey(r: { row: unknown[]; children: any[][] }): string {
    return JSON.stringify([r.row, r.children.map(rs => [...new Set(rs.map(nestedKey))].sort())]);
}

/** A result jinaga.js's runner projects, in the vector's form: its row, and each child specification's results. */
function nested(projection: any, r: any): { row: unknown[]; children: any[][] } {
    const components: any[] = projection.type === "composite" ? projection.components : [projection];
    return {
        row: components.filter(c => c.type !== "specification").map(c => r.tuple[c.label] ? idOf(r.tuple[c.label]) : null),
        children: components.filter(c => c.type === "specification").map(c => r.result[c.name].map((x: any) => nested(c.projection, x)))
    };
}

/** What a replica holding these facts, their predecessors and the givens reads. */
async function readReplica(v: any, ids: number[]): Promise<{ rows: unknown[]; nested: string[] }> {
    const givenIds = Object.values(v.givens) as number[];
    const { store, ref } = await storeOf(v, closure(v, [...ids, ...givenIds]));
    const start = v.specification.given.map((g: any) => ref(v.givens[g.label.name]));
    const results = await store.read(start, structuredClone(v.specification));
    return {
        rows: results.map((r: any) => v.rowLabels.map((l: string) => r.tuple[l] ? idOf(r.tuple[l]) : null)),
        nested: results.map((r: any) => nestedKey(nested(v.specification.projection, r)))
    };
}

/** The replica reads the vector's results, and its child specifications' results at every depth. */
const readsExpected = (v: any, read: { rows: unknown[]; nested: string[] }) =>
    sameSet(read.rows, v.expected.results) &&
    (v.expected.nestedResults === undefined || sameSet(read.nested, v.expected.nestedResults.map(nestedKey)));

let failures = 0;
let structural = 0, covered = 0, bounded = 0, total = 0;
const report: string[] = [];
for (const file of readdirSync(vectorsDir).filter(f => f.endsWith(".json")).sort()) {
    const v = JSON.parse(readFileSync(join(vectorsDir, file), "utf8"));
    total++;
    const expectedFeeds = v.expected.feeds.map((f: any) => f.specification);
    const givenIds = new Set(Object.values(v.givens) as number[]);

    // 1. jinaga.js reads the vector's feeds as the reference semantics does.
    const delivered = (await deliver(v, expectedFeeds)).filter(id => !givenIds.has(id) || v.expected.delivered.includes(id));
    if (!sameSet(delivered, v.expected.delivered)) {
        failures++;
        console.log(`FAIL ${v.name}: jinaga.js's MemoryStore delivers ${JSON.stringify(delivered)} from the vector's feeds, expected ${JSON.stringify(v.expected.delivered)}`);
    }

    // 2. The implementation under test.
    const feeds = normalize(implementation.buildFeeds(structuredClone(v.specification)));
    let same = true;
    try { deepStrictEqual(feeds, normalize(expectedFeeds)); } catch { same = false; }
    if (same) structural++;
    // Deferral: a new client is sent nothing the vector's feeds do not send.
    const sent = await deliver(v, feeds).catch(() => [] as number[]);
    const extra = sent.filter(id => !givenIds.has(id) && !v.expected.delivered.includes(id));
    if (extra.length === 0) bounded++;
    else if (strict) { failures++; console.log(`FAIL ${v.name}: sends ${JSON.stringify(extra)}, which the vector's feeds withhold`); }
    // A feed the store cannot read covers nothing.
    const results = await deliver(v, feeds).then(ids => readReplica(v, ids), (e: Error) => `an error: ${e.message}`);
    const covers = typeof results !== "string" && readsExpected(v, results);
    if (covers) covered++;
    if (strict) {
        if (!same) { failures++; console.log(`FAIL ${v.name}: feeds differ from the vector's`); }
        if (!covers) { failures++; console.log(`FAIL ${v.name}: a replica reads ${JSON.stringify(results)}, expected ${JSON.stringify(v.expected.nestedResults ?? v.expected.results)}`); }
    } else if (!covers) {
        if (!jinagaMisses.has(v.name)) failures++;
        report.push(`${jinagaMisses.has(v.name) ? "expected" : "FAIL"} ${v.name}: a replica of jinaga.js's feeds reads ${JSON.stringify(results)}, expected ${JSON.stringify(v.expected.nestedResults ?? v.expected.results)}`);
    } else if (jinagaMisses.has(v.name)) {
        report.push(`${v.name}: jinaga.js's feeds now cover it; remove it from jinagaMisses`);
    }
}
for (const line of report) console.log(line);
console.log(`${total} feed vectors: ${structural} with the vector's feeds, ${covered} covered, ${bounded} sending no more than the vector's (${strict ? process.env.PORT : "jinaga.js"})`);
process.exit(failures === 0 ? 0 : 1);
