// Runs the content vectors (vectors/content/) against a content store.
//
//   npm run --silent content
//   PORT=./my-content-store.ts npm run --silent content
//
// The store under test is content-store.ts, or the module PORT names, which
// must export a `ContentStore` class of the same shape. Each vector's policy is
// data (vectors/README.md): the harness below turns it into a `Policy`. The
// one input it does not compute is `yields`, which needs a specification
// engine: it takes it from each read's `yields`, the oracle's answer. A
// replicator's own test should compute it with its engine, and can check that
// engine against the same field.
//
// Every write's and read's response must equal `expected`, and the objects
// stored at the end must equal `expected.objects`.
import { deepStrictEqual } from "node:assert";
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import type { Fact, FactId, Policy, Proof } from "./content-store.ts";

const here = dirname(fileURLToPath(import.meta.url));
const vectorsDir = join(resolve(process.env.VECTORS ?? join(here, "../../vectors")), "content");
const { ContentStore } = await import(pathToFileURL(resolve(process.env.PORT ?? join(here, "content-store.ts"))).href);

/** The vector's policy. `yields` answers from `current`, the read being run. */
function policyOf(v: any, current: { yields: boolean }): Policy {
    const content = new Map<FactId, { hash: string; maxLength: number }>(
        v.policy.content.map((c: any) => [c.fact, { hash: c.hash, maxLength: c.maxLength }]));
    const sameIds = (a: FactId[], b: FactId[]) => a.length === b.length && a.every((x, i) => x === b[i]);
    return {
        hash: bytes => "#" + bytes,
        contentHash: fact => content.get(fact.id)?.hash,
        fits: (fact, bytes) => [...bytes].length <= (content.get(fact.id)?.maxLength ?? -1),
        mayCreate: (user, _, fact) => v.policy.writers.some((w: any) => w.user === user && w.fact === fact.id),
        distributes: (user, _, givens) => v.policy.readers.some((r: any) => r.user === user && sameIds(r.givens, givens)),
        yields: () => current.yields
    };
}

let passed = 0, failures = 0;
for (const file of readdirSync(vectorsDir).filter(f => f.endsWith(".json")).sort()) {
    const v = JSON.parse(readFileSync(join(vectorsDir, file), "utf8"));
    const current = { yields: false };
    // The vectors' specifications are well formed; a bad request comes only from the givens.
    const store = new ContentStore(policyOf(v, current), () => true);
    const problems: string[] = [];
    v.steps.forEach((step: any, i: number) => {
        let actual;
        if (step.save) { store.save(step.save as Fact); return; }
        if (step.write) actual = store.write(step.write.user, step.write.key, step.write.bytes);
        else {
            current.yields = step.yields;
            const proof: Proof = { specification: v.specification, givens: step.read.givens };
            actual = store.read(step.read.user, step.read.key, proof);
        }
        try { deepStrictEqual(actual, step.expected); }
        catch { problems.push(`step ${i}: ${JSON.stringify(actual)}, expected ${JSON.stringify(step.expected)}`); }
    });
    const objects = [...store.objects].map(([key, bytes]) => ({ key, bytes }));
    try { deepStrictEqual(objects, v.expected.objects); }
    catch { problems.push(`objects ${JSON.stringify(objects)}, expected ${JSON.stringify(v.expected.objects)}`); }
    if (problems.length === 0) passed++;
    else { failures++; console.log(`FAIL ${v.name}: ${problems.join("; ")}`); }
}
console.log(`${passed} of ${passed + failures} content vectors pass`);
process.exit(failures === 0 ? 0 : 1);
