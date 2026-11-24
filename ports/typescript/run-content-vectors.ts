// Runs the content vectors (vectors/content/) against a content store.
//
//   npm run --silent content
//   PORT=./my-content-store.ts npm run --silent content
//
// The store under test is content-store.ts, or the module PORT names, which
// must export a `ContentStore` class of the same shape; and the cached store,
// content-cache.ts or the module CACHE_PORT names, which must export a
// `CachedContentStore`. A cache never changes an answer (`cached_read`), so
// both must give every vector's expected responses. Each vector's policy is
// data (vectors/README.md): the harness below turns it into a `Policy`, whose
// distribution rule is the vector's `rule`, run with the proof's givens. The
// store checks each proof itself, with `isWellFormed` and `confirms`
// (./content-proof.ts), which the harness also checks against each read's
// `yields`, the oracle's answer, for every bound proof.
//
// Every write's and read's response must equal `expected`, and the objects
// stored at the end must equal `expected.objects`.
import { deepStrictEqual } from "node:assert";
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import type { Fact, FactId, Policy, Proof } from "./content-store.ts";
import { bound, isClosed, isFresh } from "./content-store.ts";
import { confirms } from "./content-proof.ts";

const here = dirname(fileURLToPath(import.meta.url));
const vectorsDir = join(resolve(process.env.VECTORS ?? join(here, "../../vectors")), "content");
const { ContentStore } = await import(pathToFileURL(resolve(process.env.PORT ?? join(here, "content-store.ts"))).href);
const { CachedContentStore } = await import(pathToFileURL(resolve(process.env.CACHE_PORT ?? join(here, "content-cache.ts"))).href);

/** The vector's policy. */
function policyOf(v: any): Policy {
    const content = new Map<FactId, { hash: string; maxLength: number }>(
        v.policy.content.map((c: any) => [c.fact, { hash: c.hash, maxLength: c.maxLength }]));
    return {
        hash: bytes => "#" + bytes,
        contentHash: fact => content.get(fact.id)?.hash,
        fits: (fact, bytes) => [...bytes].length <= (content.get(fact.id)?.maxLength ?? -1),
        mayCreate: (user, _, fact) => v.policy.writers.some((w: any) => w.user === user && w.fact === fact.id),
        distribution: (_, givens) => [[{ specification: v.policy.rule, givens }]]
    };
}

const vectors = readdirSync(vectorsDir).filter(f => f.endsWith(".json")).sort()
    .map(file => JSON.parse(readFileSync(join(vectorsDir, file), "utf8")));

function run(Store: any, label: string): number {
    let passed = 0, failures = 0;
    for (const v of vectors) {
        const store = new Store(policyOf(v));
        const problems: string[] = [];
        v.steps.forEach((step: any, i: number) => {
            let actual;
            if (step.save) {
                if (isFresh(store.store, step.save) !== step.fresh) problems.push(`step ${i}: isFresh is ${!step.fresh}`);
                if (isClosed(store.store, step.save) !== step.closed) problems.push(`step ${i}: isClosed is ${!step.closed}`);
                store.save(step.save as Fact[]);
                return;
            }
            if (step.write) actual = store.write(step.write.user, step.write.key, step.write.bytes);
            else {
                const proof: Proof = { specification: v.specification, givens: step.read.givens };
                if (bound(proof) && confirms(v.specification, proof.givens, store.store, step.read.key) !== step.yields)
                    problems.push(`step ${i}: confirms is ${!step.yields}, yields ${step.yields}`);
                actual = store.read(step.read.user, step.read.key, proof);
            }
            try { deepStrictEqual(actual, step.expected); }
            catch { problems.push(`step ${i}: ${JSON.stringify(actual)}, expected ${JSON.stringify(step.expected)}`); }
        });
        const objects = [...store.objects].map(([key, bytes]) => ({ key, bytes }));
        try { deepStrictEqual(objects, v.expected.objects); }
        catch { problems.push(`objects ${JSON.stringify(objects)}, expected ${JSON.stringify(v.expected.objects)}`); }
        if (problems.length === 0) passed++;
        else { failures++; console.log(`FAIL ${label} ${v.name}: ${problems.join("; ")}`); }
    }
    console.log(`${passed} of ${passed + failures} content vectors pass, ${label}`);
    return failures;
}

/*
 * Port-only cases: conditions on a given. Lean's `Specification` has no
 * conditions on its givens, so the oracle cannot generate a vector with them;
 * jinaga.js's specification type has them, and evaluates them. The store must
 * not ignore them: a reader's proof with them is refused with 400 (RR-1,
 * `bound`), and a rule proof with them is not bound, so authorizes nothing.
 * Each case runs `content-fact-as-given` to its end, where its own proof is
 * served, with the plan then archived, which the conditions exclude.
 */
const archived = { type: "existential", exists: false, matches: [{ unknown: { name: "a", type: "Archived" },
    conditions: [{ type: "path", rolesLeft: [{ name: "doc", predecessorType: "Document" }], labelRight: "d", rolesRight: [] }] }] };
const withArchived = (s: any) => ({ ...s, given: s.given.map((g: any) => ({ ...g, conditions: [archived] })) });

function runGivenConditions(Store: any, label: string): number {
    const v = vectors.find(v => v.name === "content-fact-as-given");
    const last = v.steps[v.steps.length - 1].read;
    const cases: { name: string; rule: any; specification: any; expected: any }[] = [
        { name: "reader's proof has conditions on a given", rule: v.policy.rule,
          specification: withArchived(v.specification), expected: { status: 400, code: "bad_request" } },
        { name: "rule proof has conditions on a given", rule: withArchived(v.policy.rule),
          specification: v.specification, expected: { status: 403, code: "forbidden" } }
    ];
    let failures = 0;
    for (const c of cases) {
        const store = new Store(policyOf({ ...v, policy: { ...v.policy, rule: c.rule } }));
        for (const step of v.steps) {
            if (step.save) store.save(step.save);
            else if (step.write) store.write(step.write.user, step.write.key, step.write.bytes);
        }
        store.save([{ id: 50, type: "Archived", predecessors: [{ role: "doc", id: last.key }] }]);
        const actual = store.read(last.user, last.key, { specification: c.specification, givens: last.givens });
        try { deepStrictEqual(actual, c.expected); }
        catch { failures++; console.log(`FAIL ${label} given conditions, ${c.name}: ${JSON.stringify(actual)}, expected ${JSON.stringify(c.expected)}`); }
    }
    console.log(`${cases.length - failures} of ${cases.length} port-only given-condition cases pass, ${label}`);
    return failures;
}

const failures = run(ContentStore, "uncached") + run(CachedContentStore, "cached") +
    runGivenConditions(ContentStore, "uncached") + runGivenConditions(CachedContentStore, "cached");
process.exit(failures === 0 ? 0 : 1);
