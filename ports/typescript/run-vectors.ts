// Runs the conformance vectors: the split against jinaga.js, and the
// well-formedness and connectivity checks against the reference
// implementation in this directory and against jinaga.js.
//
//   JINAGA_JS=/path/to/jinaga.js npm run vectors
//
// JINAGA_JS defaults to a sibling checkout. The runner imports the source
// directly, so it tests whatever that checkout has on disk.
import { deepStrictEqual } from "node:assert";
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { buildFeeds } from "./feed-builder.ts";
import { isConnectedDeep, isWellFormed } from "./well-formed.ts";

const here = dirname(fileURLToPath(import.meta.url));
const jinagaJs = resolve(process.env.JINAGA_JS ?? join(here, "../../../jinaga.js"));
const vectorsRoot = resolve(process.env.VECTORS ?? join(here, "../../vectors"));
const vectorsDir = join(vectorsRoot, "split");
const wellFormedDir = join(vectorsRoot, "well-formed");

const { splitBeforeFirstSuccessor } = await import(pathToFileURL(join(jinagaJs, "src/specification/specification.ts")).href);
const { describeSpecification } = await import(pathToFileURL(join(jinagaJs, "src/specification/description.ts")).href);
// Earlier commits of jinaga.js have no well-formedness check, so it is optional.
const { wellFormedErrors } = await import(pathToFileURL(join(jinagaJs, "src/specification/specification-validation.ts")).href);
const { AuthorizationRules } = await import(pathToFileURL(join(jinagaJs, "src/authorization/authorizationRules.ts")).href);
const { detectDisconnectedSpecification } = await import(pathToFileURL(join(jinagaJs, "src/specification/UnionFind.ts")).href);
const { buildFeeds: jinagaBuildFeeds } = await import(pathToFileURL(join(jinagaJs, "src/specification/feed-builder.ts")).href);
const { skeletonOfSpecification } = await import(pathToFileURL(join(jinagaJs, "src/specification/skeleton.ts")).href);

// A missing head or tail is `undefined` in TypeScript and `null` in a vector.
const normalize = (value: unknown) => JSON.parse(JSON.stringify(value ?? null));
const text = (s: any) => (s ? describeSpecification(s, 0) : null);

let failed = 0;
const files = readdirSync(vectorsDir).filter(f => f.endsWith(".json")).sort();
for (const file of files) {
    const vector = JSON.parse(readFileSync(join(vectorsDir, file), "utf8"));
    const problems: string[] = [];
    try {
        // Compare structure before describing: describeSpecification sorts a
        // composite projection's components in place.
        const { head, tail } = splitBeforeFirstSuccessor(structuredClone(vector.specification));
        const check = (label: string, fn: () => void) => {
            try { fn(); } catch (e: any) { problems.push(`${label}: ${e.message.split("\n").slice(0, 12).join("\n")}`); }
        };
        // `splitBeforeFirstSuccessor` is jinaga.js's export of this split
        // (jinaga/jinaga.js#325).
        check("head", () => deepStrictEqual(normalize(head), vector.expected.head));
        check("tail", () => deepStrictEqual(normalize(tail), vector.expected.tail));
        check("headText", () => deepStrictEqual(text(head), vector.expected.headText));
        check("tailText", () => deepStrictEqual(text(tail), vector.expected.tailText));
        check("text", () => deepStrictEqual(describeSpecification(structuredClone(vector.specification), 0), vector.text));
    } catch (e: any) {
        problems.push(`threw: ${e.message}`);
    }
    if (problems.length === 0) {
        console.log(`  ok    ${vector.name}`);
    } else {
        failed++;
        console.log(`  FAIL  ${vector.name}   (${vector.source})`);
        for (const p of problems) console.log(p.split("\n").map(l => "        " + l).join("\n"));
    }
}
console.log(`\n${files.length - failed} of ${files.length} split vectors pass against ${jinagaJs}`);

// The rule-level check: a rule with one given and a fact projection is what
// `AuthorizationRuleSpecification`'s constructor accepts. It throws exactly
// when the tail is given the rule's own given, which the store cannot supply
// while the fact is under authorization (`docs/contracts.md`, `Store.lean`).
let tailReadsGivenChecked = 0;
let tailReadsGivenFailed = 0;
for (const file of files) {
    const vector = JSON.parse(readFileSync(join(vectorsDir, file), "utf8"));
    if (vector.specification.given.length !== 1 || vector.specification.projection.type !== "fact") continue;
    tailReadsGivenChecked++;
    let threw = false;
    try {
        AuthorizationRules.loadFromDescription("authorization {\n" + vector.text + "}\n");
    } catch {
        threw = true;
    }
    if (threw !== vector.expected.tailReadsGiven) {
        tailReadsGivenFailed++;
        console.log(`  FAIL  ${vector.name}   (${vector.source}): tailReadsGiven=${vector.expected.tailReadsGiven}, constructor ${threw ? "threw" : "did not throw"}`);
    }
}
console.log(`\n${tailReadsGivenChecked - tailReadsGivenFailed} of ${tailReadsGivenChecked} tailReadsGiven vectors agree with the constructor's check`);

function refusesAsDisconnected(specification: any): boolean {
    try { buildFeeds(structuredClone(specification)); return false; }
    catch (e) { return String(e).includes("not connected"); }
}
let wellFormedFailed = 0;
const checkers: [string, (specification: any) => boolean][] = [["reference", isWellFormed]];
if (wellFormedErrors) checkers.push(["jinaga.js", specification => wellFormedErrors(structuredClone(specification)).length === 0]);
// The vectors jinaga.js's wellFormedErrors is expected to disagree on. None
// since jinaga/jinaga.js#431 made it look inside child specifications.
const jinagaWellFormedMisses = new Set<string>();
// jinaga.js refuses a disconnected specification by throwing from
// detectDisconnectedSpecification, which its parser and buildFeeds call
// (jinaga/jinaga.js#436, #437). It is held to `connected` on every well-formed
// vector, as the reference's buildFeeds is. A jinaga.js that accepts a vector
// the check refuses is one whose buildFeeds can emit a product feed, so that
// is never excused. The vectors jinaga.js is expected to refuse for a given no
// match uses, which jinaga/jinaga-spec#60 allows: none since jinaga/jinaga.js#442
// and #443 stopped counting such a given.
const jinagaRefusesUnusedGiven = new Set<string>();
const jinagaConnects = (specification: any): boolean => {
    try { detectDisconnectedSpecification(structuredClone(specification)); return true; }
    catch { return false; }
};
// jinaga.js registers a feed by taking its skeleton (`computeFeedHash`), which
// checks that the two sides of each path condition have the same type. The
// oracle reads no types, so this holds the vectors themselves to being well
// typed: a well-formed, connected vector whose feeds jinaga.js cannot register
// fails here rather than in a downstream port (jinaga/jinaga-spec#68).
const jinagaRegistersFeeds = (specification: any): boolean => {
    try { jinagaBuildFeeds(structuredClone(specification)).forEach(skeletonOfSpecification); return true; }
    catch { return false; }
};
const wellFormedFiles = readdirSync(wellFormedDir).filter(f => f.endsWith(".json")).sort();
for (const file of wellFormedFiles) {
    const vector = JSON.parse(readFileSync(join(wellFormedDir, file), "utf8"));
    const wrong = checkers.filter(([, check]) => check(vector.specification) !== vector.expected.wellFormed).map(([name]) => name);
    // The connectivity check `buildFeeds` needs (`isConnectedDeep`).
    if (isConnectedDeep(vector.specification) !== vector.expected.connected) wrong.push("reference isConnectedDeep");
    const connects = vector.expected.wellFormed ? jinagaConnects(vector.specification) : vector.expected.connected;
    if (connects !== vector.expected.connected) {
        if (jinagaRefusesUnusedGiven.has(vector.name) && !connects) {
            console.log(`  known ${vector.name}: jinaga.js's detectDisconnectedSpecification refuses an unused given (jinaga/jinaga-spec#60)`);
        } else {
            wrong.push("jinaga.js detectDisconnectedSpecification");
        }
    } else if (jinagaRefusesUnusedGiven.has(vector.name) && vector.expected.wellFormed) {
        console.log(`  note  ${vector.name}: jinaga.js now accepts it; remove it from jinagaRefusesUnusedGiven`);
    }
    if (vector.expected.wellFormed && vector.expected.connected && !jinagaRefusesUnusedGiven.has(vector.name) && !jinagaRegistersFeeds(vector.specification)) wrong.push("jinaga.js buildFeeds");
    // The port's buildFeeds refuses a well-formed specification exactly when
    // it is not connected (jinaga/jinaga-spec#55).
    if (vector.expected.wellFormed && refusesAsDisconnected(vector.specification) === vector.expected.connected) wrong.push("reference buildFeeds");
    const failures = wrong.filter(name => !(name === "jinaga.js" && jinagaWellFormedMisses.has(vector.name)));
    if (jinagaWellFormedMisses.has(vector.name) && wellFormedErrors && !wrong.includes("jinaga.js")) {
        console.log(`  note  ${vector.name}: jinaga.js now agrees; remove it from jinagaWellFormedMisses`);
    }
    if (wrong.length > failures.length) {
        console.log(`  known ${vector.name}: jinaga.js's wellFormedErrors accepts it`);
    } else if (failures.length === 0) {
        console.log(`  ok    ${vector.name}`);
    } else {
        wellFormedFailed++;
        console.log(`  FAIL  ${vector.name}   (${vector.source}): ${failures.join(", ")} disagree${failures.length === 1 ? "s" : ""} with the oracle`);
    }
}
console.log(`\n${wellFormedFiles.length - wellFormedFailed} of ${wellFormedFiles.length} well-formedness vectors pass (${checkers.map(([name]) => name).join(", ")})`);
process.exit(failed === 0 && tailReadsGivenFailed === 0 && wellFormedFailed === 0 ? 0 : 1);
