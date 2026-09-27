// Runs the conformance vectors: the split against jinaga.js, and the
// well-formedness check against the reference implementation in this directory.
//
//   JINAGA_JS=/path/to/jinaga.js npm run vectors
//
// JINAGA_JS defaults to a sibling checkout. The runner imports the source
// directly, so it tests whatever that checkout has on disk.
import { deepStrictEqual } from "node:assert";
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { isWellFormed } from "./well-formed.ts";

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

let wellFormedFailed = 0;
const checkers: [string, (specification: any) => boolean][] = [["reference", isWellFormed]];
if (wellFormedErrors) checkers.push(["jinaga.js", specification => wellFormedErrors(structuredClone(specification)).length === 0]);
const wellFormedFiles = readdirSync(wellFormedDir).filter(f => f.endsWith(".json")).sort();
for (const file of wellFormedFiles) {
    const vector = JSON.parse(readFileSync(join(wellFormedDir, file), "utf8"));
    const failures = checkers.filter(([, check]) => check(vector.specification) !== vector.expected.wellFormed).map(([name]) => name);
    if (failures.length === 0) {
        console.log(`  ok    ${vector.name}`);
    } else {
        wellFormedFailed++;
        console.log(`  FAIL  ${vector.name}   (${vector.source}): ${failures.join(", ")} disagree${failures.length === 1 ? "s" : ""} with the oracle`);
    }
}
console.log(`\n${wellFormedFiles.length - wellFormedFailed} of ${wellFormedFiles.length} well-formedness vectors pass (${checkers.map(([name]) => name).join(", ")})`);
process.exit(failed === 0 && tailReadsGivenFailed === 0 && wellFormedFailed === 0 ? 0 : 1);
