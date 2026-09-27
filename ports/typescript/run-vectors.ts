// Runs the split conformance vectors against jinaga.js.
//
//   JINAGA_JS=/path/to/jinaga.js npm run vectors
//
// JINAGA_JS defaults to a sibling checkout. The runner imports the source
// directly, so it tests whatever that checkout has on disk.
import { deepStrictEqual } from "node:assert";
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const jinagaJs = resolve(process.env.JINAGA_JS ?? join(here, "../../../jinaga.js"));
const vectorsDir = resolve(process.env.VECTORS ?? join(here, "../../vectors/split"));

const { splitBeforeFirstSuccessor } = await import(pathToFileURL(join(jinagaJs, "src/specification/specification.ts")).href);
const { describeSpecification } = await import(pathToFileURL(join(jinagaJs, "src/specification/description.ts")).href);

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
console.log(`\n${files.length - failed} of ${files.length} vectors pass against ${jinagaJs}`);
process.exit(failed === 0 ? 0 : 1);
