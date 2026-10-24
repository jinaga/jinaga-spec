// Compares the reference TypeScript implementation (inverse-candidates.ts)
// with the Lean definition of `candidates`, on random specifications.
//
//   lake exe check-inverse dump-candidates candidates-dump.json [seed]
//   npx tsx reference-diff.ts candidates-dump.json
import { deepStrictEqual } from "node:assert";
import { readFileSync } from "node:fs";
import { buildInverses, reorderInverse } from "./inverse-candidates.ts";

const entries = JSON.parse(readFileSync(process.argv[2], "utf8"));
const normalize = (value: unknown) => JSON.parse(JSON.stringify(value));
let agree = 0;
let first: string | undefined;
for (const { specification, inverses, reordered } of entries) {
    try {
        const built = buildInverses(structuredClone(specification));
        deepStrictEqual(normalize(built), inverses);
        deepStrictEqual(normalize(built.map(reorderInverse)), reordered);
        agree++;
    } catch (e: any) {
        first ??= `${JSON.stringify(specification)}\n${e.message.split("\n").slice(0, 30).join("\n")}`;
    }
}
console.log(`${agree} of ${entries.length} specifications: the reference implementation's inverses equal the Lean definition's`);
if (first) { console.log(`FAIL. First:\n${first}`); process.exit(1); }
