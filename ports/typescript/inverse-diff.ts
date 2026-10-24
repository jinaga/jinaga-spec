// Compares jinaga.js's invertSpecification with the Lean port (JinagaSpec/Inverse.lean).
//
//   lake exe check-inverse dump inverse-dump.json [seed]
//   JINAGA_JS=/path/to/jinaga.js npx tsx inverse-diff.ts inverse-dump.json
//
// Each specification's inverses are printed in the same text form on both sides
// and compared as sets, since jinaga.js deduplicates and the port does not.
import { readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const jinagaJs = resolve(process.env.JINAGA_JS ?? join(here, "../../../jinaga.js"));
const { invertSpecification } = await import(pathToFileURL(join(jinagaJs, "src/specification/inverse.ts")).href);
const { Trace } = await import(pathToFileURL(join(jinagaJs, "src/util/trace.ts")).href);
Trace.off();

const indent = (depth: number) => "    ".repeat(depth);
const roles = (rs: any[]) => rs.map(r => `->${r.name}: ${r.predecessorType}`).join("");

function describeMatch(depth: number, m: any): string {
    return `${indent(depth)}${m.unknown.name}: ${m.unknown.type} [\n` +
        m.conditions.map((c: any) => describeCondition(m.unknown.name, depth + 1, c)).join("") +
        `${indent(depth)}]\n`;
}

function describeCondition(unknown: string, depth: number, c: any): string {
    if (c.type === "path") {
        return `${indent(depth)}${unknown}${roles(c.rolesLeft)} = ${c.labelRight}${roles(c.rolesRight)}\n`;
    }
    return `${indent(depth)}${c.exists ? "" : "!"}E {\n` +
        c.matches.map((m: any) => describeMatch(depth + 1, m)).join("") +
        `${indent(depth)}}\n`;
}

function describeInverse(inverse: any): string {
    const given = inverse.inverseSpecification.given[0];
    return `${inverse.operation}\n` +
        describeMatch(0, { unknown: given.label, conditions: given.conditions }) +
        inverse.inverseSpecification.matches.map((m: any) => describeMatch(1, m)).join("");
}

const entries = JSON.parse(readFileSync(process.argv[2], "utf8"));
let agree = 0;
const disagreements: string[] = [];
for (const { specification, inverses } of entries) {
    let ts: string[] | { error: string };
    try {
        ts = invertSpecification(specification).map(describeInverse);
    } catch (e: any) {
        ts = { error: e.message };
    }
    const lean = inverses;
    const same = Array.isArray(lean) && Array.isArray(ts)
        ? new Set(lean).size === new Set(ts).size && lean.every((d: string) => ts.includes(d))
        : !Array.isArray(lean) && !Array.isArray(ts) &&
          lean.error.split(" with types")[0].split(" detected")[0] === ts.error.split(" with types")[0].split(" detected")[0];
    if (same) {
        agree++;
    } else {
        disagreements.push(JSON.stringify({ specification, lean, ts }, null, 2));
    }
}
console.log(`${agree} of ${entries.length} specifications: the port's inverses equal jinaga.js's`);
if (disagreements.length > 0) {
    console.log(`FAIL: ${disagreements.length} disagree. First:\n${disagreements[0]}`);
    process.exit(1);
}
