// Audits jinaga.js against the well-formedness vectors: which specifications
// that violate a condition does its parser reject, and does
// `validateSpecification` catch what the parser lets through?
//
//   JINAGA_JS=/path/to/jinaga.js npm run audit
//
// It reads the text form of each vector, so it exercises the parser exactly as
// a rule loaded with `AuthorizationRules.loadFromDescription` would.
import { readdirSync, readFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const jinagaJs = resolve(process.env.JINAGA_JS ?? join(here, "../../../jinaga.js"));
const dir = resolve(process.env.VECTORS ?? join(here, "../../vectors"), "well-formed");
const src = (file: string) => pathToFileURL(join(jinagaJs, "src/specification", file)).href;
const { SpecificationParser } = await import(src("specification-parser.ts"));
const { validateSpecification } = await import(src("specification-validation.ts"));

const rows = readdirSync(dir).filter(f => f.endsWith(".json")).sort().map(file => {
    const vector = JSON.parse(readFileSync(join(dir, file), "utf8"));
    const e = vector.expected;
    const violates = [!e.scoped && "scoped", !e.unshadowed && "unshadowed", !e.projected && "projected"].filter(Boolean).join(", ");
    let parser = "accepts", validator = "-";
    try {
        const p = new SpecificationParser(vector.text);
        p.skipWhitespace();
        const spec = p.parseSpecification();
        const errors = validateSpecification(spec);
        validator = errors.length === 0 ? "accepts" : "rejects";
    } catch (error: any) {
        parser = "rejects";
    }
    return { name: vector.name, violates: violates || "(well-formed)", parser, validator };
});

const width = Math.max(...rows.map(r => r.name.length));
console.log(`${"vector".padEnd(width)}  violates                     parser    validateSpecification`);
for (const r of rows) {
    console.log(`${r.name.padEnd(width)}  ${r.violates.padEnd(27)}  ${r.parser.padEnd(8)}  ${r.validator}`);
}
const slipped = rows.filter(r => r.violates !== "(well-formed)" && r.parser === "accepts" && r.validator === "accepts");
const wrong = rows.filter(r => r.violates === "(well-formed)" && r.parser === "rejects");
console.log(`\n${slipped.length} ill-formed vector(s) pass both the parser and validateSpecification.`);
if (wrong.length) console.log(`${wrong.length} well-formed vector(s) are rejected by the parser: ${wrong.map(r => r.name).join(", ")}`);
