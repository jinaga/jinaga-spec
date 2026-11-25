// Runs the content-hash vectors: base64(SHA-512(bytes)) of each object, one
// shot and in chunks of several sizes, with Node's crypto.
//
//   npm run content-hash
//   JINAGA_JS=/path/to/jinaga.js npm run content-hash
//
// With a jinaga.js checkout, also hashes each object with the primitives its
// fact hash uses (src/util/encoding.ts: @stablelib/sha512's hash, then
// @stablelib/base64's encode), and checks that computeStringHash of the
// lossily decoded text differs on not-utf8: decoding is not the content hash.
import { createHash } from "node:crypto";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const jinagaJs = resolve(process.env.JINAGA_JS ?? join(here, "../../../jinaga.js"));
const vectorsDir = resolve(process.env.VECTORS ?? join(here, "../../vectors"), "content-hash");
const chunkSizes = [1, 3, 64, 1000, 65536];

const bytesOf = (v: any): Uint8Array =>
    v.ramp !== undefined
        ? Uint8Array.from({ length: v.ramp }, (_, i) => i % 256)
        : Uint8Array.from(Buffer.from(v.bytes, "hex"));

function hashInChunks(bytes: Uint8Array, size: number): string {
    const h = createHash("sha512");
    for (let i = 0; i < bytes.length; i += size) h.update(bytes.subarray(i, i + size));
    return h.digest("base64");
}

const encoding = join(jinagaJs, "src/util/encoding.ts");
let jinaga: { hash: (b: Uint8Array) => string, computeStringHash: (s: string) => string } | undefined;
if (existsSync(encoding)) {
    const require = createRequire(encoding);
    const { hash } = require("@stablelib/sha512");
    const { encode } = require("@stablelib/base64");
    const { computeStringHash } = await import(pathToFileURL(encoding).href);
    jinaga = { hash: b => encode(hash(b)), computeStringHash };
}

let failed = 0;
const files = readdirSync(vectorsDir).filter(f => f.endsWith(".json")).sort();
for (const file of files) {
    const v = JSON.parse(readFileSync(join(vectorsDir, file), "utf8"));
    const bytes = bytesOf(v);
    const got: [string, string][] = [["one shot", createHash("sha512").update(bytes).digest("base64")]];
    for (const size of chunkSizes) got.push([`chunks of ${size}`, hashInChunks(bytes, size)]);
    if (jinaga) got.push(["jinaga.js primitives", jinaga.hash(bytes)]);
    for (const [how, h] of got) {
        if (h !== v.hash) { failed++; console.log(`FAIL ${v.name}: ${how} gives ${h}`); }
    }
    if (jinaga && v.name === "not-utf8" && jinaga.computeStringHash(new TextDecoder().decode(bytes)) === v.hash) {
        failed++;
        console.log(`FAIL ${v.name}: computeStringHash of the decoded text gives the content hash`);
    }
}
if (failed) { console.log(`${failed} failures`); process.exit(1); }
console.log(`${files.length} content-hash vectors pass, one shot and in chunks of ${chunkSizes.join(", ")}` +
    (jinaga ? `, and agree with jinaga.js at ${jinagaJs}` : ` (jinaga.js check skipped: no checkout at ${jinagaJs})`));
