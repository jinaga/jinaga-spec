// Runs specifications through jinaga.js and jinaga-server and prints what each does.
//
//   npx tsx probe.mts <check> <path>
//
// <path> is a vector directory (every *.json with a `specification`), one vector
// JSON file, or a .jinaga file holding specification text.
//
// Checks:
//   wellformed    jinaga.js validateSpecification and wellFormedErrors (together,
//                 what assertWellFormed checks), and the parser for text
//   disconnected  jinaga.js detectDisconnectedSpecification
//   feeds         jinaga.js buildFeeds, printed as specification text
//   sql           jinaga-server sqlFromFeed on each feed (FEEDS=jinaga: jinaga.js's
//                 buildFeeds; default: the vector's expected.feeds, else buildFeeds)
//
// Exits 1 if any specification reports a problem: for `wellformed` on a
// directory of ill-formed vectors, that is the expected result.
//
// JINAGA_JS and JINAGA_SERVER default to sibling checkouts of jinaga-spec.
// Run it from ports/typescript (for tsx), passing this script's path.
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "../../../..");
const jsDir = resolve(process.env.JINAGA_JS ?? join(root, "../jinaga.js"));
const serverDir = resolve(process.env.JINAGA_SERVER ?? join(root, "../jinaga-server"));
const [check, target] = process.argv.slice(2);
if (!check || !target) {
  console.error("usage: probe.mts <wellformed|disconnected|feeds|sql> <dir|vector.json|spec.jinaga>");
  process.exit(2);
}

const js = await import(pathToFileURL(join(jsDir, "src/index.ts")).href);
const parse = (text: string) => {
  const p = new js.SpecificationParser(text);
  p.skipWhitespace();
  const spec = p.parseSpecification();
  p.expectEnd();
  return spec;
};

type Item = { name: string; spec: any; text?: string; feeds?: any[] };
function load(path: string): Item[] {
  if (statSync(path).isDirectory())
    return readdirSync(path).filter(f => f.endsWith(".json")).sort().flatMap(f => load(join(path, f)));
  const raw = readFileSync(path, "utf8");
  if (!path.endsWith(".json")) return [{ name: path, spec: parse(raw), text: raw }];
  const v = JSON.parse(raw);
  return v.specification ? [{ name: path, spec: v.specification, feeds: v.expected?.feeds }] : [];
}

const describe = (s: any) => js.describeSpecification(s, 0).trim();
let problems = 0;
const report = (name: string, msg: string) => { problems++; console.log(`${name}: ${msg}`); };

let sqlFromFeed: any, maps: any, serverJinaga: any;
if (check === "sql") {
  if (!existsSync(join(serverDir, "src/postgres/specification-sql.ts")))
    throw new Error(`no jinaga-server checkout at ${serverDir}`);
  ({ sqlFromFeed } = await import(pathToFileURL(join(serverDir, "src/postgres/specification-sql.ts")).href));
  maps = await import(pathToFileURL(join(serverDir, "src/postgres/maps.ts")).href);
  serverJinaga = await import(pathToFileURL(join(serverDir, "node_modules/jinaga/dist/index.js")).href);
}

const items = load(resolve(target));
for (const { name, spec, text, feeds } of items) {
  try {
    switch (check) {
      case "wellformed": {
        const errors = [...js.validateSpecification(spec), ...js.wellFormedErrors(spec)];
        if (errors.length) report(name, `rejected ${JSON.stringify(errors)}`);
        else console.log(`${name}: validateSpecification and wellFormedErrors accept it`);
        if (text) console.log(`${name}: parser accepts it`);
        break;
      }
      case "disconnected": {
        const r = js.detectDisconnectedSpecification(spec);
        if (r) report(name, `disconnected ${JSON.stringify(r)}`);
        break;
      }
      case "feeds": {
        const fs = js.buildFeeds(spec);
        console.log(`${name}: ${fs.length} feeds`);
        for (const f of fs) console.log(describe(f) + "\n");
        break;
      }
      case "sql": {
        const types = serverJinaga.getAllFactTypes(spec).reduce(
          (m: any, t: string, i: number) => maps.addFactType(m, t, i + 1), maps.emptyFactTypeMap());
        const roles = serverJinaga.getAllRoles(spec).reduce((m: any, role: any, i: number) => {
          const id = maps.getFactTypeId(types, role.successorType);
          return id ? maps.addRole(m, id, role.name, i + 100) : m;
        }, maps.emptyRoleMap());
        const fs = process.env.FEEDS === "jinaga" || !feeds
          ? js.buildFeeds(spec)
          : feeds.map((f: any) => f.specification);
        for (const f of fs) {
          const start = f.given.map((g: any) => js.dehydrateReference({ type: g.label.type, key: "value" }));
          try { sqlFromFeed(f, start, "public", "", 100, types, roles); }
          catch (e: any) { report(name, `sqlFromFeed throws "${e.message}" on\n${describe(f)}`); }
        }
        break;
      }
      default:
        throw new Error(`unknown check ${check}`);
    }
  } catch (e: any) {
    report(name, `throws "${e.message}"`);
  }
}
console.log(`${items.length} specification(s), ${problems} problem(s)`);
if (problems > 0) process.exitCode = 1;
