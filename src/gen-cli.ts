#!/usr/bin/env bun
// The command: `bend-schema gen <module.ts> <out.bend>`, run with bun (`bunx`)
// or node (`npx`). Bun does the work either way: the shebang is `env bun`,
// because the command executes the module and Node refuses to strip types from
// TypeScript in node_modules.
//
// The module must export `schemas` — an object whose keys name the Bend defs:
//
//   export const schemas = { config: Config, workers: Workers };
//
// An explicit map rather than every exported Schema: the names are the author's,
// and a schema that is a step inside another is not printed by accident.
//
// The module is **executed** to be read, so it must be schemas and nothing
// else: a file that does something on import would do it at build time. (A
// `describe()` in it fails here — `Cannot use describe outside of the test
// runner` — which is how this was found.)
//
// The import path in the generated file is computed here: this file lives in
// the package, so the core sits at <pkg>/core/core.bend, and the output file's
// own directory gives the relative path to it. The caller passes no path.
//
// Nothing here needs bun. `import.meta.dirname` is Node's name, and bun's;
// `import.meta.dir` is bun-only, which is why this file does not use it. A
// runtime new enough to strip types (Node 23.6+, or 22.6 with
// `--experimental-strip-types`) runs both this file and the schema module it
// imports, since a schema uses only erasable syntax.

import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, relative, resolve } from "node:path";
import { emit } from "./gen";
import type { Schema } from "./index";

const pkgCore = resolve(import.meta.dirname, "../core/core.bend");
const args = process.argv.slice(2);
if (args[0] === "gen") args.shift();
const [modArg, outArg] = args;
if (!modArg || !outArg) {
  console.error("usage: bunx bend-schema gen <module.ts> <out.bend>");
  process.exit(2);
}

const mod: Record<string, unknown> = await import(resolve(modArg));
const schemas = mod.schemas as Record<string, Schema<unknown>> | undefined;
if (!schemas || typeof schemas !== "object" || Array.isArray(schemas)) {
  console.error(
    `gen: ${modArg} must export \`schemas\` — an object of Schema values, one per Bend def:\n` +
      `     export const schemas = { config: Config };`,
  );
  process.exit(1);
}

const out = resolve(outArg);
mkdirSync(dirname(out), { recursive: true });
const rel = relative(dirname(out), pkgCore);
writeFileSync(
  out,
  emit(schemas, { libPath: rel.startsWith(".") ? rel : `./${rel}`, from: modArg }),
);
console.error(`gen: ${Object.keys(schemas).length} schema(s) from ${modArg} -> ${outArg}`);
