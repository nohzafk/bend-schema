// A deploy config, read from a JSON file: `bun load.ts <file.json>`.
//
// The schema is the whole specification of the file. Nothing here validates by
// hand: `parse` runs the proved core's check (core/core.bend), so the first
// thing wrong comes back with the path to it, and the returned value is typed
// from the schema itself (`Infer`).

import { readFileSync } from "node:fs";
import { s, type Infer } from "../../src/index.ts";

// A strict object: every key must be one this schema names. A named key must
// be present -- `.nullable()` means present as null, `.optional()` means the
// key may be left out.
export const Config = s.object({
    name: s.str().len(1, 64),
    notify: s.str().nullable(),
    targets: s.list(
      s.tagged("type", {
        s3: s.object({
            bucket: s.str().len(1, 63),
            region: s.enum(["eu-west-1", "us-east-1", "us-west-2"]),
            prefix: s.str().nullable(),
          }).strict(),
        ssh: s.object({
            host: s.str(),
            port: s.nat().in(1, 65535),
            user: s.str(),
          }).strict(),
      }),
    ),
  }).strict();

// The tag is not written twice: `tagged` removes it, so an `s3` case names
// only its own keys, and the TS type is `{type: "s3"} & {...}` -- a `t.type`
// test narrows.
export type Config = Infer<typeof Config>;

export type Loaded = { ok: true; value: Config } | { ok: false; error: string };

/** Either the parsed config, or one line of English saying what is wrong. */
export function loadConfig(text: string): Loaded {
  let json: unknown;
  try {
    json = JSON.parse(text);
  } catch (e) {
    // Not a schema question: the file is not JSON at all.
    return { ok: false, error: `config: not JSON: ${(e as Error).message}` };
  }
  const r = Config.parse(json);
  return r.ok ? r : { ok: false, error: r.error.text("config") };
}

if (import.meta.main) {
  const path = process.argv[2];
  if (!path) {
    console.error("usage: bun load.ts <file.json>");
    process.exit(2);
  }
  const r = loadConfig(readFileSync(path, "utf8"));
  if (!r.ok) {
    console.error(r.error);
    process.exit(1);
  }
  console.log(JSON.stringify(r.value, null, 2));
}
