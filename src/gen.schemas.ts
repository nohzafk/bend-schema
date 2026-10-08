// The fixture the printer is tested on: every constructor the builder can make,
// in one schema.
//
// Exported as `schemas` so the gate can run the real command on this file:
//
//   bun src/gen-cli.ts src/gen.schemas.ts <tmp>/schemas.bend
//   tools/bend-check <tmp>/schemas.bend
//
// A constructor with no case in the printer throws; one printed wrongly is a
// Bend error. So a new constructor cannot pass the gate by printing nothing.
//
// No test code here, and nothing at the top level but schemas: the command
// *executes* the module it reads (gen-cli.ts), so a `describe` here would run
// outside the test runner and a filesystem call would run at build time.

import { s } from "./index.ts";

export const Every = s.object({
    plain: s.str(),
    named: s.str().len(1, 32),
    seats: s.nat(),
    workers: s.nat().in(1, 64),
    offset: s.int(),
    code: s.int().in(-32768, -32000),
    active: s.bool(),
    always: s.true(),
    anything: s.json(),
    tier: s.enum(["free", "pro"]),
    note: s.str().nullable(),
    tags: s.list(s.str().len(1, 8)),
    few: s.list(s.nat()).len(1, 4),
    nick: s.str().optional(),
    pair: s.tuple(s.nat(), s.str()),
    either: s.union(s.nat(), s.str(), s.list(s.bool())),
    pay: s.oneKey({ card: s.object({ last4: s.str() }), invoice: s.object({ days: s.nat() }) }),
    event: s.tagged("type", { open: s.object({ at: s.nat() }), close: s.object({ why: s.str() }) }),
  }).strict();

export const schemas = { every: Every, workers: s.nat().in(1, 64) };
