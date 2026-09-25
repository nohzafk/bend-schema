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

export const Every = s.strict(
  s.object({
    plain: s.str(),
    named: s.str().len(1, 32),
    seats: s.nat(),
    workers: s.nat().in(1, 64),
    active: s.bool(),
    always: s.true(),
    tier: s.enum(["free", "pro"]),
    note: s.nullable(s.str()),
    tags: s.list(s.str().len(1, 8)),
    pair: s.tuple(s.nat(), s.str()),
    pay: s.oneKey({ card: s.object({ last4: s.str() }), invoice: s.object({ days: s.nat() }) }),
    event: s.tagged("type", { open: s.object({ at: s.nat() }), close: s.object({ why: s.str() }) }),
  }),
);

export const schemas = { every: Every, workers: s.nat().in(1, 64) };
