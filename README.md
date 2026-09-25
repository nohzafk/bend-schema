# bend-schema

A schema library whose checker is **proved correct**, not just tested.

Define a schema once. Check JSON against it from TypeScript or from
[Bend](https://github.com/bendlang/bend), and get the first error with
its path. The checker is written in Bend, and its laws are machine-checked
for every schema and every value.

## Install

```sh
npm install bend-schema
```

Requires Node.js 22.18 or later. You do not need Bend installed.

## Quick start

```ts
import { s, parse, errText, type Infer } from "bend-schema";

const Plan = s.strict(s.object({
  name:  s.str().len(1, 64),
  seats: s.nat().in(1, 500),
  tier:  s.enum(["free", "pro"]),
  email: s.str().refine((x) => x.includes("@"), "must be an email"),
}));
type Plan = Infer<typeof Plan>;

const r = parse(Plan, JSON.parse(body));
if (!r.ok) {
  console.error(errText(r.error, "plan"));  // "plan.seats: must be from 1 to 500"
}
```

- `check(schema, value)` returns the first error, if any.
- `parse(schema, value)` checks, then returns the value as plain JS.
- `encode(schema, value)` writes a value back to JSON. It throws if a number
  is outside its bounds, because the TS type cannot express that.

Each error is `{ path, message, proved }`. `proved: true` means the error came
from the verified core. `proved: false` means it came from a `.refine()`
predicate. Refinements run only after the proved check passes.

## Schema builders

| Builder | Accepts | TS type |
|---|---|---|
| `s.nat()`, `.in(lo, hi)` | integer 0 to 2^48-1, optionally in `[lo, hi]` | `number` |
| `s.str()`, `.len(lo, hi)` | string, optionally with length in `[lo, hi]` | `string` |
| `s.bool()` | boolean | `boolean` |
| `s.true()` | `true` only | `true` |
| `s.nullable(x)` | `null` or `x` (the key must be present) | `T \| null` |
| `s.list(x)` | array of `x` | `T[]` |
| `s.tuple(a, b, ...)` | fixed-length array | `[A, B, ...]` |
| `s.object({...})` | object; unknown keys are dropped | `{...}` |
| `s.strict(obj)` | object; unknown keys are an error | `{...}` |
| `s.enum([...])` | one of the given strings | `"a" \| "b"` |
| `s.oneKey({a: x, ...})` | object with exactly one of the keys | `{a: X} \| ...` |
| `s.tagged("type", {...})` | discriminated union on a tag key | `{type: "a"} & A \| ...` |
| `.refine(fn, message)` | any builder, plus a custom predicate (not proved) | unchanged |

Semantics:

- Every key an object schema names must be present.
- The first error is found depth-first, in document order.
- `s.oneKey` rejects an object with none of its keys or with more than one.

## Use from Bend

Export your schemas from a TypeScript module:

```ts
// schema.ts
export const schemas = { config: Config, workers: Workers };
```

Generate Bend source:

```sh
npx bend-schema gen schema.ts schema.bend
```

Then use it in a Bend program:

```bend
import ./schema.bend as Sch

def check_config(r: S.Raw) -> Maybe<&2, S.Err>:
  S.check0(Sch.config_schema(), r)
```

The command executes `schema.ts`, so that file should contain only schemas.

Bend code can also plug in its own rules through a template parameter. The
laws hold for every rule, so you only need to prove what your rule means. See
`core/core.bend` for the full schema type and the rule interface.

## What is proved

The laws in `core/LAWS.bend` hold for every schema, every rule and every value:

- **Exact:** `check` reports no error if and only if the value conforms.
- **Accurate:** the reported path leads to a real error of the reported kind.
- **Round trip:** decoding an encoded value gives back the same value.
- **Encoding conforms:** what the encoder writes always passes the check.
- Each combinator (enum, tuple, variant, tagged union, strict, bounds) has a
  law that states what it accepts.

Not proved: the TypeScript builder, the conversion between JS values and the
core, and `.refine()` predicates. These are covered by tests.

## Limits

- **Size:** a value may contain at most 3072 array elements plus object keys
  in total, counted across all nesting levels. A larger value is rejected with
  a `TooLarge` error at the point where it goes over. This keeps the checker
  within the stack.
- **Width:** an object may have at most 256 keys.

## Development

Development uses [Bun](https://bun.sh) and Bend.

```sh
sh test.sh                                        # full gate: proofs, tests, types
bun tools/bend_lib.ts core/core.bend dist-core    # rebuild the compiled core
```

| Path | Contents |
|---|---|
| `core/` | the Bend checker, its laws and their proofs |
| `src/` | the TypeScript API, codec and Bend code generator |
| `dist-core/` | the compiled core (committed) |
| `examples/` | example projects |
| `tools/` | build and verification tools |

## License

MIT
