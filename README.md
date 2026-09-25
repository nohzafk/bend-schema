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
import { s, type Infer } from "bend-schema";

const Plan = s.object({
  name:  s.str().len(1, 64),
  seats: s.nat().in(1, 500),
  tier:  s.enum(["free", "pro"]),
  email: s.str().refine((x) => x.includes("@"), "must be an email"),
  note:  s.str().optional(),
}).strict();
type Plan = Infer<typeof Plan>;

const r = Plan.parse(JSON.parse(body));
if (!r.ok) {
  console.error(r.error.text("plan"));  // "plan.seats: must be from 1 to 500"
}
```

Every schema has three methods:

- `parse(value)` checks the value, then returns it typed.
- `check(value)` returns the first error, or `null`.
- `encode(value)` turns a typed value back into JSON-ready data.

An error has a `path`, a `message`, and `proved`. `proved: true` means the
error came from the verified core. `proved: false` means it came from your
own `.refine()` function, which runs only after the proved check passes.

## Schemas

| Builder | Accepts |
|---|---|
| `s.nat()`, `.in(lo, hi)` | integer 0 to 2^48-1 |
| `s.str()`, `.len(lo, hi)` | string |
| `s.bool()`, `s.true()` | boolean, or only `true` |
| `s.enum([...])` | one of the given strings |
| `s.list(x)`, `.len(lo, hi)` | array of `x` |
| `s.tuple(a, b, ...)` | fixed-length array |
| `s.object({...})`, `.strict()` | object; `.strict()` refuses unknown keys |
| `s.tagged(key, {...})` | union chosen by a tag key |
| `s.oneKey({...})` | object with exactly one of the keys |
| `.optional()` | the object key may be absent |
| `.nullable()` | the value may be `null` |
| `.refine(fn, message)` | a custom check (not proved) |

See **[docs/schemas.md](docs/schemas.md)** for how to write schemas:
objects, unions, custom rules, error messages and encoding.

## Examples

Each example is a small runnable project with tests:

- [`examples/api-server`](examples/api-server): an HTTP endpoint that
  validates the request body and returns the error path in a 400.
- [`examples/config-loader`](examples/config-loader): reads a JSON config
  file and reports the first mistake in one line.
- [`examples/event-log`](examples/event-log): an append-only JSON-lines log
  that writes and reads with the same schema.

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
