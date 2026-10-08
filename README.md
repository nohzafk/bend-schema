# bend-schema

A schema library whose checker is **proved correct**, not just tested.

Define a schema once. Check JSON against it from TypeScript or from
[Bend](https://github.com/bendlang/bend), and get the first error with
its path. The checker is written in Bend, and its laws are machine-checked
for every schema and every value.

The npm package and the GitHub repository are `bend-schema`. The BendHub
package is `bend-schema-lib`.

## Install

```sh
bun add bend-schema
```

From a Bend file there is no install step: import the checker from the hub.

```bend
import bend-schema-lib@0.3.0.0/core.bend as S
```

Use it with [Bun](https://bun.sh). The package ships TypeScript source, and
Node.js refuses to run TypeScript from `node_modules`. You do not need Bend
installed.

The `bend-schema` command emits Bend source, and it runs under Bun whether you
start it with `bunx` or `npx`: its shebang is `env bun`.

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

### Errors on the wire

`error.toJSON()` is the error as JSON, and `JSON.stringify(error)` writes the
same thing:

```json
{ "path": ["params", 1, "n"], "message": "must be a whole number from 0 to 281474976710655", "proved": true }
```

- `path` lists object keys (strings) and list indices (whole numbers from 0
  to 2^48-1), outer first. An empty path means the value itself.
- The field names and their types are stable: a change to them is a major
  version. **The `message` text is not stable.** It is written for people, so
  do not branch on it.
- `issueSchema` is the schema of this form, so the receiver can check it like
  any other value. It is not strict: a field added later does not break an
  older reader. Each path part is a string or a whole number, as a proved
  `s.union`.

For example, as the `data` of a JSON-RPC "Invalid params" error:

```ts
const r = Params.parse(msg.params);
if (!r.ok) return { jsonrpc: "2.0", id: msg.id, error: { code: -32602, message: "Invalid params", data: r.error.toJSON() } };
```

## Schemas

| Builder | Accepts |
|---|---|
| `s.nat()`, `.in(lo, hi)` | integer 0 to 2^48-1 |
| `s.int()`, `.in(lo, hi)` | integer -(2^48-1) to 2^48-1 |
| `s.str()`, `.len(lo, hi)` | string |
| `s.bool()`, `s.true()` | boolean, or only `true` |
| `s.enum([...])` | one of the given strings |
| `s.list(x)`, `.len(lo, hi)` | array of `x` |
| `s.tuple(a, b, ...)` | fixed-length array |
| `s.object({...})`, `.strict()` | object; `.strict()` refuses unknown keys |
| `s.tagged(key, {...})` | union chosen by a tag key |
| `s.oneKey({...})` | object with exactly one of the keys |
| `s.union(a, b, ...)` | one of the alternatives, which take different JSON kinds |
| `s.json()` | any JSON value, passed through unchanged |
| `.optional()` | the object key may be absent |
| `.nullable()` | the value may be `null` |
| `.refine(fn, message)` | a custom check (not proved) |

See **[docs/schemas.md](https://github.com/nohzafk/bend-schema/blob/main/docs/schemas.md)**
for how to write schemas:
objects, unions, custom rules, error messages and encoding.

For why `s.json()` stores and checks a value the way it does, see
[docs/design/json-values.md](https://github.com/nohzafk/bend-schema/blob/main/docs/design/json-values.md).

## Optional Effect v4 adapter

Convert an existing schema into an Effect codec (a schema with decoding and
encoding). The adapter is a separate entry point; importing `bend-schema`
does not load or require Effect.

```sh
bun add bend-schema effect@4.0.1
```

```ts
import { s } from "bend-schema";
import { toEffect } from "bend-schema/effect";
import { Schema } from "effect";
import { Rpc } from "effect/rpc";

const Message = toEffect(s.object({ text: s.str(), note: s.str().optional() }));
const decoded = Schema.decodeUnknownSync(Message)({ text: "hello", extra: true });
// decoded is inferred as { text: string; note?: string }; extra is dropped.
const encoded = Schema.encodeSync(Message)(decoded);

const Echo = Rpc.make("Echo", { payload: Message, success: Message });
```

The API infers `T` from the input schema; no type assertion is needed:

```ts
function toEffect<T>(schema: Schema<T>): EffectSchema.decodeTo<
  EffectSchema.declareConstructor<T, T, readonly []>, typeof EffectSchema.Unknown
>;
// Schema is bend-schema's type; EffectSchema is effect's Schema module.
```

The concrete return type keeps Effect's constructor input (`~type.make.in`)
as `T`. RPC clients therefore accept the inferred object, tagged union, or
string payload and reject incorrectly typed fields at compile time. Widening
the adapter to `EffectSchema.Codec<T, unknown>` erases that constructor input
to `unknown`; keep the inferred return type when passing it to `Rpc.make`.
TypeScript checks field types, not refinement predicates or numeric ranges;
those are still validated at runtime.

Decoding returns `schema.parse(input).value`, not the untouched input.
Encoding validates the decoded value with `parse`, then calls `schema.encode`.
Both directions are synchronous and require no Effect services.

- **Errors:** the first parse error keeps its path and reason in an Effect
  `SchemaIssue.Pointer` and `InvalidValue`. Effect adds surrounding field paths
  when the codec is nested. `proved` is on the `InvalidValue` annotations, next
  to `message`. Effect's own formatters print only the path and the message.
- **Semantics:** unknown keys are dropped unless the object is strict. Optional
  fields, tagged unions, refinements and the existing size limits still apply.
  Effect parse options do not replace bend-schema's validation rules.
- **Representation:** the encoded type is `unknown`, as with `schema.encode`.
  The Effect AST uses an opaque declaration, not a generated structural schema,
  so Effect's own `Schema.toJsonSchemaDocument` sees `{}`. For a JSON Schema,
  use `bend-schema/json-schema` (below). No Bend datatype parser or source
  generator is involved.
- **Failures:** thrown schema configuration errors and thrown refinement
  callbacks remain programming errors, not validation issues. Exceptions from
  `encode` become Effect validation issues with the exception's message.

Effect is an optional peer dependency (`^4.0.1`); tests pin `4.0.1`.
Effect v3 and v4 prereleases are not supported by this adapter.

## JSON Schema

`toJsonSchema` writes a JSON Schema (draft 2020-12) document for the JSON a
schema accepts, for client authors and tools that read JSON Schema:

```ts
import { toJsonSchema } from "bend-schema/json-schema";

const doc = toJsonSchema(s.object({ id: s.nat(), name: s.str().optional() }));
// { $schema: "https://json-schema.org/draft/2020-12/schema", type: "object",
//   properties: { id: { type: "integer", minimum: 0, maximum: 281474976710655 },
//                 name: { type: "string" } },
//   required: ["id"], additionalProperties: true }
```

- **Never stricter than `parse`.** Every value `parse` accepts passes the
  document. Three things JSON Schema cannot state are left out, and there the
  document is looser: `.refine()` predicates, the size and depth limits, and
  a key repeated within one object. `parse` stays the authority.
- **Exact elsewhere.** Without `.refine()` and inside the limits, a JSON value
  passes the document exactly when `parse` accepts it. The tests check this
  against ajv on random schemas and values; it is tested, not proved.
- **Mapping.** `nat`, `int` and `.in()` are bounded `integer`s; `.len()` is
  `minLength`/`maxLength` (both count code points) or `minItems`/`maxItems`;
  a tuple is `prefixItems` with no further items; `.strict()` is
  `additionalProperties: false`; `tagged` and `oneKey` are `oneOf`; `union`
  is `anyOf`; `s.json()` is `{}`.
- **ajv and `__proto__`.** ajv 8 skips a `properties` entry named
  `__proto__`, so it does not check a field of that name. The document itself
  names it.

## Examples

Each example is a small runnable project with tests:

- [`examples/api-server`](https://github.com/nohzafk/bend-schema/tree/main/examples/api-server): an HTTP endpoint that
  validates the request body and returns the error path in a 400.
- [`examples/config-loader`](https://github.com/nohzafk/bend-schema/tree/main/examples/config-loader): reads a JSON config
  file and reports the first mistake in one line.
- [`examples/event-log`](https://github.com/nohzafk/bend-schema/tree/main/examples/event-log): an append-only JSON-lines log
  that writes and reads with the same schema.

## Ask an AI agent to write a schema

New to bend-schema? Paste this into your coding agent to introduce it, then
work with the agent as usual:

```text
bend-schema is a TypeScript schema library like zod, whose checker is
written in Bend and proved correct. Read its README to learn what it is
and how to install it: https://github.com/nohzafk/bend-schema

If we decide to use it, docs/schemas.md in that repo explains how to
write schemas.
```

## Use from Bend

Write a schema once in TypeScript, use it in a Bend function whose laws you
prove, and call that function from TypeScript again. The loop is:

```
schema.ts ──gen──▶ schema.bend ──import──▶ core.bend ──bend-emit──▶ dist/core.mjs ──import──▶ app.ts
```

**1. Export your schemas** from a TypeScript module:

```ts
// schema.ts
import { s } from "bend-schema";

export const Config = s.object({
  name:  s.str().len(1, 64),
  seats: s.nat().in(1, 500),
}).strict();

export const schemas = { config: Config };
```

**2. Generate Bend source.** The command executes `schema.ts`, so that file
should contain only schemas. It runs under Bun — Node cannot strip the types
from TypeScript in `node_modules`.

```sh
bunx bend-schema gen schema.ts schema.bend
```

`schema.bend` defines `config_schema()` and imports the proved checker from
this package's `core/core.bend`.

**3. Use the schema in your own Bend core.** Import the checker with the same
path that `schema.bend` uses on its second line:

```bend
# core.bend
import Base
import ./node_modules/bend-schema/core/core.bend as S
import ./schema.bend as Sch

def config_ok(r: S.Raw) -> Bool:
  S.conforms0(Sch.config_schema(), r)
```

Here you can state and prove laws about your own functions, and build on the
laws in `core/LAWS.bend`. Import `core/PROOF.bend` alongside them: its proofs
are what close them, and a file that imports `LAWS.bend` alone does not check.
The test suite proves it.

**4. Turn the core into a typed ES module** with
[bend-emit](https://github.com/nohzafk/bend-emit):

```sh
bun add -d bend-emit
bunx bend-emit core.bend dist       # writes dist/core.mjs and dist/core.d.mts
```

**5. Call it from TypeScript.** `toRaw` converts a JSON value into the
core's `Raw` input:

```ts
// app.ts
import { toRaw } from "bend-schema";
import { config_ok } from "./dist/core.mjs";

config_ok(toRaw({ name: "a", seats: 3 }));    // true
config_ok(toRaw({ name: "a", seats: 999 }));  // false
```

Commit `dist/`: at run time your package needs neither Bend nor bend-emit.

Bend code can also plug in its own rules through a template parameter. The
laws hold for every rule, so you only need to prove what your rule means. See
`core/core.bend` for the full schema type and the rule interface.

## What is proved

The laws in `core/LAWS.bend` hold for every schema, every rule and every value:

- **Exact:** `check` reports no error if and only if the value conforms.
- **Accurate:** the reported path leads to a real error of the reported kind.
- **Round trip:** decoding an encoded value gives back the same value.
- **Encoding conforms:** what the encoder writes passes the check whenever each
  enum value is one of its names and each bound holds of the value.
- **Any JSON value:** `s.json()` accepts exactly the valid JSON values (finite
  numbers, unique object keys), and decoding and encoding keep the value
  unchanged.
- **Union:** `s.union` accepts exactly what one alternative accepts, never two
  at once, and reports the error of the alternative whose JSON kind the value
  has.
- Each combinator (enum, tuple, variant, tagged union, strict, bounds) has a
  law that states what it accepts.

Not proved: the TypeScript builder, the conversion between JS values and the
core, and `.refine()` predicates. These are covered by tests.

Two JavaScript details are handled in the TypeScript layer, because the core
never sees them: a non-plain object (a `Date`, `Map` or class instance) is
refused as not being JSON, and an object key named `__proto__` is an ordinary
field, read and written as data, never as the prototype.

## Limits

- **Size:** a value may contain at most 100,000 array elements plus object
  keys, counted over the whole value and all nesting levels. A larger value is
  rejected with a `TooLarge` error at the point where it goes over.
- **Width:** an object may have at most 256 keys.
- **Depth:** containers may nest at most 128 levels; the outermost array or
  object is level 1. A container on level 129 is `TooLarge`.
- Strings are not counted.

What bounds each: size and width bound time. The checker walks lists and
objects in a loop, so length costs no stack, but an object's keys are looked up
by a scan, so the cost is linear in the count except for objects, where it is
quadratic in the object's keys. The worst case is many objects of 256 keys.
Depth bounds the stack: each level is one JavaScript call.

Why the limits are what they are: [docs/design/capacity.md](https://github.com/nohzafk/bend-schema/blob/main/docs/design/capacity.md).

Worst case, measured with `bun src/measure_budget.ts` (bend 2.0.36, bend-emit
0.3.5, bun 1.4.2, macOS arm64, Apple M3 Max): a list of objects of 256 keys at
the size limit (99,973 counted), `parse` / `encode`:

| Schema | parse | encode |
|---|---|---|
| `s.json()` | 0.38 s | 0.43 s |
| list of an object of 256 fields | 2.0 s | 2.0 s |
| the same, `.strict()` | 2.5 s | 2.7 s |

A typed schema with many fields costs more than `s.json()`, because each field
is looked up in each object; the sender controls the number of keys, you
control the number of fields. Other shapes at the limit take well under a
second (a flat list of 100,000 numbers: about 30 ms to check).

## Development

Development uses [Bun](https://bun.sh), Bend, and
[bend-emit](https://github.com/nohzafk/bend-emit) (a dev dependency), which
builds `dist-core/`.

```sh
sh test.sh                                        # full gate: proofs, tests, types
# rebuild the compiled core
bunx bend-emit core/core.bend dist-core
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
