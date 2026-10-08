# Capacity: how bend-schema bounds the cost of checking one value

This note explains the one limit bend-schema has, why the other two were
removed, and what the checker's time depends on.

For the numbers only, read [Limits in the README](../../README.md#limits).

## The problem

A host cannot choose the size of the values it receives. A sender can send a
very long list, a very wide object, or a very deep nesting. Each one can cost
the checker time or stack.

bend-schema has two parts:

- The checker is a Bend core. Its laws are proved.
- The code that runs is JavaScript. The tool
  [bend-emit](https://github.com/nohzafk/bend-emit) generates it from the core.

The Bend core cannot say how long a walk takes. It also cannot say how much
stack a walk uses. The host code decides both. This is the work of
[`src/codec.ts`](../../src/codec.ts).

The core states one law about size: `too_large_reported` in
[`core/LAWS.bend`](../../core/LAWS.bend). The law says that a `RTooBig` node
gets a `TooLarge` error at its path, for every schema. The law does not say
when a value is too large. The host codec decides that, and a run-time test
checks it.

## The cost model

| Cost | What drives it | How it is bounded |
|---|---|---|
| stack | levels of nesting | `DEPTH_MAX` = 128, in the codec |
| time | elements, keys, and schema fields | nothing in bend-schema; linear in the input, so the host's body-size limit |

Strings are not inspected.

### Depth bounds stack

The checker goes from one level to the next level with a JavaScript call. Each
level of nesting uses one frame. Nesting is the only thing that uses the stack:
the checker walks the elements of a list and the members of an object in a loop.
The depth limit caps it.

### Width costs time, linearly

For a fixed schema, the time is linear in the size of the value. Three facts
give this:

1. A list is walked once, one element at a time.
2. The core finds each schema field by one scan of the object's keys
   (`lookup`, `key_once`, `extra_err` in `core/core.bend`). One object costs
   about `fields × keys` lookups. The sender controls `keys`; the developer
   controls `fields`. So for a given schema, the cost per key is a constant.
3. An `s.json()` value is checked in one pass (`valid_json`): every number
   must be finite, and nothing else is looked for.

Measured with `bun src/measure.ts` (bend 2.0.36, bend-emit 0.3.5, bun 1.4.2,
macOS arm64, Apple M3 Max, one run each):

| keys in one object | check against 16 fields | `s.json()` parse |
|---|---|---|
| 1,000 | 4 ms | 9 ms |
| 10,000 | 30 ms | 8 ms |
| 100,000 | 79 ms | 35 ms |
| 1,000,000 | 847 ms | 325 ms |

Ten times the keys cost about ten times the time. A flat list of 1,000,000
numbers checks in 0.19 s.

A schema with many fields costs more per key: a list of 256-key objects against
256 fields takes 1.7 s per 100,000 counted elements and keys (2.3 s with
`.strict()`). The developer chose those fields, so this is not a cost the sender
can impose.

Something linear in the input is bounded by the input. An HTTP server limits the
body it accepts, and that limit bounds the checker's time the same way it bounds
`JSON.parse`. A limit inside bend-schema would restate it, and refuse values
that are not costly.

## Depth 128

The outermost container is level 1. A container on level 129 gets `TooLarge`
at its path.

The basis for 128:

- serde_json uses 128 as its default.
- protobufjs and protobuf-es use 100. 128 is a little above them.
- A protocol message nests a few dozen levels at most.
- Each level of nesting uses one JavaScript call, and 128 levels use a small
  part of the stack.

The depth limit is a policy choice with a large margin. It is not at the edge
of the stack.

## The `s.json()` position

An `s.json()` field accepts any JSON value. The checker converts it with
`toJsonRaw`, which counts depth from the position, not from the whole value.

A valid JSON value carries no failure marker inside it. If a `RTooBig` node sat
inside a JSON value, the value would not be a valid JSON value. See
[json-values.md](./json-values.md). So the rule is: if the first conversion
(`toRaw`, which counts depth from the whole value) put a depth marker anywhere
inside an `s.json()` position, the whole position gets `TooLarge`, at the
position's path. The function `rawFor` in [`src/index.ts`](../../src/index.ts)
does this. It uses `hasTooBig`, which walks with an explicit stack, because
nothing bounds the width of `raw`.

A value that is not JSON at all (a cycle, `NaN`) still reports that it is not
JSON.

## How `encode` is bounded

`encode` walks a host value and writes it. The walk checks the same depth limit
as `parse`: `toMeaning` in [`src/index.ts`](../../src/index.ts) checks the level
of every container the schema writes against `DEPTH_MAX` before it walks it,
and an `s.json()` position starts at the level it sits at. Past the limit,
`encode` throws an error with the path and the text "too large".

Only what the schema writes is walked. A property that the schema does not name
is never read. So `encode` accepts every value `parse` accepts.

`encode` has no width bound. Its input is the host's own value, not a sender's,
so a shared reference that expands under the schema costs the host what the
host built. A sparse array (`new Array(1e9)`) fails at its first hole, because
`undefined` is not a value of any schema.

## Why there was a size budget, and why it is gone

Earlier versions had two more limits: a budget of 100,000 array elements plus
object keys over the whole value, and 256 keys per object.

The budget came from the stack. An earlier version of the generated code used
one frame for each list element and each object member, and the budget was
about half of the depth where a value overflowed the stack. bend-emit 0.3.4
rewrote every self-recursive function into a loop (the "hole" rule in its
`src/loops.ts`), and replaced the Bend `String.cmp` pair with a native
comparison. After that, width cost no stack, and the budget was kept as a bound
on time.

Two facts then showed that it bounded the wrong thing:

1. The time was measured to be linear in the input for a fixed schema (the
   table above). The earlier "`keys × keys`" cost came from measuring a 256-key
   object against a 256-field schema, where `fields = keys`. The budget capped
   something the body-size limit already caps, and refused a list of 100,001
   numbers that checks in 30 ms.
2. `s.json()` was in fact quadratic, and the key limit was what hid it. The
   core's `valid_json` refused an object that held a name twice, by checking
   each member against every member after it: `keys²/2` string compares, with
   `keys` chosen by the sender. One object of 16,000 keys took 2.3 s; 100,000
   keys took about 100 s. A key limit of 256 bounded this to a few
   milliseconds per object — but the design note gave a different reason for
   the limit, and a limit that protects a cost nobody has named is a limit
   nobody can review.

The second fact was resolved in the core, not the codec. `valid_json` no longer
looks for a repeated name:

- RFC 8259 says the names in an object *should* be unique, not *must*. An
  object with a repeated name is JSON. `JSON.parse` accepts it.
- A JavaScript object cannot hold a name twice, so no value from a sender can
  have one. Only a `Json` built by hand in Bend can, and `encode` writes it as
  it is.
- The law `json_valid_spec` and its proof shrank: the specification `json_spec`
  lost its `occurs` clause, and the proof lost two lemmas. Every other `json_*`
  law treats `valid_json` as opaque and did not change.

A linear uniqueness check inside the core was considered and rejected. It would
need sorted keys or a tree, and a proof that the result agrees with the
`occurs`-based specification. That proof needs a total order on `String` with
its lemmas (antisymmetry, transitivity, agreement with `String.eq`), which no
Bend library provides. Weeks of proof for a case the host never produces.

With `s.json()` linear and the typed check linear, nothing bounded by the two
limits is left. Both were removed, together with the `BUDGET` and `KEYS_MAX`
exports.

## Accepted risks

- **The generated-code rewrite is not proved.** The loop rewrite and the native
  `String.cmp` are outside the proved core. Tests cover them: the bend-emit
  tests and the bend-schema tests, a random comparison of the output of old and
  new generated code, and a comparison of the native `String.cmp` with the
  original Bend output on random pairs. The bend version is pinned, and
  bend-emit reports a function that it cannot rewrite.
- **The checker's time is the host's responsibility.** A host that accepts a
  body of any size will spend time linear in it. This is the contract of every
  parser, and the README states it.
- **The times come from one machine.** Each number is one run. On another
  machine, trust only the order of magnitude. Run `bun src/measure.ts` again.
- **A hand-built `Json` with a repeated name is not refused.** Only Bend code
  can build one; the host cannot.

## Alternatives rejected

| Alternative | Reason |
|---|---|
| Keep a key limit at `s.json()` positions only | It protected the quadratic `valid_json`; with that gone, it protects nothing. |
| Linear uniqueness check in the core | Needs a `String` order theory and its proof; weeks, for a value the host cannot produce. |
| Keep the budget as a bound on time | Time is linear in the input; the body-size limit already bounds it, and the budget refused cheap values. |
| Budget as a `parse` option | No limit exists to make optional. A per-field bound is `.len(lo, hi)`. |
| No depth limit | Depth still uses stack. A deep hostile value throws `RangeError`. |
| Explicit work stack in the core | It needs a new proof of each place that unfolds the recursion, a fuel proof, and a frame design for `enc` and `dec`. Depth is a policy choice with margin, not a problem. |
| Report the inner path for a `s.json()` depth overflow | A valid JSON value cannot carry a marker. See [json-values.md](./json-values.md). |
