# Capacity: how bend-schema bounds the cost of checking one value

This note explains why the limits of bend-schema have their values. It also
explains what each limit protects.

For the numbers only, read [Limits in the README](../../README.md#limits).

## The problem

A host cannot choose the size of the values it receives. A sender can send a
very long list, a very wide object, or a very deep nesting. Each one can cost
the checker too much time or too much stack.

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

Three limits exist. Each one bounds a different cost.

| Limit | Value | Bounds | Cost it protects |
|---|---|---|---|
| Budget (`BUDGET`) | 100,000 | array elements plus object keys, all levels summed | time |
| Keys per object (`KEYS_MAX`) | 256 | keys in one object | time |
| Depth (`DEPTH_MAX`) | 128 | levels of nesting | stack |

Strings are not counted.

### Size and keys bound time

The checker walks a list or an object in a loop. Length costs no stack.
The time grows with the count of elements and keys.

The time is about linear in the count, with one exception. The core finds each
field of an object by a scan from the front. One object with `k` keys costs
about `k * k` lookups. At 256 keys this is about 65,000 lookups. It takes
a few milliseconds.

So the worst case is many objects with `KEYS_MAX` keys each. The total cost is
about `count * KEYS_MAX` lookups. The budget caps `count`. The key limit
caps the other factor.

### Depth bounds stack

The checker goes from one level to the next level with a JavaScript call. Each
level of nesting uses one frame. Nesting is the only thing that still uses the
stack. The depth limit caps it.

## Why the old limit came from the stack

An earlier version of the generated code used one frame for each list element
and each object member. The code went down the list tail by recursion.

The old budget was about half of the depth where a deep value overflowed the
stack. So the stack, not the time, set the budget. Some inputs also threw
`RangeError` instead of returning an error. These inputs were a long list in
`encode`, two keys with a long shared prefix, and a value nested too deep.

Two changes in bend-emit 0.3.4 removed width from the stack.

### The loop rewrite (the "hole" rule)

bend-emit rewrites a function into a loop with one general rule. In a `return`,
look at the self-call that is last in evaluation order. This call is the
"hole". The rule changes it into the next step of the loop:

- Work that must run before the hole runs first, in the original order.
- Work that must run after the hole goes into a closure frame on the heap.

The rule does not know any name from bend-schema. It covers every recursive
function of the core. The code is in bend-emit `src/loops.ts`.

### Native `String.cmp`

The Bend `String.cmp` calls `String.cmp.fin`, and `String.cmp.fin` calls
`String.cmp`. The loop pass finds only self-calls, so it does not rewrite this
pair. The pair also cuts a new tail string for each character. The time grows
with the square of the shared prefix.

bend-emit replaces the pair with a native comparison by code point
(`src/intrinsics.ts`). It replaces the pair only when the function text is
identical to the output of bend 2.0.35. Otherwise it keeps the original.

### Why the core and the proofs did not change

The proofs in `core/PROOF.bend` unfold these recursive definitions in many
places. A change to the core would need a new proof of each place. It
would also need a proof that the fuel is enough, and a new design for the
dependent types `enc` and `dec`. The generated code gives the same result with
no change to the core. The laws and proofs stay as they are.

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

## Budget 100,000 and `KEYS_MAX` 256

Once the stack stopped limiting the total, the time became the limit. So
the numbers come from measured time.

The command is `bun src/measure_budget.ts`. The conditions: bend 2.0.35,
bend-emit 0.3.4, bun 1.4.2, macOS arm64, Apple M3 Max. Each shape ran once. The
count was about 100,000.

Worst case through the public API, for a list of objects with 256 keys each
(99,973 counted):

| Schema | parse | encode |
|---|---|---|
| `s.json()` | 0.32 s | 0.38 s |
| list of an object of 256 fields | 1.8 s | 2.0 s |
| the same, `.strict()` | 2.6 s | 2.8 s |

Other shapes at the limit take well under a second. A flat list of 100,000
numbers takes about 30 ms to check.

A typed schema costs more than `s.json()`. This is because the checker looks up
each field in each object. The sender controls the number of keys. The
developer controls the number of fields.

`KEYS_MAX` is 256 because of the `keys * keys` lookup cost. An object with more
keys is `RTooBig`. A set that large belongs in a list.

## The `s.json()` position

An `s.json()` field accepts any JSON value. The checker converts it with
`toJsonRaw`, and the conversion has its own count.

Two facts shape the design:

1. A valid JSON value carries no failure marker inside it. If a `RTooBig` node
   sat inside a JSON value, the value would not be a valid JSON value. See
   [json-values.md](./json-values.md).
2. The first conversion (`toRaw`) already counted the whole message. The second
   conversion starts with a new count. Without a rule, each `s.json()` field
   would get a fresh budget, and a message of 3 times the budget would pass.

The rule: if a size marker occurs anywhere inside an `s.json()` position, the
whole position gets `TooLarge`, at the `s.json()` position's path. The function
`rawFor` in [`src/index.ts`](../../src/index.ts) does this. It uses `hasTooBig`,
which walks with an explicit stack. This is because nothing bounds the width of
`raw`.

A value that is not JSON at all (a cycle, `NaN`) still reports that it is not
JSON.

The error points at the field, not at the inner node. A typed schema reports
the exact path.

## How `encode` is bounded

`encode` walks a host value and writes it. The walk must be bounded by the same
limits as `parse`. Otherwise `encode` would do more work than `parse` allows.

`encode` counts the positions it writes before it walks them. The function
`toMeaning` in [`src/index.ts`](../../src/index.ts) works as follows:

- The whole value uses one budget. It starts at `BUDGET`.
- Before the walk goes into a container, `enter` takes the container's length
  from the budget. For an object, the count is the number of keys the schema
  writes. An optional field with value `undefined` is not written, so it is not
  counted.
- `enter` also checks the level against `DEPTH_MAX`.
- An `s.json()` position takes its count from the same budget and starts at the
  current depth.
- When a limit is passed, `encode` throws an error with the path and the text
  "too large".
- A property that the schema does not name is never read.

Two designs were rejected:

| Design | Reason for rejection |
|---|---|
| Count the whole input before the walk | It counts properties that the schema does not write. `encode` then refuses values that `parse` accepts. |
| Check only the output | The walk has no bound. A shared reference expands under the schema, so a small input can take seconds or use all the memory. A sparse `new Array(1e9)` was written as `[]`. |

Counting what is written gives both properties. The work is bounded by the
limits, and the accepted set is the same as for `parse`. A sparse array is
refused by its length.

In the `tagged` case, the case schema reads the original value directly. The
code does not copy the properties that the schema does not write, because no
limit counts that copy.

## Accepted risks

- **The generated-code rewrite is not proved.** The loop rewrite and the native
  `String.cmp` are outside the proved core. The proof does not show an error in
  them. Tests cover them:
  - the bend-emit tests and the bend-schema tests;
  - a random comparison of the output of old and new generated code;
  - a comparison of the native `String.cmp` with the original Bend output on
    random pairs.

  Three controls reduce the risk. The bend version is pinned. The native
  `String.cmp` applies only to identical text. bend-emit reports a function
  that it cannot rewrite.
- **The worst-case time depends on the schema.** A sender can force about 0.3 s
  with `s.json()`. A typed schema with 256 fields can take about 2.6 s. The
  README states this.
- **The times come from one machine.** Each number is one run. On another
  machine, trust only the order of magnitude. Run `bun src/measure_budget.ts`
  again.

## Future direction

This section describes an idea. It is not planned work. No date or promise
goes with it.

The core could use an explicit work stack. The checker would keep a list of
tasks in place of recursion. Then neither depth nor width would use the call
stack, and the proof could be made inside Bend. A Bend parser of JSON already
uses this shape and generates loops.

A change of this size has open proof obligations:

- The to-do list grows when a container opens. So the length of a list cannot
  be the decreasing measure. The proof needs a separate fuel count or a measure of remaining
  work. It must show that valid input does not run out of fuel. A large
  constant is not a proof.
- The new checker must return the same first error and path as a reference
  specification, or it must succeed on the same values. Define the
  specification without the old checker.
- Each state change must keep the invariants of the tasks and the path.
- A run-time resource limit must have a meaning that is separate from
  termination in the proof.
- Other helpers still recurse. These include `toRaw`, the decode and encode
  conversions, and the path construction. All of them need analysis.

Today these are only obligations. They are not approved laws.

## Alternatives rejected

| Alternative | Reason |
|---|---|
| Explicit work stack in the core now | It needs a new proof of each place that unfolds the recursion, a fuel proof, and a frame design for `enc` and `dec`. |
| Raise only the `BUDGET` constant | The width recursion still used one frame per element. A deep value would overflow. |
| bend-emit knows the bend-schema helper names | A generator must not depend on the names in one core. The general rule covers every recursive function. |
| No depth limit | Depth still uses stack. A deep hostile value throws `RangeError`. |
| Budget as a `parse` option | It adds an API option. No user needs a different limit now. |
| Report the inner path for a `s.json()` overflow | A valid JSON value cannot carry a marker. See [json-values.md](./json-values.md). |
| A new budget for each `s.json()` field | A message of 3 times the budget would pass. |
