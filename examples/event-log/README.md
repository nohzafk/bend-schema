# event-log — write and read a JSON-lines log with one schema

An append-only log file. Each line is one JSON event. One schema, `Event`, is used
both to write lines and to read them back.

- `append(path, event)` — checks and encodes the event, then adds one line.
- `readAll(path)` — parses every line. On the first bad line it throws, naming the
  line and the field: `line 3.qty: must be from 1 to 99`.

```ts
import { append, readAll } from "./log.ts";

append("events.jsonl", { kind: "purchase", user: "bob", sku: "SKU-9", qty: 2, coupon: null });
readAll("events.jsonl"); // [{ kind: "purchase", user: "bob", sku: "SKU-9", qty: 2, coupon: null }]
```

## Try it

Run these from the package root:

```sh
bun test examples/event-log        # the tests
bunx tsc -p examples/event-log     # type check
```

## Files

| File | What it is |
|---|---|
| `log.ts` | the `Event` schema, `append`, `readAll` |
| `log.test.ts` | every event kind, a generated batch of 200 events, a refused value, a corrupted line |
| `tsconfig.json` | extends the package's, for `tsc` |

## The schema

`"kind"` picks one of three event types:

| `kind` | Fields |
|---|---|
| `signup` | `user` (1–32 chars), `plan` (`"free"` or `"pro"`) |
| `purchase` | `user`, `sku`, `qty` (1–99), `coupon` (string or `null`) |
| `note` | `text`, `tags` (list of strings), `at` (pair of whole numbers) |

## Why one schema for both directions

With hand-written zod you usually have a writer and a reader, kept in step by hand.
When they drift — a renamed field, a nullable key, a new case — you get lines that
can be written but not read back.

Here there is one value: `Event.encode(e)` writes the line and `Event.parse(line)`
reads it. They cannot disagree about a field name, a nullable key, or a case.

**And the round trip is proved, not just tested.** `core/LAWS.bend` has this law,
for every schema:

```
law decode_encode:
  for +s: C.Schema
  for +x: C.Meaning(s)
  for hw: {C.wf(s) == True{} : Bool}
  {C.dec(s, C.enc(s, x)) == Some{x} : Maybe<&2, C.Meaning(s)>}
```

In plain words: for any well-formed schema `s` and any valid value `x`, decoding
the encoding of `x` gives back `x`. For this log that means every possible event —
every `user` up to 32 characters, every `qty` from 1 to 99, every tag list, every
null coupon — reads back as exactly what was written. The tests round-trip a few
hundred events; the law covers all of them.

## What is *not* proved

- **The JS conversion.** `toJs` / `toMeaning` in `src/index.ts` convert between plain
  JS values and the core's values. `src/index.test.ts` tests every case, but this
  part is not proved. The proof says the core agrees with itself; that your JS
  values map correctly into the core is tested.
- **Values out of range.** The law assumes the value is valid (for example,
  `qty` within 1–99). The TypeScript type cannot express that, so `append` checks
  first and throws on `qty: 100` before anything reaches the file.
