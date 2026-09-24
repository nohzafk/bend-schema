# examples/event-log — one JSON line per event, one schema for both directions

An append-only log of three kinds of event. `append` encodes an event and
writes a line; `readAll` parses every line back and throws on the first bad
one, naming the line and the field inside it (`line 3.qty: must be from 1 to 99`).

```ts
import { append, readAll } from "./log.ts";

append("events.jsonl", { kind: "purchase", user: "bob", sku: "SKU-9", qty: 2, coupon: null });
readAll("events.jsonl"); // [{ kind: "purchase", user: "bob", sku: "SKU-9", qty: 2, coupon: null }]
```

| file | what it is |
|---|---|
| `log.ts` | the `Event` schema, `append`, `readAll` |
| `log.test.ts` | every case, a generated 200-event batch, a refused value, a corrupted line |
| `tsconfig.json` | extends the package's, for `tsc` |

From the package root:

```sh
bun test examples/event-log        # the tests
bunx tsc -p examples/event-log     # the types
```

## What this bought over a hand-written zod schema

Here the format's reader and writer are the same value. `Event` is written
once: `encode(Event, e)` produces the line and `parse(Event, line)` reads it,
so the two cannot drift apart about a field name, a nullable key or a case —
a hand-written zod pair would be two declarations kept in step by hand, and
the drift shows up as a line that can be written but not read. And the
agreement is not merely tested. It is proved, for every schema, in
`core/LAWS.bend`:

```
law decode_encode:
  for +s: C.Schema
  for +x: C.Meaning(s)
  for hw: {C.wf(s) == True{} : Bool}
  {C.dec(s, C.enc(s, x)) == Some{x} : Maybe<&2, C.Meaning(s)>}
```

"What was written reads back as itself": on a well-formed schema (`wf`), the
decoder returns the meaning the encoder was given. So for this log, every
event — every `user` string up to 32 characters, every `qty` from 1 to 99,
every list of tags, every null coupon — is written to be read back, and no
test had to say so. `log.test.ts` round-trips a few hundred events through
files; the law counts none.

Be exact about what that covers. The conversion around the core is **not**
proved: `toJs`/`toMeaning` in `src/index.ts` move this host's plain JS values
into the core's `Meaning(s)` and back, and `src/index.test.ts` round-trips
every constructor rather than proving anything. The proved claim is that the
core never disagrees with itself; that these JS values sit in the core's
shape is tested, not proved. `encode` also has a premise the core states
(`encode_conforms` assumes each value is inside the bounds its constructors
state), which is why `append` throws on a `qty` of 100 — the TS type cannot
rule it out, so the value is refused before it reaches the file.
