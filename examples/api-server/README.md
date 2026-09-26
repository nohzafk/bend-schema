# api-server — validate an HTTP request body

A small orders API in one file, with no dependencies.

- `POST /orders` with a valid order → `201` and the parsed order.
- `POST /orders` with a bad order → `400` and the **first** thing that is wrong, with its path.

## Try it

Run these from the package root:

```sh
bun run examples/api-server/server.ts        # listens on PORT, default 3000

curl -s localhost:3000/orders -H 'content-type: application/json' -d '{
  "id": "o-1", "currency": "usd", "note": null, "totalQty": 3,
  "items": [{"sku": "sku-1", "qty": 3, "price": 250}]}'

bun test examples/api-server                 # the tests
bunx tsc --noEmit -p examples/api-server     # type check (the root tsconfig does not include examples/)
```

The tests do not open a port. The whole API is the function `handle(req)`, so
the tests call it with a `Request` directly.

## Files

| File | What it is |
|---|---|
| `server.ts` | the `Order` schema, `handle(req)`, and the server |
| `server.test.ts` | the tests |
| `tsconfig.json` | extends the package's, for `tsc` |

## The schema

`Order` is one strict object (unknown keys are errors):

| Field | Rule |
|---|---|
| `id` | string, 1–40 characters |
| `currency` | `"usd"` or `"eur"` |
| `note` | string up to 200 characters, or `null`. The key must be present; send `null`, not nothing. |
| `totalQty` | whole number, 1–10000 |
| `items` | list of line items: `sku` (1–32 chars), `qty` (1–999), `price` (0–1000000, in whole cents — the schema has no floats) |

One extra rule sits on top, written with `.refine()`: `totalQty` must equal the
sum of the item quantities.

## What a 400 looks like

Every 400 has the same shape:

```json
{"path": ["items", 2, "qty"],
 "message": "must be a whole number from 0 to 281474976710655",
 "proved": true,
 "text": "order.items[2].qty: must be a whole number from 0 to 281474976710655"}
```

- `path` — where the problem is (here: the third line item's `qty`).
- `message` — what is wrong there.
- `proved` — `true` if the error came from the verified core, `false` if it came from your `.refine()` rule.
- `text` — `path` and `message` as one readable line.

## Why "proved" matters

With a hand-written zod schema you can send the same JSON. The difference is how
much you can trust it.

**1. The path and message are always correct.** A `proved: true` error comes
from the core checker, which has a machine-checked law (`check_accurate` in
`core/LAWS.bend`) for every schema and every value:

> If `check` says "at this path, the value is wrong for this reason", then
> following that path really does reach a value that is wrong for exactly that reason.

So a proved 400 never points at a field that is fine, and never gives a reason
that is false. That is why the server sends the error to the client as it is.
With hand-written validation, the path is whatever the author wired up, and
nothing checks it.

(Which error is reported *first* is a separate rule: depth first, in order. See
`core/LAWS.bend`.)

**2. A huge body gets a clean error, not a crash.** The server sets a size limit,
`BUDGET = 3072`, counted as list elements plus object keys at every level
(re-measure it with `bun src/measure_budget.ts`). The limit itself is a choice
made in this file, not a theorem. But what happens past it is proved: the
oversized list is replaced by one "too large" marker, and the law
`too_large_reported` says `check` reports exactly that spot. So an order with
5000 line items gets:

```json
400 {"path": ["items"], "message": "too large"}
```

instead of `RangeError: Maximum call stack size exceeded`.

## What is *not* proved

- The TypeScript builder (`s.object(...)` etc.).
- The conversion between plain JS values and the core's values (tested in `src/index.test.ts`, not proved).
- Your `.refine()` rules. They are ordinary TS functions, run only after the proved check passes, and their errors say `proved: false`. The `totalQty` rule is one of these.
