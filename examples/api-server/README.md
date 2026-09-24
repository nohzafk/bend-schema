# examples/api-server — an orders API

One file, no dependencies. `POST /orders` takes an order with line items and
answers `201` with the parsed order, or `400` with the first defect. `handle(req)`
is the whole API, so the test drives it with a `Request` — no port, no server.

```sh
bun run examples/api-server/server.ts               # PORT=3000
curl -s localhost:3000/orders -H 'content-type: application/json' -d '{
  "id": "o-1", "currency": "usd", "note": null, "totalQty": 3,
  "items": [{"sku": "sku-1", "qty": 3, "price": 250}]}'

bun test examples/api-server
bunx tsc --noEmit -p examples/api-server    # the root tsconfig's include stops at src/ and tools/
```

The schema is one `s.strict(s.object({...}))`: a bounded `id`, an `enum`
currency, a `nullable` note (present as `null` — absent is an error), a bounded
`totalQty`, and a `list` of strict line items. One `.refine()` sits on top of it,
cross-field: `totalQty` must equal the sum of the item quantities.

Every `400` has the same shape — the core's issue, plus its wording:

```json
{"path":["items",2,"qty"],"message":"must be a whole number from 0 to 281474976710655",
 "proved":true,"text":"order.items[2].qty: must be a whole number from 0 to 281474976710655"}
```

## What the proved core bought

A hand-written zod schema can send a body of the same shape; the difference is
what a reader may assume about its `path` and `message`. That error is not
pointed at the third line item by the code that found it — it is the answer of
`check` in the compiled core, whose `check_accurate` law holds for **every**
schema, every rule and every value, and says:

> what check reports is there: following its path, every value passed on the way
> conforms, and at the end the value is wrong in the way it says.

Its statement is `{C.check(~rule, s, r, prev) == Some{C.Err{path, why}}}` ⟹
`{C.defect(~rule, s, r, prev, path) == Some{why}}`: whenever `check` reports an
error at `path` with reason `why`, `defect` — the predicate that walks that same
path and says what is actually wrong — returns that same `why`. So a `proved:
true` 400 cannot name a field that is fine, or a reason that does not hold;
that is why this server sends the path and the reason to the client as they
come. A hand-written schema's path is whatever its author wired up, and nothing
checks it. (Which error comes first is a separate decision, not this law's:
LAWS.bend fixes the first error depth first, by position.)

The oversized body is the second thing. `BUDGET` = 3072 (counted as list
elements plus object keys, summed over every level; `bun src/measure_budget.ts`
re-measures it) is a host decision, not a theorem — but what happens past it is
again the core's: `toRaw` puts one `RTooBig` where the array that ran past would
have been, and `too_large_reported` says `check` reports exactly that node with
`TooLarge`. So 5000 line items is `400 {"path":["items"],"message":"too large"}`
rather than `RangeError: Maximum call stack size exceeded`.

Not proved, here as everywhere: the builder, the codec's conversion between the
core's values and plain JS, and the `.refine()` predicate — it is an ordinary TS
function, it runs only after the proved check passes, and its 400 says `proved:
false`. The `totalQty` rule above is exactly that: a real check of a real
cross-field property, with no proof behind it.
