# Writing schemas

A schema describes one JSON value. You build it with `s`, and every schema
has the same three methods: `parse`, `check` and `encode`.

```ts
import { s, type Infer } from "bend-schema";
```

## Scalars

```ts
s.nat()              // integer from 0 to 2^48-1
s.nat().in(1, 500)   // integer from 1 to 500, both included
s.str()              // any string
s.str().len(1, 64)   // string of 1 to 64 characters
s.bool()             // true or false
s.true()             // only true
s.enum(["free", "pro"])  // one of these strings; TS type "free" | "pro"
```

There are no negative numbers and no fractions. Store money as whole cents,
and use a string for anything else.

## Objects

```ts
const User = s.object({
  id:    s.nat(),
  name:  s.str().len(1, 64),
  email: s.str().optional(),     // key may be left out
  phone: s.str().nullable(),     // key must be present; value may be null
});

type User = Infer<typeof User>;
// { id: number; name: string; email?: string; phone: string | null }
```

- A key is **required** by default.
- `.optional()` lets the key be absent. Use it only on an object field.
- `.nullable()` allows `null`, but the key must still be present.
- Unknown keys are **dropped** by `parse`.
- `.strict()` makes unknown keys an error:

```ts
const Config = s.object({ name: s.str() }).strict();
Config.check({ name: "x", nmae: "y" })?.text();
// "nmae: is not a key this object allows"
```

## Lists and tuples

```ts
s.list(s.str())            // string[]
s.list(s.nat()).len(1, 10) // 1 to 10 elements
s.tuple(s.nat(), s.str())  // [number, string], exactly two elements
```

## Unions

**Tagged union**: one key says which case the object is.

```ts
const Event = s.tagged("type", {
  signup:   s.object({ user: s.str() }),
  purchase: s.object({ user: s.str(), qty: s.nat().in(1, 99) }),
});
// { type: "signup"; user: string } | { type: "purchase"; user: string; qty: number }
```

Each case describes the object **without** the tag key, so a `.strict()`
case does not need to list `type`. Checking `e.type` narrows the TS type.

**One key**: the object has exactly one of the keys.

```ts
const Payment = s.oneKey({
  card:    s.object({ last4: s.str().len(4, 4) }),
  invoice: s.object({ days: s.nat() }),
});
// { card: {...} } | { invoice: {...} }
```

An object with none of the keys, or with two, is an error.

## Custom rules

`.refine(fn, message)` adds a check the built-in schemas cannot express.
It works on any schema and keeps that schema's methods, so you can still
chain `.in()`, `.len()` or `.strict()` after it.

```ts
const Email = s.str().len(3, 254).refine((x) => x.includes("@"), "must be an email");

const Range = s.object({ lo: s.nat(), hi: s.nat() })
  .refine((r) => r.lo <= r.hi, "lo must not exceed hi");
```

A refinement runs only after the value passes the proved check. Its error has
`proved: false`, because the function is your code, not the verified core.

## Parsing and errors

```ts
const r = User.parse(input);
if (r.ok) {
  r.value;               // typed as User
} else {
  r.error.path;          // ["email"]
  r.error.message;       // "must be a string"
  r.error.proved;        // true
  r.error.text("user");  // "user.email: must be a string"
}
```

- `parse` returns `{ ok: true, value }` or `{ ok: false, error }`. It never
  throws on bad input.
- `check` returns the error, or `null`.
- Only the **first** error is reported: depth first, in document order.
- `error.text(name)` formats the error as one line; `name` names the value.

Common messages:

| Message | Cause |
|---|---|
| `missing` | a required key is absent |
| `must be a string` (or other kind) | wrong type |
| `must be from 1 to 500` | number outside `.in()` |
| `must be 1 to 64 characters long` | string outside `.len()` |
| `must have 1 to 10 elements` | list outside `.len()` |
| `is not one of the allowed names` | enum or unknown tag |
| `is not a key this object allows` | extra key in a strict object |
| `must have one of its keys` | `oneKey` object with none of the keys |
| `is a second key, where only one is allowed` | `oneKey` object with two keys |
| `too large` | value is over the size limit |

## Encoding

`encode` turns a typed value back into JSON-ready data. It is the inverse of
`parse`, and it throws if the value breaks a bound or a refinement:

```ts
const line = JSON.stringify(Event.encode({ type: "signup", user: "ann" }));
```

Use the same schema to write and to read, so the two cannot drift apart.

## Mistakes caught when the schema is first used

Some schemas cannot round-trip, so `parse`, `check` and `encode` throw on
first use:

- the same key twice in one object or union;
- `.nullable().nullable()`;
- `.optional()` anywhere except directly on an object field.
