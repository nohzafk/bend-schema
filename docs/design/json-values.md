# Design: `s.json()`, any JSON value

`s.json()` accepts any JSON value and gives it back unchanged. This note
explains why it is built the way it is. It describes the code as it ships.

The code is in [`core/core.bend`](../../core/core.bend) (the types and
`valid_json`), [`core/LAWS.bend`](../../core/LAWS.bend) (the laws), and
[`src/codec.ts`](../../src/codec.ts) and [`src/index.ts`](../../src/index.ts)
(the conversion between JavaScript values and the core).

## The need

Some fields carry a value that the schema does not own. A JSON-RPC `params` or
`result` field is one example. The schema must check that the value is JSON. It
must not look inside, and it must not change the value.

Other schemas cannot do this. `s.nat()` and `s.int()` accept whole numbers
only. `s.object()` needs known fields. So the core has one more schema,
`SJson`, with its own value type, `Json`:

```
type Json:
  JNull
  JBool{value}
  JNumber{value: NumberBits}
  JString{value}
  JArray{values: List<Json>}
  JObject{members: List<JMember>}

type JMember:  JMember{key, value: Json}
```

`parse` returns the JavaScript value that the input held. `encode` writes it
back. Between the two, the value stays the same.

## Numbers

A JSON number in a JavaScript value is a `number`. The core stores a finite
`number` as its IEEE-754 binary64 bit pattern. It uses two 32-bit words:

```
type NumberBits:  NumberBits{hi: U32, lo: U32}
```

`hi` is the high word and `lo` is the low word. The host reads and writes them
with a `DataView` in big-endian order (`numberBits` and `bitsNumber` in
`src/codec.ts`). The core never does arithmetic on them. It only keeps them.

Three rules follow from this choice.

- **Finite is part of valid.** A pattern is finite when its exponent bits are
  not all ones. `finite_number` tests this on `hi`. `NaN`, `Infinity` and
  `-Infinity` are not valid JSON numbers, so `valid_json` is false for them.
  The type name alone does not give this guarantee. The validity check does.
- **`-0` is kept.** The bit pattern of `-0` is different from that of `0`, and
  the pattern comes back unchanged. The host checks the round trip with
  `Object.is`.
- **The decimal spelling is not kept.** `1.0`, `1e0` and `1` are one value.
  The host sees a `number`, not text. `s.json()` is not a JSON text parser.

### Why not the other options

| Option | Reason it was not used |
| --- | --- |
| `Nat` | Cannot hold negative numbers, fractions, or large values. |
| Numeric text | Keeps the value, but needs a rule to tell valid number syntax from a finite JavaScript number. `1e400` is valid syntax but is not a finite `number`. The fixed bit pattern needs no such rule. |
| `F32` | Has too little precision and range to hold every JavaScript `number`. |
| An outside JSON library | A parser and a printer are not what was missing. The library value types and laws would still need work to fit this core. |

## Value, failure and absence

Four different things can happen at an `s.json()` position. The design keeps
them apart.

| Case | Representation | Result |
| --- | --- | --- |
| A valid JSON value, `null` included | `RJson{value}` | Accepted. |
| Input that is not JSON, for example `NaN`, `undefined`, a function, a cycle, or a `Date` | `RBad` | `NotJson` error. |
| Input that is JSON but too large | `RTooBig` | `TooLarge` error. |
| A field that is not there | `RMissing` | `Missing` error, unless the field is `.optional()`. |

`null` is a value. `JNull` is valid input for `s.json()`. The absence of a
field is not a value. It is a state of the read, and the core calls it
`RMissing`. The codec never builds `RMissing` from a JavaScript value. The
only exception is `.optional()`, which reads `undefined` as absent.

The codec turns a failure into a marker. It does not throw, and it does not
build a partial `Json`. `toJsonRaw` returns `RBad` or `RTooBig` if any part of
the value fails. It returns `RJson` only for a whole valid value. If a size
marker from the first conversion pass is anywhere inside an `s.json()` value,
the whole position is `TooLarge`.

Because of this, the checker has one rule for `SJson`: accept `RJson{v}` when
`valid_json(v)` is true. For every other input it reports `NotJson`, or
`Missing` or `TooLarge` for the two markers that are not shapes.

## Arrays and objects

- **Arrays** are ordered. `JArray` holds a list, and the order of elements is
  kept.
- **Objects** are lists of members. `JObject` holds a list of
  `JMember{key, value}`. `valid_json` does not look for a key that occurs in
  two members: RFC 8259 says names should be unique, not must, and the check
  would cost each member a scan of the members after it. See
  [capacity.md](./capacity.md).
- **Member order is kept.** The host reads the members in the order that
  `Object.entries` gives. The core keeps them in a list in that order.
  `jsonToJs` writes them back in the same order. The laws `json_dec_preserves`
  and `json_enc_preserves` show that `dec` and `enc` do not change the list.
  JavaScript itself puts integer-like keys, such as `"2"`, first in ascending
  order. This occurs before the value gets to bend-schema.
- **Keys are compared as they are.** There is no Unicode normalisation. Two keys
  that look the same but have different code points are two keys.

A JavaScript object cannot have the same own key twice. So a duplicate key can
come only from a host that builds a `Json` by hand. `encode` writes such a value
as it is, and the JavaScript object that results keeps the last value for the
key.

The host reads an object into a plain object with `Object.defineProperty`, so a
key named `__proto__` becomes an ordinary own property. It does not change the
prototype. The codec refuses an object that is not plain (`Date`, `Map`, a class
instance) as not JSON.

## What is proved

The core has four `json_*` laws in `core/LAWS.bend`. Each law has a proof:

- `json_valid_spec`: `valid_json` agrees, for every `Json`, with a second
  definition written in a different way. That definition says every number is
  finite.
- `json_accept_exact`: `SJson` accepts a valid `RJson` and nothing else. It
  refuses every other raw value, including a missing value and a size marker.
- `json_dec_preserves`: `dec` reads an `RJson` as the value it holds, without
  change, and reads any other raw value as nothing.
- `json_enc_preserves`: `enc` wraps a `Json` without change. The result passes
  the check exactly when the value is valid.

The second definition exists so that a `valid_json` that is always true, always
false, or tests only the first member is not a model of the law.

The specification of finiteness compares the high word, with its sign bit
removed, to `0x7FF00000` (the pattern of infinity). It does not read the
exponent field with `Nat.div`, because `Nat.div` is too slow to check a literal
of that size.

### What is not proved

The conversion between JavaScript values and the core is not proved. It lives
in `toJsonRaw` and `jsonToJs`, and it covers the bit-pattern read and write, the
walk over arrays and objects, and the checks for cycles and non-plain objects.
Tests cover it instead (`src/codec.test.ts` and `src/index.test.ts`). They are
evidence, not proof. The same is true of the TypeScript builder.

## Alternatives that were not used

| Alternative | Reason |
| --- | --- |
| Store a JSON number as text | See the number table above. |
| Keep the decimal spelling of a number | The host has a `number`, not text, and the goal is to pass a value, not a document. |
| Add a JSON text parser and printer | `parse` takes a JavaScript value, as `JSON.parse` already gives. Text is the caller's job. |
| Treat a missing field as `null` | Absence and `null` are different states, and the error differs (`Missing` and `NotJson`). |

## Limits

An `s.json()` value has the same limits as every other value. These are a
count of array elements and object keys, a width limit for an object, and a
depth limit. A value that goes over a limit is `TooLarge`. The numbers and the
reasons are in [capacity.md](capacity.md).
