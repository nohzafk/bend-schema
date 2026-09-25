# bend-schema

**A schema library whose checker is proved, not tested.**

Write a schema once with `s`; check values against it from TypeScript or from
Bend, and get the first error with the path to it. The check is a Bend program
whose laws hold for every schema, so a project that writes one gets them without
a proof of its own.

## Requirements

Node.js 22.18.0 or later. Bend is not needed: `dist-core/` is the compiled core.

## Use it from TypeScript

```ts
import { s, parse, check, encode, errText, type Infer } from "bend-schema";

const Plan = s.strict(s.object({
  name:  s.str().len(1, 64),
  seats: s.nat().in(1, 500),
  tier:  s.enum(["free", "pro"]),
  email: s.str().refine((x) => x.includes("@"), "must be an email"),
}));
type Plan = Infer<typeof Plan>;

const r = parse(Plan, JSON.parse(body));
if (!r.ok) return errText(r.error, "plan");   // "plan.seats: must be from 1 to 500"
```

`check` stops at the first error; `parse` checks and then reads the value into
plain JS. `encode` writes a value back, and throws on a number outside a bound,
which its TS type cannot rule out.

Every error is `{path, message, proved}`: `proved: true` came from the core, so
the first error in reading order is at the path it names. `proved: false` came
from a `.refine()` predicate, which runs only after the proved check passes.

## Use it from Bend

```sh
npx bend-schema gen schema.ts schema.bend
```

`schema.ts` exports `schemas`, an object whose keys name the Bend defs:

```ts
export const schemas = { config: Config, workers: Workers };
```

The generated file imports the core by a path computed from where it sits, so a
core uses it like any other schema:

```bend
import ./schema.bend as Sch

def check_config(r: S.Raw) -> Maybe<&2, S.Err>:
  S.check0(Sch.config_schema(), r)
```

The command executes the module it reads, so that file must be schemas and
nothing else.

## API

### The builder

| builder | accepts | TS type |
|---|---|---|
| `s.nat()`, `.in(lo, hi)` | whole number 0..2^48-1, in `[lo, hi]` | `number` |
| `s.str()`, `.len(lo, hi)` | string, length in `[lo, hi]` | `string` |
| `s.bool()`, `s.true()` | boolean, `true` | `boolean`, `true` |
| `s.nullable(x)` | `null` or x — the key must still be present | `T \| null` |
| `s.list(x)`, `s.tuple(a, b)` | array | `T[]`, `[A, B]` |
| `s.object({...})`, `s.strict(obj)` | object; strict refuses extra keys, non-strict drops them | `{...}` |
| `s.enum([...])` | one of the strings | `"a" \| "b"` |
| `s.oneKey({a: x, ...})` | an object with exactly one of the keys | `{a: X} \| ...` |
| `s.tagged("type", {a: obj})` | discriminated union on `type` | `{type: "a"} & A \| ...` |

### The core's schema

| schema | a value conforms when |
|---|---|
| `SNat{}` | it is a whole number from 0 to 2^48-1 |
| `SNatIn{lo, hi}` | it is a whole number from `lo` to `hi`, both included |
| `SStr{}` | it is a string |
| `SStrLen{lo, hi, s}` | it is a string of `lo` to `hi` characters (`sstr_len_meaning`) that also conforms to s |
| `SBool{}` | it is a boolean |
| `SOpt{s}` | it is null, or conforms to s |
| `SOptional{s}` | it is absent, or conforms to s (`soptional_meaning`); `null` is not absent |
| `SList{e}` | it is a list, each element conforming to e |
| `SListLen{lo, hi, s}` | it is a list of `lo` to `hi` elements (`slist_len_meaning`) that also conforms to s |
| `SField{name, s, rest}`, `SEnd{}` | it is an object whose `name` conforms to s, and so on |
| `SRule{s, tag}` | it conforms to s, then the project's rule `tag` reports nothing |
| `SStrict{s}` | it conforms to s, and has no key s does not name (s is a record or variant chain; wf asks it) |
| `STagged{key, name, s, rest}` | its `key` is the string `name` and the object without that key conforms to s; else it conforms to rest |
| `STagEnd{key}` | nothing (no case matched: a missing tag is `Missing`, an unknown one `NotOneOf`, both at `AtKey{key}`) |
| `STrue{}` | it is `true` |
| `SEnum{names}` | it is a string, one of `names` |
| `STuple{s, rest}`, `STEnd{}` | it is a list as long as the chain, each position conforming to its schema |
| `SVariant{name, s, rest}`, `SVEnd{}` | it is an object with exactly one of the chain's keys, and the value under it conforms to that key's schema |

The builder writes neither `SOptional` nor `SListLen`: `s.nullable` is `SOpt`
(a key the builder names must be present, written `null`) and `s.list` is
`SList`. Both are for a schema written in Bend, where a key may be absent and a
list bounded by its count.

Decided semantics: a key the schema names must be present; keys it does not name
are ignored, except under `SStrict`; an `SVariant` object with none of its keys,
or two, is an error (`{any: false}` is refused because `any`'s schema is
`STrue`); the first error is depth first, by position; under an `SRule` the whole
value is checked against its shape before the rule runs.

Two constructors are worth more than a sentence.

**`SStrict{s}`** refuses a key `s` does not name, reporting the first at
`AtKey{key}`. Its law, `strict_meaning`, counts rather than walks:

```
conforms(SStrict{s}, r) == conforms(s, r) and count_unknown(key_names(s), r) == 0
```

`wf` asks that `s` be a chain of keys, which is what lets `encode_conforms` hold:
every key `enc` writes is one the chain names.

**`STagged{key, name, s, rest}`** is one case of a chain ending in `STagEnd{key}`.
The case sees the object **without** its tag, so an `SStrict` case need not name
it. A repeated tag key is not taken out twice — the case sees the second, as
`lookup` reads only the first. `wf` asks that a chain use one key throughout and
name no case twice, which `decode_encode` needs: a later case must not claim a
tag an earlier one wrote.

| law | states |
|---|---|
| `tagged_meaning` | a case conforms by the object without its tag when the tag is its name, else by the rest |
| `tag_end_refuses` | the end of the chain accepts nothing |
| `drop_first` | `drop_key(k, {k: v, ...o})` is `o` |
| `drop_other` | for `j != k`, what `drop_key(k, r)` has under `j` is what `r` has |

The last two pin `drop_key`, which `conforms`, `check` and `dec` share, so a bug
in it cannot pass by being shared.

### The laws

- `check_exact`: check finds nothing exactly when the value conforms.
- `check_accurate`: following the reported path, everything passed on the way
  conforms, and the value at the end is wrong in the reported way (`defect`
  replays the path; it never searches).
- `too_large_reported`: a node the codec refused to build (`RTooBig`) is
  reported where it stands, as `TooLarge` — never as the schema kind's own
  reason for a wrong shape.
- `enum_accepts`, `enum_admits`: an `SEnum` accepts exactly its names.
- `tuple_meaning`: a tuple conforms exactly when the value is a list of the
  tuple's length and each position conforms.
- `variant_meaning`: a variant chain conforms exactly when the value is an
  object, one of its keys is present, and every present key's value conforms.

The last two exist because the first two are relative to `conforms`: a bug shared
by `check` and `conforms` passed both, and falsification found it.

Not pinned by a law: with a key repeated in an object, `lookup` reads the first.
A JSON object has no repeated keys.

### Rules

A project's refinement is a rule, not a combinator: `check`, `conforms` and
`defect` take one template parameter `~rule: Nat -> Raw -> Maybe<Err>` — the
`SRule`'s tag, the value, and the rule's first error with a path relative to the
value. A rule cannot live in the `Schema` value, because a function cannot be
stored in `Data`. The laws hold for every rule, so a project proves only what its
rule means. With no rules, pass `~no_rule`; a host calls the closed forms
`check0`/`conforms0`.

Two rules come ready-made, and a rule calls them by tag, since a tag carries no
bounds:

```bend
def my_rule(tag: Nat, r: S.Raw) -> Maybe<&2, S.Err>:
  match tag:
    case 0n:
      S.str_len_in(1n, 64n, r)
    case 1n+t:
      S.nat_in(1n, 100n, r)
```

| rule | reports nothing exactly when (law) |
|---|---|
| `str_len_in(lo, hi, r)` | r is a string of `lo` to `hi` characters (`str_len_in_meaning`) |
| `nat_in(lo, hi, r)` | r is a number from `lo` to `hi` (`nat_in_meaning`) |

Both bounds are included, and each passes any value it is not about — so wrap
the schema that fixes the kind: `SRule{SStr{}, 0n}`. `lo` past `hi` is not an
error but an empty range: nothing is in bounds, and the laws hold for every `lo`
and `hi`.

A bound a host writes itself, with no rule, is a constructor instead: `SNatIn{lo,
hi}` and `SStrLen{lo, hi, s}` carry the numbers a tag cannot. Their meaning is
the rules' own, stated once: `snat_in_meaning` restates `nat_in_meaning` and
`sstr_len_meaning` restates `str_len_in_meaning` (`SBool` is `sbool_meaning`). A
bound is a subset of the shape the encoder writes, so `encode_conforms` carries
`bounds_ok` beside `names_ok`.

### Reading a value

`Meaning(s)` is the Bend type a schema describes: a record is nested `Both<A, B>`
ending in `Unit`, a variant chain nested `Either`s ending in `Empty`, `SOpt` a
`Maybe`, `SEnum` a `String`, `SNatIn` a `Nat`, `SRule` and `SStrLen` their shape's
meaning. `enc(s, x)` writes a meaning as the host would; `dec(s, r)` reads one. A
project writes no reader: it matches the meaning into its own types.

- `decode_encode`: on a well-formed schema (`wf`), `dec(s, enc(s, x))` is `Some{x}`.
- `checked_decodes`: a value that conforms is read, so a reader has no "cannot
  happen" default to be wrong about.
- `encode_conforms`: on a well-formed schema, what `enc` writes conforms, given
  `names_ok` and `bounds_ok`.

`wf` asks that a key be named once in its record or chain, and that an optional
value not be itself nullable — without either, the round trip fails. A schema is
the programmer's, not the wire's, so `wf` is a premise.

## Limits

**What is not proved.** The builder, the conversion between the core's values
and plain JS, and `.refine()` predicates. `src/index.test.ts` round-trips every
constructor.

**How large a value may be.** The walks cost a native frame per step and no law
can see a stack, so the codec refuses a value past a measured budget instead: it
counts list elements plus object keys, summed over every level of nesting, and
past `BUDGET` = 3072 puts one `RTooBig` in place of the array or object that ran
past, which `check` reports as `TooLarge` at that node's path. One budget covers
lists, objects and nesting alike, and it is spent in reading order.

A second limit is on time: an object may hold at most `KEYS_MAX` = 256 keys. A
field is found by scanning the object from the front, so walking one costs about
keys² lookups — at 3072 keys that was about 8 s per call. A wider object is
`RTooBig` too.

The budget is measured, not guessed: the largest count where every walk returns,
then halved. Bun 1.4.2, bend 2.0.27, macOS arm64:

| shape | largest count that returns | next step throws |
|---|---|---|
| flat list | 12,288 | `check0: RangeError` |
| flat object | 6,144 | `check0: RangeError` |
| nested object | 10,637 | `check0: RangeError` |
| nested list | 10,639 | `check0: RangeError` |
| list of lists, list of objects, mixed | > 30,000 (not the binding shape) | |

The flat object binds first: each field's `lookup` scans from the front, so the
last key is read with one frame per key before it still on the stack. Half of
6,144 is 3,072, which leaves the worst shape 2x its margin. `bun
src/measure_budget.ts` re-measures the table; `codec.test.ts` holds it.

## Development

### Layout

```
core/core.bend    Raw (any JSON value), Schema, check, conforms and defect,
                  the predicate the laws state
core/LAWS.bend    22 laws, for every schema, every rule and every value
core/PROOF.bend   their proofs; imports ./base-facts
core/base-facts/  the base facts those proofs import
core/falsify/     literal instances of the laws, for tools/falsify.ts
core/check_mutants.ts  one false core per law; tools/bend_mutants.ts
src/codec.ts      the universal codec (JS value to Raw), its budget, error text
src/index.ts      the TS API: s, parse, check, encode, errText
src/gen.ts        the same schema as Bend source: the core's own value printed
src/gen-cli.ts    the command: `bend-schema gen <module.ts> <out.bend>`
src/codec.test.ts the codec and the check at run time, and at scale
src/measure_budget.ts the budget's measurement: the shapes, and their edges
dist-core/        the compiled core, committed; BEND-VERSION names the bend that
                  built it, and the gate rebuilds and diffs it
tools/            bend_lib.ts (the build), bend_mutants.ts and case_arms.ts (the
                  gate), bend-check (bend with a 5 s limit), falsify.ts
```

`files` ships `core/core.bend` with `src/` and `dist-core/`, because a Bend core
imports it by path.

### Commands

| command | what it settles |
|---|---|
| `sh test.sh` | the gate: the laws (no unsafe code) and their mutants, every law on its concrete instances (`core/falsify/`), the module (rebuilt and diffed against `dist-core/`), the tests, the types, the base facts |
| `bun tools/bend_lib.ts core/core.bend dist-core` | the build: the core as a typed ES module, into the committed `dist-core/` |
| `LAW=exact bun tools/falsify.ts core/falsify/spec.ts` | a law on literal instances |

The gate and the tests use bun; using the package does not.

### Notes on the core

**A new `Raw` or `Schema` constructor touches every proof that enumerates them**,
here and in each project whose proofs do (billing's). An abstract value makes
every match stuck, so each case is written out; `tools/case_arms.ts` generates
most of them (a new reason in an `# arms why:` map is one line). `src/gen.ts`
mirrors the `Schema` constructors too, and the gate compiles what it prints.

**`check`, `conforms` and `defect` are each one self-recursive def** over the
schema and the value together: a step into a field shrinks the schema, a step
along a list keeps it and shrinks the value. A generic walk with a closure per
element is not accepted — a closure cannot be passed to a template, and a
function parameter cannot be called twice. A path counts what it passed, so
replaying it never compares two names.

**`Missing` and `TooLarge` share one helper** (`missing_or`): both say "what sits
here is not a value the schema can use", which keeps the accuracy law true for
the new reason without a case per combinator. The price is that a value that is
both absent and too big reports `Missing`, which the codec never builds.
