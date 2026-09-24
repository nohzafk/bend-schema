# bend-schema — a schema, and one proved check for every schema

A community library, written and proved in Bend — not an official Bend package.

What zod gives JavaScript, with the check written and proved in Bend once.
A schema is a Bend value built from combinators; `check(~rule, schema, raw)` finds
the first thing wrong, with the path to it. Its laws hold for every schema,
so a project that writes a schema gets them without a proof of its own. A
project's own refinements are rules it passes in (`SRule`, below).

## Use it from TypeScript

No Bend needed: `dist-core/` is the compiled core, committed.

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

Every error is `{path, message, proved}`. `proved: true` came from the core,
whose laws hold for every schema: the first error in reading order, at its
path. `proved: false` came from a `.refine()` predicate, which runs only after
the proved check passes. What is NOT proved: the builder, the conversion
between the core's values and plain JS, and refinements — `src/index.test.ts`
round-trips every constructor. `encode` throws on a value outside a bound,
since its TS type cannot rule that out (`encode_conforms` assumes `bounds_ok`).

## Layout

```
core/core.bend    Raw (any JSON value), Schema, check and conforms, and defect,
                  the predicate the laws state
core/LAWS.bend    20 laws, for every schema, every rule and every value
core/PROOF.bend   their proofs; imports ./base-facts
core/base-facts/  the base facts those proofs import
core/falsify/     literal instances of the laws, for tools/falsify.ts
core/check_mutants.ts  one false core per law; tools/bend_mutants.ts
src/codec.ts      the universal codec (JS value to Raw), its budget, error text
src/index.ts      the TS API: s, parse, check, encode, errText
src/codec.test.ts the codec and the check at run time, and at scale
src/measure_budget.ts the budget's measurement: the shapes, and their edges
dist-core/        the compiled core (core.js, core.d.ts), committed: the
                  package ships it, so a user never installs bend.
                  BEND-VERSION names the bend that built it, and test.sh
                  rebuilds and diffs it
tools/            bend_lib.ts (the build), bend_mutants.ts and case_arms.ts
                  (the gate), bend-check (bend with a 5 s limit), falsify.ts
                  (the falsifier's runner)
```

The Bend sources are the library; `dist-core/` is what a host imports, and
`sh test.sh` is the gate over both.

## The combinators

| schema | a value conforms when |
|---|---|
| `SNat{}` | it is a whole number from 0 to 2^48-1 |
| `SNatIn{lo, hi}` | it is a whole number from `lo` to `hi`, both included |
| `SStr{}` | it is a string |
| `SStrLen{lo, hi, s}` | it is a string of `lo` to `hi` characters (`sstr_len_meaning`) that also conforms to s |
| `SBool{}` | it is a boolean |
| `SOpt{s}` | it is null, or conforms to s |
| `SList{e}` | it is a list, each element conforming to e |
| `SField{name, s, rest}`, `SEnd{}` | it is an object whose `name` conforms to s, and so on |
| `SRule{s, tag}` | it conforms to s, then the project's rule `tag` reports nothing |
| `SStrict{s}` | it conforms to s, and has no key s does not name (s is a record or variant chain; wf asks it) |
| `STagged{key, name, s, rest}` | its `key` is the string `name` and the object without that key conforms to s; else it conforms to rest |
| `STagEnd{key}` | nothing (no case matched: a missing tag is `Missing`, an unknown one `NotOneOf`, both at `AtKey{key}`) |
| `STrue{}` | it is `true` |
| `SEnum{names}` | it is a string, one of `names` |
| `STuple{s, rest}`, `STEnd{}` | it is a list as long as the chain, each position conforming to its schema |
| `SVariant{name, s, rest}`, `SVEnd{}` | it is an object with exactly one of the chain's keys, and the value under it conforms to that key's schema |

Decided by the human (acl): an `SVariant` object with none of its keys, or
two, is an error; `{any: false}` is refused because `any`'s schema is `STrue`.
Decided by the human: a key the schema names must be present, and an optional
value is written null; keys the schema does not name are ignored; the first
error is depth first, by position; under an `SRule`, the whole value is
checked against its shape before the rule runs (shape first, then rules).

## The laws

- `check_exact`: check finds nothing exactly when the value conforms.
- `check_accurate`: following the reported path, everything passed on the way
  conforms, and the value at the end is wrong in the reported way (`defect`
  replays the path; it never searches).
- `too_large_reported`: a node the codec refused to build (`RTooBig`) is
  reported where it stands, as `TooLarge` -- the reason is a size, never the
  schema kind's own reason for the wrong shape. It is the one claim the core
  can make about a size, since only the codec knows one; see "How large a
  value may be".
- `enum_accepts`, `enum_admits`: an `SEnum` accepts exactly its names (with
  a witness of where the accepted one is).
- `tuple_meaning`: a tuple conforms exactly when the value is a list of the
  tuple's length and each position conforms (a bug shared by check and
  conforms, skipping a position, passes the first two laws).
- `variant_meaning`: a variant chain conforms exactly when the value is an
  object, the count of its keys present is 1, and every present key's value
  conforms. The first two laws are relative to `conforms`; without
  this one, a bug shared by `check` and `conforms` (a lone open element
  refused by both) passed both laws, and falsification found it. The same
  held for `in_names` and `none_present`, which the enum and variant laws pin.

Not pinned by a law: with a key repeated in an object, `lookup` reads the
first. A JSON object has no repeated keys.

## A strict object

An object ignores keys its schema does not name; `SStrict{s}` refuses them,
and reports the first one at `AtKey{key}` (a key has no place in the schema to
count, so this step names it). `strict_meaning` states it:

```
conforms(SStrict{s}, r) == conforms(s, r) and count_unknown(key_names(s), r) == 0
```

The right side counts rather than walks, so it shares only `in_names` with the
core, and the enum laws pin that. `wf` asks that `s` be a chain of keys
(`is_keyed`), which is what lets `encode_conforms` hold: every key `enc`
writes is one the chain names.

## A tagged union

`STagged{key, name, s, rest}` is one case of a chain ending in
`STagEnd{key}`. The case sees the object **without** its tag (`drop_key`
takes out the first `key`), so an `SStrict` case need not name the tag. A
repeated tag key is not taken out twice: the case sees the second one, as
`lookup` reads only the first. It means an `Either` chain, like `SVariant`,
and `enc` writes the tag first.

| law | states |
|---|---|
| `tagged_meaning` | a case conforms by the object without its tag when the tag is its name, else by the rest |
| `tag_end_refuses` | the end of the chain accepts nothing |
| `drop_first` | `drop_key(k, {k: v, ...o})` is `o` |
| `drop_other` | for `j != k`, what `drop_key(k, r)` has under `j` is what `r` has |

The last two pin `drop_key`, which `conforms`, `check` and `dec` share, so a
bug in it cannot pass by being shared. `wf` asks that a chain name no case
twice and use one key throughout (`fresh_t`), which `decode_encode` needs: a
later case must not claim a tag an earlier one wrote. `drop_other` rests on
`string_eq_sound` (`base-facts/string_eq.bend`): `String.eq(a, b) == True`
gives `a == b`.

## Reading a value: the decoder is derived

`Meaning(s)` is the Bend type a schema describes (a record is nested
`Both<A, B>` ending in `Unit`, a variant chain nested `Either`s ending in
`Empty`, `SOpt` a `Maybe`, `SEnum` a `String`, `SBool` a `Bool`, `SNatIn` a
`Nat`, `SRule` and `SStrLen` their shape's meaning).
`enc(s, x)` writes a meaning as the host would; `dec(s, r)` reads one. A
project writes no reader: it matches the meaning into its own types.

- `decode_encode`: on a well-formed schema (`wf`), `dec(s, enc(s, x))` is
  `Some{x}`.
- `checked_decodes`: a value that conforms is read (so a reader has no
  "cannot happen" default to be wrong about).
- `encode_conforms`: on a well-formed schema, what `enc` writes conforms, if
  every enum value is one of its names (`names_ok`) and every value is inside
  the bounds its constructors state (`bounds_ok`).

`wf` asks that a key be named once in its record or chain and that an optional
value not be itself nullable. Without either, the round trip fails (a mutant
for each: `Some{None}` and `None` would both be written null; a repeated key
reads the first). Decided by the human: `wf` is a premise, since a schema is the
programmer's and not the wire's; an enum means its string.

## How the walks terminate

`check`, `conforms` and `defect` are each one self-recursive def over the
schema and the value together: a step into a field or an optional shrinks the
schema, a step along a list keeps it and shrinks the value. The checker reads
arguments left to right until one shrinks, so this is accepted. A generic walk
with a closure per element is not: a runtime closure cannot be passed to a
template (BEND.md 2.5), and a function parameter cannot be called twice.
A path counts what it passed (`AtIndex{i}`, `AtField{skip, name}`,
`BoundAt{i, key}`), so replaying it never compares two names.

## Rules

A project's refinement is a rule, not a combinator: `check`, `conforms` and
`defect` take one template parameter `~rule: Nat -> Raw -> Maybe<Err>` (the
`SRule`'s tag, the value, and the rule's first error with a path relative to
the value). A rule cannot live in the `Schema` value, since a function cannot
be stored in `Data`. The laws hold for every rule, so a project proves only
what its rule means. A project with no rules passes `~no_rule`; the host calls
the closed forms `check0`/`conforms0` (the bundler does not export template
defs). billing's rule is its own `validate` (`billing-lib/core.bend`,
`plan_rule`).

Two rules come ready-made, and a project's rule calls them by tag, since a
tag carries no bounds:

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

Both bounds are included. Each looks only at the value it is about and passes
any other, so wrap the schema that fixes the kind: `SRule{SStr{}, 0n}`.

A bound a host writes itself — no Bend program and no rule — is a constructor
instead: `SNatIn{lo, hi}` and `SStrLen{lo, hi, s}` carry the numbers, which a
rule's tag cannot. The two bounds are the rules' own tests, stated once
(`str_len_ok`, `num_ok`, shared with `str_len_in` and `nat_in`), and their
meaning is the rules' too: `snat_in_meaning` restates `nat_in_meaning`,
`sstr_len_meaning` restates `str_len_in_meaning`. Both ends are included, and
`lo` past `hi` is not an error but an empty range: nothing is in bounds, and
the laws hold for every `lo` and `hi`. A value of another kind is refused as
that kind (`NotString`, `NotNat`); `SBool` is `sbool_meaning` and `NotBool`.

A bound is a subset of the shape the encoder writes, so `encode_conforms`
carries `bounds_ok` as a premise beside `names_ok`: `enc` writes the value it
was given, and a host that holds one outside a bound is the one at fault —
`check` reports it on the way back.

## How large a value may be

A second limit is on time, not stack: **an object may hold at most
`KEYS_MAX` = 256 keys**. The core finds each field by scanning the object from
the front, so walking an object costs about keys² lookups; at 3072 keys that
was about 8 s for each of `check0`, `conforms0` and `dec`, a small request that
holds a server for seconds. At 256 keys the three together take under 0.1 s.
A wider object becomes `RTooBig` and is reported as `TooLarge`, like a value
past the budget. The budget is spent in reading order, so the node reported is
the first one past it.

`check`, `conforms`, `enc` and `dec` all walk a value one level at a time, and
the compiled JS costs a native frame per step (BEND.md 4.0): a long enough
value throws `RangeError: Maximum call stack size exceeded`. Nothing in the
core knows a size, and no law can see a stack, so the codec refuses one: it
counts **list elements plus object keys, summed over every level of nesting**,
and past `BUDGET` it puts one `RTooBig` in place of the array or object that
ran past, which `check` reports as `TooLarge` at that node's path. One budget
covers lists, objects and nesting alike, because `toRaw` never builds a value
whose count is past it: what the walks receive is bounded by the number the
walks were measured against.

The budget is measured, not guessed: the largest count where `toRaw`,
`check0`, `conforms0`, `enc` and `dec` all return, then halved. Bun 1.4.2,
bend 2.0.27, macOS arm64, Bun's default stack:

| shape | largest count that returns | next step throws |
|---|---|---|
| flat list | 12,288 | `check0: RangeError` |
| flat object | 6,144 | `check0: RangeError` |
| nested object | 10,637 | `check0: RangeError` |
| nested list | 10,639 | `check0: RangeError` |
| list of lists | > 30,000 (not the binding shape) | |
| list of objects | > 30,000 (not the binding shape) | |
| mixed | > 30,000 (not the binding shape) | |

The flat object binds first. Walking it costs one frame per key, and each
field's `lookup` scans the object from the front, so the last key is read with
one frame per key before it still on the stack: about two frames per counted
key, where a list costs one per element and a nest about one per level. Half
of 6,144 is **3,072**, which leaves the worst shape 2x its measured margin
(some 6,000 of the roughly 12,288 native frames bun has).

`codec.test.ts` holds this: at the budget every shape converts whole and
`check0`, `conforms0`, `enc` and `dec` all return; one past it, the node is
`TooLarge` at its path and the walk still returns; and what `toRaw` builds is
never past the budget. `bun src/measure_budget.ts` re-measures the table above.
Raising the budget past what the runtime walks, or a change that makes a walk
deeper, fails the gate.

The counted walk is quadratic in an object's key count (each field's lookup
scans from the front), so the flat object at the budget costs about 8 s per
call. The gate cannot skip it: it is the shape that binds the budget.

## Limits

- **A new `Raw` or `Schema` constructor touches every proof that enumerates
  them**, here and in each project whose proofs do (billing's): an abstract
  value makes every match stuck, so each case is written out. The cases are
  mechanical and were added by copying the nearest one (`RBool` beside
  `RStr`, `RTooBig` beside `RBad`). The generated case tables
  (`tools/case_arms.ts`) do most of it: a new reason in an `# arms why:` map
  is one line, and the recursive arms are the ones written by hand.
- **An absent slot's `Missing` and the codec's `TooLarge` share one helper**
  (`missing_or`): both say "what sits here is not a value the schema can use".
  `check` and every `defect` helper answer through it, which is what keeps the
  accuracy law true for the new reason without a case per combinator -- the
  price is that a value that is both absent and too big would report
  `Missing`, which the codec never builds.

| command | what it settles |
|---|---|
| `sh test.sh` | the gate: the laws (no unsafe code) and their mutants, the module (rebuilt and diffed against `dist-core/`), the tests, the types |
| `bun tools/bend_lib.ts core/core.bend dist-core` | the build: the core as a typed ES module, into the committed `dist-core/` |
| `LAW=exact bun tools/falsify.ts core/falsify/spec.ts` | a law on literal instances (from `core/falsify/`) |
