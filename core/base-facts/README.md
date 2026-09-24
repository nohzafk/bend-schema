# base-facts

Facts about Base that Base does not state, proven here once and imported
where they are needed: `core/PROOF.bend` imports all three.

## The policy

This directory accumulates **self-contained lemma files**. A file belongs
here when:

- it is about Base, not about one project in this repo;
- it imports nothing but `Base` (so it can be copied, pinned, or published
  on its own);
- every def returns an equation, which is what makes it a lemma rather than
  a function;
- `bend <file>` passes, which is the whole proof obligation.

Nothing here is published to the hub. Publishing uploads bytes and mints a
new content hash -- a deliberate step, taken file by file, and not taken for
anything here yet. These files are therefore also not a pull request against
`bendlang/bend`: the author may prefer not to carry them, and adding them
later is cheap.

## What is here

| file | about | defs |
|---|---|---|
| `comparison.bend` | that a value compares equal to itself: the `Bool` → `Word` → `U32` → `Char` → `String` ladder | `bool_cmp_refl`, `word_cmp_refl`, `u32_cmp_refl`, `char_cmp_refl`, `string_cmp_refl`, `string_eq_refl` |
| `string_eq.bend` | that `String.eq` is sound: `String.eq(a, b) == True` gives `a == b`, down the same ladder (bits, `U32`, `Char`, `String`). Carries its own `Tag2`/`ff` | `bool_eq_sound`, `word_eq_sound`, `u32_eq_sound`, `char_eq_sound`, `string_eq_sound` |
| `nat_le.bend` | that `Nat` comparison is reflexive, in both orientations, that zero is below everything, and that a witness `b == a + k` gives the order | `cmp_refl_r`, `cmp_refl`, `is_eq_refl`, `le_refl`, `le_zero_l`, `le_zero_l_r`, `le_add`, `lt_add` |

`test.sh` type-checks every file and then makes one fact false to confirm the
check can fail.

## Where these came from

Copied, byte-identical, from `~/projects/bend2-play/base-facts/` as of
2026-09-24, when the schema library moved out into this repository. The other
files in that directory (`nat.bend`, `nat_div.bend`, `nat_order.bend`,
`nat_cmp.bend`, `string.bend`, `list.bend`) are not here: nothing this core
proves imports them, and a fact that nothing imports is a fact this gate does
not need to keep proving. Taking one of them, and its control in `test.sh`,
is a copy and a line in `FILES`.

## Using one

Every def returns an equation, so an import gives you a lemma:

```bend
import ./base-facts/comparison.bend as CMP
...
%CMP.string_eq_refl(s) : {... _ ...}
```

`%e : P` rewrites with `e`: `P` is the goal with `_` marking the eliminated
side of `e`'s equation. That is why the facts here are stated with the form to
be *eliminated* on the right: `{True{} == String.eq(s, s)}` is what turns a
comparison into `True{}`.

## Why the reflexivity facts are needed

For an abstract value, `String.eq(x, x)` and `Nat.is_eq(n, n)` do **not**
reduce. The checker keeps the call:

```
expected : String.eq.fin(String.cmp(s, s))
observed : True{}
```

Equality goes to `cmp`, and `cmp` descends `String.eq` → `String.cmp` →
`Char.cmp` → `U32.cmp` → `Word.cmp`, where `Word.cmp` recurses on the bits.
Nothing in that chain can run while the value is abstract, so any program
that branches on a runtime comparison is unreachable to the proof system
until one of these is in scope.

Supplying the fact is the whole job: one induction on the width, then one
induction on the string.
