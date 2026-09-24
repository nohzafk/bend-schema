# Facts about Base that Base does not state: a value compares equal to
# itself, for Bool, Word, U32, Char and String.
#
# Each def returns an equation, so importing this file gives you a lemma you
# can rewrite with. `bend comparison.bend` is the gate: every def type-checks
# only because its proof goes through, so nothing here is axiomatized.
#
# Why this is needed at all: for an abstract value, `String.eq(x, x)` does
# not reduce. Equality goes to `cmp`, and `cmp` descends
#
#     String.eq -> String.cmp -> Char.cmp -> U32.cmp -> Word.cmp
#
# where `Word.cmp` recurses on the bits. Any program that branches on a
# runtime comparison therefore cannot be reasoned about symbolically until
# one of these is in scope.
#
# The ladder is one file because each step proves itself with the step below
# it. The order below is that dependency order.
#
# Direction: `%e : P` replaces the right-hand side of `e`'s equation with its
# left-hand side, so a lemma whose job is to turn a comparison into its
# answer is stated `{EQ{} == ...}` or `{True{} == ...}`.

import Base

# ---------- the bottom ----------

def bool_cmp_refl(b: Bool) -> {EQ{} == Bool.cmp(b, b) : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# ---------- the bits ----------

def word_cmp_refl(n: Nat, w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{ab, at}:
          %word_cmp_refl(p, at) : {EQ{} == Word.cmp.fin(ab, ab, _) : Cmp}
          %bool_cmp_refl(ab) : {EQ{} == _ : Cmp}
          {==}

def u32_cmp_refl(x: U32) -> {EQ{} == U32.cmp(x, x) : Cmp}:
  match x:
    case U32{w}:
      %word_cmp_refl(32n, w) : {EQ{} == _ : Cmp}
      {==}

# ---------- characters and strings ----------

def char_cmp_refl(c: Char) -> {((c, c), EQ{}) == Char.cmp(c, c) : (Char & Char) & Cmp}:
  match c:
    case Chr{x}:
      %u32_cmp_refl(x) : {((Chr{x}, Chr{x}), EQ{}) == ((Chr{x}, Chr{x}), _) : (Char & Char) & Cmp}
      {==}

def string_cmp_refl(s: String) -> {((s, s), EQ{}) == String.cmp(s, s) : (String & String) & Cmp}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          %u32_cmp_refl(x) : {((SCon{Chr{x}, t}, SCon{Chr{x}, t}), EQ{}) == String.cmp.fin(t, t, ((Chr{x}, Chr{x}), _)) : (String & String) & Cmp}
          %string_cmp_refl(t) : {((SCon{Chr{x}, t}, SCon{Chr{x}, t}), EQ{}) == String.cmp.rec(Chr{x}, Chr{x}, _) : (String & String) & Cmp}
          {==}

def string_eq_refl(s: String) -> {True{} == String.eq(s, s) : Bool}:
  %string_cmp_refl(s) : {True{} == String.eq.fin(_) : Bool}
  {==}
