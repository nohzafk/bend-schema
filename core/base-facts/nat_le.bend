# Facts about Nat that Base does not state: comparison is reflexive in both
# orientations, and zero is below everything.
#
# Each def returns an equation, so importing this file gives you a lemma you
# can rewrite with. `bend nat_le.bend` is the gate: every def type-checks
# only because its proof goes through, so nothing here is axiomatized.
#
# Directions come in pairs where both are useful. `%e : P` replaces the
# right-hand side of `e`'s equation with its left-hand side, so `cmp_refl_r`
# turns an occurrence of `Nat.cmp(a, a)` into `EQ{}`, while `cmp_refl` turns
# `EQ{}` into that call.

import Base

# ---------- a value compares equal to itself ----------

def cmp_refl_r(a: Nat) -> {EQ{} == Nat.cmp(a, a) : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %cmp_refl_r(p) : {EQ{} == _ : Cmp}
      {==}

def cmp_refl(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  %cmp_refl_r(a) : {_ == EQ{} : Cmp}
  {==}

def is_eq_refl(a: Nat) -> {True{} == Nat.is_eq(a, a) : Bool}:
  %cmp_refl_r(a) : {True{} == Cmp.is_eq(_) : Bool}
  {==}

# `Nat.cmp` returns a `Cmp`, so any `is_*` question about a value and itself
# answers `True{}` once `cmp_refl_r` has been applied.

def le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  %cmp_refl_r(a) : {Cmp.is_le(_) == True{} : Bool}
  {==}

# ---------- zero is below everything ----------

def le_zero_l(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_zero_l_r(a: Nat) -> {True{} == Nat.is_le(0n, a) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# ---------- a witness gives the order ----------
#
# The step from a witness equation (b == a + k) to the Bool a proof states.
# Nat.cmp and Nat.add both recurse on the left, so each is one induction on
# `a`, and the successor case is the hypothesis. `k` is the witness; neither
# lemma needs to know anything about it.

def le_add(a: Nat, +k: Nat) -> {True{} == Nat.is_le(a, Nat.add(a, k)) : Bool}:
  match a:
    case 0n:
      le_zero_l_r(k)
    case 1n+p:
      le_add(p, k)

def lt_add(a: Nat, +k: Nat) -> {True{} == Nat.is_lt(a, Nat.add(a, 1n+k)) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      lt_add(p, k)
