import Base
import ../core.bend as C

def nat_eq(+a: Nat, +b: Nat) -> Bool:
  Nat.is_eq(a, b)

def why_eq(x: C.Why, y: C.Why) -> Bool:
  match x y:
    case C.Missing{} C.Missing{}:
      True{}
    case C.NotNat{} C.NotNat{}:
      True{}
    case C.NotString{} C.NotString{}:
      True{}
    case C.UnknownKey{} C.UnknownKey{}:
      True{}
    case C.RepeatedKey{a} C.RepeatedKey{b}:
      String.eq(a, b)
    case C.NotList{} C.NotList{}:
      True{}
    case C.NotObject{} C.NotObject{}:
      True{}
    case C.NoElements{} C.NoElements{}:
      True{}
    case C.OpenNotLast{} C.OpenNotLast{}:
      True{}
    case C.LastNotOpen{} C.LastNotOpen{}:
      True{}
    case C.NotIncreasing{a, b} C.NotIncreasing{c, d}:
      Bool.and(Nat.is_eq(a, c), Nat.is_eq(b, d))
    case C.NotTrue{} C.NotTrue{}:
      True{}
    case C.NotOneOf{} C.NotOneOf{}:
      True{}
    case C.NoVariant{} C.NoVariant{}:
      True{}
    case C.TwoVariants{} C.TwoVariants{}:
      True{}
    case C.TooShort{} C.TooShort{}:
      True{}
    case C.TooLong{} C.TooLong{}:
      True{}
    case C.TooLarge{} C.TooLarge{}:
      True{}
    case _ _:
      False{}

def same(d: Maybe<&2, C.Why>, w: C.Why) -> Bool:
  match d:
    case None{}:
      False{}
    case Some{x}:
      why_eq(x, w)

# The accuracy law on one instance: whatever check reports, defect replays.
def acc_ok(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, +s: C.Schema, +r: C.Raw, m: Maybe<&2, C.Err>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{C.Err{p, w}}:
      same(C.defect(~rule, s, r, None{}, p), w)

# ---- the rules the falsifier instantiates the laws with ----
#
# no_rule is a project with no rules. r_any dispatches on the tag: 0 wants
# every element of a list value to be a positive number (its error at the
# element's index), or the scalar itself positive; 1 wants the value to be
# the tag itself. Each reports the first error with a path relative to the
# value it was given.

def no_rule(tag: Nat, r: C.Raw) -> Maybe<&2, C.Err>:
  None{}

def none_err(b: Bool) -> Maybe<&2, C.Err>:
  match b:
    case True{}:
      None{}
    case False{}:
      Some{C.Err{Nil{}, C.NotNat{}}}

def pos_rule(r: C.Raw) -> Maybe<&2, C.Err>:
  match r:
    case C.RNum{+n}:
      none_err(Nat.is_lt(0n, n))
    case _:
      Some{C.Err{Nil{}, C.NotNat{}}}

def bad_here(b: Bool, +i: Nat) -> Maybe<&2, C.Err>:
  match b:
    case True{}:
      None{}
    case False{}:
      Some{C.Err{C.AtIndex{i} <> Nil{}, C.NotNat{}}}

def elem_bad(h: C.Raw, +i: Nat) -> Maybe<&2, C.Err>:
  match h:
    case C.RNum{+n}:
      bad_here(Nat.is_lt(0n, n), i)
    case _:
      Some{C.Err{C.AtIndex{i} <> Nil{}, C.NotNat{}}}

def first_bad(r: C.Raw, +i: Nat) -> Maybe<&2, C.Err>:
  match r:
    case C.RNil{}:
      None{}
    case C.RCons{h, t}:
      C.first(elem_bad(h, i), C.later_l(first_bad(t, Nat.add(i, 1n))))
    case _:
      None{}

def tag_err(b: Bool) -> Maybe<&2, C.Err>:
  match b:
    case True{}:
      None{}
    case False{}:
      Some{C.Err{Nil{}, C.NotNat{}}}

def tag_rule(tag: Nat, r: C.Raw) -> Maybe<&2, C.Err>:
  match r:
    case C.RNum{+n}:
      tag_err(Nat.is_eq(n, tag))
    case _:
      Some{C.Err{Nil{}, C.NotNat{}}}

def by_tag(+tag: Nat, r: C.Raw) -> Maybe<&2, C.Err>:
  match tag r:
    case 0n C.RNil{}:
      None{}
    case 0n C.RCons{h, t}:
      C.first(elem_bad(h, 0n), C.later_l(first_bad(t, 1n)))
    case 0n x:
      pos_rule(x)
    case _ x:
      tag_rule(tag, x)

def r_any(tag: Nat, r: C.Raw) -> Maybe<&2, C.Err>:
  by_tag(tag, r)

# The tagged example, written by hand: the tag is read, the case gets the
# object with that key taken out, and an unknown tag is refused.
def rm_pick(b: Bool, +o: C.Raw, +keep: C.Raw) -> C.Raw:
  match b:
    case True{}:
      o
    case False{}:
      keep

def rm_first(+k: String, r: C.Raw) -> C.Raw:
  match r:
    case C.RKey{+j, +v, +o}:
      rm_pick(String.eq(j, k), o, C.RKey{j, v, rm_first(k, o)})
    case x:
      x

def second_type(r: C.Raw) -> C.Raw:
  C.lookup("type", rm_first("type", r))

def str_or_empty(v: C.Raw) -> String:
  match v:
    case C.RStr{x}:
      x
    case _:
      ""

def case_a(+r: C.Raw) -> Bool:
  C.conforms(~no_rule, C.SStrict{C.SField{"x", C.SNat{}, C.SEnd{}}}, rm_first("type", r), None{})

def case_b(+r: C.Raw) -> Bool:
  C.conforms(~no_rule, C.SField{"y", C.SStr{}, C.SEnd{}}, rm_first("type", r), None{})

def pick_b(b: Bool, +yes: Bool, +no: Bool) -> Bool:
  match b:
    case True{}:
      yes
    case False{}:
      no

# How many times "type" is a key of the object, counted here rather than read
# off the core's own walk: the tag key is read once, so one that stands twice
# says something the schema cannot mean.
def plus_one(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      (1n + n : Nat)
    case False{}:
      n

def type_count(r: C.Raw) -> Nat:
  match r:
    case C.RKey{j, v, o}:
      plus_one(String.eq(j, "type"), type_count(o))
    case x:
      0n

def once_type(r: C.Raw) -> Bool:
  Nat.is_le(type_count(r), 1n)

# An object whose tag is not a string (or absent) is refused, like one whose
# tag names no case; the string "" names no case here either. At the case the
# tag names, the tag key must also be there once: it is the key the case was
# chosen by, and a second one is unreachable.
def tagged_spec(+r: C.Raw) -> Bool:
  pick_b(String.eq(str_or_empty(C.lookup("type", r)), "a"), Bool.and(once_type(r), case_a(r)), pick_b(String.eq(str_or_empty(C.lookup("type", r)), "b"), Bool.and(once_type(r), case_b(r)), False{}))
