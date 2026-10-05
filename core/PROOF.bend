import Base
import ./LAWS.bend as Laws
import ./core.bend as C
import bend-mathlib@0.7.1.0/string.bend as MS
import bend-mathlib@0.7.1.0/nat.bend as MN

# The proofs of bend-schema's laws. The gate is `bend core/PROOF.bend` (through
# tools/bend-check). Each law's proof sits under its own
# "# ---- name ----" header, which core/check_mutants.ts relies on.

# ---- tools: what first, under and the rest do to "nothing found" ----
#
# Each lemma is stated {simple == complex}, so that a rewrite replaces the
# complex side.

def Tag(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def to_empty(e: {False{} == True{} : Bool}) -> Empty:
  %e : Tag(_)
  Unit{}

def none_first(m: Maybe<&2, C.Err>, n: Maybe<&2, C.Err>) -> {Bool.and(Maybe.is_none(&2, C.Err, m), Maybe.is_none(&2, C.Err, n)) == Maybe.is_none(&2, C.Err, C.first(m, n)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

# is_none(in_err(b, w)) is b: a failing test becomes an error, and the error
# was made only where the test failed. A rule's bound and a constructor's are
# the same test, so both readings use this.
def in_err_none(b: Bool, +w: C.Why) -> {Maybe.is_none(&2, C.Err, C.in_err(b, w)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# is_none(len_err(lo, hi, r)) is len_ok(lo, hi, r), for every value: at an
# SStrLen the bound is the same test read two ways, and a value that is not a
# string is not in bounds (it is refused as NotString, and len_ok is False).
def len_err_none(+lo: Nat, +hi: Nat, r: C.Raw) -> {Maybe.is_none(&2, C.Err, C.len_err(lo, hi, r)) == C.len_ok(lo, hi, r) : Bool}:
  match r:
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{+x}:
      in_err_none(C.str_len_ok(lo, hi, x), C.LengthNotIn{lo, hi})
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h_, t_}:
      {==}
    case C.REnd{}:
      {==}
    case C.RKey{k_, v_, o_}:
      {==}

# is_none(count_err(lo, hi, r)) is list_len_ok(lo, hi, r), for every value: at
# an SListLen the count is the same test read two ways. A list out of bounds is
# CountNotIn at the list's own path, and a value that is not a list is refused
# by count_err (NotList, Missing, TooLarge) exactly where list_len_ok is False.
def count_err_none(+lo: Nat, +hi: Nat, r: C.Raw) -> {Maybe.is_none(&2, C.Err, C.count_err(lo, hi, r)) == C.list_len_ok(lo, hi, r) : Bool}:
  match r:
    case C.RNil{}:
      in_err_none(C.list_len_ok(lo, hi, r), C.CountNotIn{lo, hi})
    case C.RCons{+h, +t}:
      in_err_none(C.list_len_ok(lo, hi, r), C.CountNotIn{lo, hi})
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{s_}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.REnd{}:
      {==}
    case C.RKey{k_, v_, o_}:
      {==}

def none_under(+st: C.Step, m: Maybe<&2, C.Err>) -> {Maybe.is_none(&2, C.Err, m) == Maybe.is_none(&2, C.Err, C.under(st, m)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{C.Err{p, w}}:
      {==}

def none_later_i(m: Maybe<&2, C.Err>) -> {Maybe.is_none(&2, C.Err, m) == Maybe.is_none(&2, C.Err, C.later_i(m)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{C.Err{p, w}}:
      {==}

def none_later_l(m: Maybe<&2, C.Err>) -> {Maybe.is_none(&2, C.Err, m) == Maybe.is_none(&2, C.Err, C.later_l(m)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{C.Err{p, w}}:
      {==}

def none_later_f(m: Maybe<&2, C.Err>) -> {Maybe.is_none(&2, C.Err, m) == Maybe.is_none(&2, C.Err, C.later_f(m)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{C.Err{p, w}}:
      {==}

def none_true(b: Bool) -> {Maybe.is_none(&2, C.Err, C.true_err(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def none_enum(b: Bool) -> {Maybe.is_none(&2, C.Err, C.enum_err(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# b is is_none(key_err(b, name)): the repeated-key test becomes an error
# exactly where key_once says the key is not read once. Stated simple first so
# that a rewrite replaces the error back with the test.
def none_key_err(b: Bool, +name: String) -> {b == Maybe.is_none(&2, C.Err, C.key_err(b, name)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def none_dup_step(b: Bool, +n: String, +rr: C.Schema, +r: C.Raw, ih: {Maybe.is_none(&2, C.Err, C.dup_err(rr, r)) == C.none_present(rr, r) : Bool}) -> {Maybe.is_none(&2, C.Err, C.pick_err(b, C.later_f(C.dup_err(rr, r)), Some{C.Err{C.AtField{0n, n} <> Nil{}, C.TwoVariants{}}})) == Bool.and(b, C.none_present(rr, r)) : Bool}:
  match b:
    case True{}:
      %none_later_f(C.dup_err(rr, r)) : {_ == C.none_present(rr, r) : Bool}
      ih
    case False{}:
      {==}

# dup_err finds nothing exactly when none of the keys is there.
# arms: s
# arms leaf: {==}
def none_dup(s: C.Schema, +r: C.Raw) -> {Maybe.is_none(&2, C.Err, C.dup_err(s, r)) == C.none_present(s, r) : Bool}:
  match s:
    case C.SNat{}:
      {==}
    case C.SNatIn{lo_, hi_}:
      {==}
    case C.SStr{}:
      {==}
    case C.SStrLen{lo_, hi_, s_}:
      {==}
    case C.SOpt{inner_}:
      {==}
    case C.SList{elem_}:
      {==}
    case C.SField{name_, s_, rest_}:
      {==}
    case C.SEnd{}:
      {==}
    case C.SRule{s_, tag_}:
      {==}
    case C.SStrict{s_}:
      {==}
    case C.STagged{key_, name_, s_, rest_}:
      {==}
    case C.STagEnd{key_}:
      {==}
    case C.SBool{}:
      {==}
    case C.STrue{}:
      {==}
    case C.SEnum{names_}:
      {==}
    case C.SVariant{+vn, vv, +vr}:
      none_dup_step(C.is_missing(C.lookup(vn, r)), vn, vr, r, none_dup(vr, r))
    case C.SVEnd{}:
      {==}
    case C.STuple{s_, rest_}:
      {==}
    case C.STEnd{}:
      {==}
    case C.SOptional{inner_}:
      {==}
    case C.SListLen{lo_, hi_, s_}:
      {==}

# ---- tools: a tagged case, one side or the other ----

def tag_exact(b: Bool, +m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +c1: Bool, +c2: Bool, e1: {Maybe.is_none(&2, C.Err, m1) == c1 : Bool}, e2: {Maybe.is_none(&2, C.Err, m2) == c2 : Bool}) -> {Maybe.is_none(&2, C.Err, C.pick_err(b, m1, m2)) == C.pick_bool(b, c1, c2) : Bool}:
  match b:
    case True{}:
      e1
    case False{}:
      e2

# The tag key's own repeated test stands in front of the case's check, exactly
# as a field key's does in front of a field's: the key's error first, then the
# case. So where the tag is the case's name the pick's answer is the key's test
# conjoined to the case's, and the pick's two answers are tag_exact's. kc is
# whether the tag key is read once, ek that test as a report -- what check asks
# key_err for.
def tag_exact_k(kc: Bool, b: Bool, +m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +c1: Bool, +c2: Bool, +name: String, ek: {kc == Maybe.is_none(&2, C.Err, C.key_err(kc, name)) : Bool}, et: {Maybe.is_none(&2, C.Err, C.pick_err(b, m1, m2)) == C.pick_bool(b, c1, c2) : Bool}) -> {Maybe.is_none(&2, C.Err, C.pick_err(b, C.first(C.key_err(kc, name), m1), m2)) == C.pick_bool(b, Bool.and(kc, c1), c2) : Bool}:
  match b:
    case True{}:
      %none_first(C.key_err(kc, name), m1) : {_ == Bool.and(kc, c1) : Bool}
      %ek : {Bool.and(_, Bool.not(Maybe.is_some(&2, C.Err, m1))) == Bool.and(kc, c1) : Bool}
      %et : {Bool.and(kc, Bool.not(Maybe.is_some(&2, C.Err, m1))) == Bool.and(kc, _) : Bool}
      {==}
    case False{}:
      et

def tag_acc(b: Bool, +m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +d1: Maybe<&2, C.Why>, +d2: Maybe<&2, C.Why>, +path: List<&2, C.Step>, +why: C.Why, h: {C.pick_err(b, m1, m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, i1: {m1 == Some{C.Err{path, why}} : Maybe<&2, C.Err>} -> {d1 == Some{why} : Maybe<&2, C.Why>}, i2: {m2 == Some{C.Err{path, why}} : Maybe<&2, C.Err>} -> {d2 == Some{why} : Maybe<&2, C.Why>}) -> {C.pick_why(b, d1, d2) == Some{why} : Maybe<&2, C.Why>}:
  match b:
    case True{}:
      i1(h)
    case False{}:
      i2(h)

# ---- check finds nothing exactly when the value conforms ----
#
# The same walk as check and conforms, case by case. A leaf case computes on
# both sides; a step case turns "nothing found" in a first/under/later into an
# and of the parts (the tools), then rewrites each part with the recursive
# call, which is the induction hypothesis.

#
# extra_err finds nothing exactly when no_extra holds: the same walk, a
# pick_err where no_extra has a Bool.and.

def extra_exact_step(b: Bool, +x: Maybe<&2, C.Err>, +e: C.Err, +d: Bool, ih: {Maybe.is_none(&2, C.Err, x) == d : Bool}) -> {Maybe.is_none(&2, C.Err, C.pick_err(b, x, Some{e})) == Bool.and(b, d) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

def extra_exact(+ns: List<&2, String>, r: C.Raw) -> {Maybe.is_none(&2, C.Err, C.extra_err(ns, r)) == C.no_extra(ns, r) : Bool}:
  match r:
    case C.RKey{+k, v, +o}:
      extra_exact_step(C.in_names(k, ns), C.extra_err(ns, o), C.Err{C.AtKey{k} <> Nil{}, C.UnknownKey{}}, C.no_extra(ns, o), extra_exact(ns, o))
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{s_}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h_, t_}:
      {==}
    case C.REnd{}:
      {==}

# A variant: the key absent, go on with the rest; present, its value must
# conform and no later key may be there.
def var_exact(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, b: Bool, +vn: String, +vv: C.Schema, +vr: C.Schema, +r: C.Raw, ih1: {Maybe.is_none(&2, C.Err, C.check(~rule, vr, r, None{})) == C.conforms(~rule, vr, r, None{}) : Bool}, ih2: {Maybe.is_none(&2, C.Err, C.check(~rule, vv, C.lookup(vn, r), None{})) == C.conforms(~rule, vv, C.lookup(vn, r), None{}) : Bool}, nd: {Maybe.is_none(&2, C.Err, C.dup_err(vr, r)) == C.none_present(vr, r) : Bool}) -> {Maybe.is_none(&2, C.Err, C.pick_err(b, C.later_f(C.check(~rule, vr, r, None{})), C.first(C.key_err(C.key_once_at(r, False{}, vn), vn), C.first(C.under(C.AtField{0n, vn}, C.check(~rule, vv, C.lookup(vn, r), None{})), C.later_f(C.dup_err(vr, r)))))) == C.pick_bool(b, C.conforms(~rule, vr, r, None{}), Bool.and(C.key_once_at(r, False{}, vn), Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.none_present(vr, r)))) : Bool}:
  match b:
    case True{}:
      %none_later_f(C.check(~rule, vr, r, None{})) : {_ == C.conforms(~rule, vr, r, None{}) : Bool}
      ih1
    case False{}:
      %none_first(C.key_err(C.key_once_at(r, False{}, vn), vn), C.first(C.under(C.AtField{0n, vn}, C.check(~rule, vv, C.lookup(vn, r), None{})), C.later_f(C.dup_err(vr, r)))) : {_ == Bool.and(C.key_once_at(r, False{}, vn), Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.none_present(vr, r))) : Bool}
      %none_key_err(C.key_once_at(r, False{}, vn), vn) : {Bool.and(_, Maybe.is_none(&2, C.Err, C.first(C.under(C.AtField{0n, vn}, C.check(~rule, vv, C.lookup(vn, r), None{})), C.later_f(C.dup_err(vr, r))))) == Bool.and(C.key_once_at(r, False{}, vn), Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.none_present(vr, r))) : Bool}
      %none_first(C.under(C.AtField{0n, vn}, C.check(~rule, vv, C.lookup(vn, r), None{})), C.later_f(C.dup_err(vr, r))) : {Bool.and(C.key_once_at(r, False{}, vn), _) == Bool.and(C.key_once_at(r, False{}, vn), Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.none_present(vr, r))) : Bool}
      %none_under(C.AtField{0n, vn}, C.check(~rule, vv, C.lookup(vn, r), None{})) : {Bool.and(C.key_once_at(r, False{}, vn), Bool.and(_, Maybe.is_none(&2, C.Err, C.later_f(C.dup_err(vr, r))))) == Bool.and(C.key_once_at(r, False{}, vn), Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.none_present(vr, r))) : Bool}
      %none_later_f(C.dup_err(vr, r)) : {Bool.and(C.key_once_at(r, False{}, vn), Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, vv, C.lookup(vn, r), None{})), _)) == Bool.and(C.key_once_at(r, False{}, vn), Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.none_present(vr, r))) : Bool}
      %ih2 : {Bool.and(C.key_once_at(r, False{}, vn), Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, vv, C.lookup(vn, r), None{})), Maybe.is_none(&2, C.Err, C.dup_err(vr, r)))) == Bool.and(C.key_once_at(r, False{}, vn), Bool.and(_, C.none_present(vr, r))) : Bool}
      %nd : {Bool.and(C.key_once_at(r, False{}, vn), Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, vv, C.lookup(vn, r), None{})), Maybe.is_none(&2, C.Err, C.dup_err(vr, r)))) == Bool.and(C.key_once_at(r, False{}, vn), Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, vv, C.lookup(vn, r), None{})), _)) : Bool}
      {==}

# arms: s r
# arms leaf: {==}
def exact(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, s: C.Schema, r: C.Raw, +prev: Maybe<&2, Nat>) -> {Maybe.is_none(&2, C.Err, C.check(~rule, s, r, prev)) == C.conforms(~rule, s, r, prev) : Bool}:
  match s r:
    case C.SNat{} C.RNum{n}:
      {==}
    case C.SNat{} C.RBool{bb}:
      {==}
    case C.SNat{} C.RNull{}:
      {==}
    case C.SNat{} C.RStr{x}:
      {==}
    case C.SNat{} C.RBad{}:
      {==}
    case C.SNat{} C.RTooBig{}:
      {==}
    case C.SNat{} C.RMissing{}:
      {==}
    case C.SNat{} C.RNil{}:
      {==}
    case C.SNat{} C.RCons{h, t}:
      {==}
    case C.SNat{} C.REnd{}:
      {==}
    case C.SNat{} C.RKey{k, v, o}:
      {==}
    case C.SNatIn{+lo, +hi} C.RNum{+n}:
      in_err_none(C.num_ok(lo, hi, n), C.NotIn{lo, hi})
    case C.SNatIn{+lo, +hi} C.RBool{bb}:
      {==}
    case C.SNatIn{+lo, +hi} C.RNull{}:
      {==}
    case C.SNatIn{+lo, +hi} C.RStr{x}:
      {==}
    case C.SNatIn{+lo, +hi} C.RBad{}:
      {==}
    case C.SNatIn{+lo, +hi} C.RTooBig{}:
      {==}
    case C.SNatIn{+lo, +hi} C.RMissing{}:
      {==}
    case C.SNatIn{+lo, +hi} C.RNil{}:
      {==}
    case C.SNatIn{+lo, +hi} C.RCons{h, t}:
      {==}
    case C.SNatIn{+lo, +hi} C.REnd{}:
      {==}
    case C.SNatIn{+lo, +hi} C.RKey{k, v, o}:
      {==}
    case C.SStr{} C.RNum{n}:
      {==}
    case C.SStr{} C.RBool{bb}:
      {==}
    case C.SStr{} C.RNull{}:
      {==}
    case C.SStr{} C.RStr{x}:
      {==}
    case C.SStr{} C.RBad{}:
      {==}
    case C.SStr{} C.RTooBig{}:
      {==}
    case C.SStr{} C.RMissing{}:
      {==}
    case C.SStr{} C.RNil{}:
      {==}
    case C.SStr{} C.RCons{h, t}:
      {==}
    case C.SStr{} C.REnd{}:
      {==}
    case C.SStr{} C.RKey{k, v, o}:
      {==}
    case C.SStrLen{+lo, +hi, +s2} +x:
      %none_first(C.check(~rule, s2, x, prev), C.len_err(lo, hi, x)) : {_ == Bool.and(C.conforms(~rule, s2, x, prev), C.len_ok(lo, hi, x)) : Bool}
      %exact(~rule, s2, x, prev) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, s2, x, prev)), Maybe.is_none(&2, C.Err, C.len_err(lo, hi, x))) == Bool.and(_, C.len_ok(lo, hi, x)) : Bool}
      %len_err_none(lo, hi, x) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, s2, x, prev)), Maybe.is_none(&2, C.Err, C.len_err(lo, hi, x))) == Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, s2, x, prev)), _) : Bool}
      {==}
    case C.SOpt{inner} C.RNum{n}:
      exact(~rule, inner, C.RNum{n}, None{})
    case C.SOpt{inner} C.RBool{bb}:
      exact(~rule, inner, C.RBool{bb}, None{})
    case C.SOpt{inner} C.RNull{}:
      {==}
    case C.SOpt{inner} C.RStr{x}:
      exact(~rule, inner, C.RStr{x}, None{})
    case C.SOpt{inner} C.RBad{}:
      exact(~rule, inner, C.RBad{}, None{})
    case C.SOpt{inner} C.RTooBig{}:
      exact(~rule, inner, C.RTooBig{}, None{})
    case C.SOpt{inner} C.RMissing{}:
      exact(~rule, inner, C.RMissing{}, None{})
    case C.SOpt{inner} C.RNil{}:
      exact(~rule, inner, C.RNil{}, None{})
    case C.SOpt{inner} C.RCons{h, t}:
      exact(~rule, inner, C.RCons{h, t}, None{})
    case C.SOpt{inner} C.REnd{}:
      exact(~rule, inner, C.REnd{}, None{})
    case C.SOpt{inner} C.RKey{k, v, o}:
      exact(~rule, inner, C.RKey{k, v, o}, None{})
    case C.SList{+e} C.RNum{n}:
      {==}
    case C.SList{+e} C.RBool{bb}:
      {==}
    case C.SList{+e} C.RNull{}:
      {==}
    case C.SList{+e} C.RStr{x}:
      {==}
    case C.SList{+e} C.RBad{}:
      {==}
    case C.SList{+e} C.RTooBig{}:
      {==}
    case C.SList{+e} C.RMissing{}:
      {==}
    case C.SList{+e} C.RNil{}:
      {==}
    case C.SList{+e} C.RCons{+h, +t}:
      %none_first(C.under(C.AtIndex{0n}, C.check(~rule, e, h, None{})), C.later_l(C.check(~rule, C.SList{e}, t, None{}))) : {_ == Bool.and(C.conforms(~rule, e, h, None{}), C.conforms(~rule, C.SList{e}, t, None{})) : Bool}
      %none_under(C.AtIndex{0n}, C.check(~rule, e, h, None{})) : {Bool.and(_, Maybe.is_none(&2, C.Err, C.later_l(C.check(~rule, C.SList{e}, t, None{})))) == Bool.and(C.conforms(~rule, e, h, None{}), C.conforms(~rule, C.SList{e}, t, None{})) : Bool}
      %none_later_l(C.check(~rule, C.SList{e}, t, None{})) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, e, h, None{})), _) == Bool.and(C.conforms(~rule, e, h, None{}), C.conforms(~rule, C.SList{e}, t, None{})) : Bool}
      %exact(~rule, e, h, None{}) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, e, h, None{})), Maybe.is_none(&2, C.Err, C.check(~rule, C.SList{e}, t, None{}))) == Bool.and(_, C.conforms(~rule, C.SList{e}, t, None{})) : Bool}
      %exact(~rule, C.SList{e}, t, None{}) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, e, h, None{})), Maybe.is_none(&2, C.Err, C.check(~rule, C.SList{e}, t, None{}))) == Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, e, h, None{})), _) : Bool}
      {==}
    case C.SList{+e} C.REnd{}:
      {==}
    case C.SList{+e} C.RKey{k, v, o}:
      {==}
    case C.SField{+name, +fs, +rest} C.RNum{n}:
      {==}
    case C.SField{+name, +fs, +rest} C.RBool{bb}:
      {==}
    case C.SField{+name, +fs, +rest} C.RNull{}:
      {==}
    case C.SField{+name, +fs, +rest} C.RStr{x}:
      {==}
    case C.SField{+name, +fs, +rest} C.RBad{}:
      {==}
    case C.SField{+name, +fs, +rest} C.RTooBig{}:
      {==}
    case C.SField{+name, +fs, +rest} C.RMissing{}:
      {==}
    case C.SField{+name, +fs, +rest} C.RNil{}:
      {==}
    case C.SField{+name, +fs, +rest} C.RCons{h, t}:
      {==}
    case C.SField{+name, +fs, +rest} C.REnd{}:
      %none_first(C.under(C.AtField{0n, name}, C.check(~rule, fs, C.RMissing{}, None{})), C.later_f(C.check(~rule, rest, C.REnd{}, None{}))) : {_ == Bool.and(C.conforms(~rule, fs, C.RMissing{}, None{}), C.conforms(~rule, rest, C.REnd{}, None{})) : Bool}
      %none_under(C.AtField{0n, name}, C.check(~rule, fs, C.RMissing{}, None{})) : {Bool.and(_, Maybe.is_none(&2, C.Err, C.later_f(C.check(~rule, rest, C.REnd{}, None{})))) == Bool.and(C.conforms(~rule, fs, C.RMissing{}, None{}), C.conforms(~rule, rest, C.REnd{}, None{})) : Bool}
      %none_later_f(C.check(~rule, rest, C.REnd{}, None{})) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, fs, C.RMissing{}, None{})), _) == Bool.and(C.conforms(~rule, fs, C.RMissing{}, None{}), C.conforms(~rule, rest, C.REnd{}, None{})) : Bool}
      %exact(~rule, fs, C.RMissing{}, None{}) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, fs, C.RMissing{}, None{})), Maybe.is_none(&2, C.Err, C.check(~rule, rest, C.REnd{}, None{}))) == Bool.and(_, C.conforms(~rule, rest, C.REnd{}, None{})) : Bool}
      %exact(~rule, rest, C.REnd{}, None{}) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, fs, C.RMissing{}, None{})), Maybe.is_none(&2, C.Err, C.check(~rule, rest, C.REnd{}, None{}))) == Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, fs, C.RMissing{}, None{})), _) : Bool}
      {==}
    case C.SField{+name, +fs, +rest} C.RKey{+k, +v, +o}:
      %none_first(C.key_err(C.key_once_at(o, String.eq(k, name), name), name), C.first(C.under(C.AtField{0n, name}, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{})), C.later_f(C.check(~rule, rest, C.RKey{k, v, o}, None{})))) : {_ == Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(C.conforms(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}), C.conforms(~rule, rest, C.RKey{k, v, o}, None{}))) : Bool}
      %none_key_err(C.key_once_at(o, String.eq(k, name), name), name) : {Bool.and(_, Maybe.is_none(&2, C.Err, C.first(C.under(C.AtField{0n, name}, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{})), C.later_f(C.check(~rule, rest, C.RKey{k, v, o}, None{}))))) == Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(C.conforms(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}), C.conforms(~rule, rest, C.RKey{k, v, o}, None{}))) : Bool}
      %none_first(C.under(C.AtField{0n, name}, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{})), C.later_f(C.check(~rule, rest, C.RKey{k, v, o}, None{}))) : {Bool.and(C.key_once_at(o, String.eq(k, name), name), _) == Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(C.conforms(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}), C.conforms(~rule, rest, C.RKey{k, v, o}, None{}))) : Bool}
      %none_under(C.AtField{0n, name}, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{})) : {Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(_, Maybe.is_none(&2, C.Err, C.later_f(C.check(~rule, rest, C.RKey{k, v, o}, None{}))))) == Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(C.conforms(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}), C.conforms(~rule, rest, C.RKey{k, v, o}, None{}))) : Bool}
      %none_later_f(C.check(~rule, rest, C.RKey{k, v, o}, None{})) : {Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{})), _)) == Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(C.conforms(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}), C.conforms(~rule, rest, C.RKey{k, v, o}, None{}))) : Bool}
      %exact(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}) : {Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{})), Maybe.is_none(&2, C.Err, C.check(~rule, rest, C.RKey{k, v, o}, None{})))) == Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(_, C.conforms(~rule, rest, C.RKey{k, v, o}, None{}))) : Bool}
      %exact(~rule, rest, C.RKey{k, v, o}, None{}) : {Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{})), Maybe.is_none(&2, C.Err, C.check(~rule, rest, C.RKey{k, v, o}, None{})))) == Bool.and(C.key_once_at(o, String.eq(k, name), name), Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{})), _)) : Bool}
      {==}
    case C.SEnd{} C.RNum{n}:
      {==}
    case C.SEnd{} C.RBool{bb}:
      {==}
    case C.SEnd{} C.RNull{}:
      {==}
    case C.SEnd{} C.RStr{x}:
      {==}
    case C.SEnd{} C.RBad{}:
      {==}
    case C.SEnd{} C.RTooBig{}:
      {==}
    case C.SEnd{} C.RMissing{}:
      {==}
    case C.SEnd{} C.RNil{}:
      {==}
    case C.SEnd{} C.RCons{h, t}:
      {==}
    case C.SEnd{} C.REnd{}:
      {==}
    case C.SEnd{} C.RKey{k, v, o}:
      {==}
    case C.SRule{+s2, +tag} +x:
      %none_first(C.check(~rule, s2, x, prev), rule(tag, x)) : {_ == Bool.and(C.conforms(~rule, s2, x, prev), Maybe.is_none(&2, C.Err, rule(tag, x))) : Bool}
      %exact(~rule, s2, x, prev) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, s2, x, prev)), Maybe.is_none(&2, C.Err, rule(tag, x))) == Bool.and(_, Maybe.is_none(&2, C.Err, rule(tag, x))) : Bool}
      {==}
    case C.SStrict{+s2} +x:
      %none_first(C.check(~rule, s2, x, prev), C.extra_err(C.key_names(s2), x)) : {_ == Bool.and(C.conforms(~rule, s2, x, prev), C.no_extra(C.key_names(s2), x)) : Bool}
      %exact(~rule, s2, x, prev) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, s2, x, prev)), Maybe.is_none(&2, C.Err, C.extra_err(C.key_names(s2), x))) == Bool.and(_, C.no_extra(C.key_names(s2), x)) : Bool}
      %extra_exact(C.key_names(s2), x) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, s2, x, prev)), Maybe.is_none(&2, C.Err, C.extra_err(C.key_names(s2), x))) == Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, s2, x, prev)), _) : Bool}
      {==}
    case C.STagged{+k, +n, +cs, +rest} +x:
      tag_exact_k(C.key_once(k, x), C.is_tag(k, n, x), C.check(~rule, cs, C.drop_key(k, x), None{}), C.check(~rule, rest, x, None{}), C.conforms(~rule, cs, C.drop_key(k, x), None{}), C.conforms(~rule, rest, x, None{}), k, none_key_err(C.key_once(k, x), k), tag_exact(C.is_tag(k, n, x), C.check(~rule, cs, C.drop_key(k, x), None{}), C.check(~rule, rest, x, None{}), C.conforms(~rule, cs, C.drop_key(k, x), None{}), C.conforms(~rule, rest, x, None{}), exact(~rule, cs, C.drop_key(k, x), None{}), exact(~rule, rest, x, None{})))
    case C.STagEnd{key_} C.RNum{n}:
      {==}
    case C.STagEnd{key_} C.RBool{bb}:
      {==}
    case C.STagEnd{key_} C.RNull{}:
      {==}
    case C.STagEnd{key_} C.RStr{x}:
      {==}
    case C.STagEnd{key_} C.RBad{}:
      {==}
    case C.STagEnd{key_} C.RTooBig{}:
      {==}
    case C.STagEnd{key_} C.RMissing{}:
      {==}
    case C.STagEnd{key_} C.RNil{}:
      {==}
    case C.STagEnd{key_} C.RCons{h, t}:
      {==}
    case C.STagEnd{key_} C.REnd{}:
      {==}
    case C.STagEnd{key_} C.RKey{k, v, o}:
      {==}
    case C.SBool{} C.RNum{n}:
      {==}
    case C.SBool{} C.RBool{bb}:
      {==}
    case C.SBool{} C.RNull{}:
      {==}
    case C.SBool{} C.RStr{x}:
      {==}
    case C.SBool{} C.RBad{}:
      {==}
    case C.SBool{} C.RTooBig{}:
      {==}
    case C.SBool{} C.RMissing{}:
      {==}
    case C.SBool{} C.RNil{}:
      {==}
    case C.SBool{} C.RCons{h, t}:
      {==}
    case C.SBool{} C.REnd{}:
      {==}
    case C.SBool{} C.RKey{k, v, o}:
      {==}
    case C.STrue{} C.RNum{n}:
      {==}
    case C.STrue{} C.RBool{bb}:
      none_true(bb)
    case C.STrue{} C.RNull{}:
      {==}
    case C.STrue{} C.RStr{x}:
      {==}
    case C.STrue{} C.RBad{}:
      {==}
    case C.STrue{} C.RTooBig{}:
      {==}
    case C.STrue{} C.RMissing{}:
      {==}
    case C.STrue{} C.RNil{}:
      {==}
    case C.STrue{} C.RCons{h, t}:
      {==}
    case C.STrue{} C.REnd{}:
      {==}
    case C.STrue{} C.RKey{k, v, o}:
      {==}
    case C.SEnum{+ns} C.RNum{n}:
      {==}
    case C.SEnum{+ns} C.RBool{bb}:
      {==}
    case C.SEnum{+ns} C.RNull{}:
      {==}
    case C.SEnum{+ns} C.RStr{+x}:
      none_enum(C.in_names(x, ns))
    case C.SEnum{+ns} C.RBad{}:
      {==}
    case C.SEnum{+ns} C.RTooBig{}:
      {==}
    case C.SEnum{+ns} C.RMissing{}:
      {==}
    case C.SEnum{+ns} C.RNil{}:
      {==}
    case C.SEnum{+ns} C.RCons{h, t}:
      {==}
    case C.SEnum{+ns} C.REnd{}:
      {==}
    case C.SEnum{+ns} C.RKey{k, v, o}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RNum{n}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RBool{bb}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RNull{}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RStr{x}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RBad{}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RTooBig{}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RMissing{}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RNil{}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RCons{h, t}:
      {==}
    case C.SVariant{+vn, +vv, +vr} C.REnd{}:
      %none_later_f(C.check(~rule, vr, C.REnd{}, None{})) : {_ == C.conforms(~rule, vr, C.REnd{}, None{}) : Bool}
      exact(~rule, vr, C.REnd{}, None{})
    case C.SVariant{+vn, +vv, +vr} C.RKey{+k, +v, +o}:
      var_exact(~rule, C.is_missing(C.lookup(vn, C.RKey{k, v, o})), vn, vv, vr, C.RKey{k, v, o}, exact(~rule, vr, C.RKey{k, v, o}, None{}), exact(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}), none_dup(vr, C.RKey{k, v, o}))
    case C.SVEnd{} C.RNum{n}:
      {==}
    case C.SVEnd{} C.RBool{bb}:
      {==}
    case C.SVEnd{} C.RNull{}:
      {==}
    case C.SVEnd{} C.RStr{x}:
      {==}
    case C.SVEnd{} C.RBad{}:
      {==}
    case C.SVEnd{} C.RTooBig{}:
      {==}
    case C.SVEnd{} C.RMissing{}:
      {==}
    case C.SVEnd{} C.RNil{}:
      {==}
    case C.SVEnd{} C.RCons{h, t}:
      {==}
    case C.SVEnd{} C.REnd{}:
      {==}
    case C.SVEnd{} C.RKey{k, v, o}:
      {==}
    case C.STuple{+tt, +tr} C.RNum{n}:
      {==}
    case C.STuple{+tt, +tr} C.RBool{bb}:
      {==}
    case C.STuple{+tt, +tr} C.RNull{}:
      {==}
    case C.STuple{+tt, +tr} C.RStr{x}:
      {==}
    case C.STuple{+tt, +tr} C.RBad{}:
      {==}
    case C.STuple{+tt, +tr} C.RTooBig{}:
      {==}
    case C.STuple{+tt, +tr} C.RMissing{}:
      {==}
    case C.STuple{+tt, +tr} C.RNil{}:
      {==}
    case C.STuple{+tt, +tr} C.RCons{+h, +t}:
      %none_first(C.under(C.AtIndex{0n}, C.check(~rule, tt, h, None{})), C.later_l(C.check(~rule, tr, t, None{}))) : {_ == Bool.and(C.conforms(~rule, tt, h, None{}), C.conforms(~rule, tr, t, None{})) : Bool}
      %none_under(C.AtIndex{0n}, C.check(~rule, tt, h, None{})) : {Bool.and(_, Maybe.is_none(&2, C.Err, C.later_l(C.check(~rule, tr, t, None{})))) == Bool.and(C.conforms(~rule, tt, h, None{}), C.conforms(~rule, tr, t, None{})) : Bool}
      %none_later_l(C.check(~rule, tr, t, None{})) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, tt, h, None{})), _) == Bool.and(C.conforms(~rule, tt, h, None{}), C.conforms(~rule, tr, t, None{})) : Bool}
      %exact(~rule, tt, h, None{}) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, tt, h, None{})), Maybe.is_none(&2, C.Err, C.check(~rule, tr, t, None{}))) == Bool.and(_, C.conforms(~rule, tr, t, None{})) : Bool}
      %exact(~rule, tr, t, None{}) : {Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, tt, h, None{})), Maybe.is_none(&2, C.Err, C.check(~rule, tr, t, None{}))) == Bool.and(Maybe.is_none(&2, C.Err, C.check(~rule, tt, h, None{})), _) : Bool}
      {==}
    case C.STuple{+tt, +tr} C.REnd{}:
      {==}
    case C.STuple{+tt, +tr} C.RKey{k, v, o}:
      {==}
    case C.STEnd{} C.RNum{n}:
      {==}
    case C.STEnd{} C.RBool{bb}:
      {==}
    case C.STEnd{} C.RNull{}:
      {==}
    case C.STEnd{} C.RStr{x}:
      {==}
    case C.STEnd{} C.RBad{}:
      {==}
    case C.STEnd{} C.RTooBig{}:
      {==}
    case C.STEnd{} C.RMissing{}:
      {==}
    case C.STEnd{} C.RNil{}:
      {==}
    case C.STEnd{} C.RCons{h, t}:
      {==}
    case C.STEnd{} C.REnd{}:
      {==}
    case C.STEnd{} C.RKey{k, v, o}:
      {==}
    case C.SOptional{inner} C.RNum{n}:
      exact(~rule, inner, C.RNum{n}, None{})
    case C.SOptional{inner} C.RBool{bb}:
      exact(~rule, inner, C.RBool{bb}, None{})
    case C.SOptional{inner} C.RNull{}:
      exact(~rule, inner, C.RNull{}, None{})
    case C.SOptional{inner} C.RStr{x}:
      exact(~rule, inner, C.RStr{x}, None{})
    case C.SOptional{inner} C.RBad{}:
      exact(~rule, inner, C.RBad{}, None{})
    case C.SOptional{inner} C.RTooBig{}:
      exact(~rule, inner, C.RTooBig{}, None{})
    case C.SOptional{inner} C.RMissing{}:
      {==}
    case C.SOptional{inner} C.RNil{}:
      exact(~rule, inner, C.RNil{}, None{})
    case C.SOptional{inner} C.RCons{h, t}:
      exact(~rule, inner, C.RCons{h, t}, None{})
    case C.SOptional{inner} C.REnd{}:
      exact(~rule, inner, C.REnd{}, None{})
    case C.SOptional{inner} C.RKey{k, v, o}:
      exact(~rule, inner, C.RKey{k, v, o}, None{})
    case C.SListLen{+lo, +hi, +s2} +r:
      %none_first(C.count_err(lo, hi, r), C.check(~rule, s2, r, None{})) : {_ == Bool.and(C.list_len_ok(lo, hi, r), C.conforms(~rule, s2, r, None{})) : Bool}
      %count_err_none(lo, hi, r) : {Bool.and(Maybe.is_none(&2, C.Err, C.count_err(lo, hi, r)), Maybe.is_none(&2, C.Err, C.check(~rule, s2, r, None{}))) == Bool.and(_, C.conforms(~rule, s2, r, None{})) : Bool}
      %exact(~rule, s2, r, None{}) : {Bool.and(Maybe.is_none(&2, C.Err, C.count_err(lo, hi, r)), Maybe.is_none(&2, C.Err, C.check(~rule, s2, r, None{}))) == Bool.and(Maybe.is_none(&2, C.Err, C.count_err(lo, hi, r)), _) : Bool}
      {==}

def Laws.check_exact(rule, s, r, prev):
  exact(~rule, s, r, prev)

# ---- tools: a rule's replay ----
#
# A path is equal to itself one step at a time; rule_defect compares the
# rule's reported path with the reported one. At an SRule the first of shape
# and rule reported the error: the shape did (its replay is the IH), or the
# shape found nothing and the rule did (first_why of Nothing is the rule's
# verdict, whose path is this path).

def nat_eq_refl_r(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  Equal.sym(Bool, True{}, Nat.is_eq(a, a), MN.is_eq_refl_sym(a))

def string_eq_refl_r(s: String) -> {String.eq(s, s) == True{} : Bool}:
  Equal.sym(Bool, True{}, String.eq(s, s), MS.eq_refl_sym(s))

def and_true2(x: Bool, +y: Bool, hx: {x == True{} : Bool}, hy: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  match x:
    case True{}:
      hy
    case False{}:
      Empty.absurd({Bool.and(x, y) == True{} : Bool}, to_empty(hx))

def step_refl(x: C.Step) -> {C.step_eq(x, x) == True{} : Bool}:
  match x:
    case C.AtIndex{+i}:
      nat_eq_refl_r(i)
    case C.AtField{+a, +n}:
      and_true2(Nat.is_eq(a, a), String.eq(n, n), nat_eq_refl_r(a), string_eq_refl_r(n))
    case C.BoundAt{+i, +k}:
      and_true2(Nat.is_eq(i, i), String.eq(k, k), nat_eq_refl_r(i), string_eq_refl_r(k))
    case C.AtKey{+k}:
      string_eq_refl_r(k)

def path_refl(p: List<&2, C.Step>) -> {C.path_eq(p, p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case +st <> +q:
      and_true2(C.step_eq(st, st), C.path_eq(q, q), step_refl(st), path_refl(q))

def path_or(m: Maybe<&2, C.Err>) -> List<&2, C.Step>:
  match m:
    case None{}:
      Nil{}
    case Some{C.Err{p, w}}:
      p

def why_or(m: Maybe<&2, C.Err>) -> C.Why:
  match m:
    case None{}:
      C.Missing{}
    case Some{C.Err{p, w}}:
      w

def same_path(-p1: List<&2, C.Step>, -w1: C.Why, -p2: List<&2, C.Step>, -w2: C.Why, h: {Some{C.Err{p1, w1}} == Some{C.Err{p2, w2}} : Maybe<&2, C.Err>}) -> {p1 == p2 : List<&2, C.Step>}:
  Equal.cong(Maybe<&2, C.Err>, List<&2, C.Step>, m => path_or(m), Some{C.Err{p1, w1}}, Some{C.Err{p2, w2}}, h)

def same_why(-p1: List<&2, C.Step>, -w1: C.Why, -p2: List<&2, C.Step>, -w2: C.Why, h: {Some{C.Err{p1, w1}} == Some{C.Err{p2, w2}} : Maybe<&2, C.Err>}) -> {w1 == w2 : C.Why}:
  Equal.cong(Maybe<&2, C.Err>, C.Why, m => why_or(m), Some{C.Err{p1, w1}}, Some{C.Err{p2, w2}}, h)


# The reason of an error, kept inside its Maybe: same_why's fact lifted to the
# report a defect is written as, where what is compared is Some{why} and not
# why. A rewrite at a Some's inside is not one the checker makes, so this one
# is a term to hand to the goal rather than a rewrite.
def maybe_why(m: Maybe<&2, C.Err>) -> Maybe<&2, C.Why>:
  match m:
    case None{}:
      None{}
    case Some{C.Err{p, w}}:
      Some{w}

def same_why_m(-p1: List<&2, C.Step>, -w1: C.Why, -p2: List<&2, C.Step>, -w2: C.Why, h: {Some{C.Err{p1, w1}} == Some{C.Err{p2, w2}} : Maybe<&2, C.Err>}) -> {Some{w1} == Some{w2} : Maybe<&2, C.Why>}:
  Equal.cong(Maybe<&2, C.Err>, Maybe<&2, C.Why>, m => maybe_why(m), Some{C.Err{p1, w1}}, Some{C.Err{p2, w2}}, h)

# The repeated tag key, in front of the case's own check: the key's error is
# the report whenever the key is not read once, and otherwise the case's own
# walk answers it. kc is whether the key is read once, so the key's report is
# there exactly when it is not.
def tag_acc_in(kc: Bool, +m1: Maybe<&2, C.Err>, +d1: Maybe<&2, C.Why>, +k: String, +path: List<&2, C.Step>, +why: C.Why, +h: {C.first(C.key_err(kc, k), m1) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, i1: {m1 == Some{C.Err{path, why}} : Maybe<&2, C.Err>} -> {d1 == Some{why} : Maybe<&2, C.Why>}) -> {C.first_why(C.tag_key_defect(Bool.not(kc), k, path), d1) == Some{why} : Maybe<&2, C.Why>}:
  match kc:
    case True{}:
      i1(h)
    case False{}:
      %same_path(C.AtField{0n, k} <> Nil{}, C.RepeatedKey{k}, path, why, h) : {C.first_why(C.tag_key_defect(True{}, k, _), d1) == Some{why} : Maybe<&2, C.Why>}
      %MS.eq_refl_sym(k) : {C.first_why(C.pick_why(_, Some{C.RepeatedKey{k}}, None{}), d1) == Some{why} : Maybe<&2, C.Why>}
      same_why_m(C.AtField{0n, k} <> Nil{}, C.RepeatedKey{k}, path, why, h)

# The pick behind check's tag key test, as defect replays it: with the key read
# once the pick is tag_acc's, and with it read twice defect answers the key's
# own report before it looks at the case.
def tag_acc_k(kc: Bool, b: Bool, +m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +d1: Maybe<&2, C.Why>, +d2: Maybe<&2, C.Why>, +k: String, +path: List<&2, C.Step>, +why: C.Why, +h: {C.pick_err(b, C.first(C.key_err(kc, k), m1), m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, i1: {m1 == Some{C.Err{path, why}} : Maybe<&2, C.Err>} -> {d1 == Some{why} : Maybe<&2, C.Why>}, i2: {m2 == Some{C.Err{path, why}} : Maybe<&2, C.Err>} -> {d2 == Some{why} : Maybe<&2, C.Why>}) -> {C.pick_why(b, C.first_why(C.tag_key_defect(Bool.not(kc), k, path), d1), d2) == Some{why} : Maybe<&2, C.Why>}:
  match b:
    case True{}:
      tag_acc_in(kc, m1, d1, k, path, why, h, i1)
    case False{}:
      i2(h)
def guard_true(b: Bool, m: Maybe<&2, C.Why>, hb: {b == True{} : Bool}) -> {C.guard(b, m) == m : Maybe<&2, C.Why>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({C.guard(b, m) == m : Maybe<&2, C.Why>}, to_empty(hb))

def rule_defect_refl(m: Maybe<&2, C.Err>, +path: List<&2, C.Step>, +why: C.Why, h: {m == Some{C.Err{path, why}} : Maybe<&2, C.Err>}) -> {C.rule_defect(m, path) == Some{why} : Maybe<&2, C.Why>}:
  %Equal.sym(Maybe<&2, C.Err>, m, Some{C.Err{path, why}}, h) : {C.rule_defect(_, path) == Some{why} : Maybe<&2, C.Why>}
  guard_true(C.path_eq(path, path), Some{why}, path_refl(path))

def rule_acc_step(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +s2: C.Schema, +x: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.first(m1, m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ex: {Maybe.is_none(&2, C.Err, m1) == C.conforms(~rule, s2, x, prev) : Bool}, ih_acc: @p:List<&2, C.Step> -> @w:C.Why -> {m1 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, s2, x, prev, p) == Some{w} : Maybe<&2, C.Why>}, ih_rd: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.rule_defect(m2, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.pick_why(C.conforms(~rule, s2, x, prev), C.rule_defect(m2, path), C.defect(~rule, s2, x, prev, path)) == Some{why} : Maybe<&2, C.Why>}:
  match m1:
    case Some{C.Err{+p1, +w1}}:
      %ex : {C.pick_why(_, C.rule_defect(m2, path), C.defect(~rule, s2, x, prev, path)) == Some{why} : Maybe<&2, C.Why>}
      %same_path(p1, w1, path, why, h) : {C.defect(~rule, s2, x, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(p1, w1, path, why, h) : {C.defect(~rule, s2, x, prev, p1) == Some{_} : Maybe<&2, C.Why>}
      ih_acc(p1, w1, {==})
    case None{}:
      %ex : {C.pick_why(_, C.rule_defect(m2, path), C.defect(~rule, s2, x, prev, path)) == Some{why} : Maybe<&2, C.Why>}
      ih_rd(path, why, h)

# At a strict object, what extra_err reports is there: its path is one key,
# the object has that key, and the key is not a name. A key found further
# along is still a key of the whole object (extra_lift).

def none_some_w(-w: C.Why, h: {None{} == Some{w} : Maybe<&2, C.Why>}) -> Empty:
  to_empty(Equal.sym(Bool, True{}, False{}, Equal.cong(Maybe<&2, C.Why>, Bool, m => Maybe.is_none(&2, C.Why, m), None{}, Some{w}, h)))

def none_some_e(-x: C.Err, h: {None{} == Some{x} : Maybe<&2, C.Err>}) -> Empty:
  to_empty(Equal.sym(Bool, True{}, False{}, Equal.cong(Maybe<&2, C.Err>, Bool, m => Maybe.is_none(&2, C.Err, m), None{}, Some{x}, h)))

def or_true_x(x: Bool) -> {True{} == Bool.or(x, True{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def guard_or(c: Bool, +d: Bool, +e: Bool, +m: Maybe<&2, C.Why>, +w: C.Why, h: {C.guard(Bool.and(c, d), m) == Some{w} : Maybe<&2, C.Why>}) -> {C.guard(Bool.and(Bool.or(e, c), d), m) == Some{w} : Maybe<&2, C.Why>}:
  match c:
    case True{}:
      %or_true_x(e) : {C.guard(Bool.and(_, d), m) == Some{w} : Maybe<&2, C.Why>}
      h
    case False{}:
      Empty.absurd({C.guard(Bool.and(Bool.or(e, False{}), d), m) == Some{w} : Maybe<&2, C.Why>}, none_some_w(w, h))

def extra_lift(+ns: List<&2, String>, +k: String, +v: C.Raw, +o: C.Raw, p: List<&2, C.Step>, +w: C.Why, ih: {C.extra_defect(ns, o, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.extra_defect(ns, C.RKey{k, v, o}, p) == Some{w} : Maybe<&2, C.Why>}:
  match p:
    case C.AtKey{+j} <> Nil{}:
      guard_or(C.has_key(j, o), Bool.not(C.in_names(j, ns)), String.eq(j, k), Some{C.UnknownKey{}}, w, ih)
    case Nil{}:
      Empty.absurd({C.extra_defect(ns, C.RKey{k, v, o}, Nil{}) == Some{w} : Maybe<&2, C.Why>}, none_some_w(w, ih))
    case C.AtIndex{i_} <> q:
      Empty.absurd({C.extra_defect(ns, C.RKey{k, v, o}, C.AtIndex{i_} <> q) == Some{w} : Maybe<&2, C.Why>}, none_some_w(w, ih))
    case C.AtField{a_, n_} <> q:
      Empty.absurd({C.extra_defect(ns, C.RKey{k, v, o}, C.AtField{a_, n_} <> q) == Some{w} : Maybe<&2, C.Why>}, none_some_w(w, ih))
    case C.BoundAt{i_, b_} <> q:
      Empty.absurd({C.extra_defect(ns, C.RKey{k, v, o}, C.BoundAt{i_, b_} <> q) == Some{w} : Maybe<&2, C.Why>}, none_some_w(w, ih))
    case C.AtKey{j} <> st <> q:
      Empty.absurd({C.extra_defect(ns, C.RKey{k, v, o}, C.AtKey{j} <> st <> q) == Some{w} : Maybe<&2, C.Why>}, none_some_w(w, ih))

def extra_acc_step(b: Bool, +ns: List<&2, String>, +k: String, +v: C.Raw, +o: C.Raw, +p: List<&2, C.Step>, +w: C.Why, eb: {b == C.in_names(k, ns) : Bool}, +h: {C.pick_err(b, C.extra_err(ns, o), Some{C.Err{C.AtKey{k} <> Nil{}, C.UnknownKey{}}}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}, ih: @pp:List<&2, C.Step> -> @ww:C.Why -> {C.extra_err(ns, o) == Some{C.Err{pp, ww}} : Maybe<&2, C.Err>} -> {C.extra_defect(ns, o, pp) == Some{ww} : Maybe<&2, C.Why>}) -> {C.extra_defect(ns, C.RKey{k, v, o}, p) == Some{w} : Maybe<&2, C.Why>}:
  match b:
    case True{}:
      extra_lift(ns, k, v, o, p, w, ih(p, w, h))
    case False{}:
      %same_path(C.AtKey{k} <> Nil{}, C.UnknownKey{}, p, w, h) : {C.extra_defect(ns, C.RKey{k, v, o}, _) == Some{w} : Maybe<&2, C.Why>}
      %same_why(C.AtKey{k} <> Nil{}, C.UnknownKey{}, p, w, h) : {C.extra_defect(ns, C.RKey{k, v, o}, C.AtKey{k} <> Nil{}) == Some{_} : Maybe<&2, C.Why>}
      %MS.eq_refl_sym(k) : {C.guard(Bool.and(Bool.or(_, C.has_key(k, o)), Bool.not(C.in_names(k, ns))), Some{C.UnknownKey{}}) == Some{C.UnknownKey{}} : Maybe<&2, C.Why>}
      %eb : {C.guard(Bool.not(_), Some{C.UnknownKey{}}) == Some{C.UnknownKey{}} : Maybe<&2, C.Why>}
      {==}

def extra_acc(+ns: List<&2, String>, r: C.Raw, +p: List<&2, C.Step>, +w: C.Why, +h: {C.extra_err(ns, r) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}) -> {C.extra_defect(ns, r, p) == Some{w} : Maybe<&2, C.Why>}:
  match r:
    case C.RKey{+k, +v, +o}:
      extra_acc_step(C.in_names(k, ns), ns, k, v, o, p, w, {==}, h, pp => ww => hh => extra_acc(ns, o, pp, ww, hh))
    case C.RNum{n_}:
      Empty.absurd({C.extra_defect(ns, C.RNum{n_}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.RBool{b_}:
      Empty.absurd({C.extra_defect(ns, C.RBool{b_}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.RNull{}:
      Empty.absurd({C.extra_defect(ns, C.RNull{}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.RStr{s_}:
      Empty.absurd({C.extra_defect(ns, C.RStr{s_}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.RBad{}:
      Empty.absurd({C.extra_defect(ns, C.RBad{}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.RTooBig{}:
      Empty.absurd({C.extra_defect(ns, C.RTooBig{}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.RMissing{}:
      Empty.absurd({C.extra_defect(ns, C.RMissing{}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.RNil{}:
      Empty.absurd({C.extra_defect(ns, C.RNil{}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.RCons{h_, t_}:
      Empty.absurd({C.extra_defect(ns, C.RCons{h_, t_}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))
    case C.REnd{}:
      Empty.absurd({C.extra_defect(ns, C.REnd{}, p) == Some{w} : Maybe<&2, C.Why>}, none_some_e(C.Err{p, w}, h))

def strict_acc_step(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m1: Maybe<&2, C.Err>, +ns: List<&2, String>, +s2: C.Schema, +x: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.first(m1, C.extra_err(ns, x)) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ex: {Maybe.is_none(&2, C.Err, m1) == C.conforms(~rule, s2, x, prev) : Bool}, ih_acc: @p:List<&2, C.Step> -> @w:C.Why -> {m1 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, s2, x, prev, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.pick_why(C.conforms(~rule, s2, x, prev), C.extra_defect(ns, x, path), C.defect(~rule, s2, x, prev, path)) == Some{why} : Maybe<&2, C.Why>}:
  match m1:
    case Some{C.Err{+p1, +w1}}:
      %ex : {C.pick_why(_, C.extra_defect(ns, x, path), C.defect(~rule, s2, x, prev, path)) == Some{why} : Maybe<&2, C.Why>}
      %same_path(p1, w1, path, why, h) : {C.defect(~rule, s2, x, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(p1, w1, path, why, h) : {C.defect(~rule, s2, x, prev, p1) == Some{_} : Maybe<&2, C.Why>}
      ih_acc(p1, w1, {==})
    case None{}:
      %ex : {C.pick_why(_, C.extra_defect(ns, x, path), C.defect(~rule, s2, x, prev, path)) == Some{why} : Maybe<&2, C.Why>}
      extra_acc(ns, x, path, why, h)

# ---- repeated_key_refused ----
#
# Both halves compute, at the explicit constructors the law names: key_once_at
# sees the second "a" (the first has set its flag), conforms is False there,
# and check reports the key at its own name before it looks at the value under
# it. Nothing here rewrites; the law is decided by evaluation, which is the
# point of stating it at literals.
def Laws.repeated_key_refused():
  (({==}, {==}), ({==}, {==}))

# ---- repeated_tag_refused ----
#
# The same reading one constructor along: the tag names the case (the first
# "t" holds the case's name), the key is there twice (the second "t" is read
# with the flag the first one set, so key_once is False), conforms is False
# there, and check reports the key at its own name before it looks at the
# case's schema. The case's own schema is SEnd{}, which reads no key and
# accepts any object, so what is decided here is the tag key's own test and
# nothing else -- the same reading as repeated_key_refused, one constructor
# along.
def Laws.repeated_tag_refused():
  ({==}, {==})

# ---- unnamed_key_ignored ----
#
# Every reading computes, at the explicit constructors the law names: a first
# key that is not the field's is not looked at, the unnamed key is never looked
# up wherever it stands, and at the variant the same two values go through
# pick_bool and none_present over the concrete chain. Nothing here rewrites;
# the law is decided by evaluation, which is the point of stating it at
# literals.
def Laws.unnamed_key_ignored():
  ({==}, ({==}, {==}))

# ---- what check reports is there ----
#
# The same walk again. Where check reports here, the path is empty and the
# reason is the one defect computes at that node. Where it reports what a
# part reported, the path has one more step in front (under), or counts one
# more place along (later_l, later_i, later_f); defect takes the step off, or
# counts back, and passes the parts before, which conform because check found
# nothing in them (exact). The induction hypotheses are passed in as functions.

def none_some(-x: C.Err, h: {None{} == Some{x} : Maybe<&2, C.Err>}) -> Empty:
  to_empty(Equal.sym(Bool, True{}, False{}, Equal.cong(Maybe<&2, C.Err>, Bool, m => Maybe.is_none(&2, C.Err, m), None{}, Some{x}, h)))


# An SNatIn whose check reported an error: the test failed (a passing test
# reports nothing), so the reason is NotIn at the value's own path.
def acc_num_in(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, b: Bool, +lo: Nat, +hi: Nat, +n: Nat, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, eb: {b == C.num_ok(lo, hi, n) : Bool}, +h: {C.in_err(b, C.NotIn{lo, hi}) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}) -> {C.nat_in_defect(lo, hi, C.RNum{n}, path) == Some{why} : Maybe<&2, C.Why>}:
  match b:
    case True{}:
      Empty.absurd({C.nat_in_defect(lo, hi, C.RNum{n}, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case False{}:
      %same_path(Nil{}, C.NotIn{lo, hi}, path, why, h) : {C.nat_in_defect(lo, hi, C.RNum{n}, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotIn{lo, hi}, path, why, h) : {C.nat_in_defect(lo, hi, C.RNum{n}, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      %eb : {C.guard(Bool.not(_), Some{C.NotIn{lo, hi}}) == Some{C.NotIn{lo, hi}} : Maybe<&2, C.Why>}
      {==}

def list_path(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, p2: List<&2, C.Step>, +w2: C.Why, +e: C.Schema, +h1: C.Raw, +t: C.Raw, +prev: Maybe<&2, Nat>, +ex1: {True{} == C.conforms(~rule, e, h1, None{}) : Bool}, ih: {C.defect(~rule, C.SList{e}, t, None{}, p2) == Some{w2} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SList{e}, C.RCons{h1, t}, prev, C.later_l_path(p2)) == Some{w2} : Maybe<&2, C.Why>}:
  match p2:
    case Nil{}:
      %ex1 : {C.guard(_, C.defect(~rule, C.SList{e}, t, None{}, Nil{})) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtIndex{+j} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, C.SList{e}, t, None{}, C.AtIndex{j} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtField{+k, +n} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, C.SList{e}, t, None{}, C.AtField{k, n} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.BoundAt{+j, +k} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, C.SList{e}, t, None{}, C.BoundAt{j, k} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtKey{+k} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, C.SList{e}, t, None{}, C.AtKey{k} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih

def list_tail(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m2: Maybe<&2, C.Err>, +e: C.Schema, +h1: C.Raw, +t: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.later_l(m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, +ex1: {True{} == C.conforms(~rule, e, h1, None{}) : Bool}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, C.SList{e}, t, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SList{e}, C.RCons{h1, t}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m2:
    case None{}:
            Empty.absurd({C.defect(~rule, C.SList{e}, C.RCons{h1, t}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case Some{C.Err{+p2, +w2}}:
      %same_path(C.later_l_path(p2), w2, path, why, h) : {C.defect(~rule, C.SList{e}, C.RCons{h1, t}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.later_l_path(p2), w2, path, why, h) : {C.defect(~rule, C.SList{e}, C.RCons{h1, t}, prev, C.later_l_path(p2)) == Some{_} : Maybe<&2, C.Why>}
      list_path(~rule, p2, w2, e, h1, t, prev, ex1, ih2(p2, w2, {==}))

def list_step(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +e: C.Schema, +h1: C.Raw, +t: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.first(C.under(C.AtIndex{0n}, m1), C.later_l(m2)) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ex1: {Maybe.is_none(&2, C.Err, m1) == C.conforms(~rule, e, h1, None{}) : Bool}, ih1: @p:List<&2, C.Step> -> @w:C.Why -> {m1 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, e, h1, None{}, p) == Some{w} : Maybe<&2, C.Why>}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, C.SList{e}, t, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SList{e}, C.RCons{h1, t}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m1:
    case Some{C.Err{+p1, +w1}}:
      %same_path(C.AtIndex{0n} <> p1, w1, path, why, h) : {C.defect(~rule, C.SList{e}, C.RCons{h1, t}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.AtIndex{0n} <> p1, w1, path, why, h) : {C.defect(~rule, C.SList{e}, C.RCons{h1, t}, prev, C.AtIndex{0n} <> p1) == Some{_} : Maybe<&2, C.Why>}
      ih1(p1, w1, {==})
    case None{}:
      list_tail(~rule, m2, e, h1, t, prev, path, why, h, ex1, ih2)

def tup_path(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, p2: List<&2, C.Step>, +w2: C.Why, +e: C.Schema, +tr: C.Schema, +h1: C.Raw, +t: C.Raw, +prev: Maybe<&2, Nat>, +ex1: {True{} == C.conforms(~rule, e, h1, None{}) : Bool}, ih: {C.defect(~rule, tr, t, None{}, p2) == Some{w2} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.STuple{e, tr}, C.RCons{h1, t}, prev, C.later_l_path(p2)) == Some{w2} : Maybe<&2, C.Why>}:
  match p2:
    case Nil{}:
      %ex1 : {C.guard(_, C.defect(~rule, tr, t, None{}, Nil{})) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtIndex{+j} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, tr, t, None{}, C.AtIndex{j} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtField{+k, +n} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, tr, t, None{}, C.AtField{k, n} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.BoundAt{+j, +k} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, tr, t, None{}, C.BoundAt{j, k} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtKey{+k} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, tr, t, None{}, C.AtKey{k} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih

def tup_tail(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m2: Maybe<&2, C.Err>, +e: C.Schema, +tr: C.Schema, +h1: C.Raw, +t: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.later_l(m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, +ex1: {True{} == C.conforms(~rule, e, h1, None{}) : Bool}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, tr, t, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.STuple{e, tr}, C.RCons{h1, t}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m2:
    case None{}:
            Empty.absurd({C.defect(~rule, C.STuple{e, tr}, C.RCons{h1, t}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case Some{C.Err{+p2, +w2}}:
      %same_path(C.later_l_path(p2), w2, path, why, h) : {C.defect(~rule, C.STuple{e, tr}, C.RCons{h1, t}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.later_l_path(p2), w2, path, why, h) : {C.defect(~rule, C.STuple{e, tr}, C.RCons{h1, t}, prev, C.later_l_path(p2)) == Some{_} : Maybe<&2, C.Why>}
      tup_path(~rule, p2, w2, e, tr, h1, t, prev, ex1, ih2(p2, w2, {==}))

def tup_step(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +e: C.Schema, +tr: C.Schema, +h1: C.Raw, +t: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.first(C.under(C.AtIndex{0n}, m1), C.later_l(m2)) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ex1: {Maybe.is_none(&2, C.Err, m1) == C.conforms(~rule, e, h1, None{}) : Bool}, ih1: @p:List<&2, C.Step> -> @w:C.Why -> {m1 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, e, h1, None{}, p) == Some{w} : Maybe<&2, C.Why>}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, tr, t, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.STuple{e, tr}, C.RCons{h1, t}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m1:
    case Some{C.Err{+p1, +w1}}:
      %same_path(C.AtIndex{0n} <> p1, w1, path, why, h) : {C.defect(~rule, C.STuple{e, tr}, C.RCons{h1, t}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.AtIndex{0n} <> p1, w1, path, why, h) : {C.defect(~rule, C.STuple{e, tr}, C.RCons{h1, t}, prev, C.AtIndex{0n} <> p1) == Some{_} : Maybe<&2, C.Why>}
      ih1(p1, w1, {==})
    case None{}:
      tup_tail(~rule, m2, e, tr, h1, t, prev, path, why, h, ex1, ih2)

def field_path_end(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, p2: List<&2, C.Step>, +w2: C.Why, +name: String, +fs: C.Schema, +rest: C.Schema, +prev: Maybe<&2, Nat>, +ex1: {True{} == C.conforms(~rule, fs, C.RMissing{}, None{}) : Bool}, ih: {C.defect(~rule, rest, C.REnd{}, None{}, p2) == Some{w2} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SField{name, fs, rest}, C.REnd{}, prev, C.later_f_path(p2)) == Some{w2} : Maybe<&2, C.Why>}:
  match p2:
    case Nil{}:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.REnd{}, None{}, Nil{})) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtField{+j, +n} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.REnd{}, None{}, C.AtField{j, n} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtIndex{+j} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.REnd{}, None{}, C.AtIndex{j} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.BoundAt{+j, +kk} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.REnd{}, None{}, C.BoundAt{j, kk} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtKey{+kk} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.REnd{}, None{}, C.AtKey{kk} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih

def field_tail_end(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m2: Maybe<&2, C.Err>, +name: String, +fs: C.Schema, +rest: C.Schema, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.later_f(m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, +ex1: {True{} == C.conforms(~rule, fs, C.RMissing{}, None{}) : Bool}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, rest, C.REnd{}, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SField{name, fs, rest}, C.REnd{}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m2:
    case None{}:
      Empty.absurd({C.defect(~rule, C.SField{name, fs, rest}, C.REnd{}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case Some{C.Err{+p2, +w2}}:
      %same_path(C.later_f_path(p2), w2, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.later_f_path(p2), w2, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.REnd{}, prev, C.later_f_path(p2)) == Some{_} : Maybe<&2, C.Why>}
      field_path_end(~rule, p2, w2, name, fs, rest, prev, ex1, ih2(p2, w2, {==}))

def field_step_end(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +name: String, +fs: C.Schema, +rest: C.Schema, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.first(C.under(C.AtField{0n, name}, m1), C.later_f(m2)) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ex1: {Maybe.is_none(&2, C.Err, m1) == C.conforms(~rule, fs, C.RMissing{}, None{}) : Bool}, ih1: @p:List<&2, C.Step> -> @w:C.Why -> {m1 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, fs, C.RMissing{}, None{}, p) == Some{w} : Maybe<&2, C.Why>}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, rest, C.REnd{}, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SField{name, fs, rest}, C.REnd{}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m1:
    case Some{C.Err{+p1, +w1}}:
      %same_path(C.AtField{0n, name} <> p1, w1, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.AtField{0n, name} <> p1, w1, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.REnd{}, prev, C.AtField{0n, name} <> p1) == Some{_} : Maybe<&2, C.Why>}
      %MS.eq_refl_sym(name) : {C.guard(_, C.defect(~rule, fs, C.RMissing{}, None{}, p1)) == Some{w1} : Maybe<&2, C.Why>}
      ih1(p1, w1, {==})
    case None{}:
      field_tail_end(~rule, m2, name, fs, rest, prev, path, why, h, ex1, ih2)

def field_path_key(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, p2: List<&2, C.Step>, +w2: C.Why, +name: String, +fs: C.Schema, +rest: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +ex1: {True{} == C.conforms(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}) : Bool}, ih: {C.defect(~rule, rest, C.RKey{k, v, o}, None{}, p2) == Some{w2} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, C.later_f_path(p2)) == Some{w2} : Maybe<&2, C.Why>}:
  match p2:
    case Nil{}:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.RKey{k, v, o}, None{}, Nil{})) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtField{+j, +n} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.RKey{k, v, o}, None{}, C.AtField{j, n} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtIndex{+j} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.RKey{k, v, o}, None{}, C.AtIndex{j} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.BoundAt{+j, +kk} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.RKey{k, v, o}, None{}, C.BoundAt{j, kk} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtKey{+kk} <> +q:
      %ex1 : {C.guard(_, C.defect(~rule, rest, C.RKey{k, v, o}, None{}, C.AtKey{kk} <> q)) == Some{w2} : Maybe<&2, C.Why>}
      ih

def field_tail_key(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m2: Maybe<&2, C.Err>, +name: String, +fs: C.Schema, +rest: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.later_f(m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, +ex1: {True{} == C.conforms(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}) : Bool}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, rest, C.RKey{k, v, o}, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m2:
    case None{}:
      Empty.absurd({C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case Some{C.Err{+p2, +w2}}:
      %same_path(C.later_f_path(p2), w2, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.later_f_path(p2), w2, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, C.later_f_path(p2)) == Some{_} : Maybe<&2, C.Why>}
      field_path_key(~rule, p2, w2, name, fs, rest, k, v, o, prev, ex1, ih2(p2, w2, {==}))

def field_step_key(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m1: Maybe<&2, C.Err>, +m2: Maybe<&2, C.Err>, +name: String, +fs: C.Schema, +rest: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, k0: Bool, +kc: {k0 == C.key_once_at(o, String.eq(k, name), name) : Bool}, +h: {C.first(C.key_err(k0, name), C.first(C.under(C.AtField{0n, name}, m1), C.later_f(m2))) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ex1: {Maybe.is_none(&2, C.Err, m1) == C.conforms(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}) : Bool}, ih1: @p:List<&2, C.Step> -> @w:C.Why -> {m1 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}, p) == Some{w} : Maybe<&2, C.Why>}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, rest, C.RKey{k, v, o}, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m1:
    case Some{C.Err{+p1, +w1}}:
      match k0:
        case True{}:
          %same_path(C.AtField{0n, name} <> p1, w1, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
          %same_why(C.AtField{0n, name} <> p1, w1, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, C.AtField{0n, name} <> p1) == Some{_} : Maybe<&2, C.Why>}
          %kc : {C.pick_why(Bool.not(_), C.at_end(C.RepeatedKey{name}, p1), C.guard(String.eq(name, name), C.defect(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}, p1))) == Some{w1} : Maybe<&2, C.Why>}
          %MS.eq_refl_sym(name) : {C.guard(_, C.defect(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}, p1)) == Some{w1} : Maybe<&2, C.Why>}
          ih1(p1, w1, {==})
        case False{}:
          %same_path(C.AtField{0n, name} <> Nil{}, C.RepeatedKey{name}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
          %same_why(C.AtField{0n, name} <> Nil{}, C.RepeatedKey{name}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, C.AtField{0n, name} <> Nil{}) == Some{_} : Maybe<&2, C.Why>}
          %kc : {C.pick_why(Bool.not(_), C.at_end(C.RepeatedKey{name}, Nil{}), C.guard(String.eq(name, name), C.defect(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}, Nil{}))) == Some{C.RepeatedKey{name}} : Maybe<&2, C.Why>}
          {==}
    case None{}:
      match k0:
        case True{}:
          field_tail_key(~rule, m2, name, fs, rest, k, v, o, prev, path, why, h, ex1, ih2)
        case False{}:
          %same_path(C.AtField{0n, name} <> Nil{}, C.RepeatedKey{name}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
          %same_why(C.AtField{0n, name} <> Nil{}, C.RepeatedKey{name}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RKey{k, v, o}, prev, C.AtField{0n, name} <> Nil{}) == Some{_} : Maybe<&2, C.Why>}
          %kc : {C.pick_why(Bool.not(_), C.at_end(C.RepeatedKey{name}, Nil{}), C.guard(String.eq(name, name), C.defect(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}, Nil{}))) == Some{C.RepeatedKey{name}} : Maybe<&2, C.Why>}
          {==}

def acc_true(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, bb: Bool, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.true_err(bb) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}) -> {C.defect(~rule, C.STrue{}, C.RBool{bb}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match bb:
    case True{}:
      Empty.absurd({C.defect(~rule, C.STrue{}, C.RBool{True{}}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case False{}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RBool{False{}}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RBool{False{}}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}

def acc_enum(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, b: Bool, +x: String, +ns: List<&2, String>, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, eb: {b == C.in_names(x, ns) : Bool}, +h: {C.enum_err(b) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}) -> {C.defect(~rule, C.SEnum{ns}, C.RStr{x}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match b:
    case True{}:
      Empty.absurd({C.defect(~rule, C.SEnum{ns}, C.RStr{x}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case False{}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      %eb : {C.guard(Bool.not(_), Some{C.NotOneOf{}}) == Some{C.NotOneOf{}} : Maybe<&2, C.Why>}
      {==}

# A variant on an empty object: every key is absent, go on with the rest.
def var_end_path(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, p2: List<&2, C.Step>, +w2: C.Why, +vn: String, +vv: C.Schema, +vr: C.Schema, +prev: Maybe<&2, Nat>, ih: {C.defect(~rule, vr, C.REnd{}, None{}, p2) == Some{w2} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.REnd{}, prev, C.later_f_path(p2)) == Some{w2} : Maybe<&2, C.Why>}:
  match p2:
    case Nil{}:
      ih
    case C.AtField{+j, +n} <> +q:
      ih
    case C.AtIndex{+j} <> +q:
      ih
    case C.BoundAt{+j, +kk} <> +q:
      ih
    case C.AtKey{+kk} <> +q:
      ih

def var_end_tail(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m2: Maybe<&2, C.Err>, +vn: String, +vv: C.Schema, +vr: C.Schema, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.later_f(m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, vr, C.REnd{}, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.REnd{}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m2:
    case None{}:
      Empty.absurd({C.defect(~rule, C.SVariant{vn, vv, vr}, C.REnd{}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case Some{C.Err{+p2, +w2}}:
      %same_path(C.later_f_path(p2), w2, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.later_f_path(p2), w2, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.REnd{}, prev, C.later_f_path(p2)) == Some{_} : Maybe<&2, C.Why>}
      var_end_path(~rule, p2, w2, vn, vv, vr, prev, ih2(p2, w2, {==}))

# A key absent from the object: the error is the rest's, one field along.
def var_absent_path(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, p2: List<&2, C.Step>, +w2: C.Why, +vn: String, +vv: C.Schema, +vr: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +eb: {True{} == C.is_missing(C.lookup(vn, C.RKey{k, v, o})) : Bool}, ih: {C.defect(~rule, vr, C.RKey{k, v, o}, None{}, p2) == Some{w2} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.later_f_path(p2)) == Some{w2} : Maybe<&2, C.Why>}:
  match p2:
    case Nil{}:
      %eb : {C.pick_why(_, C.defect(~rule, vr, C.RKey{k, v, o}, None{}, Nil{}), None{}) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtField{+j, +n} <> +q:
      %eb : {C.pick_why(_, C.defect(~rule, vr, C.RKey{k, v, o}, None{}, C.AtField{j, n} <> q), C.guard(C.conforms(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}), C.dup_defect(vr, C.RKey{k, v, o}, C.AtField{j, n} <> q))) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtIndex{+j} <> +q:
      %eb : {C.pick_why(_, C.defect(~rule, vr, C.RKey{k, v, o}, None{}, C.AtIndex{j} <> q), None{}) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.BoundAt{+j, +kk} <> +q:
      %eb : {C.pick_why(_, C.defect(~rule, vr, C.RKey{k, v, o}, None{}, C.BoundAt{j, kk} <> q), None{}) == Some{w2} : Maybe<&2, C.Why>}
      ih
    case C.AtKey{+kk} <> +q:
      %eb : {C.pick_why(_, C.defect(~rule, vr, C.RKey{k, v, o}, None{}, C.AtKey{kk} <> q), None{}) == Some{w2} : Maybe<&2, C.Why>}
      ih

def var_absent(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m2: Maybe<&2, C.Err>, +vn: String, +vv: C.Schema, +vr: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +eb: {True{} == C.is_missing(C.lookup(vn, C.RKey{k, v, o})) : Bool}, +h: {C.later_f(m2) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ih1: @p:List<&2, C.Step> -> @w:C.Why -> {m2 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, vr, C.RKey{k, v, o}, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m2:
    case None{}:
      Empty.absurd({C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case Some{C.Err{+p2, +w2}}:
      %same_path(C.later_f_path(p2), w2, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.later_f_path(p2), w2, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.later_f_path(p2)) == Some{_} : Maybe<&2, C.Why>}
      var_absent_path(~rule, p2, w2, vn, vv, vr, k, v, o, prev, eb, ih1(p2, w2, {==}))

# The shape of a second-key error: its path starts with a field step.
def head_is_field(p: List<&2, C.Step>) -> Bool:
  match p:
    case C.AtField{k, n} <> q:
      True{}
    case _:
      False{}

def shape_path(pp: List<&2, C.Step>, sh: {head_is_field(pp) == True{} : Bool}) -> {head_is_field(C.later_f_path(pp)) == True{} : Bool}:
  match pp:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, to_empty(sh))
    case C.AtField{j, n} <> q:
      {==}
    case C.AtIndex{j} <> q:
      Empty.absurd({False{} == True{} : Bool}, to_empty(sh))
    case C.BoundAt{j, kk} <> q:
      Empty.absurd({False{} == True{} : Bool}, to_empty(sh))
    case C.AtKey{kk} <> q:
      Empty.absurd({False{} == True{} : Bool}, to_empty(sh))

def shape_tail(m: Maybe<&2, C.Err>, +p: List<&2, C.Step>, +w: C.Why, +h: {C.later_f(m) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}, ih: @pp:List<&2, C.Step> -> @ww:C.Why -> {m == Some{C.Err{pp, ww}} : Maybe<&2, C.Err>} -> {head_is_field(pp) == True{} : Bool}) -> {head_is_field(p) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case Some{C.Err{+p1, +w1}}:
      %same_path(C.later_f_path(p1), w1, p, w, h) : {head_is_field(_) == True{} : Bool}
      shape_path(p1, ih(p1, w1, {==}))

def shape_step(b: Bool, +n: String, +rr: C.Schema, +r: C.Raw, +p: List<&2, C.Step>, +w: C.Why, +h: {C.pick_err(b, C.later_f(C.dup_err(rr, r)), Some{C.Err{C.AtField{0n, n} <> Nil{}, C.TwoVariants{}}}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}, ih: @pp:List<&2, C.Step> -> @ww:C.Why -> {C.dup_err(rr, r) == Some{C.Err{pp, ww}} : Maybe<&2, C.Err>} -> {head_is_field(pp) == True{} : Bool}) -> {head_is_field(p) == True{} : Bool}:
  match b:
    case True{}:
      shape_tail(C.dup_err(rr, r), p, w, h, ih)
    case False{}:
      %same_path(C.AtField{0n, n} <> Nil{}, C.TwoVariants{}, p, w, h) : {head_is_field(_) == True{} : Bool}
      {==}

# arms: s
# arms leaf: Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
def dup_shape(s: C.Schema, +r: C.Raw, +p: List<&2, C.Step>, +w: C.Why, +h: {C.dup_err(s, r) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}) -> {head_is_field(p) == True{} : Bool}:
  match s:
    case C.SNat{}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SNatIn{lo_, hi_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SStr{}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SStrLen{lo_, hi_, s_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SOpt{inner_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SList{elem_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SField{name_, s_, rest_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SEnd{}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SRule{s_, tag_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SStrict{s_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.STagged{key_, name_, s_, rest_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.STagEnd{key_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SBool{}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.STrue{}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SEnum{names_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SVariant{+vn, vv, +vr}:
      shape_step(C.is_missing(C.lookup(vn, r)), vn, vr, r, p, w, h, pp => ww => hh => dup_shape(vr, r, pp, ww, hh))
    case C.SVEnd{}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.STuple{s_, rest_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.STEnd{}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SOptional{inner_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))
    case C.SListLen{lo_, hi_, s_}:
      Empty.absurd({head_is_field(p) == True{} : Bool}, none_some(C.Err{p, w}, h))

# What dup_err reports, dup_defect replays.
def dup_path(pp: List<&2, C.Step>, +ww: C.Why, +n: String, +vs: C.Schema, +rr: C.Schema, +r: C.Raw, +eb: {True{} == C.is_missing(C.lookup(n, r)) : Bool}, d: {C.dup_defect(rr, r, pp) == Some{ww} : Maybe<&2, C.Why>}, sh: {head_is_field(pp) == True{} : Bool}) -> {C.dup_defect(C.SVariant{n, vs, rr}, r, C.later_f_path(pp)) == Some{ww} : Maybe<&2, C.Why>}:
  match pp:
    case Nil{}:
      Empty.absurd({C.dup_defect(C.SVariant{n, vs, rr}, r, Nil{}) == Some{ww} : Maybe<&2, C.Why>}, to_empty(sh))
    case C.AtField{+j, +m} <> +q:
      %eb : {C.guard(_, C.dup_defect(rr, r, C.AtField{j, m} <> q)) == Some{ww} : Maybe<&2, C.Why>}
      d
    case C.AtIndex{j} <> q:
      Empty.absurd({C.dup_defect(C.SVariant{n, vs, rr}, r, C.AtIndex{j} <> q) == Some{ww} : Maybe<&2, C.Why>}, to_empty(sh))
    case C.BoundAt{j, kk} <> q:
      Empty.absurd({C.dup_defect(C.SVariant{n, vs, rr}, r, C.BoundAt{j, kk} <> q) == Some{ww} : Maybe<&2, C.Why>}, to_empty(sh))
    case C.AtKey{kk} <> q:
      Empty.absurd({C.dup_defect(C.SVariant{n, vs, rr}, r, C.AtKey{kk} <> q) == Some{ww} : Maybe<&2, C.Why>}, to_empty(sh))

def dup_tail(m: Maybe<&2, C.Err>, +n: String, +vs: C.Schema, +rr: C.Schema, +r: C.Raw, +p: List<&2, C.Step>, +w: C.Why, +eb: {True{} == C.is_missing(C.lookup(n, r)) : Bool}, +h: {C.later_f(m) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}, ih: @pp:List<&2, C.Step> -> @ww:C.Why -> {m == Some{C.Err{pp, ww}} : Maybe<&2, C.Err>} -> {C.dup_defect(rr, r, pp) == Some{ww} : Maybe<&2, C.Why>}, sh: @pp:List<&2, C.Step> -> @ww:C.Why -> {m == Some{C.Err{pp, ww}} : Maybe<&2, C.Err>} -> {head_is_field(pp) == True{} : Bool}) -> {C.dup_defect(C.SVariant{n, vs, rr}, r, p) == Some{w} : Maybe<&2, C.Why>}:
  match m:
    case None{}:
      Empty.absurd({C.dup_defect(C.SVariant{n, vs, rr}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case Some{C.Err{+p1, +w1}}:
      %same_path(C.later_f_path(p1), w1, p, w, h) : {C.dup_defect(C.SVariant{n, vs, rr}, r, _) == Some{w} : Maybe<&2, C.Why>}
      %same_why(C.later_f_path(p1), w1, p, w, h) : {C.dup_defect(C.SVariant{n, vs, rr}, r, C.later_f_path(p1)) == Some{_} : Maybe<&2, C.Why>}
      dup_path(p1, w1, n, vs, rr, r, eb, ih(p1, w1, {==}), sh(p1, w1, {==}))

def dup_step(b: Bool, +n: String, +vs: C.Schema, +rr: C.Schema, +r: C.Raw, eb: {b == C.is_missing(C.lookup(n, r)) : Bool}, +p: List<&2, C.Step>, +w: C.Why, +h: {C.pick_err(b, C.later_f(C.dup_err(rr, r)), Some{C.Err{C.AtField{0n, n} <> Nil{}, C.TwoVariants{}}}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}, ih: @pp:List<&2, C.Step> -> @ww:C.Why -> {C.dup_err(rr, r) == Some{C.Err{pp, ww}} : Maybe<&2, C.Err>} -> {C.dup_defect(rr, r, pp) == Some{ww} : Maybe<&2, C.Why>}, sh: @pp:List<&2, C.Step> -> @ww:C.Why -> {C.dup_err(rr, r) == Some{C.Err{pp, ww}} : Maybe<&2, C.Err>} -> {head_is_field(pp) == True{} : Bool}) -> {C.dup_defect(C.SVariant{n, vs, rr}, r, p) == Some{w} : Maybe<&2, C.Why>}:
  match b:
    case True{}:
      dup_tail(C.dup_err(rr, r), n, vs, rr, r, p, w, eb, h, ih, sh)
    case False{}:
      %same_path(C.AtField{0n, n} <> Nil{}, C.TwoVariants{}, p, w, h) : {C.dup_defect(C.SVariant{n, vs, rr}, r, _) == Some{w} : Maybe<&2, C.Why>}
      %same_why(C.AtField{0n, n} <> Nil{}, C.TwoVariants{}, p, w, h) : {C.dup_defect(C.SVariant{n, vs, rr}, r, C.AtField{0n, n} <> Nil{}) == Some{_} : Maybe<&2, C.Why>}
      %MS.eq_refl_sym(n) : {C.guard(Bool.and(_, Bool.not(C.is_missing(C.lookup(n, r)))), Some{C.TwoVariants{}}) == Some{C.TwoVariants{}} : Maybe<&2, C.Why>}
      %eb : {C.guard(Bool.and(True{}, Bool.not(_)), Some{C.TwoVariants{}}) == Some{C.TwoVariants{}} : Maybe<&2, C.Why>}
      {==}

# arms: s
# arms leaf: Empty.absurd({C.dup_defect($S, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
def dup_acc(s: C.Schema, +r: C.Raw, +p: List<&2, C.Step>, +w: C.Why, +h: {C.dup_err(s, r) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}) -> {C.dup_defect(s, r, p) == Some{w} : Maybe<&2, C.Why>}:
  match s:
    case C.SNat{}:
      Empty.absurd({C.dup_defect(C.SNat{}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SNatIn{lo_, hi_}:
      Empty.absurd({C.dup_defect(C.SNatIn{lo_, hi_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SStr{}:
      Empty.absurd({C.dup_defect(C.SStr{}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SStrLen{lo_, hi_, s_}:
      Empty.absurd({C.dup_defect(C.SStrLen{lo_, hi_, s_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SOpt{inner_}:
      Empty.absurd({C.dup_defect(C.SOpt{inner_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SList{elem_}:
      Empty.absurd({C.dup_defect(C.SList{elem_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SField{name_, s_, rest_}:
      Empty.absurd({C.dup_defect(C.SField{name_, s_, rest_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SEnd{}:
      Empty.absurd({C.dup_defect(C.SEnd{}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SRule{s_, tag_}:
      Empty.absurd({C.dup_defect(C.SRule{s_, tag_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SStrict{s_}:
      Empty.absurd({C.dup_defect(C.SStrict{s_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.STagged{key_, name_, s_, rest_}:
      Empty.absurd({C.dup_defect(C.STagged{key_, name_, s_, rest_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.STagEnd{key_}:
      Empty.absurd({C.dup_defect(C.STagEnd{key_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SBool{}:
      Empty.absurd({C.dup_defect(C.SBool{}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.STrue{}:
      Empty.absurd({C.dup_defect(C.STrue{}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SEnum{names_}:
      Empty.absurd({C.dup_defect(C.SEnum{names_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SVariant{+vn, +vv, +vr}:
      dup_step(C.is_missing(C.lookup(vn, r)), vn, vv, vr, r, {==}, p, w, h, pp => ww => hh => dup_acc(vr, r, pp, ww, hh), pp => ww => hh => dup_shape(vr, r, pp, ww, hh))
    case C.SVEnd{}:
      Empty.absurd({C.dup_defect(C.SVEnd{}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.STuple{s_, rest_}:
      Empty.absurd({C.dup_defect(C.STuple{s_, rest_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.STEnd{}:
      Empty.absurd({C.dup_defect(C.STEnd{}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SOptional{inner_}:
      Empty.absurd({C.dup_defect(C.SOptional{inner_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))
    case C.SListLen{lo_, hi_, s_}:
      Empty.absurd({C.dup_defect(C.SListLen{lo_, hi_, s_}, r, p) == Some{w} : Maybe<&2, C.Why>}, none_some(C.Err{p, w}, h))

# A key present: an error in its value is under its field; else a second key
# is one field along, found by dup_err.
def var_dup_path(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, p3: List<&2, C.Step>, +w3: C.Why, +vn: String, +vv: C.Schema, +vr: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +eb: {False{} == C.is_missing(C.lookup(vn, C.RKey{k, v, o})) : Bool}, +ex1: {True{} == C.conforms(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}) : Bool}, d: {C.dup_defect(vr, C.RKey{k, v, o}, p3) == Some{w3} : Maybe<&2, C.Why>}, sh: {head_is_field(p3) == True{} : Bool}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.later_f_path(p3)) == Some{w3} : Maybe<&2, C.Why>}:
  match p3:
    case C.AtField{+j, +n} <> +q:
      %eb : {C.pick_why(_, C.defect(~rule, vr, C.RKey{k, v, o}, None{}, C.AtField{j, n} <> q), C.guard(C.conforms(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}), C.dup_defect(vr, C.RKey{k, v, o}, C.AtField{j, n} <> q))) == Some{w3} : Maybe<&2, C.Why>}
      %ex1 : {C.guard(_, C.dup_defect(vr, C.RKey{k, v, o}, C.AtField{j, n} <> q)) == Some{w3} : Maybe<&2, C.Why>}
      d
    case Nil{}:
      Empty.absurd({C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, Nil{}) == Some{w3} : Maybe<&2, C.Why>}, to_empty(sh))
    case C.AtIndex{j} <> q:
      Empty.absurd({C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.AtIndex{j} <> q) == Some{w3} : Maybe<&2, C.Why>}, to_empty(sh))
    case C.BoundAt{j, kk} <> q:
      Empty.absurd({C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.BoundAt{j, kk} <> q) == Some{w3} : Maybe<&2, C.Why>}, to_empty(sh))
    case C.AtKey{kk} <> q:
      Empty.absurd({C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.AtKey{kk} <> q) == Some{w3} : Maybe<&2, C.Why>}, to_empty(sh))

def var_dup(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m3: Maybe<&2, C.Err>, +vn: String, +vv: C.Schema, +vr: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +eb: {False{} == C.is_missing(C.lookup(vn, C.RKey{k, v, o})) : Bool}, +h: {C.later_f(m3) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, +ex1: {True{} == C.conforms(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}) : Bool}, hd: @p:List<&2, C.Step> -> @w:C.Why -> {m3 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.dup_defect(vr, C.RKey{k, v, o}, p) == Some{w} : Maybe<&2, C.Why>}, hs: @p:List<&2, C.Step> -> @w:C.Why -> {m3 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {head_is_field(p) == True{} : Bool}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m3:
    case None{}:
      Empty.absurd({C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case Some{C.Err{+p3, +w3}}:
      %same_path(C.later_f_path(p3), w3, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.later_f_path(p3), w3, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.later_f_path(p3)) == Some{_} : Maybe<&2, C.Why>}
      var_dup_path(~rule, p3, w3, vn, vv, vr, k, v, o, prev, eb, ex1, hd(p3, w3, {==}), hs(p3, w3, {==}))

# The second occurrence of a variant key: check reports it before it looks at
# the value under the key, so defect carries nothing but the report -- at the
# key's own name, with no step after it. hk is the test at the value it was
# false on, which is what the walk above has left of kc.
def var_key_repeat(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, +vn: String, +vv: C.Schema, +vr: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +eb: {False{} == C.is_missing(C.lookup(vn, C.RKey{k, v, o})) : Bool}, hk: {False{} == C.key_once_at(o, String.eq(k, vn), vn) : Bool}, +h: {Some{C.Err{C.AtField{0n, vn} <> Nil{}, C.RepeatedKey{vn}}} == Some{C.Err{path, why}} : Maybe<&2, C.Err>}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  %same_path(C.AtField{0n, vn} <> Nil{}, C.RepeatedKey{vn}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
  %same_why(C.AtField{0n, vn} <> Nil{}, C.RepeatedKey{vn}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.AtField{0n, vn} <> Nil{}) == Some{_} : Maybe<&2, C.Why>}
  %eb : {C.pick_why(_, C.defect(~rule, vr, C.RKey{k, v, o}, None{}, C.AtField{0n, vn} <> Nil{}), C.pick_why(Bool.not(C.key_once(vn, C.RKey{k, v, o})), C.at_end(C.RepeatedKey{vn}, Nil{}), C.guard(String.eq(vn, vn), C.defect(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}, Nil{})))) == Some{C.RepeatedKey{vn}} : Maybe<&2, C.Why>}
  %hk : {C.pick_why(Bool.not(_), C.at_end(C.RepeatedKey{vn}, Nil{}), C.guard(String.eq(vn, vn), C.defect(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}, Nil{}))) == Some{C.RepeatedKey{vn}} : Maybe<&2, C.Why>}
  {==}

def var_present(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m1: Maybe<&2, C.Err>, +m3: Maybe<&2, C.Err>, +vn: String, +vv: C.Schema, +vr: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, k0: Bool, +kc: {k0 == C.key_once_at(o, String.eq(k, vn), vn) : Bool}, +eb: {False{} == C.is_missing(C.lookup(vn, C.RKey{k, v, o})) : Bool}, +h: {C.first(C.key_err(k0, vn), C.first(C.under(C.AtField{0n, vn}, m1), C.later_f(m3))) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ex1: {Maybe.is_none(&2, C.Err, m1) == C.conforms(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}) : Bool}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {m1 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}, p) == Some{w} : Maybe<&2, C.Why>}, hd: @p:List<&2, C.Step> -> @w:C.Why -> {m3 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.dup_defect(vr, C.RKey{k, v, o}, p) == Some{w} : Maybe<&2, C.Why>}, hs: @p:List<&2, C.Step> -> @w:C.Why -> {m3 == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {head_is_field(p) == True{} : Bool}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match m1:
    case Some{C.Err{+p1, +w1}}:
      match k0:
        case True{}:
          %same_path(C.AtField{0n, vn} <> p1, w1, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
          %same_why(C.AtField{0n, vn} <> p1, w1, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, C.AtField{0n, vn} <> p1) == Some{_} : Maybe<&2, C.Why>}
          %eb : {C.pick_why(_, C.defect(~rule, vr, C.RKey{k, v, o}, None{}, C.AtField{0n, vn} <> p1), C.pick_why(Bool.not(C.key_once(vn, C.RKey{k, v, o})), C.at_end(C.RepeatedKey{vn}, p1), C.guard(String.eq(vn, vn), C.defect(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}, p1)))) == Some{w1} : Maybe<&2, C.Why>}
          %kc : {C.pick_why(Bool.not(_), C.at_end(C.RepeatedKey{vn}, p1), C.guard(String.eq(vn, vn), C.defect(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}, p1))) == Some{w1} : Maybe<&2, C.Why>}
          %MS.eq_refl_sym(vn) : {C.guard(_, C.defect(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}, p1)) == Some{w1} : Maybe<&2, C.Why>}
          ih2(p1, w1, {==})
        case False{}:
          var_key_repeat(~rule, vn, vv, vr, k, v, o, prev, path, why, eb, kc, h)
    case None{}:
      match k0:
        case True{}:
          var_dup(~rule, m3, vn, vv, vr, k, v, o, prev, path, why, eb, h, ex1, hd, hs)
        case False{}:
          var_key_repeat(~rule, vn, vv, vr, k, v, o, prev, path, why, eb, kc, h)

def var_acc(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, b: Bool, +vn: String, +vv: C.Schema, +vr: C.Schema, +k: String, +v: C.Raw, +o: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, k0: Bool, +kc: {k0 == C.key_once_at(o, String.eq(k, vn), vn) : Bool}, eb: {b == C.is_missing(C.lookup(vn, C.RKey{k, v, o})) : Bool}, +h: {C.pick_err(b, C.later_f(C.check(~rule, vr, C.RKey{k, v, o}, None{})), C.first(C.key_err(k0, vn), C.first(C.under(C.AtField{0n, vn}, C.check(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{})), C.later_f(C.dup_err(vr, C.RKey{k, v, o}))))) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ex2: {Maybe.is_none(&2, C.Err, C.check(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{})) == C.conforms(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}) : Bool}, ih1: @p:List<&2, C.Step> -> @w:C.Why -> {C.check(~rule, vr, C.RKey{k, v, o}, None{}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, vr, C.RKey{k, v, o}, None{}, p) == Some{w} : Maybe<&2, C.Why>}, ih2: @p:List<&2, C.Step> -> @w:C.Why -> {C.check(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}, p) == Some{w} : Maybe<&2, C.Why>}, hd: @p:List<&2, C.Step> -> @w:C.Why -> {C.dup_err(vr, C.RKey{k, v, o}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.dup_defect(vr, C.RKey{k, v, o}, p) == Some{w} : Maybe<&2, C.Why>}, hs: @p:List<&2, C.Step> -> @w:C.Why -> {C.dup_err(vr, C.RKey{k, v, o}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {head_is_field(p) == True{} : Bool}) -> {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match b:
    case True{}:
      var_absent(~rule, C.check(~rule, vr, C.RKey{k, v, o}, None{}), vn, vv, vr, k, v, o, prev, path, why, eb, h, ih1)
    case False{}:
      var_present(~rule, C.check(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}), C.dup_err(vr, C.RKey{k, v, o}), vn, vv, vr, k, v, o, prev, path, why, k0, kc, eb, h, ex2, ih2, hd, hs)

# An SListLen whose check reported an error. The count is read before any
# element, so the error is the count's own exactly when count_err reported one
# (count_err_none turns the guard, which is written on the conforms side, into
# that question; its reason is CountNotIn at the list's own path, or the reason
# a list schema gives a value that is not a list). Otherwise the count found
# nothing and the error is the inner schema's, replayed by the IH.
def sll_acc_step(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, m1: Maybe<&2, C.Err>, +lo: Nat, +hi: Nat, +s2: C.Schema, +r: C.Raw, +path: List<&2, C.Step>, +why: C.Why, em: {m1 == C.count_err(lo, hi, r) : Maybe<&2, C.Err>}, +h: {C.first(m1, C.check(~rule, s2, r, None{})) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}, ih_acc: @p:List<&2, C.Step> -> @w:C.Why -> {C.check(~rule, s2, r, None{}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>} -> {C.defect(~rule, s2, r, None{}, p) == Some{w} : Maybe<&2, C.Why>}) -> {C.pick_why(Bool.not(C.list_len_ok(lo, hi, r)), C.rule_defect(C.count_err(lo, hi, r), path), C.defect(~rule, s2, r, None{}, path)) == Some{why} : Maybe<&2, C.Why>}:
  match m1:
    case Some{C.Err{+p1, +w1}}:
      %count_err_none(lo, hi, r) : {C.pick_why(Bool.not(_), C.rule_defect(C.count_err(lo, hi, r), path), C.defect(~rule, s2, r, None{}, path)) == Some{why} : Maybe<&2, C.Why>}
      %em : {C.pick_why(Bool.not(Maybe.is_none(&2, C.Err, _)), C.rule_defect(_, path), C.defect(~rule, s2, r, None{}, path)) == Some{why} : Maybe<&2, C.Why>}
      %same_path(p1, w1, path, why, h) : {C.rule_defect(Some{C.Err{p1, w1}}, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(p1, w1, path, why, h) : {C.guard(C.path_eq(p1, p1), Some{w1}) == Some{_} : Maybe<&2, C.Why>}
      guard_true(C.path_eq(p1, p1), Some{w1}, path_refl(p1))
    case None{}:
      %count_err_none(lo, hi, r) : {C.pick_why(Bool.not(_), C.rule_defect(C.count_err(lo, hi, r), path), C.defect(~rule, s2, r, None{}, path)) == Some{why} : Maybe<&2, C.Why>}
      %em : {C.pick_why(Bool.not(Maybe.is_none(&2, C.Err, _)), C.rule_defect(_, path), C.defect(~rule, s2, r, None{}, path)) == Some{why} : Maybe<&2, C.Why>}
      ih_acc(path, why, h)


# arms: s r
# arms leaf: %same_path(Nil{}, $W, path, why, h) : {C.defect(~rule, $S, $R, prev, _) == Some{why} : Maybe<&2, C.Why>}
# arms leaf: %same_why(Nil{}, $W, path, why, h) : {C.defect(~rule, $S, $R, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
# arms leaf: {==}
# arms why: SBool=C.NotBool{} SNatIn=C.NotNat{} SStrLen=C.NotString{} RTooBig=C.TooLarge{} SNat=C.NotNat{} SStr=C.NotString{} SList=C.NotList{} SField=C.NotObject{} SEnd=C.NotObject{} STrue=C.NotTrue{} SEnum=C.NotOneOf{} SVariant=C.NotObject{} SVEnd=C.NotObject{} STuple=C.NotList{} STEnd=C.NotList{} STagEnd=C.NotObject{} RMissing=C.Missing{} SVEnd.REnd=C.NoVariant{} SVEnd.RKey=C.NoVariant{} STuple.RNil=C.TooShort{} STEnd.RCons=C.TooLong{}
# arms accept: SNat.RNum SStr.RStr SOpt.RNull SList.RNil SEnd.REnd SEnd.RKey STEnd.RNil
# arms accept leaf: Empty.absurd({C.defect(~rule, $S, $R, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
def acc(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, s: C.Schema, r: C.Raw, +prev: Maybe<&2, Nat>, +path: List<&2, C.Step>, +why: C.Why, +h: {C.check(~rule, s, r, prev) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}) -> {C.defect(~rule, s, r, prev, path) == Some{why} : Maybe<&2, C.Why>}:
  match s r:
    case C.SNat{} C.RNum{n}:
      Empty.absurd({C.defect(~rule, C.SNat{}, C.RNum{n}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.SNat{} C.RBool{bb}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.RNull{}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.RStr{x}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.RBad{}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.RNil{}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.REnd{}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNat{} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNat{}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RNum{+n}:
      acc_num_in(~rule, C.num_ok(lo, hi, n), lo, hi, n, prev, path, why, {==}, h)
    case C.SNatIn{+lo, +hi} C.RBool{bb}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RNull{}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RStr{x}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RBad{}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RNil{}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.REnd{}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SNatIn{+lo, +hi} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotNat{}, path, why, h) : {C.defect(~rule, C.SNatIn{lo, hi}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RNum{n}:
      %same_path(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RBool{bb}:
      %same_path(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RNull{}:
      %same_path(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RStr{x}:
      Empty.absurd({C.defect(~rule, C.SStr{}, C.RStr{x}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.SStr{} C.RBad{}:
      %same_path(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RNil{}:
      %same_path(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.REnd{}:
      %same_path(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStr{} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotString{}, path, why, h) : {C.defect(~rule, C.SStr{}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SStrLen{+lo, +hi, +s2} +x:
      rule_acc_step(~rule, C.check(~rule, s2, x, prev), C.len_err(lo, hi, x), s2, x, prev, path, why, h, exact(~rule, s2, x, prev), p => w => hh => acc(~rule, s2, x, prev, p, w, hh), p => w => hh => rule_defect_refl(C.len_err(lo, hi, x), p, w, hh))
    case C.SOpt{+inner} C.RNum{n}:
      acc(~rule, inner, C.RNum{n}, None{}, path, why, h)
    case C.SOpt{+inner} C.RBool{bb}:
      acc(~rule, inner, C.RBool{bb}, None{}, path, why, h)
    case C.SOpt{+inner} C.RNull{}:
      Empty.absurd({C.defect(~rule, C.SOpt{inner}, C.RNull{}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.SOpt{+inner} C.RStr{x}:
      acc(~rule, inner, C.RStr{x}, None{}, path, why, h)
    case C.SOpt{+inner} C.RBad{}:
      acc(~rule, inner, C.RBad{}, None{}, path, why, h)
    case C.SOpt{+inner} C.RTooBig{}:
      acc(~rule, inner, C.RTooBig{}, None{}, path, why, h)
    case C.SOpt{+inner} C.RMissing{}:
      acc(~rule, inner, C.RMissing{}, None{}, path, why, h)
    case C.SOpt{+inner} C.RNil{}:
      acc(~rule, inner, C.RNil{}, None{}, path, why, h)
    case C.SOpt{+inner} C.RCons{hd, tl}:
      acc(~rule, inner, C.RCons{hd, tl}, None{}, path, why, h)
    case C.SOpt{+inner} C.REnd{}:
      acc(~rule, inner, C.REnd{}, None{}, path, why, h)
    case C.SOpt{+inner} C.RKey{k, v, o}:
      acc(~rule, inner, C.RKey{k, v, o}, None{}, path, why, h)
    case C.SList{+e} C.RNum{n}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SList{+e} C.RBool{bb}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SList{+e} C.RNull{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SList{+e} C.RStr{x}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SList{+e} C.RBad{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SList{+e} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SList{+e} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SList{+e} C.RNil{}:
      Empty.absurd({C.defect(~rule, C.SList{e}, C.RNil{}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.SList{+e} C.RCons{+h1, +t}:
      list_step(~rule, C.check(~rule, e, h1, None{}), C.check(~rule, C.SList{e}, t, None{}), e, h1, t, prev, path, why, h, exact(~rule, e, h1, None{}), p => w => hh => acc(~rule, e, h1, None{}, p, w, hh), p => w => hh => acc(~rule, C.SList{e}, t, None{}, p, w, hh))
    case C.SList{+e} C.REnd{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SList{+e} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.SList{e}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RNum{n}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RBool{bb}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RNull{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RStr{x}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RBad{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RNil{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SField{name, fs, rest}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SField{+name, +fs, +rest} C.REnd{}:
      field_step_end(~rule, C.check(~rule, fs, C.RMissing{}, None{}), C.check(~rule, rest, C.REnd{}, None{}), name, fs, rest, prev, path, why, h, exact(~rule, fs, C.RMissing{}, None{}), p => w => hh => acc(~rule, fs, C.RMissing{}, None{}, p, w, hh), p => w => hh => acc(~rule, rest, C.REnd{}, None{}, p, w, hh))
    case C.SField{+name, +fs, +rest} C.RKey{+k, +v, +o}:
      field_step_key(~rule, C.check(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}), C.check(~rule, rest, C.RKey{k, v, o}, None{}), name, fs, rest, k, v, o, prev, path, why, C.key_once(name, C.RKey{k, v, o}), {==}, h, exact(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}), p => w => hh => acc(~rule, fs, C.lookup(name, C.RKey{k, v, o}), None{}, p, w, hh), p => w => hh => acc(~rule, rest, C.RKey{k, v, o}, None{}, p, w, hh))
    case C.SEnd{} C.RNum{n}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.RBool{bb}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.RNull{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.RStr{x}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.RBad{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.RNil{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SEnd{}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnd{} C.REnd{}:
      Empty.absurd({C.defect(~rule, C.SEnd{}, C.REnd{}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.SEnd{} C.RKey{k, v, o}:
      Empty.absurd({C.defect(~rule, C.SEnd{}, C.RKey{k, v, o}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.SRule{+s2, +tag} +x:
      rule_acc_step(~rule, C.check(~rule, s2, x, prev), rule(tag, x), s2, x, prev, path, why, h, exact(~rule, s2, x, prev), p => w => hh => acc(~rule, s2, x, prev, p, w, hh), p => w => hh => rule_defect_refl(rule(tag, x), p, w, hh))
    case C.SStrict{+s2} +x:
      strict_acc_step(~rule, C.check(~rule, s2, x, prev), C.key_names(s2), s2, x, prev, path, why, h, exact(~rule, s2, x, prev), p => w => hh => acc(~rule, s2, x, prev, p, w, hh))
    case C.STagged{+k, +n, +cs, +rest} +x:
      tag_acc_k(C.key_once(k, x), C.is_tag(k, n, x), C.check(~rule, cs, C.drop_key(k, x), None{}), C.check(~rule, rest, x, None{}), C.defect(~rule, cs, C.drop_key(k, x), None{}, path), C.defect(~rule, rest, x, None{}, path), k, path, why, h, hh => acc(~rule, cs, C.drop_key(k, x), None{}, path, why, hh), hh => acc(~rule, rest, x, None{}, path, why, hh))
    case C.STagEnd{+k} C.RNum{n}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RBool{bb}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RNull{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RStr{x}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RBad{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RNil{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.REnd{}:
      %same_path(C.AtKey{k} <> Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.AtKey{k} <> Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.REnd{}, prev, C.AtKey{k} <> Nil{}) == Some{_} : Maybe<&2, C.Why>}
      %MS.eq_refl_sym(k) : {C.guard(_, Some{C.Missing{}}) == Some{C.Missing{}} : Maybe<&2, C.Why>}
      {==}
    case C.STagEnd{+k} C.RKey{+j, +v, +o}:
      %same_path(C.AtKey{k} <> Nil{}, C.missing_or(C.lookup(k, C.RKey{j, v, o}), C.NotOneOf{}), path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RKey{j, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(C.AtKey{k} <> Nil{}, C.missing_or(C.lookup(k, C.RKey{j, v, o}), C.NotOneOf{}), path, why, h) : {C.defect(~rule, C.STagEnd{k}, C.RKey{j, v, o}, prev, C.AtKey{k} <> Nil{}) == Some{_} : Maybe<&2, C.Why>}
      %MS.eq_refl_sym(k) : {C.guard(_, Some{C.missing_or(C.lookup(k, C.RKey{j, v, o}), C.NotOneOf{})}) == Some{C.missing_or(C.lookup(k, C.RKey{j, v, o}), C.NotOneOf{})} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RNum{n}:
      %same_path(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RBool{bb}:
      Empty.absurd({C.defect(~rule, C.SBool{}, C.RBool{bb}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.SBool{} C.RNull{}:
      %same_path(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RStr{x}:
      %same_path(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RBad{}:
      %same_path(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RNil{}:
      %same_path(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.REnd{}:
      %same_path(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SBool{} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotBool{}, path, why, h) : {C.defect(~rule, C.SBool{}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RNum{n}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RBool{bb}:
      acc_true(~rule, bb, prev, path, why, h)
    case C.STrue{} C.RNull{}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RStr{x}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RBad{}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RNil{}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.REnd{}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STrue{} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotTrue{}, path, why, h) : {C.defect(~rule, C.STrue{}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RNum{n}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RBool{bb}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RNull{}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RStr{+x}:
      acc_enum(~rule, C.in_names(x, ns), x, ns, prev, path, why, {==}, h)
    case C.SEnum{+ns} C.RBad{}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RNil{}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.REnd{}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SEnum{+ns} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotOneOf{}, path, why, h) : {C.defect(~rule, C.SEnum{ns}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RNum{n}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RBool{bb}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RNull{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RStr{x}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RBad{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RNil{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVariant{vn, vv, vr}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVariant{+vn, +vv, +vr} C.REnd{}:
      var_end_tail(~rule, C.check(~rule, vr, C.REnd{}, None{}), vn, vv, vr, prev, path, why, h, p => w => hh => acc(~rule, vr, C.REnd{}, None{}, p, w, hh))
    case C.SVariant{+vn, +vv, +vr} C.RKey{+k, +v, +o}:
      var_acc(~rule, C.is_missing(C.lookup(vn, C.RKey{k, v, o})), vn, vv, vr, k, v, o, prev, path, why, C.key_once(vn, C.RKey{k, v, o}), {==}, {==}, h, exact(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}), p => w => hh => acc(~rule, vr, C.RKey{k, v, o}, None{}, p, w, hh), p => w => hh => acc(~rule, vv, C.lookup(vn, C.RKey{k, v, o}), None{}, p, w, hh), p => w => hh => dup_acc(vr, C.RKey{k, v, o}, p, w, hh), p => w => hh => dup_shape(vr, C.RKey{k, v, o}, p, w, hh))
    case C.SVEnd{} C.RNum{n}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RBool{bb}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RNull{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RStr{x}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RBad{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RNil{}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RCons{hd, tl}:
      %same_path(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotObject{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.REnd{}:
      %same_path(Nil{}, C.NoVariant{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NoVariant{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SVEnd{} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NoVariant{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NoVariant{}, path, why, h) : {C.defect(~rule, C.SVEnd{}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RNum{n}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RBool{bb}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RNull{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RStr{x}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RBad{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RNil{}:
      %same_path(Nil{}, C.TooShort{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RNil{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooShort{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RNil{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RCons{+h1, +t}:
      tup_step(~rule, C.check(~rule, tt, h1, None{}), C.check(~rule, tr, t, None{}), tt, tr, h1, t, prev, path, why, h, exact(~rule, tt, h1, None{}), p => w => hh => acc(~rule, tt, h1, None{}, p, w, hh), p => w => hh => acc(~rule, tr, t, None{}, p, w, hh))
    case C.STuple{+tt, +tr} C.REnd{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STuple{+tt, +tr} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STuple{tt, tr}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RNum{n}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RNum{n}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RNum{n}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RBool{bb}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RBool{bb}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RBool{bb}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RNull{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RNull{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RNull{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RStr{x}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RStr{x}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RStr{x}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RBad{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RBad{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RBad{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RTooBig{}:
      %same_path(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RTooBig{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLarge{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RTooBig{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RMissing{}:
      %same_path(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RMissing{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.Missing{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RMissing{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RNil{}:
      Empty.absurd({C.defect(~rule, C.STEnd{}, C.RNil{}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.STEnd{} C.RCons{hd, tl}:
      %same_path(Nil{}, C.TooLong{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RCons{hd, tl}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.TooLong{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RCons{hd, tl}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.REnd{}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.REnd{}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.REnd{}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.STEnd{} C.RKey{k, v, o}:
      %same_path(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RKey{k, v, o}, prev, _) == Some{why} : Maybe<&2, C.Why>}
      %same_why(Nil{}, C.NotList{}, path, why, h) : {C.defect(~rule, C.STEnd{}, C.RKey{k, v, o}, prev, Nil{}) == Some{_} : Maybe<&2, C.Why>}
      {==}
    case C.SOptional{+inner} C.RNum{n}:
      acc(~rule, inner, C.RNum{n}, None{}, path, why, h)
    case C.SOptional{+inner} C.RBool{bb}:
      acc(~rule, inner, C.RBool{bb}, None{}, path, why, h)
    case C.SOptional{+inner} C.RNull{}:
      acc(~rule, inner, C.RNull{}, None{}, path, why, h)
    case C.SOptional{+inner} C.RStr{x}:
      acc(~rule, inner, C.RStr{x}, None{}, path, why, h)
    case C.SOptional{+inner} C.RBad{}:
      acc(~rule, inner, C.RBad{}, None{}, path, why, h)
    case C.SOptional{+inner} C.RTooBig{}:
      acc(~rule, inner, C.RTooBig{}, None{}, path, why, h)
    case C.SOptional{+inner} C.RMissing{}:
      Empty.absurd({C.defect(~rule, C.SOptional{inner}, C.RMissing{}, prev, path) == Some{why} : Maybe<&2, C.Why>}, none_some(C.Err{path, why}, h))
    case C.SOptional{+inner} C.RNil{}:
      acc(~rule, inner, C.RNil{}, None{}, path, why, h)
    case C.SOptional{+inner} C.RCons{hd, tl}:
      acc(~rule, inner, C.RCons{hd, tl}, None{}, path, why, h)
    case C.SOptional{+inner} C.REnd{}:
      acc(~rule, inner, C.REnd{}, None{}, path, why, h)
    case C.SOptional{+inner} C.RKey{k, v, o}:
      acc(~rule, inner, C.RKey{k, v, o}, None{}, path, why, h)
    case C.SListLen{+lo, +hi, +s2} +r:
      sll_acc_step(~rule, C.count_err(lo, hi, r), lo, hi, s2, r, path, why, {==}, h, p => w => hh => acc(~rule, s2, r, None{}, p, w, hh))

def Laws.check_accurate(rule, s, r, prev, path, why, h):
  acc(~rule, s, r, prev, path, why, h)

# ---- a too big value is reported where it stands ----
#
# The same walk as check, one arm per schema kind: a value the codec refused to
# build is not the shape any kind wants, so every kind reaches the arm that
# answers with missing_or, and that arm is where TooLarge comes from. The kinds
# that look further into the value (an optional, a rule, a strict object, a
# tag) reach their own arm first, and each of those either recurses or takes
# the reason straight from the sub-walk.

# arms: s
# arms leaf: {==}
def too_large_go(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, s: C.Schema, +prev: Maybe<&2, Nat>) -> {C.check(~rule, s, C.RTooBig{}, prev) == Some{C.Err{Nil{}, C.TooLarge{}}} : Maybe<&2, C.Err>}:
  match s:
    case C.SNat{}:
      {==}
    case C.SNatIn{lo_, hi_}:
      {==}
    case C.SStr{}:
      {==}
    case C.SStrLen{lo, hi, s2}:
      %Equal.sym(Maybe<&2, C.Err>, C.check(~rule, s2, C.RTooBig{}, prev), Some{C.Err{Nil{}, C.TooLarge{}}}, too_large_go(~rule, s2, prev)) : {C.first(_, C.len_err(lo, hi, C.RTooBig{})) == Some{C.Err{Nil{}, C.TooLarge{}}} : Maybe<&2, C.Err>}
      {==}
    case C.SOpt{inner}:
      too_large_go(~rule, inner, None{})
    case C.SList{elem_}:
      {==}
    case C.SField{name_, s_, rest_}:
      {==}
    case C.SEnd{}:
      {==}
    case C.SRule{s2, tag}:
      %Equal.sym(Maybe<&2, C.Err>, C.check(~rule, s2, C.RTooBig{}, prev), Some{C.Err{Nil{}, C.TooLarge{}}}, too_large_go(~rule, s2, prev)) : {C.first(_, rule(tag, C.RTooBig{})) == Some{C.Err{Nil{}, C.TooLarge{}}} : Maybe<&2, C.Err>}
      {==}
    case C.SStrict{s2}:
      %Equal.sym(Maybe<&2, C.Err>, C.check(~rule, s2, C.RTooBig{}, prev), Some{C.Err{Nil{}, C.TooLarge{}}}, too_large_go(~rule, s2, prev)) : {C.first(_, C.extra_err(C.key_names(s2), C.RTooBig{})) == Some{C.Err{Nil{}, C.TooLarge{}}} : Maybe<&2, C.Err>}
      {==}
    case C.STagged{k, n, cs, rest}:
      too_large_go(~rule, rest, None{})
    case C.STagEnd{key_}:
      {==}
    case C.SBool{}:
      {==}
    case C.STrue{}:
      {==}
    case C.SEnum{names_}:
      {==}
    case C.SVariant{name_, s_, rest_}:
      {==}
    case C.SVEnd{}:
      {==}
    case C.STuple{s_, rest_}:
      {==}
    case C.STEnd{}:
      {==}
    case C.SOptional{inner}:
      too_large_go(~rule, inner, None{})
    case C.SListLen{lo_, hi_, s2_}:
      {==}

def Laws.too_large_reported(rule, s, prev):
  too_large_go(~rule, s, prev)

# ---- every listed name is accepted ----
#
# in_names looks for n through pre, then finds it: String.eq(n, n) is True
# (MS.eq_refl_sym), and an or with True is True whatever came first.

def or_true_r(x: Bool) -> {True{} == Bool.or(x, True{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def names_has(pre: List<&2, String>, +n: String, +post: List<&2, String>) -> {C.in_names(n, List.append(&2, String, pre, n <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      %MS.eq_refl_sym(n) : {Bool.or(_, C.in_names(n, post)) == True{} : Bool}
      {==}
    case +m <> +t:
      %Equal.sym(Bool, C.in_names(n, List.append(&2, String, t, n <> post)), True{}, names_has(t, n, post)) : {Bool.or(String.eq(n, m), _) == True{} : Bool}
      Equal.sym(Bool, True{}, Bool.or(String.eq(n, m), True{}), or_true_r(String.eq(n, m)))

def Laws.enum_accepts(rule, pre, n, post):
  names_has(pre, n, post)

# ---- an accepted string is one of the names ----
#
# By induction on the names: the first one matches (the witness has an empty
# pre), or the rest holds it, and the witness moves one name along.

def one_of_cons(+m: String, +t: List<&2, String>, +x: String, w: Laws.OneOf(t, x)) -> Laws.OneOf(m <> t, x):
  match w:
    case (+pre, +n, +post, eq, hx):
      (m <> pre, n, post, Equal.cong(List<&2, String>, List<&2, String>, l => m <> l, t, List.append(&2, String, pre, n <> post), eq), hx)

def one_of_step(b: Bool, +m: String, +t: List<&2, String>, +x: String, eb: {b == String.eq(x, m) : Bool}, h: {Bool.or(b, C.in_names(x, t)) == True{} : Bool}, ih: {C.in_names(x, t) == True{} : Bool} -> Laws.OneOf(t, x)) -> Laws.OneOf(m <> t, x):
  match b:
    case True{}:
      (Nil{}, m, t, {==}, Equal.sym(Bool, True{}, String.eq(x, m), eb))
    case False{}:
      one_of_cons(m, t, x, ih(h))

def one_of(ns: List<&2, String>, +x: String, h: {C.in_names(x, ns) == True{} : Bool}) -> Laws.OneOf(ns, x):
  match ns:
    case Nil{}:
      Empty.absurd(Laws.OneOf(Nil{}, x), to_empty(h))
    case +m <> +t:
      one_of_step(String.eq(x, m), m, t, x, {==}, h, hh => one_of(t, x, hh))

def Laws.enum_admits(rule, ns, x, h):
  one_of(ns, x, h)

# ---- a variant chain, read by counting ----
#
# One key along at a time: an absent key adds 0 to the count and says
# nothing of the value; a present one adds 1, so no later key may be there
# (count_zero), and then every later key is absent (np_pc).

def and_false_l(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def count_step(b: Bool, +rr: C.Schema, +r: C.Raw, ih: {Nat.is_eq(C.count_present(rr, r), 0n) == C.none_present(rr, r) : Bool}) -> {Nat.is_eq(Nat.add(C.one_if_there(b), C.count_present(rr, r)), 0n) == Bool.and(b, C.none_present(rr, r)) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# arms: s
# arms leaf: {==}
def count_zero(s: C.Schema, +r: C.Raw) -> {Nat.is_eq(C.count_present(s, r), 0n) == C.none_present(s, r) : Bool}:
  match s:
    case C.SNat{}:
      {==}
    case C.SNatIn{lo_, hi_}:
      {==}
    case C.SStr{}:
      {==}
    case C.SStrLen{lo_, hi_, s_}:
      {==}
    case C.SOpt{inner_}:
      {==}
    case C.SList{elem_}:
      {==}
    case C.SField{name_, s_, rest_}:
      {==}
    case C.SEnd{}:
      {==}
    case C.SRule{s_, tag_}:
      {==}
    case C.SStrict{s_}:
      {==}
    case C.STagged{key_, name_, s_, rest_}:
      {==}
    case C.STagEnd{key_}:
      {==}
    case C.SBool{}:
      {==}
    case C.STrue{}:
      {==}
    case C.SEnum{names_}:
      {==}
    case C.SVariant{+vn, vv, +vr}:
      count_step(C.is_missing(C.lookup(vn, r)), vr, r, count_zero(vr, r))
    case C.SVEnd{}:
      {==}
    case C.STuple{s_, rest_}:
      {==}
    case C.STEnd{}:
      {==}
    case C.SOptional{inner_}:
      {==}
    case C.SListLen{lo_, hi_, s_}:
      {==}

def np_pc_step(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, b: Bool, +cv: Bool, +vn: String, +vv: C.Schema, +rr: C.Schema, +r: C.Raw, ih: {Bool.and(cv, C.none_present(rr, r)) == Bool.and(C.none_present(rr, r), Bool.and(cv, C.present_conform(~rule, rr, r))) : Bool}) -> {Bool.and(cv, Bool.and(b, C.none_present(rr, r))) == Bool.and(Bool.and(b, C.none_present(rr, r)), Bool.and(cv, C.pick_bool(b, C.present_conform(~rule, rr, r), Bool.and(C.key_once(vn, r), Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.present_conform(~rule, rr, r)))))) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      and_false_l(cv)

# cv and "no key" is "no key", cv and every present value conforming.
# arms: s
# arms leaf: {==}
def np_pc(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, s: C.Schema, +r: C.Raw, +cv: Bool) -> {Bool.and(cv, C.none_present(s, r)) == Bool.and(C.none_present(s, r), Bool.and(cv, C.present_conform(~rule, s, r))) : Bool}:
  match s:
    case C.SNat{}:
      {==}
    case C.SNatIn{lo_, hi_}:
      {==}
    case C.SStr{}:
      {==}
    case C.SStrLen{lo_, hi_, s_}:
      {==}
    case C.SOpt{inner_}:
      {==}
    case C.SList{elem_}:
      {==}
    case C.SField{name_, s_, rest_}:
      {==}
    case C.SEnd{}:
      {==}
    case C.SRule{s_, tag_}:
      {==}
    case C.SStrict{s_}:
      {==}
    case C.STagged{key_, name_, s_, rest_}:
      {==}
    case C.STagEnd{key_}:
      {==}
    case C.SBool{}:
      {==}
    case C.STrue{}:
      {==}
    case C.SEnum{names_}:
      {==}
    case C.SVariant{+vn, +vv, +vr}:
      np_pc_step(~rule, C.is_missing(C.lookup(vn, r)), cv, vn, vv, vr, r, np_pc(~rule, vr, r, cv))
    case C.SVEnd{}:
      {==}
    case C.STuple{s_, rest_}:
      {==}
    case C.STEnd{}:
      {==}
    case C.SOptional{inner_}:
      {==}
    case C.SListLen{lo_, hi_, s_}:
      {==}

# The key's own case, in two splits. b is whether the chain's key is in the
# value: an absent key adds nothing to the count and says nothing of the
# value, which is the IH untouched. A key that is there adds 1, so the rest
# must hold none (count_zero turned round) and the value under the key must
# conform (np_pc) -- and it must be read once (k0), which is what conforms
# asks at the same place; a key taken twice leaves false on both sides.
def var_key(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, b: Bool, k0: Bool, +vn: String, +vv: C.Schema, +vr: C.Schema, +r: C.Raw, +kc: {k0 == C.key_once(vn, r) : Bool}, ih: {C.conforms(~rule, vr, r, None{}) == Bool.and(True{}, Bool.and(Nat.is_eq(C.count_present(vr, r), 1n), C.present_conform(~rule, vr, r))) : Bool}) -> {C.pick_bool(b, C.conforms(~rule, vr, r, None{}), Bool.and(k0, Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.none_present(vr, r)))) == Bool.and(Nat.is_eq(Nat.add(C.one_if_there(b), C.count_present(vr, r)), 1n), C.pick_bool(b, C.present_conform(~rule, vr, r), Bool.and(k0, Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.present_conform(~rule, vr, r))))) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      match k0:
        case True{}:
          %Equal.sym(Bool, Nat.is_eq(C.count_present(vr, r), 0n), C.none_present(vr, r), count_zero(vr, r)) : {Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.none_present(vr, r)) == Bool.and(_, Bool.and(C.conforms(~rule, vv, C.lookup(vn, r), None{}), C.present_conform(~rule, vr, r))) : Bool}
          np_pc(~rule, vr, r, C.conforms(~rule, vv, C.lookup(vn, r), None{}))
        case False{}:
          Equal.sym(Bool, Bool.and(Nat.is_eq(Nat.add(C.one_if_there(b), C.count_present(vr, r)), 1n), False{}), False{}, and_false_l(Nat.is_eq(Nat.add(C.one_if_there(b), C.count_present(vr, r)), 1n)))

def vm_raw(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, r: C.Raw, +vn: String, +vv: C.Schema, +vr: C.Schema, hc: {C.is_chain(vr) == True{} : Bool}, ih: @rr:C.Raw -> {C.conforms(~rule, vr, rr, None{}) == Bool.and(C.is_object(rr), Bool.and(Nat.is_eq(C.count_present(vr, rr), 1n), C.present_conform(~rule, vr, rr))) : Bool}) -> {C.conforms(~rule, C.SVariant{vn, vv, vr}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SVariant{vn, vv, vr}, r), 1n), C.present_conform(~rule, C.SVariant{vn, vv, vr}, r))) : Bool}:
  match r:
    case C.RNum{n}:
      {==}
    case C.RBool{bb}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{x}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{hd, tl}:
      {==}
    case C.REnd{}:
      ih(C.REnd{})
    case C.RKey{+k, +v, +o}:
      var_key(~rule, C.is_missing(C.lookup(vn, C.RKey{k, v, o})), C.key_once(vn, C.RKey{k, v, o}), vn, vv, vr, C.RKey{k, v, o}, {==}, ih(C.RKey{k, v, o}))

# arms: s
# arms leaf: Empty.absurd({C.conforms(~rule, $S, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present($S, r), 1n), C.present_conform(~rule, $S, r))) : Bool}, to_empty(hc))
def vm(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, s: C.Schema, r: C.Raw, +hc: {C.is_chain(s) == True{} : Bool}) -> {C.conforms(~rule, s, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(s, r), 1n), C.present_conform(~rule, s, r))) : Bool}:
  match s:
    case C.SNat{}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SNat{}, r), 1n), C.present_conform(~rule, C.SNat{}, r))) : Bool}, to_empty(hc))
    case C.SNatIn{lo_, hi_}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SNatIn{lo_, hi_}, r), 1n), C.present_conform(~rule, C.SNatIn{lo_, hi_}, r))) : Bool}, to_empty(hc))
    case C.SStr{}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SStr{}, r), 1n), C.present_conform(~rule, C.SStr{}, r))) : Bool}, to_empty(hc))
    case C.SStrLen{lo_, hi_, s_}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SStrLen{lo_, hi_, s_}, r), 1n), C.present_conform(~rule, C.SStrLen{lo_, hi_, s_}, r))) : Bool}, to_empty(hc))
    case C.SOpt{inner_}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SOpt{inner_}, r), 1n), C.present_conform(~rule, C.SOpt{inner_}, r))) : Bool}, to_empty(hc))
    case C.SList{elem_}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SList{elem_}, r), 1n), C.present_conform(~rule, C.SList{elem_}, r))) : Bool}, to_empty(hc))
    case C.SField{name_, s_, rest_}:
      Empty.absurd({C.conforms(~rule, C.SField{name_, s_, rest_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SField{name_, s_, rest_}, r), 1n), C.present_conform(~rule, C.SField{name_, s_, rest_}, r))) : Bool}, to_empty(hc))
    case C.SEnd{}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SEnd{}, r), 1n), C.present_conform(~rule, C.SEnd{}, r))) : Bool}, to_empty(hc))
    case C.SRule{s_, tag_}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SRule{s_, tag_}, r), 1n), C.present_conform(~rule, C.SRule{s_, tag_}, r))) : Bool}, to_empty(hc))
    case C.SStrict{s_}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SStrict{s_}, r), 1n), C.present_conform(~rule, C.SStrict{s_}, r))) : Bool}, to_empty(hc))
    case C.STagged{key_, name_, s_, rest_}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.STagged{key_, name_, s_, rest_}, r), 1n), C.present_conform(~rule, C.STagged{key_, name_, s_, rest_}, r))) : Bool}, to_empty(hc))
    case C.STagEnd{key_}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.STagEnd{key_}, r), 1n), C.present_conform(~rule, C.STagEnd{key_}, r))) : Bool}, to_empty(hc))
    case C.SBool{}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SBool{}, r), 1n), C.present_conform(~rule, C.SBool{}, r))) : Bool}, to_empty(hc))
    case C.STrue{}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.STrue{}, r), 1n), C.present_conform(~rule, C.STrue{}, r))) : Bool}, to_empty(hc))
    case C.SEnum{names_}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SEnum{names_}, r), 1n), C.present_conform(~rule, C.SEnum{names_}, r))) : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vv, +vr}:
      vm_raw(~rule, r, vn, vv, vr, hc, rr => vm(~rule, vr, rr, hc))
    case C.SVEnd{}:
      Equal.sym(Bool, Bool.and(C.is_object(r), False{}), False{}, and_false_l(C.is_object(r)))
    case C.STuple{s_, rest_}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.STuple{s_, rest_}, r), 1n), C.present_conform(~rule, C.STuple{s_, rest_}, r))) : Bool}, to_empty(hc))
    case C.STEnd{}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.STEnd{}, r), 1n), C.present_conform(~rule, C.STEnd{}, r))) : Bool}, to_empty(hc))
    case C.SOptional{inner_}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SOptional{inner_}, r), 1n), C.present_conform(~rule, C.SOptional{inner_}, r))) : Bool}, to_empty(hc))
    case C.SListLen{lo_, hi_, s_}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(C.SListLen{lo_, hi_, s_}, r), 1n), C.present_conform(~rule, C.SListLen{lo_, hi_, s_}, r))) : Bool}, to_empty(hc))

def Laws.variant_meaning(rule, s, r, hc):
  vm(~rule, s, r, hc)

# ---- a tuple means its positions ----
#
# By induction on the list of schemas, generalized over the raw value. The
# step reads position i of RCons{h, t} as position i-1 of t (each_shift), so
# the tail's claim is the tail's own, from position 0.

def each_shift(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, ss: List<&2, C.Schema>, +h: C.Raw, +t: C.Raw, +i: Nat) -> {C.each_pos(~rule, ss, C.RCons{h, t}, 1n+i) == C.each_pos(~rule, ss, t, i) : Bool}:
  match ss:
    case Nil{}:
      {==}
    case x <> xs:
      Equal.cong(Bool, Bool, v => Bool.and(C.conforms(~rule, x, C.at_raw(t, i), None{}), v), C.each_pos(~rule, xs, C.RCons{h, t}, 2n+i), C.each_pos(~rule, xs, t, 1n+i), each_shift(~rule, xs, h, t, 1n+i))

def zero3(l: Bool, e: Bool) -> {Bool.and(l, Bool.and(e, False{})) == False{} : Bool}:
  match l e:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def and3_swap(a: Bool, +l: Bool, +e: Bool, +c: Bool) -> {Bool.and(a, Bool.and(l, Bool.and(e, c))) == Bool.and(l, Bool.and(e, Bool.and(a, c))) : Bool}:
  match a:
    case True{}:
      Equal.sym(Bool, Bool.and(l, Bool.and(e, c)), Bool.and(l, Bool.and(e, Bool.and(True{}, c))), {==})
    case False{}:
      Equal.sym(Bool, Bool.and(l, Bool.and(e, False{})), False{}, zero3(l, e))

def tm(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, ss: List<&2, C.Schema>, r: C.Raw) -> {C.conforms(~rule, C.tuple_of(ss), r, None{}) == Bool.and(C.raw_list(r), Bool.and(Nat.is_eq(C.raw_len(r), List.length(&2, C.Schema, ss)), C.each_pos(~rule, ss, r, 0n))) : Bool}:
  match ss r:
    case Nil{} C.RNil{}:
      {==}
    case Nil{} C.RCons{h, t}:
      Equal.sym(Bool, Bool.and(C.raw_list(t), False{}), False{}, and_false_l(C.raw_list(t)))
    case Nil{} C.RNum{n}:
      {==}
    case Nil{} C.RBool{b}:
      {==}
    case Nil{} C.RNull{}:
      {==}
    case Nil{} C.RStr{x}:
      {==}
    case Nil{} C.RBad{}:
      {==}
    case Nil{} C.RTooBig{}:
      {==}
    case Nil{} C.RMissing{}:
      {==}
    case Nil{} C.REnd{}:
      {==}
    case Nil{} C.RKey{k, v, o}:
      {==}
    case +x <> +xs C.RCons{+h, +t}:
      %Equal.sym(Bool, C.conforms(~rule, C.tuple_of(xs), t, None{}), Bool.and(C.raw_list(t), Bool.and(Nat.is_eq(C.raw_len(t), List.length(&2, C.Schema, xs)), C.each_pos(~rule, xs, t, 0n))), tm(~rule, xs, t)) : {Bool.and(C.conforms(~rule, x, h, None{}), _) == Bool.and(C.raw_list(t), Bool.and(Nat.is_eq(C.raw_len(t), List.length(&2, C.Schema, xs)), Bool.and(C.conforms(~rule, x, h, None{}), C.each_pos(~rule, xs, C.RCons{h, t}, 1n)))) : Bool}
      %Equal.sym(Bool, C.each_pos(~rule, xs, C.RCons{h, t}, 1n), C.each_pos(~rule, xs, t, 0n), each_shift(~rule, xs, h, t, 0n)) : {Bool.and(C.conforms(~rule, x, h, None{}), Bool.and(C.raw_list(t), Bool.and(Nat.is_eq(C.raw_len(t), List.length(&2, C.Schema, xs)), C.each_pos(~rule, xs, t, 0n)))) == Bool.and(C.raw_list(t), Bool.and(Nat.is_eq(C.raw_len(t), List.length(&2, C.Schema, xs)), Bool.and(C.conforms(~rule, x, h, None{}), _))) : Bool}
      and3_swap(C.conforms(~rule, x, h, None{}), C.raw_list(t), Nat.is_eq(C.raw_len(t), List.length(&2, C.Schema, xs)), C.each_pos(~rule, xs, t, 0n))
    case +x <> +xs C.RNil{}:
      {==}
    case x <> xs C.RNum{n}:
      {==}
    case x <> xs C.RBool{b}:
      {==}
    case x <> xs C.RNull{}:
      {==}
    case x <> xs C.RStr{s}:
      {==}
    case x <> xs C.RBad{}:
      {==}
    case x <> xs C.RTooBig{}:
      {==}
    case x <> xs C.RMissing{}:
      {==}
    case x <> xs C.REnd{}:
      {==}
    case x <> xs C.RKey{k, v, o}:
      {==}

def Laws.tuple_meaning(rule, ss, r):
  tm(~rule, ss, r)

# ---- tools: what enc writes, for the decoder's laws ----
#
# Facts about the value enc writes and the keys a well-formed chain holds.
# Each fact is stated {simple == complex}, so a rewrite replaces the complex
# side (as above).

def and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, to_empty(h))

def and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, to_empty(h))

# The two conjuncts behind the key test. A key a schema reads that is in the
# value carries key_once first, and what conforms asks at that key and after
# it come behind it; a premise that says the whole conjunction holds is read
# as either of the two, for the value under the key (l) or for the rest (r).
def and_key_l(a: Bool, +b: Bool, +c: Bool, h: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      and_l(b, c, h)
    case False{}:
      Empty.absurd({b == True{} : Bool}, to_empty(h))

def and_key_r(a: Bool, +b: Bool, +c: Bool, h: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {c == True{} : Bool}:
  match a:
    case True{}:
      and_r(b, c, h)
    case False{}:
      Empty.absurd({c == True{} : Bool}, to_empty(h))

def not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {False{} == b : Bool}:
  match b:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, to_empty(h))
    case False{}:
      {==}

# enc never writes a missing value, as long as no absent value can reach the
# top of what it writes (opt_at): the schemas that would are an SOptional
# itself, and the ones that hand their value straight to one.
def not_missing(s: C.Schema, x: C.Meaning(s), +hn: {False{} == C.opt_at(s) : Bool}) -> {False{} == C.is_missing(C.enc(s, x)) : Bool}:
  match s x:
    case C.SNat{} n:
      {==}
    case C.SNatIn{lo_, hi_} n:
      {==}
    case C.SBool{} b:
      {==}
    case C.SStr{} n:
      {==}
    case C.SStrLen{lo_, hi_, s2} v:
      not_missing(s2, v, hn)
    case C.SListLen{lo_, hi_, s2} v:
      not_missing(s2, v, hn)
    case C.SOpt{i} None{}:
      {==}
    case C.SOpt{i} Some{v}:
      not_missing(i, v, hn)
    case C.SList{e} Nil{}:
      {==}
    case C.SList{e} h <> t:
      {==}
    case C.SField{n, fs, rest} C.Both{a, b}:
      {==}
    case C.SEnd{} Unit{}:
      {==}
    case C.SRule{s2, tag} v:
      not_missing(s2, v, hn)
    case C.SStrict{s2} v:
      not_missing(s2, v, hn)
    case C.STagged{k, n, cs, rest} Inl{a}:
      {==}
    case C.STagged{k, n, cs, rest} Inr{b}:
      not_missing(rest, b, hn)
    case C.STagEnd{k_} e:
      Empty.absurd({False{} == C.is_missing(C.enc(C.STagEnd{k_}, e)) : Bool}, e)
    case C.STrue{} Unit{}:
      {==}
    case C.SEnum{names} v:
      {==}
    case C.SVariant{+n, vs, +rest} Inl{a}:
      {==}
    case C.SVariant{n, vs, rest} Inr{b}:
      not_missing(rest, b, hn)
    case C.SVEnd{} e:
      Empty.absurd({False{} == C.is_missing(C.enc(C.SVEnd{}, e)) : Bool}, e)
    case C.STuple{ts, rest} C.Both{a, b}:
      {==}
    case C.STEnd{} Unit{}:
      {==}
    case C.SOptional{i} None{}:
      Empty.absurd({False{} == C.is_missing(C.enc(C.SOptional{i}, None{})) : Bool}, to_empty(hn))
    case C.SOptional{i} Some{v}:
      Empty.absurd({False{} == C.is_missing(C.enc(C.SOptional{i}, Some{v})) : Bool}, to_empty(hn))

# Reading a key from the object that starts with it.
def lk_self(+n: String, +v: C.Raw, +o: C.Raw) -> {v == C.lookup(n, C.RKey{n, v, o}) : C.Raw}:
  %MS.eq_refl_sym(n) : {v == C.pick_raw(_, v, C.lookup(n, o)) : C.Raw}
  {==}

# Reading past a key of another name.
def lk_skip(+n: String, +m: String, +v: C.Raw, +o: C.Raw, ne: {False{} == String.eq(n, m) : Bool}) -> {C.lookup(m, o) == C.lookup(m, C.RKey{n, v, o}) : C.Raw}:
  %ne : {C.lookup(m, o) == C.pick_raw(_, v, C.lookup(m, o)) : C.Raw}
  {==}

# The same for the key test: a key of another name is compared to m and never
# matches, so it can be neither the first read of m nor a second one, and the
# test reads the same past it as without it.
def kc_skip(+n: String, +m: String, +v: C.Raw, +o: C.Raw, ne: {False{} == String.eq(n, m) : Bool}) -> {C.key_once(m, o) == C.key_once(m, C.RKey{n, v, o}) : Bool}:
  %ne : {C.key_once(m, o) == C.key_once_at(o, _, m) : Bool}
  {==}

# A key no variant of a well-formed chain names is absent from what enc
# writes for the chain.
def absent(+n: String, s: C.Schema, x: C.Meaning(s), +hf: {C.fresh_v(n, s) == True{} : Bool}) -> {True{} == C.is_missing(C.lookup(n, C.enc(s, x))) : Bool}:
  match s x:
    case C.SVariant{+m, vs, rest} Inl{a}:
      %not_true(String.eq(m, n), and_l(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_v(n, rest)), hf)) : {True{} == C.is_missing(C.pick_raw(_, C.enc(vs, a), C.lookup(n, C.REnd{}))) : Bool}
      {==}
    case C.SVariant{+m, vs, +rest} Inr{b}:
      absent(n, rest, b, and_r(Bool.not(String.eq(n, m)), C.fresh_v(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_v(n, rest)), hf)))
    case C.SVEnd{} e:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SVEnd{}, e))) : Bool}, e)
    case C.SBool{} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SBool{}, v))) : Bool}, to_empty(hf))
    case C.SNatIn{lo_, hi_} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SNatIn{lo_, hi_}, v))) : Bool}, to_empty(hf))
    case C.SStrLen{lo_, hi_, s2} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SStrLen{lo_, hi_, s2}, v))) : Bool}, to_empty(hf))
    case C.SNat{} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SNat{}, v))) : Bool}, to_empty(hf))
    case C.SStr{} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SStr{}, v))) : Bool}, to_empty(hf))
    case C.SOpt{i} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SOpt{i}, v))) : Bool}, to_empty(hf))
    case C.SList{e} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SList{e}, v))) : Bool}, to_empty(hf))
    case C.SField{k, fs, rest} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SField{k, fs, rest}, v))) : Bool}, to_empty(hf))
    case C.SEnd{} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SEnd{}, v))) : Bool}, to_empty(hf))
    case C.SRule{s2, tag} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SRule{s2, tag}, v))) : Bool}, to_empty(hf))
    case C.SStrict{s2} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SStrict{s2}, v))) : Bool}, to_empty(hf))
    case C.STagged{k_, n_, cs_, rest_} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.STagged{k_, n_, cs_, rest_}, v))) : Bool}, to_empty(hf))
    case C.STagEnd{k_} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.STagEnd{k_}, v))) : Bool}, to_empty(hf))
    case C.STrue{} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.STrue{}, v))) : Bool}, to_empty(hf))
    case C.SEnum{names} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SEnum{names}, v))) : Bool}, to_empty(hf))
    case C.STuple{ts, rest} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.STuple{ts, rest}, v))) : Bool}, to_empty(hf))
    case C.STEnd{} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.STEnd{}, v))) : Bool}, to_empty(hf))
    case C.SOptional{i_} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SOptional{i_}, v))) : Bool}, to_empty(hf))
    case C.SListLen{lo_, hi_, s2_} v:
      Empty.absurd({True{} == C.is_missing(C.lookup(n, C.enc(C.SListLen{lo_, hi_, s2_}, v))) : Bool}, to_empty(hf))

# A schema that is not nullable does not write null.
def not_nullish(s: C.Schema, x: C.Meaning(s), +hn: {False{} == C.nullable(s) : Bool}) -> {False{} == C.nullish(C.enc(s, x)) : Bool}:
  match s x:
    case C.SNat{} n:
      {==}
    case C.SNatIn{lo_, hi_} n:
      {==}
    case C.SBool{} b:
      {==}
    case C.SStr{} n:
      {==}
    case C.SStrLen{lo_, hi_, s2} v:
      not_nullish(s2, v, hn)
    case C.SOpt{i} v:
      Empty.absurd({False{} == C.nullish(C.enc(C.SOpt{i}, v)) : Bool}, to_empty(hn))
    case C.SList{e} Nil{}:
      {==}
    case C.SList{e} h <> t:
      {==}
    case C.SField{n, fs, rest} C.Both{a, b}:
      {==}
    case C.SEnd{} Unit{}:
      {==}
    case C.SRule{s2, tag} v:
      not_nullish(s2, v, hn)
    case C.SStrict{s2} v:
      not_nullish(s2, v, hn)
    case C.STagged{k, n, cs, rest} Inl{a}:
      {==}
    case C.STagged{k, n, cs, rest} Inr{b}:
      not_nullish(rest, b, hn)
    case C.STagEnd{k_} e:
      Empty.absurd({False{} == C.nullish(C.enc(C.STagEnd{k_}, e)) : Bool}, e)
    case C.STrue{} Unit{}:
      {==}
    case C.SEnum{names} v:
      {==}
    case C.SVariant{n, vs, rest} Inl{a}:
      {==}
    case C.SVariant{n, vs, rest} Inr{b}:
      not_nullish(rest, b, hn)
    case C.SVEnd{} e:
      Empty.absurd({False{} == C.nullish(C.enc(C.SVEnd{}, e)) : Bool}, e)
    case C.STuple{ts, rest} C.Both{a, b}:
      {==}
    case C.STEnd{} Unit{}:
      {==}
    case C.SOptional{i} v:
      Empty.absurd({False{} == C.nullish(C.enc(C.SOptional{i}, v)) : Bool}, to_empty(hn))
    case C.SListLen{lo_, hi_, s2} v:
      not_nullish(s2, v, hn)

# A tagged case: the tag enc writes reads back as this case's, drop_key
# takes it out again, and no later case of a well-formed chain claims it.

def tag_self(+k: String, +n: String, e: C.Raw) -> {True{} == C.is_tag(k, n, C.RKey{k, C.RStr{n}, e}) : Bool}:
  %MS.eq_refl_sym(k) : {True{} == C.is_str(n, C.pick_raw(_, C.RStr{n}, C.lookup(k, e))) : Bool}
  %MS.eq_refl_sym(n) : {True{} == _ : Bool}
  {==}

def drop_self(+k: String, +v: C.Raw, +e: C.Raw) -> {e == C.drop_key(k, C.RKey{k, v, e}) : C.Raw}:
  %MS.eq_refl_sym(k) : {e == C.pick_raw(_, e, C.RKey{k, v, C.drop_key(k, e)}) : C.Raw}
  {==}

def tag_other(+k: String, +n: String, s: C.Schema, x: C.Meaning(s), +hf: {C.fresh_t(k, n, s) == True{} : Bool}) -> {False{} == C.is_tag(k, n, C.enc(s, x)) : Bool}:
  match s x:
    case C.STagged{+k2, +m, +cs, +rest} Inl{+a}:
      %Equal.sym(Bool, String.eq(k2, k), True{}, and_l(String.eq(k2, k), Bool.and(Bool.not(String.eq(m, n)), C.fresh_t(k, n, rest)), hf)) : {False{} == C.is_str(n, C.pick_raw(_, C.RStr{m}, C.lookup(k, C.enc(cs, a)))) : Bool}
      %not_true(String.eq(m, n), and_l(Bool.not(String.eq(m, n)), C.fresh_t(k, n, rest), and_r(String.eq(k2, k), Bool.and(Bool.not(String.eq(m, n)), C.fresh_t(k, n, rest)), hf))) : {False{} == _ : Bool}
      {==}
    case C.STagged{+k2, +m, cs, +rest} Inr{b}:
      tag_other(k, n, rest, b, and_r(Bool.not(String.eq(m, n)), C.fresh_t(k, n, rest), and_r(String.eq(k2, k), Bool.and(Bool.not(String.eq(m, n)), C.fresh_t(k, n, rest)), hf)))
    case C.STagEnd{k2} e:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.STagEnd{k2}, e)) : Bool}, e)
    case C.SBool{} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SBool{}, x_)) : Bool}, to_empty(hf))
    case C.SNatIn{lo_, hi_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SNatIn{lo_, hi_}, x_)) : Bool}, to_empty(hf))
    case C.SStrLen{lo_, hi_, s2} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SStrLen{lo_, hi_, s2}, x_)) : Bool}, to_empty(hf))
    case C.SNat{} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SNat{}, x_)) : Bool}, to_empty(hf))
    case C.SStr{} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SStr{}, x_)) : Bool}, to_empty(hf))
    case C.SOpt{i_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SOpt{i_}, x_)) : Bool}, to_empty(hf))
    case C.SOptional{i_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SOptional{i_}, x_)) : Bool}, to_empty(hf))
    case C.SListLen{lo_, hi_, s2_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SListLen{lo_, hi_, s2_}, x_)) : Bool}, to_empty(hf))
    case C.SList{e_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SList{e_}, x_)) : Bool}, to_empty(hf))
    case C.SField{f_, fs_, r_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SField{f_, fs_, r_}, x_)) : Bool}, to_empty(hf))
    case C.SEnd{} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SEnd{}, x_)) : Bool}, to_empty(hf))
    case C.SRule{s_, t_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SRule{s_, t_}, x_)) : Bool}, to_empty(hf))
    case C.SStrict{s_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SStrict{s_}, x_)) : Bool}, to_empty(hf))
    case C.STrue{} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.STrue{}, x_)) : Bool}, to_empty(hf))
    case C.SEnum{ns_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SEnum{ns_}, x_)) : Bool}, to_empty(hf))
    case C.SVariant{v_, vs_, r_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SVariant{v_, vs_, r_}, x_)) : Bool}, to_empty(hf))
    case C.SVEnd{} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.SVEnd{}, x_)) : Bool}, to_empty(hf))
    case C.STuple{ts_, rs_} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.STuple{ts_, rs_}, x_)) : Bool}, to_empty(hf))
    case C.STEnd{} x_:
      Empty.absurd({False{} == C.is_tag(k, n, C.enc(C.STEnd{}, x_)) : Bool}, to_empty(hf))

# ---- what was written reads back as itself ----

# A record chain reads past a key it does not name.
def skip_f(+n: String, s: C.Schema, +v: C.Raw, +o: C.Raw, +hf: {C.fresh_f(n, s) == True{} : Bool}) -> {C.dec(s, o) == C.dec(s, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(s)>}:
  match s:
    case C.SField{+m, +fs, +rest}:
      %not_true(String.eq(n, m), and_l(Bool.not(String.eq(n, m)), C.fresh_f(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf))) : {C.dec(C.SField{m, fs, rest}, o) == C.both(C.Meaning(fs), C.Meaning(rest), C.dec(fs, C.pick_raw(_, v, C.lookup(m, o))), C.dec(rest, C.RKey{n, v, o})) : Maybe<&2, C.Both<C.Meaning(fs), C.Meaning(rest)>>}
      %skip_f(n, rest, v, o, and_r(Bool.not(String.eq(n, m)), C.fresh_f(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf))) : {C.dec(C.SField{m, fs, rest}, o) == C.both(C.Meaning(fs), C.Meaning(rest), C.dec(fs, C.lookup(m, o)), _) : Maybe<&2, C.Both<C.Meaning(fs), C.Meaning(rest)>>}
      {==}
    case C.SEnd{}:
      {==}
    case C.SBool{}:
      Empty.absurd({C.dec(C.SBool{}, o) == C.dec(C.SBool{}, C.RKey{n, v, o}) : Maybe<&2, Bool>}, to_empty(hf))
    case C.SNatIn{lo_, hi_}:
      Empty.absurd({C.dec(C.SNatIn{lo_, hi_}, o) == C.dec(C.SNatIn{lo_, hi_}, C.RKey{n, v, o}) : Maybe<&2, Nat>}, to_empty(hf))
    case C.SStrLen{lo_, hi_, s2}:
      Empty.absurd({C.dec(C.SStrLen{lo_, hi_, s2}, o) == C.dec(C.SStrLen{lo_, hi_, s2}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(s2)>}, to_empty(hf))
    case C.SNat{}:
      Empty.absurd({C.dec(C.SNat{}, o) == C.dec(C.SNat{}, C.RKey{n, v, o}) : Maybe<&2, Nat>}, to_empty(hf))
    case C.SStr{}:
      Empty.absurd({C.dec(C.SStr{}, o) == C.dec(C.SStr{}, C.RKey{n, v, o}) : Maybe<&2, String>}, to_empty(hf))
    case C.SOpt{i}:
      Empty.absurd({C.dec(C.SOpt{i}, o) == C.dec(C.SOpt{i}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(C.SOpt{i})>}, to_empty(hf))
    case C.SList{e}:
      Empty.absurd({C.dec(C.SList{e}, o) == C.dec(C.SList{e}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(C.SList{e})>}, to_empty(hf))
    case C.SRule{s2, tag}:
      Empty.absurd({C.dec(C.SRule{s2, tag}, o) == C.dec(C.SRule{s2, tag}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(s2)>}, to_empty(hf))
    case C.SStrict{s2}:
      Empty.absurd({C.dec(C.SStrict{s2}, o) == C.dec(C.SStrict{s2}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(s2)>}, to_empty(hf))
    case C.STagged{k_, n_, cs_, rest_}:
      Empty.absurd({C.dec(C.STagged{k_, n_, cs_, rest_}, o) == C.dec(C.STagged{k_, n_, cs_, rest_}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(C.STagged{k_, n_, cs_, rest_})>}, to_empty(hf))
    case C.STagEnd{k_}:
      Empty.absurd({C.dec(C.STagEnd{k_}, o) == C.dec(C.STagEnd{k_}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(C.STagEnd{k_})>}, to_empty(hf))
    case C.STrue{}:
      Empty.absurd({C.dec(C.STrue{}, o) == C.dec(C.STrue{}, C.RKey{n, v, o}) : Maybe<&2, Unit>}, to_empty(hf))
    case C.SEnum{names}:
      Empty.absurd({C.dec(C.SEnum{names}, o) == C.dec(C.SEnum{names}, C.RKey{n, v, o}) : Maybe<&2, String>}, to_empty(hf))
    case C.SVariant{k, vs, rest}:
      Empty.absurd({C.dec(C.SVariant{k, vs, rest}, o) == C.dec(C.SVariant{k, vs, rest}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(C.SVariant{k, vs, rest})>}, to_empty(hf))
    case C.SVEnd{}:
      Empty.absurd({C.dec(C.SVEnd{}, o) == C.dec(C.SVEnd{}, C.RKey{n, v, o}) : Maybe<&2, Empty>}, to_empty(hf))
    case C.STuple{ts, rest}:
      Empty.absurd({C.dec(C.STuple{ts, rest}, o) == C.dec(C.STuple{ts, rest}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(C.STuple{ts, rest})>}, to_empty(hf))
    case C.STEnd{}:
      Empty.absurd({C.dec(C.STEnd{}, o) == C.dec(C.STEnd{}, C.RKey{n, v, o}) : Maybe<&2, Unit>}, to_empty(hf))
    case C.SOptional{i_}:
      Empty.absurd({C.dec(C.SOptional{i_}, o) == C.dec(C.SOptional{i_}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(C.SOptional{i_})>}, to_empty(hf))
    case C.SListLen{lo_, hi_, s2_}:
      Empty.absurd({C.dec(C.SListLen{lo_, hi_, s2_}, o) == C.dec(C.SListLen{lo_, hi_, s2_}, C.RKey{n, v, o}) : Maybe<&2, C.Meaning(C.SListLen{lo_, hi_, s2_})>}, to_empty(hf))

def de(s: C.Schema, x: C.Meaning(s), +hw: {C.wf(s) == True{} : Bool}) -> {Some{x} == C.dec(s, C.enc(s, x)) : Maybe<&2, C.Meaning(s)>}:
  match s x:
    case C.SNat{} n:
      {==}
    case C.SNatIn{lo_, hi_} n:
      {==}
    case C.SBool{} b:
      {==}
    case C.SStr{} n:
      {==}
    case C.SOpt{i} None{}:
      {==}
    case C.SOpt{+i} Some{+v}:
      %not_nullish(i, v, not_true(C.nullable(i), and_l(Bool.not(C.nullable(i)), C.wf(i), hw))) : {Some{Some{v}} == C.pick_m(Maybe<&2, Maybe<&2, C.Meaning(i)>>, _, Some{None{}}, C.opt_some(C.Meaning(i), C.dec(i, C.enc(i, v)))) : Maybe<&2, Maybe<&2, C.Meaning(i)>>}
      %de(i, v, and_r(Bool.not(C.nullable(i)), C.wf(i), hw)) : {Some{Some{v}} == C.opt_some(C.Meaning(i), _) : Maybe<&2, Maybe<&2, C.Meaning(i)>>}
      {==}
    case C.SList{e} Nil{}:
      {==}
    case C.SList{+e} +h <> +t:
      %de(e, h, and_r(Bool.not(C.opt_at(e)), C.wf(e), hw)) : {Some{h <> t} == C.lcons(C.Meaning(e), _, C.dec(C.SList{e}, C.enc(C.SList{e}, t))) : Maybe<&2, List<&2, C.Meaning(e)>>}
      %de(C.SList{e}, t, hw) : {Some{h <> t} == C.lcons(C.Meaning(e), Some{h}, _) : Maybe<&2, List<&2, C.Meaning(e)>>}
      {==}
    case C.SListLen{lo_, hi_, +s2} v:
      de(s2, v, and_r(Bool.not(C.opt_at(s2)), C.wf(s2), hw))
    case C.SOptional{+i} None{}:
      {==}
    case C.SOptional{+i} Some{+v}:
      %not_missing(i, v, not_true(C.opt_at(i), and_l(Bool.not(C.opt_at(i)), C.wf(i), hw))) : {Some{Some{v}} == C.pick_m(Maybe<&2, Maybe<&2, C.Meaning(i)>>, _, Some{None{}}, C.opt_some(C.Meaning(i), C.dec(i, C.enc(i, v)))) : Maybe<&2, Maybe<&2, C.Meaning(i)>>}
      %de(i, v, and_r(Bool.not(C.opt_at(i)), C.wf(i), hw)) : {Some{Some{v}} == C.opt_some(C.Meaning(i), _) : Maybe<&2, Maybe<&2, C.Meaning(i)>>}
      {==}
    case C.SField{+n, +fs, +rest} C.Both{+a, +b}:
      %lk_self(n, C.enc(fs, a), C.enc(rest, b)) : {Some{C.Both{a, b}} == C.both(C.Meaning(fs), C.Meaning(rest), C.dec(fs, _), C.dec(rest, C.RKey{n, C.enc(fs, a), C.enc(rest, b)})) : Maybe<&2, C.Both<C.Meaning(fs), C.Meaning(rest)>>}
      %skip_f(n, rest, C.enc(fs, a), C.enc(rest, b), and_l(C.fresh_f(n, rest), C.wf(rest), and_r(C.wf(fs), Bool.and(C.fresh_f(n, rest), C.wf(rest)), hw))) : {Some{C.Both{a, b}} == C.both(C.Meaning(fs), C.Meaning(rest), C.dec(fs, C.enc(fs, a)), _) : Maybe<&2, C.Both<C.Meaning(fs), C.Meaning(rest)>>}
      %de(fs, a, and_l(C.wf(fs), Bool.and(C.fresh_f(n, rest), C.wf(rest)), hw)) : {Some{C.Both{a, b}} == C.both(C.Meaning(fs), C.Meaning(rest), _, C.dec(rest, C.enc(rest, b))) : Maybe<&2, C.Both<C.Meaning(fs), C.Meaning(rest)>>}
      %de(rest, b, and_r(C.fresh_f(n, rest), C.wf(rest), and_r(C.wf(fs), Bool.and(C.fresh_f(n, rest), C.wf(rest)), hw))) : {Some{C.Both{a, b}} == C.both(C.Meaning(fs), C.Meaning(rest), Some{a}, _) : Maybe<&2, C.Both<C.Meaning(fs), C.Meaning(rest)>>}
      {==}
    case C.SEnd{} Unit{}:
      {==}
    case C.SStrLen{lo_, hi_, +s2} v:
      de(s2, v, and_r(Bool.not(C.opt_at(s2)), C.wf(s2), hw))
    case C.SRule{+s2, tag} v:
      de(s2, v, and_r(Bool.not(C.opt_at(s2)), C.wf(s2), hw))
    case C.SStrict{+s2} v:
      de(s2, v, and_r(Bool.not(C.opt_at(s2)), C.wf(s2), and_r(C.is_keyed(s2), Bool.and(Bool.not(C.opt_at(s2)), C.wf(s2)), hw)))
    case C.STagged{+k, +n, +cs, +rest} Inl{+a}:
      %tag_self(k, n, C.enc(cs, a)) : {Some{Inl{a}} == C.pick_m(Maybe<&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>>, _, C.map_inl(C.Meaning(cs), C.Meaning(rest), C.dec(cs, C.drop_key(k, C.RKey{k, C.RStr{n}, C.enc(cs, a)}))), C.map_inr(C.Meaning(cs), C.Meaning(rest), C.dec(rest, C.RKey{k, C.RStr{n}, C.enc(cs, a)}))) : Maybe<&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>>}
      %drop_self(k, C.RStr{n}, C.enc(cs, a)) : {Some{Inl{a}} == C.map_inl(C.Meaning(cs), C.Meaning(rest), C.dec(cs, _)) : Maybe<&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>>}
      %de(cs, a, and_l(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest))), and_r(Bool.not(C.opt_at(cs)), Bool.and(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)))), hw))) : {Some{Inl{a}} == C.map_inl(C.Meaning(cs), C.Meaning(rest), _) : Maybe<&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>>}
      {==}
    case C.STagged{+k, +n, +cs, +rest} Inr{+b}:
      %tag_other(k, n, rest, b, and_l(C.fresh_t(k, n, rest), C.wf(rest), and_r(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)), and_r(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest))), and_r(Bool.not(C.opt_at(cs)), Bool.and(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)))), hw))))) : {Some{Inr{b}} == C.pick_m(Maybe<&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>>, _, C.map_inl(C.Meaning(cs), C.Meaning(rest), C.dec(cs, C.drop_key(k, C.enc(rest, b)))), C.map_inr(C.Meaning(cs), C.Meaning(rest), C.dec(rest, C.enc(rest, b)))) : Maybe<&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>>}
      %de(rest, b, and_r(C.fresh_t(k, n, rest), C.wf(rest), and_r(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)), and_r(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest))), and_r(Bool.not(C.opt_at(cs)), Bool.and(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)))), hw))))) : {Some{Inr{b}} == C.map_inr(C.Meaning(cs), C.Meaning(rest), _) : Maybe<&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>>}
      {==}
    case C.STagEnd{k_} e:
      Empty.absurd({Some{e} == C.dec(C.STagEnd{k_}, C.enc(C.STagEnd{k_}, e)) : Maybe<&2, Empty>}, e)
    case C.STrue{} Unit{}:
      {==}
    case C.SEnum{names} v:
      {==}
    case C.SVariant{+n, +vs, +rest} Inl{+a}:
      %lk_self(n, C.enc(vs, a), C.REnd{}) : {Some{Inl{a}} == C.pick_m(Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>, C.is_missing(_), C.map_inr(C.Meaning(vs), C.Meaning(rest), C.dec(rest, C.RKey{n, C.enc(vs, a), C.REnd{}})), C.map_inl(C.Meaning(vs), C.Meaning(rest), C.dec(vs, _))) : Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>}
      %not_missing(vs, a, not_true(C.opt_at(vs), and_l(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw))) : {Some{Inl{a}} == C.pick_m(Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>, _, C.map_inr(C.Meaning(vs), C.Meaning(rest), C.dec(rest, C.RKey{n, C.enc(vs, a), C.REnd{}})), C.map_inl(C.Meaning(vs), C.Meaning(rest), C.dec(vs, C.enc(vs, a)))) : Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>}
      %de(vs, a, and_l(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest)), and_r(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw))) : {Some{Inl{a}} == C.map_inl(C.Meaning(vs), C.Meaning(rest), _) : Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>}
      {==}
    case C.SVariant{+n, +vs, +rest} Inr{+b}:
      %absent(n, rest, b, and_l(C.fresh_v(n, rest), C.wf(rest), and_r(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest)), and_r(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw)))) : {Some{Inr{b}} == C.pick_m(Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>, _, C.map_inr(C.Meaning(vs), C.Meaning(rest), C.dec(rest, C.enc(rest, b))), C.map_inl(C.Meaning(vs), C.Meaning(rest), C.dec(vs, C.lookup(n, C.enc(rest, b))))) : Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>}
      %de(rest, b, and_r(C.fresh_v(n, rest), C.wf(rest), and_r(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest)), and_r(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw)))) : {Some{Inr{b}} == C.map_inr(C.Meaning(vs), C.Meaning(rest), _) : Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>}
      {==}
    case C.SVEnd{} e:
      Empty.absurd({Some{e} == C.dec(C.SVEnd{}, C.enc(C.SVEnd{}, e)) : Maybe<&2, Empty>}, e)
    case C.STuple{+ts, +rest} C.Both{+a, +b}:
      %de(ts, a, and_l(C.wf(ts), Bool.and(Bool.not(C.opt_at(rest)), C.wf(rest)), and_r(Bool.not(C.opt_at(ts)), Bool.and(C.wf(ts), Bool.and(Bool.not(C.opt_at(rest)), C.wf(rest))), hw))) : {Some{C.Both{a, b}} == C.both(C.Meaning(ts), C.Meaning(rest), _, C.dec(rest, C.enc(rest, b))) : Maybe<&2, C.Both<C.Meaning(ts), C.Meaning(rest)>>}
      %de(rest, b, and_r(Bool.not(C.opt_at(rest)), C.wf(rest), and_r(C.wf(ts), Bool.and(Bool.not(C.opt_at(rest)), C.wf(rest)), and_r(Bool.not(C.opt_at(ts)), Bool.and(C.wf(ts), Bool.and(Bool.not(C.opt_at(rest)), C.wf(rest))), hw)))) : {Some{C.Both{a, b}} == C.both(C.Meaning(ts), C.Meaning(rest), Some{a}, _) : Maybe<&2, C.Both<C.Meaning(ts), C.Meaning(rest)>>}
      {==}
    case C.STEnd{} Unit{}:
      {==}

def Laws.decode_encode(s, x, hw):
  Equal.sym(Maybe<&2, C.Meaning(s)>, Some{x}, C.dec(s, C.enc(s, x)), de(s, x, hw))




# ---- a value check accepts can be read ----

def is_some_m(-A: Data, m: Maybe<&2, A>) -> Bool:
  Maybe.is_some(&2, A, m)

def some_opt(-A: Data, m: Maybe<&2, A>, h: {Maybe.is_some(&2, A, m) == True{} : Bool}) -> {Maybe.is_some(&2, Maybe<&2, A>, C.opt_some(A, m)) == True{} : Bool}:
  match m:
    case Some{v}:
      {==}
    case None{}:
      Empty.absurd({Maybe.is_some(&2, Maybe<&2, A>, C.opt_some(A, None{})) == True{} : Bool}, to_empty(h))

def some_cons(-A: Data, m: Maybe<&2, A>, +n: Maybe<&2, List<&2, A>>, h1: {Maybe.is_some(&2, A, m) == True{} : Bool}, h2: {Maybe.is_some(&2, List<&2, A>, n) == True{} : Bool}) -> {Maybe.is_some(&2, List<&2, A>, C.lcons(A, m, n)) == True{} : Bool}:
  match m n:
    case Some{x} Some{xs}:
      {==}
    case None{} n2:
      Empty.absurd({Maybe.is_some(&2, List<&2, A>, C.lcons(A, None{}, n2)) == True{} : Bool}, to_empty(h1))
    case Some{x} None{}:
      Empty.absurd({Maybe.is_some(&2, List<&2, A>, C.lcons(A, Some{x}, None{})) == True{} : Bool}, to_empty(h2))

def some_both(-A: Data, -B: Data, m: Maybe<&2, A>, +n: Maybe<&2, B>, h1: {Maybe.is_some(&2, A, m) == True{} : Bool}, h2: {Maybe.is_some(&2, B, n) == True{} : Bool}) -> {Maybe.is_some(&2, C.Both<A, B>, C.both(A, B, m, n)) == True{} : Bool}:
  match m n:
    case Some{x} Some{y}:
      {==}
    case None{} n2:
      Empty.absurd({Maybe.is_some(&2, C.Both<A, B>, C.both(A, B, None{}, n2)) == True{} : Bool}, to_empty(h1))
    case Some{x} None{}:
      Empty.absurd({Maybe.is_some(&2, C.Both<A, B>, C.both(A, B, Some{x}, None{})) == True{} : Bool}, to_empty(h2))

def some_inl(-A: Data, -B: Data, m: Maybe<&2, A>, h: {Maybe.is_some(&2, A, m) == True{} : Bool}) -> {Maybe.is_some(&2, Either<&2, &2, A, B>, C.map_inl(A, B, m)) == True{} : Bool}:
  match m:
    case Some{v}:
      {==}
    case None{}:
      Empty.absurd({Maybe.is_some(&2, Either<&2, &2, A, B>, C.map_inl(A, B, None{})) == True{} : Bool}, to_empty(h))

def some_inr(-A: Data, -B: Data, m: Maybe<&2, B>, h: {Maybe.is_some(&2, B, m) == True{} : Bool}) -> {Maybe.is_some(&2, Either<&2, &2, A, B>, C.map_inr(A, B, m)) == True{} : Bool}:
  match m:
    case Some{v}:
      {==}
    case None{}:
      Empty.absurd({Maybe.is_some(&2, Either<&2, &2, A, B>, C.map_inr(A, B, None{})) == True{} : Bool}, to_empty(h))

# The variant case: by whether the key is there.
def cd_var(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, b: Bool, +vs: C.Schema, +rest: C.Schema, +n: String, +x: C.Raw, ihr: {C.conforms(~rule, rest, x, None{}) == True{} : Bool} -> {Maybe.is_some(&2, C.Meaning(rest), C.dec(rest, x)) == True{} : Bool}, ihv: {C.conforms(~rule, vs, C.lookup(n, x), None{}) == True{} : Bool} -> {Maybe.is_some(&2, C.Meaning(vs), C.dec(vs, C.lookup(n, x))) == True{} : Bool}, hc: {C.pick_bool(b, C.conforms(~rule, rest, x, None{}), Bool.and(C.key_once(n, x), Bool.and(C.conforms(~rule, vs, C.lookup(n, x), None{}), C.none_present(rest, x)))) == True{} : Bool}) -> {Maybe.is_some(&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>, C.pick_m(Maybe<&2, Either<&2, &2, C.Meaning(vs), C.Meaning(rest)>>, b, C.map_inr(C.Meaning(vs), C.Meaning(rest), C.dec(rest, x)), C.map_inl(C.Meaning(vs), C.Meaning(rest), C.dec(vs, C.lookup(n, x))))) == True{} : Bool}:
  match b:
    case True{}:
      some_inr(C.Meaning(vs), C.Meaning(rest), C.dec(rest, x), ihr(hc))
    case False{}:
      some_inl(C.Meaning(vs), C.Meaning(rest), C.dec(vs, C.lookup(n, x)), ihv(and_key_l(C.key_once(n, x), C.conforms(~rule, vs, C.lookup(n, x), None{}), C.none_present(rest, x), hc)))

def cd_tag(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, kc: Bool, b: Bool, +cs: C.Schema, +rest: C.Schema, +xd: C.Raw, +x: C.Raw, ihc: {C.conforms(~rule, cs, xd, None{}) == True{} : Bool} -> {Maybe.is_some(&2, C.Meaning(cs), C.dec(cs, xd)) == True{} : Bool}, ihr: {C.conforms(~rule, rest, x, None{}) == True{} : Bool} -> {Maybe.is_some(&2, C.Meaning(rest), C.dec(rest, x)) == True{} : Bool}, hc: {C.pick_bool(b, Bool.and(kc, C.conforms(~rule, cs, xd, None{})), C.conforms(~rule, rest, x, None{})) == True{} : Bool}) -> {Maybe.is_some(&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>, C.pick_m(Maybe<&2, Either<&2, &2, C.Meaning(cs), C.Meaning(rest)>>, b, C.map_inl(C.Meaning(cs), C.Meaning(rest), C.dec(cs, xd)), C.map_inr(C.Meaning(cs), C.Meaning(rest), C.dec(rest, x)))) == True{} : Bool}:
  match b:
    case True{}:
      some_inl(C.Meaning(cs), C.Meaning(rest), C.dec(cs, xd), ihc(and_r(kc, C.conforms(~rule, cs, xd, None{}), hc)))
    case False{}:
      some_inr(C.Meaning(cs), C.Meaning(rest), C.dec(rest, x), ihr(hc))

def tu(b: Bool, h: {b == True{} : Bool}) -> {Maybe.is_some(&2, Unit, C.true_unit(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Maybe.is_some(&2, Unit, C.true_unit(False{})) == True{} : Bool}, to_empty(h))

# arms: s r
# arms leaf: Empty.absurd({Maybe.is_some(&2, C.Meaning($S), C.dec($S, $R)) == True{} : Bool}, to_empty(hc))
def cd(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, s: C.Schema, r: C.Raw, +hc: {C.conforms(~rule, s, r, None{}) == True{} : Bool}) -> {Maybe.is_some(&2, C.Meaning(s), C.dec(s, r)) == True{} : Bool}:
  match s r:
    case C.SNat{} C.RNum{n}:
      {==}
    case C.SNat{} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.SNat{} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNat{}), C.dec(C.SNat{}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RNum{+n}:
      {==}
    case C.SNatIn{+lo, +hi} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.SNatIn{+lo, +hi} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SNatIn{lo, hi}), C.dec(C.SNatIn{lo, hi}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RStr{+x}:
      {==}
    case C.SStr{} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.SStr{} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SStr{}), C.dec(C.SStr{}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.SStrLen{+lo, +hi, +s2} +x:
      cd(~rule, s2, x, and_l(C.conforms(~rule, s2, x, None{}), C.len_ok(lo, hi, x), hc))
    case C.SOpt{+i} C.RNum{+n}:
      some_opt(C.Meaning(i), C.dec(i, C.RNum{n}), cd(~rule, i, C.RNum{n}, hc))
    case C.SOpt{+i} C.RBool{+bb}:
      some_opt(C.Meaning(i), C.dec(i, C.RBool{bb}), cd(~rule, i, C.RBool{bb}, hc))
    case C.SOpt{+i} C.RNull{}:
      {==}
    case C.SOpt{+i} C.RStr{+x}:
      some_opt(C.Meaning(i), C.dec(i, C.RStr{x}), cd(~rule, i, C.RStr{x}, hc))
    case C.SOpt{+i} C.RBad{}:
      some_opt(C.Meaning(i), C.dec(i, C.RBad{}), cd(~rule, i, C.RBad{}, hc))
    case C.SOpt{+i} C.RTooBig{}:
      some_opt(C.Meaning(i), C.dec(i, C.RTooBig{}), cd(~rule, i, C.RTooBig{}, hc))
    case C.SOpt{+i} C.RMissing{}:
      {==}
    case C.SOpt{+i} C.RNil{}:
      some_opt(C.Meaning(i), C.dec(i, C.RNil{}), cd(~rule, i, C.RNil{}, hc))
    case C.SOpt{+i} C.RCons{+h, +t}:
      some_opt(C.Meaning(i), C.dec(i, C.RCons{h, t}), cd(~rule, i, C.RCons{h, t}, hc))
    case C.SOpt{+i} C.REnd{}:
      some_opt(C.Meaning(i), C.dec(i, C.REnd{}), cd(~rule, i, C.REnd{}, hc))
    case C.SOpt{+i} C.RKey{+k, +v, +o}:
      some_opt(C.Meaning(i), C.dec(i, C.RKey{k, v, o}), cd(~rule, i, C.RKey{k, v, o}, hc))
    case C.SList{+e} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.SList{+e} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SList{+e} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SList{+e} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.SList{+e} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SList{+e} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SList{+e} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SList{+e} C.RNil{}:
      {==}
    case C.SList{+e} C.RCons{+h, +t}:
      some_cons(C.Meaning(e), C.dec(e, h), C.dec(C.SList{e}, t), cd(~rule, e, h, and_l(C.conforms(~rule, e, h, None{}), C.conforms(~rule, C.SList{e}, t, None{}), hc)), cd(~rule, C.SList{e}, t, and_r(C.conforms(~rule, e, h, None{}), C.conforms(~rule, C.SList{e}, t, None{}), hc)))
    case C.SList{+e} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.SList{+e} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SList{e}), C.dec(C.SList{e}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SField{fn, fs, rest}), C.dec(C.SField{fn, fs, rest}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SField{+fn, +fs, +rest} C.REnd{}:
      some_both(C.Meaning(fs), C.Meaning(rest), C.dec(fs, C.RMissing{}), C.dec(rest, C.REnd{}), cd(~rule, fs, C.RMissing{}, and_l(C.conforms(~rule, fs, C.RMissing{}, None{}), C.conforms(~rule, rest, C.REnd{}, None{}), hc)), cd(~rule, rest, C.REnd{}, and_r(C.conforms(~rule, fs, C.RMissing{}, None{}), C.conforms(~rule, rest, C.REnd{}, None{}), hc)))
    case C.SField{+fn, +fs, +rest} C.RKey{+k, +v, +o}:
      some_both(C.Meaning(fs), C.Meaning(rest), C.dec(fs, C.lookup(fn, C.RKey{k, v, o})), C.dec(rest, C.RKey{k, v, o}), cd(~rule, fs, C.lookup(fn, C.RKey{k, v, o}), and_key_l(C.key_once(fn, C.RKey{k, v, o}), C.conforms(~rule, fs, C.lookup(fn, C.RKey{k, v, o}), None{}), C.conforms(~rule, rest, C.RKey{k, v, o}, None{}), hc)), cd(~rule, rest, C.RKey{k, v, o}, and_key_r(C.key_once(fn, C.RKey{k, v, o}), C.conforms(~rule, fs, C.lookup(fn, C.RKey{k, v, o}), None{}), C.conforms(~rule, rest, C.RKey{k, v, o}, None{}), hc)))
    case C.SEnd{} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnd{}), C.dec(C.SEnd{}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SEnd{} C.REnd{}:
      {==}
    case C.SEnd{} C.RKey{k, v, o}:
      {==}
    case C.SRule{+s2, +tag} +x:
      cd(~rule, s2, x, and_l(C.conforms(~rule, s2, x, None{}), Maybe.is_none(&2, C.Err, rule(tag, x)), hc))
    case C.SStrict{+s2} +x:
      cd(~rule, s2, x, and_l(C.conforms(~rule, s2, x, None{}), C.no_extra(C.key_names(s2), x), hc))
    case C.STagged{+k, +n, +cs, +rest} +x:
      cd_tag(~rule, C.key_once(k, x), C.is_tag(k, n, x), cs, rest, C.drop_key(k, x), x, hh => cd(~rule, cs, C.drop_key(k, x), hh), hh => cd(~rule, rest, x, hh), hc)
    case C.STagEnd{key_} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.STagEnd{key_} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STagEnd{key_}), C.dec(C.STagEnd{key_}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RBool{bb}:
      {==}
    case C.SBool{} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.SBool{} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SBool{}), C.dec(C.SBool{}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RBool{bb}:
      tu(bb, hc)
    case C.STrue{} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.STrue{} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STrue{}), C.dec(C.STrue{}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RStr{x}:
      {==}
    case C.SEnum{names} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.SEnum{names} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SEnum{names}), C.dec(C.SEnum{names}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVariant{vn, vs, rest}), C.dec(C.SVariant{vn, vs, rest}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SVariant{+vn, +vs, +rest} C.REnd{}:
      some_inr(C.Meaning(vs), C.Meaning(rest), C.dec(rest, C.REnd{}), cd(~rule, rest, C.REnd{}, hc))
    case C.SVariant{+vn, +vs, +rest} C.RKey{+k, +v, +o}:
      cd_var(~rule, C.is_missing(C.lookup(vn, C.RKey{k, v, o})), vs, rest, vn, C.RKey{k, v, o}, h => cd(~rule, rest, C.RKey{k, v, o}, h), h => cd(~rule, vs, C.lookup(vn, C.RKey{k, v, o}), h), hc)
    case C.SVEnd{} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.SVEnd{} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.SVEnd{}), C.dec(C.SVEnd{}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RNil{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RNil{})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RCons{+h, +t}:
      some_both(C.Meaning(ts), C.Meaning(rest), C.dec(ts, h), C.dec(rest, t), cd(~rule, ts, h, and_l(C.conforms(~rule, ts, h, None{}), C.conforms(~rule, rest, t, None{}), hc)), cd(~rule, rest, t, and_r(C.conforms(~rule, ts, h, None{}), C.conforms(~rule, rest, t, None{}), hc)))
    case C.STuple{+ts, +rest} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.STuple{+ts, +rest} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STuple{ts, rest}), C.dec(C.STuple{ts, rest}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RNum{n}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RNum{n})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RBool{+bb}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RBool{bb})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RNull{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RNull{})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RStr{+x}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RStr{x})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RBad{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RBad{})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RTooBig{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RTooBig{})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RMissing{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RMissing{})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RNil{}:
      {==}
    case C.STEnd{} C.RCons{+h, +t}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RCons{h, t})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.REnd{}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.REnd{})) == True{} : Bool}, to_empty(hc))
    case C.STEnd{} C.RKey{+k, +v, +o}:
      Empty.absurd({Maybe.is_some(&2, C.Meaning(C.STEnd{}), C.dec(C.STEnd{}, C.RKey{k, v, o})) == True{} : Bool}, to_empty(hc))
    case C.SOptional{+i} C.RNum{+n}:
      some_opt(C.Meaning(i), C.dec(i, C.RNum{n}), cd(~rule, i, C.RNum{n}, hc))
    case C.SOptional{+i} C.RBool{+bb}:
      some_opt(C.Meaning(i), C.dec(i, C.RBool{bb}), cd(~rule, i, C.RBool{bb}, hc))
    case C.SOptional{+i} C.RNull{}:
      some_opt(C.Meaning(i), C.dec(i, C.RNull{}), cd(~rule, i, C.RNull{}, hc))
    case C.SOptional{+i} C.RStr{+x}:
      some_opt(C.Meaning(i), C.dec(i, C.RStr{x}), cd(~rule, i, C.RStr{x}, hc))
    case C.SOptional{+i} C.RBad{}:
      some_opt(C.Meaning(i), C.dec(i, C.RBad{}), cd(~rule, i, C.RBad{}, hc))
    case C.SOptional{+i} C.RTooBig{}:
      some_opt(C.Meaning(i), C.dec(i, C.RTooBig{}), cd(~rule, i, C.RTooBig{}, hc))
    case C.SOptional{+i} C.RMissing{}:
      {==}
    case C.SOptional{+i} C.RNil{}:
      some_opt(C.Meaning(i), C.dec(i, C.RNil{}), cd(~rule, i, C.RNil{}, hc))
    case C.SOptional{+i} C.RCons{+h, +t}:
      some_opt(C.Meaning(i), C.dec(i, C.RCons{h, t}), cd(~rule, i, C.RCons{h, t}, hc))
    case C.SOptional{+i} C.REnd{}:
      some_opt(C.Meaning(i), C.dec(i, C.REnd{}), cd(~rule, i, C.REnd{}, hc))
    case C.SOptional{+i} C.RKey{+k, +v, +o}:
      some_opt(C.Meaning(i), C.dec(i, C.RKey{k, v, o}), cd(~rule, i, C.RKey{k, v, o}, hc))
    case C.SListLen{+lo, +hi, +s2} +r:
      cd(~rule, s2, r, and_r(C.list_len_ok(lo, hi, r), C.conforms(~rule, s2, r, None{}), hc))

def Laws.checked_decodes(rule, s, r, hc):
  cd(~rule, s, r, hc)


# ---- tools: what wf's tag rule buys, the key is nowhere in what enc wrote ----
#
# no_key(k, s) says the object enc builds for s holds no key k. That is what
# key_once_at needs of the value a tag key was already written into: the walk
# reads every key of the object, so a key that is not there is never the
# second one -- whatever flag the walk arrived with. The flag is a parameter
# because the walk's own step at a key j turns it into Bool.or(b, eq(j, k)),
# and with eq(j, k) false (which is what no_key's own arms say of j) that is
# the flag it already had.

def key_step(b: Bool, +j: String, +k: String, +s2: C.Schema, x2: C.Meaning(s2), +hf: {False{} == String.eq(j, k) : Bool}, ih1: {C.key_once_at(C.enc(s2, x2), True{}, k) == True{} : Bool}, ih0: {C.key_once_at(C.enc(s2, x2), False{}, k) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.and(b, String.eq(j, k))), C.key_once_at(C.enc(s2, x2), Bool.or(b, String.eq(j, k)), k)) == True{} : Bool}:
  match b:
    case True{}:
      %hf : {Bool.and(Bool.not(_), C.key_once_at(C.enc(s2, x2), True{}, k)) == True{} : Bool}
      ih1
    case False{}:
      %hf : {C.key_once_at(C.enc(s2, x2), _, k) == True{} : Bool}
      ih0

def no_key_once(+k: String, s: C.Schema, x: C.Meaning(s), b: Bool, +h: {C.no_key(k, s) == True{} : Bool}) -> {C.key_once_at(C.enc(s, x), b, k) == True{} : Bool}:
  match s x:
    case C.SNat{} n:
      {==}
    case C.SNatIn{lo_, hi_} n:
      {==}
    case C.SStr{} n:
      {==}
    case C.SBool{} bb:
      {==}
    case C.STrue{} Unit{}:
      {==}
    case C.SEnum{ns} e:
      {==}
    case C.SEnd{} Unit{}:
      {==}
    case C.STEnd{} Unit{}:
      {==}
    case C.SVEnd{} e:
      Empty.absurd({C.key_once_at(C.enc(C.SVEnd{}, e), b, k) == True{} : Bool}, e)
    case C.STagEnd{k2} e:
      Empty.absurd({C.key_once_at(C.enc(C.STagEnd{k2}, e), b, k) == True{} : Bool}, e)
    case C.SList{e} Nil{}:
      {==}
    case C.SList{e} +hh <> +tt:
      {==}
    case C.STuple{ts, rs} C.Both{aa, bb}:
      {==}
    case C.SStrLen{lo_, hi_, s2} v:
      no_key_once(k, s2, v, b, h)
    case C.SListLen{lo_, hi_, s2} v:
      no_key_once(k, s2, v, b, h)
    case C.SRule{s2, tag} v:
      no_key_once(k, s2, v, b, h)
    case C.SStrict{s2} v:
      no_key_once(k, s2, v, b, h)
    case C.SOpt{i} None{}:
      {==}
    case C.SOpt{i} Some{v}:
      no_key_once(k, i, v, b, h)
    case C.SOptional{i} None{}:
      {==}
    case C.SOptional{i} Some{v}:
      no_key_once(k, i, v, b, h)
    case C.SField{+n, fs, +rest} C.Both{a, +b2}:
      key_step(b, n, k, rest, b2, not_true(String.eq(n, k), and_l(Bool.not(String.eq(n, k)), Bool.and(Bool.not(String.eq(k, n)), C.no_key(k, rest)), h)), no_key_once(k, rest, b2, True{}, and_r(Bool.not(String.eq(k, n)), C.no_key(k, rest), and_r(Bool.not(String.eq(n, k)), Bool.and(Bool.not(String.eq(k, n)), C.no_key(k, rest)), h))), no_key_once(k, rest, b2, False{}, and_r(Bool.not(String.eq(k, n)), C.no_key(k, rest), and_r(Bool.not(String.eq(n, k)), Bool.and(Bool.not(String.eq(k, n)), C.no_key(k, rest)), h))))
    case C.SVariant{n, vs, rest} Inl{a}:
      key_step(b, n, k, C.SEnd{}, Unit{}, not_true(String.eq(n, k), and_l(Bool.not(String.eq(n, k)), Bool.and(Bool.not(String.eq(k, n)), C.no_key(k, rest)), h)), {==}, {==})
    case C.SVariant{+n, vs, +rest} Inr{b2}:
      no_key_once(k, rest, b2, b, and_r(Bool.not(String.eq(k, n)), C.no_key(k, rest), and_r(Bool.not(String.eq(n, k)), Bool.and(Bool.not(String.eq(k, n)), C.no_key(k, rest)), h)))
    case C.STagged{+k2, n2, +cs2, +rest2} Inl{+a}:
      key_step(b, k2, k, cs2, a, not_true(String.eq(k2, k), and_l(Bool.not(String.eq(k2, k)), Bool.and(Bool.not(String.eq(k, k2)), Bool.and(C.no_key(k, cs2), C.no_key(k, rest2))), h)), no_key_once(k, cs2, a, True{}, and_l(C.no_key(k, cs2), C.no_key(k, rest2), and_r(Bool.not(String.eq(k, k2)), Bool.and(C.no_key(k, cs2), C.no_key(k, rest2)), and_r(Bool.not(String.eq(k2, k)), Bool.and(Bool.not(String.eq(k, k2)), Bool.and(C.no_key(k, cs2), C.no_key(k, rest2))), h)))), no_key_once(k, cs2, a, False{}, and_l(C.no_key(k, cs2), C.no_key(k, rest2), and_r(Bool.not(String.eq(k, k2)), Bool.and(C.no_key(k, cs2), C.no_key(k, rest2)), and_r(Bool.not(String.eq(k2, k)), Bool.and(Bool.not(String.eq(k, k2)), Bool.and(C.no_key(k, cs2), C.no_key(k, rest2))), h)))))
    case C.STagged{+k2, n2, +cs2, +rest2} Inr{b2}:
      no_key_once(k, rest2, b2, b, and_r(C.no_key(k, cs2), C.no_key(k, rest2), and_r(Bool.not(String.eq(k, k2)), Bool.and(C.no_key(k, cs2), C.no_key(k, rest2)), and_r(Bool.not(String.eq(k2, k)), Bool.and(Bool.not(String.eq(k, k2)), Bool.and(C.no_key(k, cs2), C.no_key(k, rest2))), h))))

# ---- what is written is accepted ----

# enc writes an object for a record chain and for a variant chain.
def obj_f(+n: String, s: C.Schema, x: C.Meaning(s), +hf: {C.fresh_f(n, s) == True{} : Bool}) -> {C.is_object(C.enc(s, x)) == True{} : Bool}:
  match s x:
    case C.SBool{} v:
      Empty.absurd({C.is_object(C.enc(C.SBool{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SNatIn{lo_, hi_} v:
      Empty.absurd({C.is_object(C.enc(C.SNatIn{lo_, hi_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SStrLen{lo_, hi_, s2} v:
      Empty.absurd({C.is_object(C.enc(C.SStrLen{lo_, hi_, s2}, v)) == True{} : Bool}, to_empty(hf))
    case C.SNat{} v:
      Empty.absurd({C.is_object(C.enc(C.SNat{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SStr{} v:
      Empty.absurd({C.is_object(C.enc(C.SStr{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SOpt{i_} v:
      Empty.absurd({C.is_object(C.enc(C.SOpt{i_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SList{e_} v:
      Empty.absurd({C.is_object(C.enc(C.SList{e_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SField{k, fs, rest} C.Both{a, b}:
      {==}
    case C.SEnd{} Unit{}:
      {==}
    case C.SRule{s2_, tag_} v:
      Empty.absurd({C.is_object(C.enc(C.SRule{s2_, tag_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SStrict{s2_} v:
      Empty.absurd({C.is_object(C.enc(C.SStrict{s2_}, v)) == True{} : Bool}, to_empty(hf))
    case C.STagged{k_, n_, cs_, rest_} v:
      Empty.absurd({C.is_object(C.enc(C.STagged{k_, n_, cs_, rest_}, v)) == True{} : Bool}, to_empty(hf))
    case C.STagEnd{k_} v:
      Empty.absurd({C.is_object(C.enc(C.STagEnd{k_}, v)) == True{} : Bool}, to_empty(hf))
    case C.STrue{} v:
      Empty.absurd({C.is_object(C.enc(C.STrue{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SEnum{names_} v:
      Empty.absurd({C.is_object(C.enc(C.SEnum{names_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SVariant{k_, vs_, rest_} v:
      Empty.absurd({C.is_object(C.enc(C.SVariant{k_, vs_, rest_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SVEnd{} e:
      Empty.absurd({C.is_object(C.enc(C.SVEnd{}, e)) == True{} : Bool}, e)
    case C.STuple{ts_, rest_} v:
      Empty.absurd({C.is_object(C.enc(C.STuple{ts_, rest_}, v)) == True{} : Bool}, to_empty(hf))
    case C.STEnd{} v:
      Empty.absurd({C.is_object(C.enc(C.STEnd{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SOptional{i_} v:
      Empty.absurd({C.is_object(C.enc(C.SOptional{i_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SListLen{lo_, hi_, s2_} v:
      Empty.absurd({C.is_object(C.enc(C.SListLen{lo_, hi_, s2_}, v)) == True{} : Bool}, to_empty(hf))

def obj_v(+n: String, s: C.Schema, x: C.Meaning(s), +hf: {C.fresh_v(n, s) == True{} : Bool}) -> {C.is_object(C.enc(s, x)) == True{} : Bool}:
  match s x:
    case C.SBool{} v:
      Empty.absurd({C.is_object(C.enc(C.SBool{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SNatIn{lo_, hi_} v:
      Empty.absurd({C.is_object(C.enc(C.SNatIn{lo_, hi_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SStrLen{lo_, hi_, s2} v:
      Empty.absurd({C.is_object(C.enc(C.SStrLen{lo_, hi_, s2}, v)) == True{} : Bool}, to_empty(hf))
    case C.SNat{} v:
      Empty.absurd({C.is_object(C.enc(C.SNat{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SStr{} v:
      Empty.absurd({C.is_object(C.enc(C.SStr{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SOpt{i_} v:
      Empty.absurd({C.is_object(C.enc(C.SOpt{i_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SList{e_} v:
      Empty.absurd({C.is_object(C.enc(C.SList{e_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SField{k_, fs_, rest_} v:
      Empty.absurd({C.is_object(C.enc(C.SField{k_, fs_, rest_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SEnd{} v:
      Empty.absurd({C.is_object(C.enc(C.SEnd{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SRule{s2_, tag_} v:
      Empty.absurd({C.is_object(C.enc(C.SRule{s2_, tag_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SStrict{s2_} v:
      Empty.absurd({C.is_object(C.enc(C.SStrict{s2_}, v)) == True{} : Bool}, to_empty(hf))
    case C.STagged{k_, n_, cs_, rest_} v:
      Empty.absurd({C.is_object(C.enc(C.STagged{k_, n_, cs_, rest_}, v)) == True{} : Bool}, to_empty(hf))
    case C.STagEnd{k_} v:
      Empty.absurd({C.is_object(C.enc(C.STagEnd{k_}, v)) == True{} : Bool}, to_empty(hf))
    case C.STrue{} v:
      Empty.absurd({C.is_object(C.enc(C.STrue{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SEnum{names_} v:
      Empty.absurd({C.is_object(C.enc(C.SEnum{names_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SVariant{k, vs, rest} Inl{a}:
      {==}
    case C.SVariant{+k, vs, +rest} Inr{b}:
      obj_v(n, rest, b, and_r(Bool.not(String.eq(n, k)), C.fresh_v(n, rest), and_r(Bool.not(String.eq(k, n)), Bool.and(Bool.not(String.eq(n, k)), C.fresh_v(n, rest)), hf)))
    case C.SVEnd{} e:
      Empty.absurd({C.is_object(C.enc(C.SVEnd{}, e)) == True{} : Bool}, e)
    case C.STuple{ts_, rest_} v:
      Empty.absurd({C.is_object(C.enc(C.STuple{ts_, rest_}, v)) == True{} : Bool}, to_empty(hf))
    case C.STEnd{} v:
      Empty.absurd({C.is_object(C.enc(C.STEnd{}, v)) == True{} : Bool}, to_empty(hf))
    case C.SOptional{i_} v:
      Empty.absurd({C.is_object(C.enc(C.SOptional{i_}, v)) == True{} : Bool}, to_empty(hf))
    case C.SListLen{lo_, hi_, s2_} v:
      Empty.absurd({C.is_object(C.enc(C.SListLen{lo_, hi_, s2_}, v)) == True{} : Bool}, to_empty(hf))

# No variant of a well-formed chain is in an object holding one other key.
def np(+n: String, s: C.Schema, +v: C.Raw, +hf: {C.fresh_v(n, s) == True{} : Bool}) -> {C.none_present(s, C.RKey{n, v, C.REnd{}}) == True{} : Bool}:
  match s:
    case C.SVariant{+m, vs, +rest}:
      %not_true(String.eq(n, m), and_l(Bool.not(String.eq(n, m)), C.fresh_v(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_v(n, rest)), hf))) : {Bool.and(C.is_missing(C.pick_raw(_, v, C.lookup(m, C.REnd{}))), C.none_present(rest, C.RKey{n, v, C.REnd{}})) == True{} : Bool}
      np(n, rest, v, and_r(Bool.not(String.eq(n, m)), C.fresh_v(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_v(n, rest)), hf)))
    case C.SNat{}:
      {==}
    case C.SNatIn{lo_, hi_}:
      {==}
    case C.SBool{}:
      {==}
    case C.SStrLen{lo_, hi_, s2_}:
      {==}
    case C.SStr{}:
      {==}
    case C.SOpt{i_}:
      {==}
    case C.SList{e_}:
      {==}
    case C.SField{k_, fs_, rest_}:
      {==}
    case C.SEnd{}:
      {==}
    case C.SRule{s2_, tag_}:
      {==}
    case C.SStrict{s2_}:
      {==}
    case C.STagged{k_, n_, cs_, rest_}:
      {==}
    case C.STagEnd{k_}:
      {==}
    case C.STrue{}:
      {==}
    case C.SEnum{names_}:
      {==}
    case C.SVEnd{}:
      {==}
    case C.SOptional{i_}:
      {==}
    case C.SListLen{lo_, hi_, s2_}:
      {==}
    case C.STuple{ts_, rest_}:
      {==}
    case C.STEnd{}:
      {==}

# n is not a key of what enc writes for the record chain s: enc writes the
# chain's own keys and nothing else, and the chain names none of them n. The
# key test is read with its flag already set -- the read that set it is the
# schema's own first key, and this says the walk past it never reads n again.
def key_once_enc(+n: String, s: C.Schema, x: C.Meaning(s), +hf: {C.fresh_f(n, s) == True{} : Bool}) -> {True{} == C.key_once_at(C.enc(s, x), True{}, n) : Bool}:
  match s x:
    case C.SBool{} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SBool{}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SNatIn{lo_, hi_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SNatIn{lo_, hi_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SStrLen{lo_, hi_, s2} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SStrLen{lo_, hi_, s2}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SNat{} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SNat{}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SStr{} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SStr{}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SOpt{i_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SOpt{i_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SList{e_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SList{e_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SField{+m, +fs, +rest} C.Both{+a, +b}:
      %not_true(String.eq(m, n), and_l(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf)) : {True{} == Bool.and(Bool.not(_), C.key_once_at(C.enc(rest, b), True{}, n)) : Bool}
      key_once_enc(n, rest, b, and_r(Bool.not(String.eq(n, m)), C.fresh_f(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf)))
    case C.SEnd{} Unit{}:
      {==}
    case C.SRule{s2_, tag_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SRule{s2_, tag_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SStrict{s2_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SStrict{s2_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.STagged{k_, n_, cs_, rest_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.STagged{k_, n_, cs_, rest_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.STagEnd{k_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.STagEnd{k_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.STrue{} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.STrue{}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SEnum{names_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SEnum{names_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SVariant{k_, vs_, rest_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SVariant{k_, vs_, rest_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SVEnd{} e:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SVEnd{}, e), True{}, n) : Bool}, e)
    case C.STuple{ts_, rest_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.STuple{ts_, rest_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.STEnd{} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.STEnd{}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SOptional{i_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SOptional{i_}, v), True{}, n) : Bool}, to_empty(hf))
    case C.SListLen{lo_, hi_, s2_} v:
      Empty.absurd({True{} == C.key_once_at(C.enc(C.SListLen{lo_, hi_, s2_}, v), True{}, n) : Bool}, to_empty(hf))

# A present value of an optional schema conforms as its inner schema does.
def opt_conf(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, i: C.Schema, r: C.Raw, +hn: {False{} == C.nullish(r) : Bool}) -> {C.conforms(~rule, i, r, None{}) == C.conforms(~rule, C.SOpt{i}, r, None{}) : Bool}:
  match r:
    case C.RNull{}:
      Empty.absurd({C.conforms(~rule, i, C.RNull{}, None{}) == C.conforms(~rule, C.SOpt{i}, C.RNull{}, None{}) : Bool}, to_empty(hn))
    case C.RMissing{}:
      Empty.absurd({C.conforms(~rule, i, C.RMissing{}, None{}) == C.conforms(~rule, C.SOpt{i}, C.RMissing{}, None{}) : Bool}, to_empty(hn))
    case C.RNum{n}:
      {==}
    case C.RBool{b}:
      {==}
    case C.RStr{s}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h, t}:
      {==}
    case C.REnd{}:
      {==}
    case C.RKey{k, w, o}:
      {==}

# A variant chain reads past its first variant when that key is absent.
def var_skip(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, +n: String, +vs: C.Schema, +rest: C.Schema, r: C.Raw, +ho: {C.is_object(r) == True{} : Bool}, +hm: {True{} == C.is_missing(C.lookup(n, r)) : Bool}) -> {C.conforms(~rule, rest, r, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, r, None{}) : Bool}:
  match r:
    case C.REnd{}:
      {==}
    case C.RKey{+k, +w, +o}:
      %hm : {C.conforms(~rule, rest, C.RKey{k, w, o}, None{}) == C.pick_bool(_, C.conforms(~rule, rest, C.RKey{k, w, o}, None{}), Bool.and(C.key_once(n, C.RKey{k, w, o}), Bool.and(C.conforms(~rule, vs, C.lookup(n, C.RKey{k, w, o}), None{}), C.none_present(rest, C.RKey{k, w, o})))) : Bool}
      {==}
    case C.RNum{n_}:
      Empty.absurd({C.conforms(~rule, rest, C.RNum{n_}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RNum{n_}, None{}) : Bool}, to_empty(ho))
    case C.RBool{b_}:
      Empty.absurd({C.conforms(~rule, rest, C.RBool{b_}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RBool{b_}, None{}) : Bool}, to_empty(ho))
    case C.RNull{}:
      Empty.absurd({C.conforms(~rule, rest, C.RNull{}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RNull{}, None{}) : Bool}, to_empty(ho))
    case C.RStr{s_}:
      Empty.absurd({C.conforms(~rule, rest, C.RStr{s_}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RStr{s_}, None{}) : Bool}, to_empty(ho))
    case C.RBad{}:
      Empty.absurd({C.conforms(~rule, rest, C.RBad{}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RBad{}, None{}) : Bool}, to_empty(ho))
    case C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, rest, C.RTooBig{}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RTooBig{}, None{}) : Bool}, to_empty(ho))
    case C.RMissing{}:
      Empty.absurd({C.conforms(~rule, rest, C.RMissing{}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RMissing{}, None{}) : Bool}, to_empty(ho))
    case C.RNil{}:
      Empty.absurd({C.conforms(~rule, rest, C.RNil{}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RNil{}, None{}) : Bool}, to_empty(ho))
    case C.RCons{h_, t_}:
      Empty.absurd({C.conforms(~rule, rest, C.RCons{h_, t_}, None{}) == C.conforms(~rule, C.SVariant{n, vs, rest}, C.RCons{h_, t_}, None{}) : Bool}, to_empty(ho))

# A record chain ignores a key it does not name.
# arms: s o
# arms leaf: Empty.absurd({C.conforms(~rule, $S, $R, None{}) == C.conforms(~rule, $S, C.RKey{n, v, $R}, None{}) : Bool}, to_empty($W))
# arms why: RNum=ho RBool=ho RNull=ho RStr=ho RBad=ho RTooBig=ho RMissing=ho RNil=ho RCons=ho SNat=hf SStr=hf SOpt=hf SList=hf SRule=hf SStrict=hf SBool=hf SNatIn=hf SStrLen=hf STagged=hf STagEnd=hf STrue=hf SEnum=hf SVariant=hf SVEnd=hf STuple=hf STEnd=hf SOptional=hf SListLen=hf
def skip_c(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, +n: String, s: C.Schema, +v: C.Raw, o: C.Raw, +hf: {C.fresh_f(n, s) == True{} : Bool}, +ho: {C.is_object(o) == True{} : Bool}) -> {C.conforms(~rule, s, o, None{}) == C.conforms(~rule, s, C.RKey{n, v, o}, None{}) : Bool}:
  match s o:
    case C.SNat{} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RNull{}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RBad{}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RMissing{}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RNil{}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SNat{} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.REnd{}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SNat{} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SNat{}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SNat{}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SNatIn{lo_, hi_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RNull{}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RBad{}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RNil{}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SNatIn{lo_, hi_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.REnd{}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SNatIn{lo_, hi_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SNatIn{lo_, hi_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SStr{} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RNull{}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RBad{}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RMissing{}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RNil{}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SStr{} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.REnd{}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SStr{} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SStr{}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SStr{}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SStrLen{lo_, hi_, s_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RNull{}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RBad{}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RNil{}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SStrLen{lo_, hi_, s_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.REnd{}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SStrLen{lo_, hi_, s_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SStrLen{lo_, hi_, s_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SOpt{inner_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RNull{}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RBad{}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RNil{}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SOpt{inner_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.REnd{}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SOpt{inner_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SOpt{inner_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SOpt{inner_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SList{elem_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RNull{}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RBad{}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RNil{}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SList{elem_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.REnd{}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SList{elem_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SList{elem_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SList{elem_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SField{+m, +fs, +rest} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RNull{}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RBad{}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RMissing{}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RNil{}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SField{m, fs, rest}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SField{m, fs, rest}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SField{+m, +fs, +rest} C.REnd{}:
      %lk_skip(n, m, v, C.REnd{}, not_true(String.eq(n, m), and_l(Bool.not(String.eq(n, m)), C.fresh_f(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf)))) : {Bool.and(C.conforms(~rule, fs, C.RMissing{}, None{}), C.conforms(~rule, rest, C.REnd{}, None{})) == Bool.and(C.conforms(~rule, fs, _, None{}), C.conforms(~rule, rest, C.RKey{n, v, C.REnd{}}, None{})) : Bool}
      %skip_c(~rule, n, rest, v, C.REnd{}, and_r(Bool.not(String.eq(n, m)), C.fresh_f(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf)), {==}) : {Bool.and(C.conforms(~rule, fs, C.RMissing{}, None{}), C.conforms(~rule, rest, C.REnd{}, None{})) == Bool.and(C.conforms(~rule, fs, C.RMissing{}, None{}), _) : Bool}
      {==}
    case C.SField{+m, +fs, +rest} C.RKey{+k, +w, +o2}:
      %kc_skip(n, m, v, C.RKey{k, w, o2}, not_true(String.eq(n, m), and_l(Bool.not(String.eq(n, m)), C.fresh_f(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf)))) : {Bool.and(C.key_once(m, C.RKey{k, w, o2}), Bool.and(C.conforms(~rule, fs, C.lookup(m, C.RKey{k, w, o2}), None{}), C.conforms(~rule, rest, C.RKey{k, w, o2}, None{}))) == Bool.and(_, Bool.and(C.conforms(~rule, fs, C.lookup(m, C.RKey{n, v, C.RKey{k, w, o2}}), None{}), C.conforms(~rule, rest, C.RKey{n, v, C.RKey{k, w, o2}}, None{}))) : Bool}
      %lk_skip(n, m, v, C.RKey{k, w, o2}, not_true(String.eq(n, m), and_l(Bool.not(String.eq(n, m)), C.fresh_f(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf)))) : {Bool.and(C.key_once(m, C.RKey{k, w, o2}), Bool.and(C.conforms(~rule, fs, C.lookup(m, C.RKey{k, w, o2}), None{}), C.conforms(~rule, rest, C.RKey{k, w, o2}, None{}))) == Bool.and(C.key_once(m, C.RKey{k, w, o2}), Bool.and(C.conforms(~rule, fs, _, None{}), C.conforms(~rule, rest, C.RKey{n, v, C.RKey{k, w, o2}}, None{}))) : Bool}
      %skip_c(~rule, n, rest, v, C.RKey{k, w, o2}, and_r(Bool.not(String.eq(n, m)), C.fresh_f(n, rest), and_r(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), C.fresh_f(n, rest)), hf)), {==}) : {Bool.and(C.key_once(m, C.RKey{k, w, o2}), Bool.and(C.conforms(~rule, fs, C.lookup(m, C.RKey{k, w, o2}), None{}), C.conforms(~rule, rest, C.RKey{k, w, o2}, None{}))) == Bool.and(C.key_once(m, C.RKey{k, w, o2}), Bool.and(C.conforms(~rule, fs, C.lookup(m, C.RKey{k, w, o2}), None{}), _)) : Bool}
      {==}
    case C.SEnd{} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RNull{}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RBad{}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RMissing{}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RNil{}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SEnd{}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SEnd{}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SEnd{} C.REnd{}:
      {==}
    case C.SEnd{} C.RKey{+k, +w, +o2}:
      {==}
    case C.SRule{s_, tag_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RNull{}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RBad{}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RNil{}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SRule{s_, tag_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.REnd{}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SRule{s_, tag_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SRule{s_, tag_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SStrict{s_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RNull{}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RBad{}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RNil{}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SStrict{s_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.REnd{}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SStrict{s_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SStrict{s_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SStrict{s_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.STagged{key_, name_, s_, rest_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RNull{}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RBad{}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RMissing{}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RNil{}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.STagged{key_, name_, s_, rest_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.REnd{}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.STagged{key_, name_, s_, rest_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.STagged{key_, name_, s_, rest_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.STagEnd{key_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RNull{}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RBad{}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RMissing{}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RNil{}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.STagEnd{key_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.REnd{}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.STagEnd{key_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.STagEnd{key_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.STagEnd{key_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SBool{} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RNull{}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RBad{}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RMissing{}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RNil{}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SBool{} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.REnd{}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SBool{} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SBool{}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SBool{}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.STrue{} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RNum{n__}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RBool{b__}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RNull{}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RStr{s__}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RBad{}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RTooBig{}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RMissing{}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RNil{}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.STrue{} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.REnd{}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.STrue{} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.STrue{}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.STrue{}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SEnum{names_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RNull{}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RBad{}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RNil{}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SEnum{names_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.REnd{}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SEnum{names_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SEnum{names_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SEnum{names_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SVariant{name_, s_, rest_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RNull{}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RBad{}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RNil{}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SVariant{name_, s_, rest_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.REnd{}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SVariant{name_, s_, rest_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SVariant{name_, s_, rest_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SVEnd{} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RNull{}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RBad{}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RMissing{}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RNil{}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SVEnd{} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.REnd{}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SVEnd{} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SVEnd{}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SVEnd{}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.STuple{s_, rest_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RNull{}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RBad{}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RMissing{}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RNil{}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.STuple{s_, rest_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.REnd{}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.STuple{s_, rest_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.STuple{s_, rest_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.STEnd{} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RNum{n__}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RBool{b__}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RNull{}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RStr{s__}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RBad{}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RTooBig{}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RMissing{}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RNil{}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.STEnd{} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.REnd{}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.STEnd{} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.STEnd{}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.STEnd{}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SOptional{inner_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RNull{}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RBad{}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RNil{}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SOptional{inner_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.REnd{}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SOptional{inner_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SOptional{inner_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SOptional{inner_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))
    case C.SListLen{lo_, hi_, s_} C.RNum{n__}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RNum{n__}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RNum{n__}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.RBool{b__}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RBool{b__}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RBool{b__}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.RNull{}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RNull{}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RNull{}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.RStr{s__}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RStr{s__}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RStr{s__}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.RBad{}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RBad{}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RBad{}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.RTooBig{}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RTooBig{}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RTooBig{}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.RMissing{}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RMissing{}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RMissing{}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.RNil{}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RNil{}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RNil{}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.RCons{head__, tail__}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RCons{head__, tail__}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RCons{head__, tail__}}, None{}) : Bool}, to_empty(ho))
    case C.SListLen{lo_, hi_, s_} C.REnd{}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.REnd{}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.REnd{}}, None{}) : Bool}, to_empty(hf))
    case C.SListLen{lo_, hi_, s_} C.RKey{+k, +w, +o2}:
      Empty.absurd({C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{k, w, o2}, None{}) == C.conforms(~rule, C.SListLen{lo_, hi_, s_}, C.RKey{n, v, C.RKey{k, w, o2}}, None{}) : Bool}, to_empty(hf))

# A strict object's encoding: every key enc writes for a chain of keys is
# one of the chain's names; a longer list of names allows at least as much.

def or_r_true(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def extra_mono(+m: String, +ns: List<&2, String>, r: C.Raw, +h: {C.no_extra(ns, r) == True{} : Bool}) -> {C.no_extra(m <> ns, r) == True{} : Bool}:
  match r:
    case C.RKey{+k, v, +o}:
      and_true2(Bool.or(String.eq(k, m), C.in_names(k, ns)), C.no_extra(m <> ns, o), or_r_true(String.eq(k, m), C.in_names(k, ns), and_l(C.in_names(k, ns), C.no_extra(ns, o), h)), extra_mono(m, ns, o, and_r(C.in_names(k, ns), C.no_extra(ns, o), h)))
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{s_}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h_, t_}:
      {==}
    case C.REnd{}:
      {==}

def keyed_enc(s: C.Schema, x: C.Meaning(s), +hk: {C.is_keyed(s) == True{} : Bool}) -> {C.no_extra(C.key_names(s), C.enc(s, x)) == True{} : Bool}:
  match s x:
    case C.SField{+n, fs, +rest} C.Both{a, +b}:
      and_true2(C.in_names(n, n <> C.key_names(rest)), C.no_extra(n <> C.key_names(rest), C.enc(rest, b)), names_has(Nil{}, n, C.key_names(rest)), extra_mono(n, C.key_names(rest), C.enc(rest, b), keyed_enc(rest, b, hk)))
    case C.SEnd{} Unit{}:
      {==}
    case C.SVariant{+n, vs, +rest} Inl{a}:
      and_true2(C.in_names(n, n <> C.key_names(rest)), C.no_extra(n <> C.key_names(rest), C.REnd{}), names_has(Nil{}, n, C.key_names(rest)), {==})
    case C.SVariant{+n, vs, +rest} Inr{+b}:
      extra_mono(n, C.key_names(rest), C.enc(rest, b), keyed_enc(rest, b, hk))
    case C.SVEnd{} e:
      Empty.absurd({C.no_extra(C.key_names(C.SVEnd{}), C.enc(C.SVEnd{}, e)) == True{} : Bool}, e)
    case C.SBool{} v:
      Empty.absurd({C.no_extra(C.key_names(C.SBool{}), C.enc(C.SBool{}, v)) == True{} : Bool}, to_empty(hk))
    case C.SNatIn{lo_, hi_} v:
      Empty.absurd({C.no_extra(C.key_names(C.SNatIn{lo_, hi_}), C.enc(C.SNatIn{lo_, hi_}, v)) == True{} : Bool}, to_empty(hk))
    case C.SStrLen{lo_, hi_, s2} v:
      Empty.absurd({C.no_extra(C.key_names(C.SStrLen{lo_, hi_, s2}), C.enc(C.SStrLen{lo_, hi_, s2}, v)) == True{} : Bool}, to_empty(hk))
    case C.SNat{} v:
      Empty.absurd({C.no_extra(C.key_names(C.SNat{}), C.enc(C.SNat{}, v)) == True{} : Bool}, to_empty(hk))
    case C.SStr{} v:
      Empty.absurd({C.no_extra(C.key_names(C.SStr{}), C.enc(C.SStr{}, v)) == True{} : Bool}, to_empty(hk))
    case C.SOpt{i_} v:
      Empty.absurd({C.no_extra(C.key_names(C.SOpt{i_}), C.enc(C.SOpt{i_}, v)) == True{} : Bool}, to_empty(hk))
    case C.SList{e_} v:
      Empty.absurd({C.no_extra(C.key_names(C.SList{e_}), C.enc(C.SList{e_}, v)) == True{} : Bool}, to_empty(hk))
    case C.SRule{s_, t_} v:
      Empty.absurd({C.no_extra(C.key_names(C.SRule{s_, t_}), C.enc(C.SRule{s_, t_}, v)) == True{} : Bool}, to_empty(hk))
    case C.SStrict{s_} v:
      Empty.absurd({C.no_extra(C.key_names(C.SStrict{s_}), C.enc(C.SStrict{s_}, v)) == True{} : Bool}, to_empty(hk))
    case C.STagged{k_, n_, cs_, rest_} v:
      Empty.absurd({C.no_extra(C.key_names(C.STagged{k_, n_, cs_, rest_}), C.enc(C.STagged{k_, n_, cs_, rest_}, v)) == True{} : Bool}, to_empty(hk))
    case C.STagEnd{k_} v:
      Empty.absurd({C.no_extra(C.key_names(C.STagEnd{k_}), C.enc(C.STagEnd{k_}, v)) == True{} : Bool}, to_empty(hk))
    case C.STrue{} v:
      Empty.absurd({C.no_extra(C.key_names(C.STrue{}), C.enc(C.STrue{}, v)) == True{} : Bool}, to_empty(hk))
    case C.SEnum{ns_} v:
      Empty.absurd({C.no_extra(C.key_names(C.SEnum{ns_}), C.enc(C.SEnum{ns_}, v)) == True{} : Bool}, to_empty(hk))
    case C.STuple{ts_, rs_} v:
      Empty.absurd({C.no_extra(C.key_names(C.STuple{ts_, rs_}), C.enc(C.STuple{ts_, rs_}, v)) == True{} : Bool}, to_empty(hk))
    case C.STEnd{} v:
      Empty.absurd({C.no_extra(C.key_names(C.STEnd{}), C.enc(C.STEnd{}, v)) == True{} : Bool}, to_empty(hk))
    case C.SOptional{i_} v:
      Empty.absurd({C.no_extra(C.key_names(C.SOptional{i_}), C.enc(C.SOptional{i_}, v)) == True{} : Bool}, to_empty(hk))
    case C.SListLen{lo_, hi_, s2_} v:
      Empty.absurd({C.no_extra(C.key_names(C.SListLen{lo_, hi_, s2_}), C.enc(C.SListLen{lo_, hi_, s2_}, v)) == True{} : Bool}, to_empty(hk))

def ec(s: C.Schema, x: C.Meaning(s), +hw: {C.wf(s) == True{} : Bool}, +hn: {C.names_ok(s, x) == True{} : Bool}, +hb: {C.bounds_ok(s, x) == True{} : Bool}) -> {C.conforms(~C.no_rule, s, C.enc(s, x), None{}) == True{} : Bool}:
  match s x:
    case C.SNat{} n:
      {==}
    case C.SNatIn{+lo, +hi} n:
      hb
    case C.SStr{} n:
      {==}
    case C.SStrLen{+lo, +hi, +s2} +v:
      and_true2(C.conforms(~C.no_rule, s2, C.enc(s2, v), None{}), C.len_ok(lo, hi, C.enc(s2, v)), ec(s2, v, and_r(Bool.not(C.opt_at(s2)), C.wf(s2), hw), hn, and_l(C.bounds_ok(s2, v), C.len_ok(lo, hi, C.enc(s2, v)), hb)), and_r(C.bounds_ok(s2, v), C.len_ok(lo, hi, C.enc(s2, v)), hb))
    case C.SListLen{+lo, +hi, +s2} +v:
      and_true2(C.list_len_ok(lo, hi, C.enc(s2, v)), C.conforms(~C.no_rule, s2, C.enc(s2, v), None{}), and_r(C.bounds_ok(s2, v), C.list_len_ok(lo, hi, C.enc(s2, v)), hb), ec(s2, v, and_r(Bool.not(C.opt_at(s2)), C.wf(s2), hw), hn, and_l(C.bounds_ok(s2, v), C.list_len_ok(lo, hi, C.enc(s2, v)), hb)))
    case C.SOpt{i} None{}:
      {==}
    case C.SOpt{+i} Some{+v}:
      %opt_conf(~C.no_rule, i, C.enc(i, v), not_nullish(i, v, not_true(C.nullable(i), and_l(Bool.not(C.nullable(i)), C.wf(i), hw)))) : {_ == True{} : Bool}
      ec(i, v, and_r(Bool.not(C.nullable(i)), C.wf(i), hw), hn, hb)
    case C.SOptional{+i} None{}:
      {==}
    case C.SOptional{+i} Some{+v}:
      %not_missing(i, v, not_true(C.opt_at(i), and_l(Bool.not(C.opt_at(i)), C.wf(i), hw))) : {Bool.or(_, C.conforms(~C.no_rule, i, C.enc(i, v), None{})) == True{} : Bool}
      ec(i, v, and_r(Bool.not(C.opt_at(i)), C.wf(i), hw), hn, hb)
    case C.SList{e} Nil{}:
      {==}
    case C.SList{+e} +h <> +t:
      and_true2(C.conforms(~C.no_rule, e, C.enc(e, h), None{}), C.conforms(~C.no_rule, C.SList{e}, C.enc(C.SList{e}, t), None{}), ec(e, h, and_r(Bool.not(C.opt_at(e)), C.wf(e), hw), and_l(C.names_ok(e, h), C.names_ok(C.SList{e}, t), hn), and_l(C.bounds_ok(e, h), C.bounds_ok(C.SList{e}, t), hb)), ec(C.SList{e}, t, hw, and_r(C.names_ok(e, h), C.names_ok(C.SList{e}, t), hn), and_r(C.bounds_ok(e, h), C.bounds_ok(C.SList{e}, t), hb)))
    case C.SField{+n, +fs, +rest} C.Both{+a, +b}:
      %lk_self(n, C.enc(fs, a), C.enc(rest, b)) : {Bool.and(C.key_once_at(C.enc(rest, b), String.eq(n, n), n), Bool.and(C.conforms(~C.no_rule, fs, _, None{}), C.conforms(~C.no_rule, rest, C.RKey{n, C.enc(fs, a), C.enc(rest, b)}, None{}))) == True{} : Bool}
      %MS.eq_refl_sym(n) : {Bool.and(C.key_once_at(C.enc(rest, b), _, n), Bool.and(C.conforms(~C.no_rule, fs, C.enc(fs, a), None{}), C.conforms(~C.no_rule, rest, C.RKey{n, C.enc(fs, a), C.enc(rest, b)}, None{}))) == True{} : Bool}
      %key_once_enc(n, rest, b, and_l(C.fresh_f(n, rest), C.wf(rest), and_r(C.wf(fs), Bool.and(C.fresh_f(n, rest), C.wf(rest)), hw))) : {Bool.and(_, Bool.and(C.conforms(~C.no_rule, fs, C.enc(fs, a), None{}), C.conforms(~C.no_rule, rest, C.RKey{n, C.enc(fs, a), C.enc(rest, b)}, None{}))) == True{} : Bool}
      %skip_c(~C.no_rule, n, rest, C.enc(fs, a), C.enc(rest, b), and_l(C.fresh_f(n, rest), C.wf(rest), and_r(C.wf(fs), Bool.and(C.fresh_f(n, rest), C.wf(rest)), hw)), obj_f(n, rest, b, and_l(C.fresh_f(n, rest), C.wf(rest), and_r(C.wf(fs), Bool.and(C.fresh_f(n, rest), C.wf(rest)), hw)))) : {Bool.and(C.conforms(~C.no_rule, fs, C.enc(fs, a), None{}), _) == True{} : Bool}
      and_true2(C.conforms(~C.no_rule, fs, C.enc(fs, a), None{}), C.conforms(~C.no_rule, rest, C.enc(rest, b), None{}), ec(fs, a, and_l(C.wf(fs), Bool.and(C.fresh_f(n, rest), C.wf(rest)), hw), and_l(C.names_ok(fs, a), C.names_ok(rest, b), hn), and_l(C.bounds_ok(fs, a), C.bounds_ok(rest, b), hb)), ec(rest, b, and_r(C.fresh_f(n, rest), C.wf(rest), and_r(C.wf(fs), Bool.and(C.fresh_f(n, rest), C.wf(rest)), hw)), and_r(C.names_ok(fs, a), C.names_ok(rest, b), hn), and_r(C.bounds_ok(fs, a), C.bounds_ok(rest, b), hb)))
    case C.SEnd{} Unit{}:
      {==}
    case C.SRule{+s2, +tag} +v:
      and_true2(C.conforms(~C.no_rule, s2, C.enc(s2, v), None{}), Maybe.is_none(&2, C.Err, C.no_rule(tag, C.enc(s2, v))), ec(s2, v, and_r(Bool.not(C.opt_at(s2)), C.wf(s2), hw), hn, hb), {==})
    case C.SStrict{+s2} +v:
      and_true2(C.conforms(~C.no_rule, s2, C.enc(s2, v), None{}), C.no_extra(C.key_names(s2), C.enc(s2, v)), ec(s2, v, and_r(Bool.not(C.opt_at(s2)), C.wf(s2), and_r(C.is_keyed(s2), Bool.and(Bool.not(C.opt_at(s2)), C.wf(s2)), hw)), hn, hb), keyed_enc(s2, v, and_l(C.is_keyed(s2), Bool.and(Bool.not(C.opt_at(s2)), C.wf(s2)), hw)))
    case C.STagged{+k, +n, +cs, +rest} Inl{+a}:
      %tag_self(k, n, C.enc(cs, a)) : {C.pick_bool(_, Bool.and(C.key_once(k, C.RKey{k, C.RStr{n}, C.enc(cs, a)}), C.conforms(~C.no_rule, cs, C.drop_key(k, C.RKey{k, C.RStr{n}, C.enc(cs, a)}), None{})), C.conforms(~C.no_rule, rest, C.RKey{k, C.RStr{n}, C.enc(cs, a)}, None{})) == True{} : Bool}
      %drop_self(k, C.RStr{n}, C.enc(cs, a)) : {Bool.and(C.key_once(k, C.RKey{k, C.RStr{n}, C.enc(cs, a)}), C.conforms(~C.no_rule, cs, _, None{})) == True{} : Bool}
      and_true2(C.key_once(k, C.RKey{k, C.RStr{n}, C.enc(cs, a)}), C.conforms(~C.no_rule, cs, C.enc(cs, a), None{}), no_key_once(k, cs, a, String.eq(k, k), and_l(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)), and_r(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest))), and_r(Bool.not(C.opt_at(cs)), Bool.and(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)))), hw)))), ec(cs, a, and_l(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest))), and_r(Bool.not(C.opt_at(cs)), Bool.and(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)))), hw)), hn, hb))
    case C.STagged{+k, +n, +cs, +rest} Inr{+b}:
      %tag_other(k, n, rest, b, and_l(C.fresh_t(k, n, rest), C.wf(rest), and_r(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)), and_r(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest))), and_r(Bool.not(C.opt_at(cs)), Bool.and(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)))), hw))))) : {C.pick_bool(_, Bool.and(C.key_once(k, C.enc(rest, b)), C.conforms(~C.no_rule, cs, C.drop_key(k, C.enc(rest, b)), None{})), C.conforms(~C.no_rule, rest, C.enc(rest, b), None{})) == True{} : Bool}
      ec(rest, b, and_r(C.fresh_t(k, n, rest), C.wf(rest), and_r(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)), and_r(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest))), and_r(Bool.not(C.opt_at(cs)), Bool.and(C.wf(cs), Bool.and(C.no_key(k, cs), Bool.and(C.fresh_t(k, n, rest), C.wf(rest)))), hw)))), hn, hb)
    case C.STagEnd{k_} e:
      Empty.absurd({C.conforms(~C.no_rule, C.STagEnd{k_}, C.enc(C.STagEnd{k_}, e), None{}) == True{} : Bool}, e)
    case C.STrue{} Unit{}:
      {==}
    case C.SBool{} b:
      {==}
    case C.SEnum{names} v:
      hn
    case C.SVariant{+n, +vs, +rest} Inl{+a}:
      %lk_self(n, C.enc(vs, a), C.REnd{}) : {C.pick_bool(C.is_missing(_), C.conforms(~C.no_rule, rest, C.RKey{n, C.enc(vs, a), C.REnd{}}, None{}), Bool.and(C.conforms(~C.no_rule, vs, _, None{}), C.none_present(rest, C.RKey{n, C.enc(vs, a), C.REnd{}}))) == True{} : Bool}
      %not_missing(vs, a, not_true(C.opt_at(vs), and_l(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw))) : {C.pick_bool(_, C.conforms(~C.no_rule, rest, C.RKey{n, C.enc(vs, a), C.REnd{}}, None{}), Bool.and(C.conforms(~C.no_rule, vs, C.enc(vs, a), None{}), C.none_present(rest, C.RKey{n, C.enc(vs, a), C.REnd{}}))) == True{} : Bool}
      and_true2(C.conforms(~C.no_rule, vs, C.enc(vs, a), None{}), C.none_present(rest, C.RKey{n, C.enc(vs, a), C.REnd{}}), ec(vs, a, and_l(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest)), and_r(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw)), hn, hb), np(n, rest, C.enc(vs, a), and_l(C.fresh_v(n, rest), C.wf(rest), and_r(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest)), and_r(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw)))))
    case C.SVariant{+n, +vs, +rest} Inr{+b}:
      %var_skip(~C.no_rule, n, vs, rest, C.enc(rest, b), obj_v(n, rest, b, and_l(C.fresh_v(n, rest), C.wf(rest), and_r(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest)), and_r(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw)))), absent(n, rest, b, and_l(C.fresh_v(n, rest), C.wf(rest), and_r(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest)), and_r(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw))))) : {_ == True{} : Bool}
      ec(rest, b, and_r(C.fresh_v(n, rest), C.wf(rest), and_r(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest)), and_r(Bool.not(C.opt_at(vs)), Bool.and(C.wf(vs), Bool.and(C.fresh_v(n, rest), C.wf(rest))), hw))), hn, hb)
    case C.SVEnd{} e:
      Empty.absurd({C.conforms(~C.no_rule, C.SVEnd{}, C.enc(C.SVEnd{}, e), None{}) == True{} : Bool}, e)
    case C.STuple{+ts, +rest} C.Both{+a, +b}:
      and_true2(C.conforms(~C.no_rule, ts, C.enc(ts, a), None{}), C.conforms(~C.no_rule, rest, C.enc(rest, b), None{}), ec(ts, a, and_l(C.wf(ts), Bool.and(Bool.not(C.opt_at(rest)), C.wf(rest)), and_r(Bool.not(C.opt_at(ts)), Bool.and(C.wf(ts), Bool.and(Bool.not(C.opt_at(rest)), C.wf(rest))), hw)), and_l(C.names_ok(ts, a), C.names_ok(rest, b), hn), and_l(C.bounds_ok(ts, a), C.bounds_ok(rest, b), hb)), ec(rest, b, and_r(Bool.not(C.opt_at(rest)), C.wf(rest), and_r(C.wf(ts), Bool.and(Bool.not(C.opt_at(rest)), C.wf(rest)), and_r(Bool.not(C.opt_at(ts)), Bool.and(C.wf(ts), Bool.and(Bool.not(C.opt_at(rest)), C.wf(rest))), hw))), and_r(C.names_ok(ts, a), C.names_ok(rest, b), hn), and_r(C.bounds_ok(ts, a), C.bounds_ok(rest, b), hb)))
    case C.STEnd{} Unit{}:
      {==}

def Laws.encode_conforms(s, x, hw, hn, hb):
  ec(s, x, hw, hn, hb)

# ---- a string's length is in its bounds ----

def Laws.str_len_in_meaning(lo, hi, x):
  in_err_none(Bool.and(Nat.is_le(lo, String.length(x)), Nat.is_le(String.length(x), hi)), C.LengthNotIn{lo, hi})

# ---- a number is in its bounds ----

def Laws.nat_in_meaning(lo, hi, n):
  in_err_none(Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi)), C.NotIn{lo, hi})

# ---- a boolean, and nothing else ----
#
# A second reading of SBool, by a walk of its own over the value: conforms
# accepts exactly the booleans. A host that writes "a boolean" gets a check
# that agrees with it for every value, not only for the ones it thought of.

# arms: r
# arms leaf: {==}
def sbool_go(~rule: Nat -> C.Raw -> Maybe<&2, C.Err>, r: C.Raw) -> {C.conforms(~rule, C.SBool{}, r, None{}) == C.is_bool(r) : Bool}:
  match r:
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{s_}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h_, t_}:
      {==}
    case C.REnd{}:
      {==}
    case C.RKey{k_, v_, o_}:
      {==}

def Laws.sbool_meaning(rule, r):
  sbool_go(~rule, r)

# ---- a string's length, as a constructor ----
#
# str_len_in_meaning, restated for SStrLen: what the rule tested, the
# constructor means -- the same str_len_ok, and the shape s the value must also
# satisfy. The rule read no other kind; here the other kinds are not in bounds.

def Laws.sstr_len_meaning(rule, lo, hi, s, x):
  {==}

# ---- a number's bounds, as a constructor ----
#
# nat_in_meaning, restated for SNatIn: the same num_ok, both ends included.

def Laws.snat_in_meaning(rule, lo, hi, n):
  {==}

# ---- a strict object has no other key ----

def unk_step(b: Bool, +c: Nat, +d: Bool, ih: {Nat.is_eq(c, 0n) == d : Bool}) -> {Nat.is_eq(Nat.add(C.one_if_there(b), c), 0n) == Bool.and(b, d) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

def strict_count(+ns: List<&2, String>, r: C.Raw) -> {Nat.is_eq(C.count_unknown(ns, r), 0n) == C.no_extra(ns, r) : Bool}:
  match r:
    case C.RKey{+k, v, +o}:
      unk_step(C.in_names(k, ns), C.count_unknown(ns, o), C.no_extra(ns, o), strict_count(ns, o))
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{s_}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h_, t_}:
      {==}
    case C.REnd{}:
      {==}

def Laws.strict_meaning(rule, s, r):
  %strict_count(C.key_names(s), r) : {Bool.and(C.conforms(~rule, s, r, None{}), _) == Bool.and(C.conforms(~rule, s, r, None{}), Nat.is_eq(C.count_unknown(C.key_names(s), r), 0n)) : Bool}
  {==}

# ---- a tagged case reads the object without its tag ----

def Laws.tagged_meaning(rule, k, n, cs, rest, r):
  {==}

# ---- the end of a tagged chain accepts nothing ----

def Laws.tag_end_refuses(rule, k, r):
  match r:
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{s_}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h_, t_}:
      {==}
    case C.REnd{}:
      {==}
    case C.RKey{j_, v_, o_}:
      {==}

# ---- drop_key takes out the first key it names ----

def Laws.drop_first(k, v, o):
  Equal.sym(C.Raw, o, C.drop_key(k, C.RKey{k, v, o}), drop_self(k, v, o))

# ---- drop_key leaves every other key as it was ----

def drop_step(b: Bool, +i: String, +k: String, +j: String, +v: C.Raw, +o: C.Raw, eb: {b == String.eq(i, k) : Bool}, +h: {False{} == String.eq(k, j) : Bool}, ih: {C.lookup(j, C.drop_key(k, o)) == C.lookup(j, o) : C.Raw}) -> {C.lookup(j, C.pick_raw(b, o, C.RKey{i, v, C.drop_key(k, o)})) == C.lookup(j, C.RKey{i, v, o}) : C.Raw}:
  match b:
    case True{}:
      %Equal.sym(String, i, k, MS.eq_of_eq_true(i, k, Equal.sym(Bool, True{}, String.eq(i, k), eb))) : {C.lookup(j, o) == C.pick_raw(String.eq(_, j), v, C.lookup(j, o)) : C.Raw}
      %h : {C.lookup(j, o) == C.pick_raw(_, v, C.lookup(j, o)) : C.Raw}
      {==}
    case False{}:
      %ih : {C.pick_raw(String.eq(i, j), v, C.lookup(j, C.drop_key(k, o))) == C.pick_raw(String.eq(i, j), v, _) : C.Raw}
      {==}

def drop_other_go(+k: String, +j: String, r: C.Raw, +h: {False{} == String.eq(k, j) : Bool}) -> {C.lookup(j, C.drop_key(k, r)) == C.lookup(j, r) : C.Raw}:
  match r:
    case C.RKey{+i, +v, +o}:
      drop_step(String.eq(i, k), i, k, j, v, o, {==}, h, drop_other_go(k, j, o, h))
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{s_}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RMissing{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h_, t_}:
      {==}
    case C.REnd{}:
      {==}

def Laws.drop_other(k, j, r, h):
  drop_other_go(k, j, r, h)


# ---- a list's element count, as a constructor ----

# conforms(SListLen{lo, hi, s}, r) unfolds to the count (list_len_ok: is it a
# list at all, and are its elements in the bounds) beside conforms(s, r) --
# which is the law's right side, with the helper the core reads written out.
# The two sides are the same term, so nothing is left to prove.
def Laws.slist_len_meaning(rule, lo, hi, s, r):
  {==}


# ---- an optional field, as a constructor ----

# Every value but the absent one is the inner schema's to decide, and the
# absent one is accepted. Bool.or reduces on the first argument, which is the
# value's own kind, so each arm is the same equation with the constructor
# fixed: no rule is read at an SOptional's own node.
def Laws.soptional_meaning(rule, i, r):
  match r:
    case C.RMissing{}:
      {==}
    case C.RNum{n_}:
      {==}
    case C.RBool{b_}:
      {==}
    case C.RNull{}:
      {==}
    case C.RStr{s_}:
      {==}
    case C.RBad{}:
      {==}
    case C.RTooBig{}:
      {==}
    case C.RNil{}:
      {==}
    case C.RCons{h_, t_}:
      {==}
    case C.REnd{}:
      {==}
    case C.RKey{k_, v_, o_}:
      {==}
