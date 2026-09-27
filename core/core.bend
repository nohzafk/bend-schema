import Base

# bend-schema: a schema, and one check for every schema, proved once.
#
# The host turns any JSON value into a Raw with one universal codec that knows
# no schema: numbers that are whole and within the runtime's Nat become RNum,
# every other number, boolean or unsupported value becomes RBad. A list or an
# object past the codec's budget becomes one RTooBig, in its place: the codec
# counts elements and keys so that these walks never receive a value the
# runtime cannot carry, and a size becomes an error (TooLarge, at the node's
# path) rather than a crash. Lists and objects are chains built into Raw
# (RNil/RCons, REnd/RKey), so that every walk here is structural. RMissing is
# never produced by the codec: it is what looking up an absent key gives.
#
# A Schema says what a valid value is (`conforms`), and `check` finds the
# first thing wrong, with the path to it: depth first, lists in element order,
# objects in the schema's field order; an element of a bounded list is read
# whole before its bound, and an SListLen's element count is read before any
# element. Keys the schema does not name are ignored; a key it names must be
# present, and two constructors say what may be there instead: SOpt is a value
# that may be null, SOptional a field that may be absent (the host writes no
# key at all, so it is well-formed only as a field's own schema).
#
# Both walk the schema and the value together, in one self-recursive def: a
# step into a field or an optional shrinks the schema, a step along a list
# keeps it and shrinks the value (the checker reads the arguments left to
# right until one shrinks). A project's rules arrive as one template
# parameter, `~rule: Nat -> Raw -> Maybe<Err>`: at an SRule the value must
# conform to the rule's schema first, then the rule decides (the tag picks
# the rule; the rule's error path is relative to the value it was given).
# Template defs cannot cross the bundler, so the host calls the closed forms
# below (check0, conforms0). `prev` is carried but no case reads it today; a
# stateful combinator would.

type Raw is Data:
  RNum{n: Nat}
  RBool{b: Bool}
  RNull{}
  RStr{s: String}
  RBad{}
  RTooBig{}
  RMissing{}
  RNil{}
  RCons{head: Raw, tail: Raw}
  REnd{}
  RKey{key: String, val: Raw, rest: Raw}

type Schema is Data:
  SNat{}
  SNatIn{lo: Nat, hi: Nat}
  SStr{}
  SStrLen{lo: Nat, hi: Nat, s: Schema}
  SOpt{inner: Schema}
  SList{elem: Schema}
  SField{name: String, s: Schema, rest: Schema}
  SEnd{}
  SRule{s: Schema, tag: Nat}
  SStrict{s: Schema}
  STagged{key: String, name: String, s: Schema, rest: Schema}
  STagEnd{key: String}
  SBool{}
  STrue{}
  SEnum{names: List<&2, String>}
  SVariant{name: String, s: Schema, rest: Schema}
  SVEnd{}
  STuple{s: Schema, rest: Schema}
  STEnd{}
  SOptional{inner: Schema}
  SListLen{lo: Nat, hi: Nat, s: Schema}

# A step of a path. Positions count what was passed on the way, so that
# following a path never compares two names: AtIndex{i} is element i of a
# list, AtField{skip, name} the field `skip` places after this one in the
# schema, BoundAt{i, key} the bound of element i of a bounded list. The names
# are for the host to print.
type Step is Data:
  AtIndex{i: Nat}
  AtField{skip: Nat, name: String}
  BoundAt{i: Nat, key: String}
  AtKey{key: String}

type Why is Data:
  Missing{}
  NotNat{}
  NotString{}
  NotBool{}
  NotList{}
  NotObject{}
  NoElements{}
  OpenNotLast{}
  LastNotOpen{}
  NotIncreasing{prev: Nat, got: Nat}
  NotTrue{}
  NotOneOf{}
  NoVariant{}
  TwoVariants{}
  TooShort{}
  TooLong{}
  LengthNotIn{lo: Nat, hi: Nat}
  NotIn{lo: Nat, hi: Nat}
  UnknownKey{}
  RepeatedKey{key: String}
  TooLarge{}
  CountNotIn{lo: Nat, hi: Nat}

type Err is Data:
  Err{path: List<&2, Step>, why: Why}

# ---- reading a value ----

def pick_raw(b: Bool, +x: Raw, +y: Raw) -> Raw:
  match b:
    case True{}:
      x
    case False{}:
      y

# The value under `name` in an object, or RMissing.
def lookup(+name: String, r: Raw) -> Raw:
  match r:
    case RKey{k, +v, rest}:
      pick_raw(String.eq(k, name), v, lookup(name, rest))
    case _:
      RMissing{}

def pick_bool(b: Bool, +x: Bool, +y: Bool) -> Bool:
  match b:
    case True{}:
      x
    case False{}:
      y

def is_rnil(r: Raw) -> Bool:
  match r:
    case RNil{}:
      True{}
    case _:
      False{}

# ---- the helpers of the choices: true, one of some names, one of some keys ----

def is_missing(v: Raw) -> Bool:
  match v:
    case RMissing{}:
      True{}
    case _:
      False{}

def in_names(+x: String, names: List<&2, String>) -> Bool:
  match names:
    case Nil{}:
      False{}
    case n <> t:
      Bool.or(String.eq(x, n), in_names(x, t))

# None of the keys of a variant chain is in the object r.
def none_present(s: Schema, +r: Raw) -> Bool:
  match s:
    case SVariant{n, vs, rest}:
      Bool.and(is_missing(lookup(n, r)), none_present(rest, r))
    case _:
      True{}

# ---- a strict object: its keys ----
#
# The names a record or variant chain declares. SStrict refuses a key that is
# not one of them; wf asks that SStrict wrap such a chain.
def key_names(s: Schema) -> List<&2, String>:
  match s:
    case SField{n, fs, rest}:
      n <> key_names(rest)
    case SVariant{n, vs, rest}:
      n <> key_names(rest)
    case _:
      Nil{}

# Every key of the object r is one of ns (anything but an object has none).
def no_extra(+ns: List<&2, String>, r: Raw) -> Bool:
  match r:
    case RKey{+k, v, o}:
      Bool.and(in_names(k, ns), no_extra(ns, o))
    case _:
      True{}

# ---- a tagged union: its tag, and the object a case sees ----
#
# STagged{key, name, s, rest} is one case of a chain ending in STagEnd{key}:
# when the value under `key` is the string `name`, the object without that
# key must conform to s; otherwise the chain goes on. The case does not see
# the tag, so an SStrict case need not name it.

# The object r without its first key k (what lookup(k, r) reads).
def drop_key(+k: String, r: Raw) -> Raw:
  match r:
    case RKey{+j, +v, +o}:
      pick_raw(String.eq(j, k), o, RKey{j, v, drop_key(k, o)})
    case x:
      x

def is_str(+n: String, v: Raw) -> Bool:
  match v:
    case RStr{x}:
      String.eq(x, n)
    case _:
      False{}

# The tag under k is the string n.
def is_tag(+k: String, +n: String, r: Raw) -> Bool:
  is_str(n, lookup(k, r))

# ---- a bound, as a test and as a reason ----
#
# SStrLen{lo, hi, s} is a string in the bounds that also satisfies s, SListLen
# the same over a list's elements, SNatIn is a number in the bounds, and SBool
# is a boolean. The bound travels with the schema instead of with a rule's tag,
# which is what lets a host build one (a rule is chosen by a number, and a
# number carries no bounds).
#
# A rule and a constructor state the same bounds, and these defs are where they
# are written once: str_len_ok and num_ok are the tests, in_err is how a failing
# test becomes an error at the value's own path, and len_ok is the same test
# read as a Bool (what conforms asks at an SStrLen). Both ends are included;
# lo > hi is not an error but an empty range, in which nothing is in bounds.

def in_err(b: Bool, w: Why) -> Maybe<&2, Err>:
  match b:
    case True{}:
      None{}
    case False{}:
      Some{Err{Nil{}, w}}

def str_len_ok(+lo: Nat, +hi: Nat, +x: String) -> Bool:
  Bool.and(Nat.is_le(lo, String.length(x)), Nat.is_le(String.length(x), hi))

def num_ok(+lo: Nat, +hi: Nat, +n: Nat) -> Bool:
  Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi))

# r is a string whose length is in the bounds: what conforms reads at an
# SStrLen, and what len_err refuses exactly when it fails.
def len_ok(+lo: Nat, +hi: Nat, r: Raw) -> Bool:
  match r:
    case RStr{+x}:
      str_len_ok(lo, hi, x)
    case _:
      False{}

# The same bounds as ready-made rules: a project's rule calls them by tag
# (`case 0n: str_len_in(1n, 64n, r)`), since a tag carries no numbers. Each
# refuses only the value it is about -- a string, a number -- and leaves any
# other kind to the schema's own check; the constructors below read the tests
# directly, because their bound is in the schema.
def str_len_in(+lo: Nat, +hi: Nat, r: Raw) -> Maybe<&2, Err>:
  match r:
    case RStr{+x}:
      in_err(str_len_ok(lo, hi, x), LengthNotIn{lo, hi})
    case _:
      None{}

def nat_in(+lo: Nat, +hi: Nat, r: Raw) -> Maybe<&2, Err>:
  match r:
    case RNum{+n}:
      in_err(num_ok(lo, hi, n), NotIn{lo, hi})
    case _:
      None{}

def is_bool(r: Raw) -> Bool:
  match r:
    case RBool{b}:
      True{}
    case _:
      False{}

# A list's element count, as a test. SListLen{lo, hi, s} is a list whose
# element count is in the bounds that also satisfies s: the same shape an
# SStrLen has, over elements instead of characters. raw_list is "r is a list at
# all", raw_len counts a proper list's elements (0 for anything else, which is
# why every use asks raw_list too), count_ok is the bound read as a Bool, and
# list_len_ok is both together -- what conforms asks at an SListLen, and what
# count_err refuses exactly when it fails. Both ends are included; lo > hi is
# not an error but an empty range, in which no list is in bounds.

def raw_list(r: Raw) -> Bool:
  match r:
    case RNil{}:
      True{}
    case RCons{h, t}:
      raw_list(t)
    case _:
      False{}

def raw_len(r: Raw) -> Nat:
  match r:
    case RCons{h, t}:
      1n+raw_len(t)
    case _:
      0n

def count_ok(+lo: Nat, +hi: Nat, +r: Raw) -> Bool:
  Bool.and(Nat.is_le(lo, raw_len(r)), Nat.is_le(raw_len(r), hi))

def list_len_ok(+lo: Nat, +hi: Nat, +r: Raw) -> Bool:
  Bool.and(raw_list(r), count_ok(lo, hi, r))

# ---- a key the schema reads ----
#
# A key the schema reads as a field key (SField) or as a variant key (SVariant)
# must appear at most once in the value: with a key repeated, lookup reads the
# first one and the second is unreachable, so the value says something the
# schema cannot mean. A key the schema does not name is never read, so
# repeating it is unobservable and is left alone.
#
# The tag key of a tagged case is read the same way -- it is how the chain
# picks its case -- so it is checked the same way, and at the case the tag
# names: conforms, check and defect all ask key_once at the value's own tag
# key, and a case whose tag matched is refused when the key is there twice.
# The check sits at the case and not at the chain because a value whose tag
# names no case is refused at the chain's end whatever its keys are, and
# because the case is the only place the question has an answer: the case is
# checked against the object with the tag key taken out, which is the object
# its own schema is about.
#
# So the other half is wf's: a case's own schema may not read the tag key at
# all (no_key, above wf). If it did, enc would write that key twice -- the tag
# first, then the case's own field -- and the host builds the object as a JS
# object, where the second write overwrites the first, so the value written
# could not be read back. Refusing the schema is what keeps encode_conforms
# true.

# k is a key of the object r.
def has_key(+k: String, r: Raw) -> Bool:
  match r:
    case RKey{j, v, o}:
      Bool.or(String.eq(k, j), has_key(k, o))
    case _:
      False{}

# name appears at most once among the keys of the object r. b is whether a key
# read before r was already name; the flag carries forward, and a key that is
# name while the flag is set is the second one -- refused here and nowhere
# else. The value is the first argument because a self-call must read its
# arguments left to right, unchanged until one shrinks, and only the value
# shrinks; the value is matched first because a match cannot be nested inside
# the branch of a match on another parameter. One pass, so a walk costs one
# key per key, the same as the lookup beside it.
def key_once_at(r: Raw, +b: Bool, +name: String) -> Bool:
  match r:
    case RKey{+k, +v, +o}:
      Bool.and(Bool.not(Bool.and(b, String.eq(k, name))), key_once_at(o, Bool.or(b, String.eq(k, name)), name))
    case _:
      True{}

# name appears at most once among the keys of the object r: nothing has been
# read yet.
def key_once(+name: String, r: Raw) -> Bool:
  key_once_at(r, False{}, name)

# The repeated key as check reports it: at the key's own name, with no step
# after it (the second occurrence is not a place in the schema). The test is
# passed in rather than read here (a match cannot scrutinize a computed value):
# b is key_once(name, r), so nothing is reported exactly when key_once holds,
# which is what check_exact needs.
def key_err(b: Bool, +name: String) -> Maybe<&2, Err>:
  match b:
    case True{}:
      None{}
    case False{}:
      Some{Err{AtField{0n, name} <> Nil{}, RepeatedKey{name}}}

# ---- what a valid value is ----

def conforms(~rule: Nat -> Raw -> Maybe<&2, Err>, s: Schema, r: Raw, +prev: Maybe<&2, Nat>) -> Bool:
  match s r:
    case SNat{} RNum{n}:
      True{}
    case SNatIn{+lo, +hi} RNum{+n}:
      num_ok(lo, hi, n)
    case SStr{} RStr{x}:
      True{}
    case SStrLen{+lo, +hi, +s2} +x:
      Bool.and(conforms(~rule, s2, x, prev), len_ok(lo, hi, x))
    case SListLen{+lo, +hi, +s2} +r:
      Bool.and(list_len_ok(lo, hi, r), conforms(~rule, s2, r, None{}))
    case SOpt{inner} RNull{}:
      True{}
    case SOpt{inner} x:
      conforms(~rule, inner, x, None{})
    case SOptional{+inner} +x:
      Bool.or(is_missing(x), conforms(~rule, inner, x, None{}))
    case SList{e} RNil{}:
      True{}
    case SList{+e} RCons{h, t}:
      Bool.and(conforms(~rule, e, h, None{}), conforms(~rule, SList{e}, t, None{}))
    case SField{+name, fs, rest} REnd{}:
      Bool.and(conforms(~rule, fs, RMissing{}, None{}), conforms(~rule, rest, REnd{}, None{}))
    case SField{+name, fs, rest} RKey{+k, +v, +o}:
      Bool.and(key_once(name, RKey{k, v, o}), Bool.and(conforms(~rule, fs, lookup(name, RKey{k, v, o}), None{}), conforms(~rule, rest, RKey{k, v, o}, None{})))
    case SEnd{} REnd{}:
      True{}
    case SEnd{} RKey{k, v, o}:
      True{}
    case SRule{+s2, +tag} +x:
      Bool.and(conforms(~rule, s2, x, prev), Maybe.is_none(&2, Err, rule(tag, x)))
    case SStrict{+s2} +x:
      Bool.and(conforms(~rule, s2, x, prev), no_extra(key_names(s2), x))
    case STagged{+k, +n, cs, rest} +x:
      pick_bool(is_tag(k, n, x), Bool.and(key_once(k, x), conforms(~rule, cs, drop_key(k, x), None{})), conforms(~rule, rest, x, None{}))
    case STagEnd{k} x:
      False{}  # the end of a tagged chain: no case matched
    case SBool{} RBool{b}:
      True{}  # any boolean is a boolean, and nothing else is
    case STrue{} RBool{b}:
      b
    case SEnum{names} RStr{+x}:
      in_names(x, names)
    case SVariant{+name, +vs, +rest} REnd{}:
      conforms(~rule, rest, REnd{}, None{})
    case SVariant{+name, +vs, +rest} RKey{+k, +v, +o}:
      pick_bool(is_missing(lookup(name, RKey{k, v, o})), conforms(~rule, rest, RKey{k, v, o}, None{}), Bool.and(key_once(name, RKey{k, v, o}), Bool.and(conforms(~rule, vs, lookup(name, RKey{k, v, o}), None{}), none_present(rest, RKey{k, v, o}))))
    case STuple{ts, rest} RCons{h, t}:
      Bool.and(conforms(~rule, ts, h, None{}), conforms(~rule, rest, t, None{}))
    case STEnd{} RNil{}:
      True{}
    case _ _:
      False{}

# ---- the first thing wrong ----

def here(w: Why) -> Maybe<&2, Err>:
  Some{Err{Nil{}, w}}

# An error found under a step gets the step in front of its path.
def under(+st: Step, m: Maybe<&2, Err>) -> Maybe<&2, Err>:
  match m:
    case None{}:
      None{}
    case Some{Err{p, w}}:
      Some{Err{st <> p, w}}

# At an SStrLen the shape comes first, as everywhere else: a value that is not
# a string is NotString, a string out of its bounds is LengthNotIn, and a node
# the codec refused to build or that is absent reads as it does at every kind.
def len_err(+lo: Nat, +hi: Nat, r: Raw) -> Maybe<&2, Err>:
  match r:
    case RStr{+x}:
      in_err(str_len_ok(lo, hi, x), LengthNotIn{lo, hi})
    case RMissing{}:
      here(Missing{})
    case RTooBig{}:
      here(TooLarge{})
    case _:
      here(NotString{})

# An error found further along a list is one element further: its first
# step, if it counts elements, counts one more. A plain list's steps are
# AtIndex; a bounded list's are AtIndex and BoundAt.
def later_l_path(p: List<&2, Step>) -> List<&2, Step>:
  match p:
    case AtIndex{j} <> q:
      AtIndex{1n+j} <> q
    case q:
      q

def later_l(m: Maybe<&2, Err>) -> Maybe<&2, Err>:
  match m:
    case None{}:
      None{}
    case Some{Err{p, w}}:
      Some{Err{later_l_path(p), w}}

def later_i_path(p: List<&2, Step>) -> List<&2, Step>:
  match p:
    case AtIndex{j} <> q:
      AtIndex{1n+j} <> q
    case BoundAt{j, key} <> q:
      BoundAt{1n+j, key} <> q
    case q:
      q

def later_i(m: Maybe<&2, Err>) -> Maybe<&2, Err>:
  match m:
    case None{}:
      None{}
    case Some{Err{p, w}}:
      Some{Err{later_i_path(p), w}}

# An error found in a later field is one field further.
def later_f_path(p: List<&2, Step>) -> List<&2, Step>:
  match p:
    case AtField{k, n} <> q:
      AtField{1n+k, n} <> q
    case q:
      q

def later_f(m: Maybe<&2, Err>) -> Maybe<&2, Err>:
  match m:
    case None{}:
      None{}
    case Some{Err{p, w}}:
      Some{Err{later_f_path(p), w}}

# The first of two: the second counts only when the first found nothing.
def first(m: Maybe<&2, Err>, n: Maybe<&2, Err>) -> Maybe<&2, Err>:
  match m:
    case None{}:
      n
    case Some{e}:
      Some{e}

# The reason a value that is not the shape is refused, at the place it was
# found: an absent slot is Missing, a node the host refused to build (RTooBig)
# is TooLarge, anything else is the schema kind's own reason. check and the
# defect helpers both answer through here, so the reason a path reports is the
# same one for both.
def missing_or(r: Raw, w: Why) -> Why:
  match r:
    case RMissing{}:
      Missing{}
    case RTooBig{}:
      TooLarge{}
    case _:
      w

def pick_err(b: Bool, +x: Maybe<&2, Err>, +y: Maybe<&2, Err>) -> Maybe<&2, Err>:
  match b:
    case True{}:
      x
    case False{}:
      y

def true_err(b: Bool) -> Maybe<&2, Err>:
  match b:
    case True{}:
      None{}
    case False{}:
      here(NotTrue{})

def enum_err(b: Bool) -> Maybe<&2, Err>:
  match b:
    case True{}:
      None{}
    case False{}:
      here(NotOneOf{})

# A second key of a variant chain in the object r: the first one found.
def dup_err(s: Schema, +r: Raw) -> Maybe<&2, Err>:
  match s:
    case SVariant{+n, vs, rest}:
      pick_err(is_missing(lookup(n, r)), later_f(dup_err(rest, r)), Some{Err{AtField{0n, n} <> Nil{}, TwoVariants{}}})
    case _:
      None{}

# The first key of r that is not one of ns, at its own name.
def extra_err(+ns: List<&2, String>, r: Raw) -> Maybe<&2, Err>:
  match r:
    case RKey{+k, v, o}:
      pick_err(in_names(k, ns), extra_err(ns, o), Some{Err{AtKey{k} <> Nil{}, UnknownKey{}}})
    case _:
      None{}

# At the end of a tagged chain no case matched: the value is not an object,
# or its tag is missing, or it names no case.
def tag_err(+k: String, r: Raw) -> Maybe<&2, Err>:
  match r:
    case REnd{}:
      Some{Err{AtKey{k} <> Nil{}, Missing{}}}
    case RKey{j, v, o}:
      Some{Err{AtKey{k} <> Nil{}, missing_or(lookup(k, RKey{j, v, o}), NotOneOf{})}}
    case x:
      here(missing_or(x, NotObject{}))

# The count, as an error: at an SListLen the count is read before any element,
# so a list out of bounds is CountNotIn at the list's own path. A value that is
# not a list has no count to object to, and is refused as a list schema refuses
# it: NotList, or Missing/TooLarge for the two nodes that are never a shape
# (the same reasons check's own arms give them).
def count_err(+lo: Nat, +hi: Nat, r: Raw) -> Maybe<&2, Err>:
  match r:
    case RNil{}:
      in_err(list_len_ok(lo, hi, r), CountNotIn{lo, hi})
    case RCons{h, t}:
      in_err(list_len_ok(lo, hi, r), CountNotIn{lo, hi})
    case _:
      here(missing_or(r, NotList{}))

def check(~rule: Nat -> Raw -> Maybe<&2, Err>, s: Schema, r: Raw, +prev: Maybe<&2, Nat>) -> Maybe<&2, Err>:
  match s r:
    case SNat{} RNum{n}:
      None{}
    case SNat{} x:
      here(missing_or(x, NotNat{}))
    case SStr{} RStr{x}:
      None{}
    case SStr{} x:
      here(missing_or(x, NotString{}))
    case SNatIn{+lo, +hi} RNum{+n}:
      nat_in(lo, hi, RNum{n})
    case SNatIn{lo_, hi_} +x:
      here(missing_or(x, NotNat{}))
    case SStrLen{+lo, +hi, +s2} +x:
      first(check(~rule, s2, x, prev), len_err(lo, hi, x))
    case SListLen{+lo, +hi, +s2} +r:
      first(count_err(lo, hi, r), check(~rule, s2, r, None{}))
    case SOpt{inner} RNull{}:
      None{}
    case SOpt{inner} x:
      check(~rule, inner, x, None{})
    case SOptional{inner} RMissing{}:
      None{}
    case SOptional{inner} x:
      check(~rule, inner, x, None{})
    case SList{e} RNil{}:
      None{}
    case SList{+e} RCons{h, t}:
      first(under(AtIndex{0n}, check(~rule, e, h, None{})), later_l(check(~rule, SList{e}, t, None{})))
    case SList{e} x:
      here(missing_or(x, NotList{}))
    case SField{+name, fs, rest} REnd{}:
      first(under(AtField{0n, name}, check(~rule, fs, RMissing{}, None{})), later_f(check(~rule, rest, REnd{}, None{})))
    case SField{+name, fs, rest} RKey{+k, +v, +o}:
      first(key_err(key_once(name, RKey{k, v, o}), name), first(under(AtField{0n, name}, check(~rule, fs, lookup(name, RKey{k, v, o}), None{})), later_f(check(~rule, rest, RKey{k, v, o}, None{}))))
    case SField{name, fs, rest} x:
      here(missing_or(x, NotObject{}))
    case SEnd{} REnd{}:
      None{}
    case SEnd{} RKey{k, v, o}:
      None{}
    case SEnd{} x:
      here(missing_or(x, NotObject{}))
    case SRule{+s2, +tag} +x:
      first(check(~rule, s2, x, prev), rule(tag, x))
    case SStrict{+s2} +x:
      first(check(~rule, s2, x, prev), extra_err(key_names(s2), x))
    case STagged{+k, +n, cs, rest} +x:
      pick_err(is_tag(k, n, x), first(key_err(key_once(k, x), k), check(~rule, cs, drop_key(k, x), None{})), check(~rule, rest, x, None{}))
    case STagEnd{k} x:
      tag_err(k, x)
    case SBool{} RBool{b}:
      None{}
    case SBool{} +x:
      here(missing_or(x, NotBool{}))
    case STrue{} RBool{b}:
      true_err(b)
    case STrue{} x:
      here(missing_or(x, NotTrue{}))
    case SEnum{names} RStr{+x}:
      enum_err(in_names(x, names))
    case SEnum{names} x:
      here(missing_or(x, NotOneOf{}))
    case SVariant{+name, +vs, +rest} REnd{}:
      later_f(check(~rule, rest, REnd{}, None{}))
    case SVariant{+name, +vs, +rest} RKey{+k, +v, +o}:
      pick_err(is_missing(lookup(name, RKey{k, v, o})), later_f(check(~rule, rest, RKey{k, v, o}, None{})), first(key_err(key_once(name, RKey{k, v, o}), name), first(under(AtField{0n, name}, check(~rule, vs, lookup(name, RKey{k, v, o}), None{})), later_f(dup_err(rest, RKey{k, v, o})))))
    case SVariant{+name, +vs, +rest} x:
      here(missing_or(x, NotObject{}))
    case SVEnd{} REnd{}:
      here(NoVariant{})
    case SVEnd{} RKey{k, v, o}:
      here(NoVariant{})
    case SVEnd{} x:
      here(missing_or(x, NotObject{}))
    case STuple{ts, rest} RCons{h, t}:
      first(under(AtIndex{0n}, check(~rule, ts, h, None{})), later_l(check(~rule, rest, t, None{})))
    case STuple{ts, rest} RNil{}:
      here(TooShort{})
    case STuple{ts, rest} x:
      here(missing_or(x, NotList{}))
    case STEnd{} RNil{}:
      None{}
    case STEnd{} RCons{h, t}:
      here(TooLong{})
    case STEnd{} x:
      here(missing_or(x, NotList{}))

# ---- the claim the accuracy law makes ----
#
# defect follows a path instead of searching for one. Everything it passes on
# the way must conform, a step's name must be the schema's, and at the end of
# the path it answers what is wrong there. A path that does not fit the value
# leads nowhere (None).

def guard(b: Bool, m: Maybe<&2, Why>) -> Maybe<&2, Why>:
  match b:
    case True{}:
      m
    case False{}:
      None{}

# The same two reasons at an SNatIn and an SBool, replayed along a path: the
# value's own kind is the defect when the path ends here, and it is not a
# defect at all further along (the walk passed it).
def nat_in_defect(+lo: Nat, +hi: Nat, r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match r p:
    case RNum{+n} Nil{}:
      guard(Bool.not(num_ok(lo, hi, n)), Some{NotIn{lo, hi}})
    case RNum{n} st <> q:
      None{}
    case x Nil{}:
      Some{missing_or(x, NotNat{})}
    case x st <> q:
      None{}

def bool_defect(r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match r p:
    case RBool{b} _:
      None{}
    case x Nil{}:
      Some{missing_or(x, NotBool{})}
    case x st <> q:
      None{}

# ---- a rule, its replay, and the closed forms ----
#
# A rule reports its first error with a path relative to the value it was
# given. defect replays it by running the rule again: its path must be the
# reported one (path_eq, which never compares two names), and the claim of
# the accuracy law at an SRule is that the value conforms to the rule's
# schema and the rule itself reported this error.

def no_rule(tag: Nat, r: Raw) -> Maybe<&2, Err>:
  None{}

def first_why(m: Maybe<&2, Why>, +n: Maybe<&2, Why>) -> Maybe<&2, Why>:
  match m:
    case None{}:
      n
    case Some{w}:
      Some{w}

def step_eq(x: Step, y: Step) -> Bool:
  match x y:
    case AtIndex{i} AtIndex{j}:
      Nat.is_eq(i, j)
    case AtField{a, n} AtField{b, m}:
      Bool.and(Nat.is_eq(a, b), String.eq(n, m))
    case BoundAt{i, k} BoundAt{j, m}:
      Bool.and(Nat.is_eq(i, j), String.eq(k, m))
    case AtKey{k} AtKey{m}:
      String.eq(k, m)
    case _ _:
      False{}

def path_eq(x: List<&2, Step>, y: List<&2, Step>) -> Bool:
  match x y:
    case Nil{} Nil{}:
      True{}
    case a <> at b <> bt:
      Bool.and(step_eq(a, b), path_eq(at, bt))
    case _ _:
      False{}

def rule_defect(m: Maybe<&2, Err>, +p: List<&2, Step>) -> Maybe<&2, Why>:
  match m:
    case Some{Err{q, w}}:
      guard(path_eq(q, p), Some{w})
    case None{}:
      None{}

def not_list(x: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match p:
    case Nil{}:
      Some{missing_or(x, NotList{})}
    case st <> q:
      None{}

def not_object(x: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match p:
    case Nil{}:
      Some{missing_or(x, NotObject{})}
    case st <> q:
      None{}

def nat_defect(r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match r p:
    case RNum{n} _:
      None{}
    case x Nil{}:
      Some{missing_or(x, NotNat{})}
    case x st <> q:
      None{}

def str_defect(r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match r p:
    case RStr{x} _:
      None{}
    case x Nil{}:
      Some{missing_or(x, NotString{})}
    case x st <> q:
      None{}

def pick_why(b: Bool, +x: Maybe<&2, Why>, +y: Maybe<&2, Why>) -> Maybe<&2, Why>:
  match b:
    case True{}:
      x
    case False{}:
      y

def true_defect(r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match r p:
    case RBool{True{}} _:
      None{}
    case RBool{False{}} Nil{}:
      Some{NotTrue{}}
    case x Nil{}:
      Some{missing_or(x, NotTrue{})}
    case x st <> q:
      None{}

def enum_defect(names: List<&2, String>, r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match r p:
    case RStr{x} Nil{}:
      guard(Bool.not(in_names(x, names)), Some{NotOneOf{}})
    case RStr{x} st <> q:
      None{}
    case x Nil{}:
      Some{missing_or(x, NotOneOf{})}
    case x st <> q:
      None{}

def no_variant(p: List<&2, Step>) -> Maybe<&2, Why>:
  match p:
    case Nil{}:
      Some{NoVariant{}}
    case st <> q:
      None{}

# The claim about a second key: every key passed is absent, and the key the
# path names is there.
def dup_defect(s: Schema, +r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match s p:
    case SVariant{+n2, vs, rr} AtField{0n, m} <> Nil{}:
      guard(Bool.and(String.eq(m, n2), Bool.not(is_missing(lookup(n2, r)))), Some{TwoVariants{}})
    case SVariant{+n2, vs, rr} AtField{1n+j, m} <> q:
      guard(is_missing(lookup(n2, r)), dup_defect(rr, r, AtField{j, m} <> q))
    case _ _:
      None{}

def at_end(w: Why, p: List<&2, Step>) -> Maybe<&2, Why>:
  match p:
    case Nil{}:
      Some{w}
    case st <> q:
      None{}

# At a strict object the path is one key, and the replay checks it on its
# own: the key is there, and it is not one of the names.
def extra_defect(ns: List<&2, String>, +r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match p:
    case AtKey{+k} <> Nil{}:
      guard(Bool.and(has_key(k, r), Bool.not(in_names(k, ns))), Some{UnknownKey{}})
    case _:
      None{}

def tag_defect(+k: String, r: Raw, p: List<&2, Step>) -> Maybe<&2, Why>:
  match r p:
    case REnd{} AtKey{j} <> Nil{}:
      guard(String.eq(j, k), Some{Missing{}})
    case RKey{+j, +v, +o} AtKey{i} <> Nil{}:
      guard(String.eq(i, k), Some{missing_or(lookup(k, RKey{j, v, o}), NotOneOf{})})
    case REnd{} q:
      None{}
    case RKey{j, v, o} q:
      None{}
    case x Nil{}:
      Some{missing_or(x, NotObject{})}
    case x q:
      None{}

# The tag key of a tagged case, taken twice, as defect replays it. check
# reports it before the case's own schema is walked -- there is no place in the
# schema for the second occurrence -- so the path is one field step at the
# tag's own name and nothing after it. b is whether the key is not read once,
# so nothing is reported exactly when key_once holds; a path of any other shape
# is the case's own report, which the walk below answers.
def tag_key_defect(b: Bool, +k: String, p: List<&2, Step>) -> Maybe<&2, Why>:
  match b p:
    case False{} q:
      None{}
    case True{} AtField{0n, +j} <> Nil{}:
      pick_why(String.eq(j, k), Some{RepeatedKey{k}}, None{})
    case True{} q:
      None{}

def defect(~rule: Nat -> Raw -> Maybe<&2, Err>, s: Schema, r: Raw, +prev: Maybe<&2, Nat>, p: List<&2, Step>) -> Maybe<&2, Why>:
  match s r p:
    case SNat{} x q:
      nat_defect(x, q)
    case SStr{} x q:
      str_defect(x, q)
    case SNatIn{+lo, +hi} x q:
      nat_in_defect(lo, hi, x, q)
    case SStrLen{+lo, +hi, +s2} +x +q:
      pick_why(conforms(~rule, s2, x, prev), rule_defect(len_err(lo, hi, x), q), defect(~rule, s2, x, prev, q))
    case SListLen{+lo, +hi, +s2} +r +q:
      # The count came first in check, so the count's own error is the one
      # reported here exactly when there was one to report -- for a list out of
      # bounds and for a value that is not a list at all (list_len_ok is False
      # for both, and count_err reported something for both).
      pick_why(Bool.not(list_len_ok(lo, hi, r)), rule_defect(count_err(lo, hi, r), q), defect(~rule, s2, r, None{}, q))
    case SOpt{inner} RNull{} q:
      None{}
    case SOpt{inner} x q:
      defect(~rule, inner, x, None{}, q)
    case SOptional{inner} RMissing{} q:
      None{}  # absent is not wrong, at this path or below it
    case SOptional{inner} x q:
      defect(~rule, inner, x, None{}, q)
    case SList{e} RNil{} q:
      None{}
    case SList{e} RCons{h, t} AtIndex{0n} <> q:
      defect(~rule, e, h, None{}, q)
    case SList{+e} RCons{h, t} AtIndex{1n+j} <> q:
      guard(conforms(~rule, e, h, None{}), defect(~rule, SList{e}, t, None{}, AtIndex{j} <> q))
    case SList{+e} RCons{h, t} q:
      guard(conforms(~rule, e, h, None{}), defect(~rule, SList{e}, t, None{}, q))
    case SList{e} x q:
      not_list(x, q)
    case SField{+name, fs, rest} REnd{} AtField{0n, n} <> q:
      guard(String.eq(n, name), defect(~rule, fs, RMissing{}, None{}, q))
    case SField{+name, fs, rest} REnd{} AtField{1n+k, n} <> q:
      guard(conforms(~rule, fs, RMissing{}, None{}), defect(~rule, rest, REnd{}, None{}, AtField{k, n} <> q))
    case SField{+name, fs, rest} REnd{} q:
      guard(conforms(~rule, fs, RMissing{}, None{}), defect(~rule, rest, REnd{}, None{}, q))
    case SField{+name, fs, rest} RKey{+k, +v, +o} AtField{0n, n} <> +q:
      pick_why(Bool.not(key_once(name, RKey{k, v, o})), at_end(RepeatedKey{name}, q), guard(String.eq(n, name), defect(~rule, fs, lookup(name, RKey{k, v, o}), None{}, q)))
    case SField{+name, fs, rest} RKey{+k, +v, +o} AtField{1n+j, n} <> q:
      guard(conforms(~rule, fs, lookup(name, RKey{k, v, o}), None{}), defect(~rule, rest, RKey{k, v, o}, None{}, AtField{j, n} <> q))
    case SField{+name, fs, rest} RKey{+k, +v, +o} q:
      guard(conforms(~rule, fs, lookup(name, RKey{k, v, o}), None{}), defect(~rule, rest, RKey{k, v, o}, None{}, q))
    case SField{name, fs, rest} x q:
      not_object(x, q)
    case SEnd{} REnd{} q:
      None{}
    case SEnd{} RKey{k, v, o} q:
      None{}
    case SEnd{} x q:
      not_object(x, q)
    case SRule{+s2, +tag} +x +q:
      pick_why(conforms(~rule, s2, x, prev), rule_defect(rule(tag, x), q), defect(~rule, s2, x, prev, q))
    case SStrict{+s2} +x +q:
      pick_why(conforms(~rule, s2, x, prev), extra_defect(key_names(s2), x, q), defect(~rule, s2, x, prev, q))
    case STagged{+k, +n, cs, rest} +x +q:
      pick_why(is_tag(k, n, x), first_why(tag_key_defect(Bool.not(key_once(k, x)), k, q), defect(~rule, cs, drop_key(k, x), None{}, q)), defect(~rule, rest, x, None{}, q))
    case STagEnd{k} x q:
      tag_defect(k, x, q)
    case SBool{} x q:
      bool_defect(x, q)
    case STrue{} x q:
      true_defect(x, q)
    case SEnum{names} x q:
      enum_defect(names, x, q)
    case SVariant{+name, +vs, +rest} REnd{} AtField{1n+j, n} <> q:
      defect(~rule, rest, REnd{}, None{}, AtField{j, n} <> q)
    case SVariant{+name, +vs, +rest} REnd{} q:
      defect(~rule, rest, REnd{}, None{}, q)
    case SVariant{+name, +vs, +rest} RKey{+k, +v, +o} AtField{0n, +n} <> +q:
      pick_why(is_missing(lookup(name, RKey{k, v, o})), defect(~rule, rest, RKey{k, v, o}, None{}, AtField{0n, n} <> q), pick_why(Bool.not(key_once(name, RKey{k, v, o})), at_end(RepeatedKey{name}, q), guard(String.eq(n, name), defect(~rule, vs, lookup(name, RKey{k, v, o}), None{}, q))))
    case SVariant{+name, +vs, +rest} RKey{+k, +v, +o} AtField{1n+j, +n} <> +q:
      pick_why(is_missing(lookup(name, RKey{k, v, o})), defect(~rule, rest, RKey{k, v, o}, None{}, AtField{j, n} <> q), guard(conforms(~rule, vs, lookup(name, RKey{k, v, o}), None{}), dup_defect(rest, RKey{k, v, o}, AtField{j, n} <> q)))
    case SVariant{+name, +vs, +rest} RKey{+k, +v, +o} +q:
      pick_why(is_missing(lookup(name, RKey{k, v, o})), defect(~rule, rest, RKey{k, v, o}, None{}, q), None{})
    case SVariant{+name, +vs, +rest} x q:
      not_object(x, q)
    case SVEnd{} REnd{} q:
      no_variant(q)
    case SVEnd{} RKey{k, v, o} q:
      no_variant(q)
    case SVEnd{} x q:
      not_object(x, q)
    case STuple{ts, rest} RCons{h, t} AtIndex{0n} <> q:
      defect(~rule, ts, h, None{}, q)
    case STuple{+ts, rest} RCons{h, t} AtIndex{1n+j} <> q:
      guard(conforms(~rule, ts, h, None{}), defect(~rule, rest, t, None{}, AtIndex{j} <> q))
    case STuple{+ts, rest} RCons{h, t} q:
      guard(conforms(~rule, ts, h, None{}), defect(~rule, rest, t, None{}, q))
    case STuple{ts, rest} RNil{} q:
      at_end(TooShort{}, q)
    case STuple{ts, rest} x q:
      not_list(x, q)
    case STEnd{} RNil{} q:
      None{}
    case STEnd{} RCons{h, t} q:
      at_end(TooLong{}, q)
    case STEnd{} x q:
      not_list(x, q)

# The closed forms: template defs cannot cross the bundler, so the host
# calls these (a project with no rules).

def check0(s: Schema, r: Raw) -> Maybe<&2, Err>:
  check(~no_rule, s, r, None{})

def conforms0(s: Schema, r: Raw) -> Bool:
  conforms(~no_rule, s, r, None{})

# ---- the claims the choice laws make ----
#
# A second reading of a variant chain, by counting: the value is an object,
# exactly one of the chain's keys is in it, and every key that is there holds
# a value that conforms. A key that is there is read the way conforms reads
# it, key_once included: a key the chain names, taken twice, is not read once,
# so the counting reading refuses it exactly where conforms does.

def is_chain(s: Schema) -> Bool:
  match s:
    case SVariant{n, vs, rest}:
      is_chain(rest)
    case SVEnd{}:
      True{}
    case _:
      False{}

def is_object(r: Raw) -> Bool:
  match r:
    case REnd{}:
      True{}
    case RKey{k, v, o}:
      True{}
    case _:
      False{}

def one_if_there(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

def count_present(s: Schema, +r: Raw) -> Nat:
  match s:
    case SVariant{+n, vs, rest}:
      Nat.add(one_if_there(is_missing(lookup(n, r))), count_present(rest, r))
    case _:
      0n

def present_conform(~rule: Nat -> Raw -> Maybe<&2, Err>, +s: Schema, +r: Raw) -> Bool:
  match s:
    case SVariant{+n, vs, rest}:
      pick_bool(is_missing(lookup(n, r)), present_conform(~rule, rest, r), Bool.and(key_once(n, r), Bool.and(conforms(~rule, vs, lookup(n, r), None{}), present_conform(~rule, rest, r))))
    case _:
      True{}

# ---- the claim the tuple law makes ----
#
# A second reading of a tuple, over plain lists: the schema is built from a
# list of schemas, and the value conforms when it is a list of the same
# length and each position conforms to the schema at the same position.

def tuple_of(ss: List<&2, Schema>) -> Schema:
  match ss:
    case Nil{}:
      STEnd{}
    case h <> t:
      STuple{h, tuple_of(t)}

# raw_list and raw_len (a list, and how many elements it has) sit with the
# other bound helpers, above: an SListLen's test reads them.

def at_raw(r: Raw, +i: Nat) -> Raw:
  match r i:
    case RCons{h, t} 0n:
      h
    case RCons{h, t} 1n+j:
      at_raw(t, j)
    case _ _:
      RMissing{}

def each_pos(~rule: Nat -> Raw -> Maybe<&2, Err>, ss: List<&2, Schema>, +r: Raw, +i: Nat) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(conforms(~rule, h, at_raw(r, i), None{}), each_pos(~rule, t, r, 1n+i))

# ---- the claim the strict law makes ----
#
# How many keys of r are not in ns, counted rather than walked with a
# Bool.and: a second algorithm, so that a no_extra that lets a key through
# (or refuses a named one) disagrees with it.
def count_unknown(+ns: List<&2, String>, r: Raw) -> Nat:
  match r:
    case RKey{+k, v, o}:
      Nat.add(one_if_there(in_names(k, ns)), count_unknown(ns, o))
    case _:
      0n

# ---- a schema's meaning, and reading a value into it ----
#
# Meaning(s) is the Bend type a schema describes: a record is its fields,
# nested pairs ending in Unit; a variant chain is nested Eithers ending in
# Empty; a value that may be null (SOpt) or absent (SOptional) is a Maybe. A
# rule refines a shape and does not change its meaning. `enc` writes a
# meaning as the host's JSON would be; `dec` reads one back. Both are written
# once, for every schema, and LAWS.bend proves the round trip once.
#
# dec is a reader, not a check: run it on a value check accepted
# (checked_decodes says it then succeeds). On a value check refuses it may
# still read something, since a record reads its keys and ignores the rest.
#
# The round trip needs a well-formed schema (wf): a key named once in its
# object or chain (lookup reads the first), and an optional value that is not
# itself nullable (Some{None} and None would both be written null).

type Both<A: Data, B: Data> is Data:
  Both{a: A, b: B}

def Meaning(s: Schema) -> Data:
  match s:
    case SNat{}:
      Nat
    case SNatIn{lo, hi}:
      Nat
    case SStr{}:
      String
    case SStrLen{lo, hi, s2}:
      Meaning(s2)
    case SListLen{lo, hi, s2}:
      Meaning(s2)
    case SOpt{i}:
      Maybe<&2, Meaning(i)>
    case SOptional{i}:
      Maybe<&2, Meaning(i)>
    case SList{e}:
      List<&2, Meaning(e)>
    case SField{n, fs, rest}:
      Both<Meaning(fs), Meaning(rest)>
    case SEnd{}:
      Unit
    case SRule{s2, tag}:
      Meaning(s2)
    case SStrict{s2}:
      Meaning(s2)
    case STagged{k, n, cs, rest}:
      Either<&2, &2, Meaning(cs), Meaning(rest)>
    case STagEnd{k}:
      Empty
    case SBool{}:
      Bool
    case STrue{}:
      Unit
    case SEnum{names}:
      String
    case SVariant{n, vs, rest}:
      Either<&2, &2, Meaning(vs), Meaning(rest)>
    case SVEnd{}:
      Empty
    case STuple{ts, rest}:
      Both<Meaning(ts), Meaning(rest)>
    case STEnd{}:
      Unit

def enc(s: Schema, x: Meaning(s)) -> Raw:
  match s x:
    case SNat{} n:
      RNum{n}
    case SNatIn{lo_, hi_} n:
      RNum{n}
    case SStr{} x:
      RStr{x}
    case SStrLen{lo_, hi_, s2} v:
      enc(s2, v)
    case SListLen{lo_, hi_, s2} v:
      enc(s2, v)
    case SOpt{i} None{}:
      RNull{}
    case SOpt{i} Some{v}:
      enc(i, v)
    case SOptional{i} None{}:
      RMissing{}  # absent: the host writes no key where this one lands
    case SOptional{i} Some{v}:
      enc(i, v)
    case SList{e} Nil{}:
      RNil{}
    case SList{+e} h <> t:
      RCons{enc(e, h), enc(SList{e}, t)}
    case SField{n, fs, rest} Both{a, b}:
      RKey{n, enc(fs, a), enc(rest, b)}
    case SEnd{} Unit{}:
      REnd{}
    case SRule{s2, tag} v:
      enc(s2, v)
    case SStrict{s2} v:
      enc(s2, v)
    case STagged{k, n, cs, rest} Inl{a}:
      RKey{k, RStr{n}, enc(cs, a)}
    case STagged{k, n, cs, rest} Inr{b}:
      enc(rest, b)
    case STagEnd{k} e:
      Empty.absurd(Raw, e)
    case STrue{} Unit{}:
      RBool{True{}}
    case SBool{} b:
      RBool{b}
    case SEnum{names} x:
      RStr{x}
    case SVariant{n, vs, rest} Inl{a}:
      RKey{n, enc(vs, a), REnd{}}
    case SVariant{n, vs, rest} Inr{b}:
      enc(rest, b)
    case SVEnd{} e:
      Empty.absurd(Raw, e)
    case STuple{ts, rest} Both{a, b}:
      RCons{enc(ts, a), enc(rest, b)}
    case STEnd{} Unit{}:
      RNil{}

def lcons(-A: Data, h: Maybe<&2, A>, t: Maybe<&2, List<&2, A>>) -> Maybe<&2, List<&2, A>>:
  match h t:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

def both(-A: Data, -B: Data, p: Maybe<&2, A>, q: Maybe<&2, B>) -> Maybe<&2, Both<A, B>>:
  match p q:
    case Some{x} Some{y}:
      Some{Both{x, y}}
    case _ _:
      None{}

def opt_some(-A: Data, m: Maybe<&2, A>) -> Maybe<&2, Maybe<&2, A>>:
  match m:
    case Some{v}:
      Some{Some{v}}
    case None{}:
      None{}

def map_inl(-A: Data, -B: Data, m: Maybe<&2, A>) -> Maybe<&2, Either<&2, &2, A, B>>:
  match m:
    case Some{v}:
      Some{Inl{v}}
    case None{}:
      None{}

def map_inr(-A: Data, -B: Data, m: Maybe<&2, B>) -> Maybe<&2, Either<&2, &2, A, B>>:
  match m:
    case Some{v}:
      Some{Inr{v}}
    case None{}:
      None{}

def pick_m(-A: Data, b: Bool, x: A, y: A) -> A:
  match b:
    case True{}:
      x
    case False{}:
      y

def true_unit(b: Bool) -> Maybe<&2, Unit>:
  match b:
    case True{}:
      Some{Unit{}}
    case False{}:
      None{}

def nullish(r: Raw) -> Bool:
  match r:
    case RNull{}:
      True{}
    case RMissing{}:
      True{}
    case _:
      False{}

def dec(s: Schema, r: Raw) -> Maybe<&2, Meaning(s)>:
  match s r:
    case SNat{} RNum{n}:
      Some{n}
    case SNatIn{lo_, hi_} RNum{n}:
      Some{n}
    case SStr{} RStr{x}:
      Some{x}
    case SStrLen{lo_, hi_, s2} x:
      dec(s2, x)
    case SListLen{lo_, hi_, s2} x:
      dec(s2, x)
    case SOpt{+i} +x:
      pick_m(Maybe<&2, Maybe<&2, Meaning(i)>>, nullish(x), Some{None{}}, opt_some(Meaning(i), dec(i, x)))
    case SOptional{+i} +x:
      pick_m(Maybe<&2, Maybe<&2, Meaning(i)>>, is_missing(x), Some{None{}}, opt_some(Meaning(i), dec(i, x)))
    case SList{e} RNil{}:
      Some{Nil{}}
    case SList{+e} RCons{h, t}:
      lcons(Meaning(e), dec(e, h), dec(SList{e}, t))
    case SField{+n, +fs, +rest} +x:
      both(Meaning(fs), Meaning(rest), dec(fs, lookup(n, x)), dec(rest, x))
    case SEnd{} x:
      Some{Unit{}}
    case SRule{s2, tag} x:
      dec(s2, x)
    case SStrict{s2} x:
      dec(s2, x)
    case STagged{+k, +n, +cs, +rest} +x:
      pick_m(Maybe<&2, Either<&2, &2, Meaning(cs), Meaning(rest)>>, is_tag(k, n, x), map_inl(Meaning(cs), Meaning(rest), dec(cs, drop_key(k, x))), map_inr(Meaning(cs), Meaning(rest), dec(rest, x)))
    case STrue{} RBool{b}:
      true_unit(b)
    case SBool{} RBool{b}:
      Some{b}
    case SEnum{names} RStr{x}:
      Some{x}
    case SVariant{+n, +vs, +rest} +x:
      pick_m(Maybe<&2, Either<&2, &2, Meaning(vs), Meaning(rest)>>, is_missing(lookup(n, x)), map_inr(Meaning(vs), Meaning(rest), dec(rest, x)), map_inl(Meaning(vs), Meaning(rest), dec(vs, lookup(n, x))))
    case STuple{+ts, +rest} RCons{h, t}:
      both(Meaning(ts), Meaning(rest), dec(ts, h), dec(rest, t))
    case STEnd{} RNil{}:
      Some{Unit{}}
    case _ _:
      None{}

# ---- a well-formed schema ----
#
# wf is what the round trip needs: a key named once in its object or chain
# (lookup reads the first), an optional value that is not itself nullable, and
# a tagged case whose own schema leaves the tag key alone.
# Three constructors ask more than their own shape:
#
#   STagged writes its key and then the case's own object beside it, so the
#   case's schema may not put that key anywhere in the same object (no_key).
#   A case that names its own tag key encodes to a document holding the key
#   twice: enc writes the tag and the case's own field writes it again, and
#   the host builds that document as a JS object, where the second write --
#   the spread of the case's own fields -- overwrites the first. What the
#   encoder wrote is then not what the decoder reads, so refusing the schema
#   is what keeps encode_conforms true.
#
#   SOptional is where a field may be absent, so it belongs immediately under
#   a field and nowhere else: every other place a schema sits is guarded by
#   opt_at, which asks whether an absent value can reach the top of what enc
#   writes for it. That excludes an SOptional anywhere but a field's schema,
#   and also a schema that would pass one straight through (SOpt{SOptional{i}}
#   writes RMissing for Some{None}, where nothing can tell it from an absent
#   key). An SOptional's own inner is guarded the same way: None and
#   Some{None} would both be written as an absent key.
#
#   SOpt's inner may not be nullable at all (its own None and the inner's null
#   would both be written null), and nullable asks an SOptional too.

# An absent value reaches the top of what enc writes for s: s is an SOptional,
# or it hands the value it was given straight to a schema that is (a rule, a
# strict object, a bound, or the tail of a variant or tagged chain -- and an
# SOpt, whose Some case passes the value through). Everything else wraps what
# it writes in a constructor of its own, so an absent value cannot surface.
def opt_at(s: Schema) -> Bool:
  match s:
    case SOptional{i}:
      True{}
    case SOpt{i}:
      opt_at(i)
    case SRule{s2, tag}:
      opt_at(s2)
    case SStrict{s2}:
      opt_at(s2)
    case SStrLen{lo, hi, s2}:
      opt_at(s2)
    case SListLen{lo, hi, s2}:
      opt_at(s2)
    case STagged{k, n, cs, rest}:
      opt_at(rest)
    case SVariant{n, vs, rest}:
      opt_at(rest)
    case _:
      False{}

def nullable(s: Schema) -> Bool:
  match s:
    case SOpt{i}:
      True{}
    case SOptional{i}:
      True{}  # absent and the inner's own null read as the same None
    case SRule{s2, tag}:
      nullable(s2)
    case SStrict{s2}:
      nullable(s2)
    case SStrLen{lo, hi, s2}:
      nullable(s2)
    case SListLen{lo, hi, s2}:
      nullable(s2)
    case STagged{k, n, cs, rest}:
      nullable(rest)
    case SVariant{n, vs, rest}:
      nullable(rest)
    case _:
      False{}

# ---- the object a schema's encoding lands in ----
#
# enc writes an object as one flat chain of keys. An SField writes its name and
# its rest continues that object; an SVariant writes its name and the value
# under it is a chain of its own (REnd ends it, so it is a value and not a
# continuation). A wrapper -- a rule, a strict object, a bound, an optional --
# writes no key of its own and hands its value straight to its inner schema,
# so a key reaches the top of the object from inside any of them. A tagged
# case's schema is the same object the tag key was written into, and so is the
# rest of its chain.
#
# no_key is that, written down: k does not reach the top of the object enc
# builds for s, for any value of s. wf asks it of a tagged case's own schema,
# which is what keeps the tag key from being written twice.
def no_key(+k: String, s: Schema) -> Bool:
  match s:
    case SField{+n, fs, rest}:
      Bool.and(Bool.not(String.eq(n, k)), Bool.and(Bool.not(String.eq(k, n)), no_key(k, rest)))
    case SVariant{+n, vs, rest}:
      Bool.and(Bool.not(String.eq(n, k)), Bool.and(Bool.not(String.eq(k, n)), no_key(k, rest)))
    case SStrict{s2}:
      no_key(k, s2)
    case SRule{s2, tag}:
      no_key(k, s2)
    case SStrLen{lo, hi, s2}:
      no_key(k, s2)
    case SListLen{lo, hi, s2}:
      no_key(k, s2)
    case SOpt{i}:
      no_key(k, i)
    case SOptional{i}:
      no_key(k, i)
    case STagged{+k2, n2, cs2, rest2}:
      Bool.and(Bool.not(String.eq(k2, k)), Bool.and(Bool.not(String.eq(k, k2)), Bool.and(no_key(k, cs2), no_key(k, rest2))))
    case _:
      True{}

# n is not a key of the record chain s (a chain ends in SEnd). Both orders are
# asked, as fresh_v asks them: which of the two names a step puts first depends
# on which of them is the value's key there, and asking both spares a proof
# that String.eq is symmetric.
def fresh_f(+n: String, s: Schema) -> Bool:
  match s:
    case SField{+m, fs, rest}:
      Bool.and(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), fresh_f(n, rest)))
    case SEnd{}:
      True{}
    case _:
      False{}

# n is not a key of the variant chain s (a chain ends in SVEnd). Both orders
# are asked: reading a key compares the names one way, reading past it the
# other, and asking both spares a proof that String.eq is symmetric.
def fresh_v(+n: String, s: Schema) -> Bool:
  match s:
    case SVariant{+m, vs, rest}:
      Bool.and(Bool.not(String.eq(m, n)), Bool.and(Bool.not(String.eq(n, m)), fresh_v(n, rest)))
    case SVEnd{}:
      True{}
    case _:
      False{}

# A record chain (ending in SEnd) or a variant chain (ending in SVEnd): what
# SStrict may wrap, so every key its encoding writes is a declared name.
# A chain of keys (SField or SVariant links, ending in SEnd or SVEnd): what
# SStrict may wrap, so every key its encoding writes is a name it declares.
def is_keyed(s: Schema) -> Bool:
  match s:
    case SField{n, fs, rest}:
      is_keyed(rest)
    case SEnd{}:
      True{}
    case SVariant{n, vs, rest}:
      is_keyed(rest)
    case SVEnd{}:
      True{}
    case _:
      False{}

# n names no case of the tagged chain s, whose key is k, and the chain ends
# in STagEnd{k}: one key for the whole chain.
def fresh_t(+k: String, +n: String, s: Schema) -> Bool:
  match s:
    case STagged{+k2, +m, cs, rest}:
      Bool.and(String.eq(k2, k), Bool.and(Bool.not(String.eq(m, n)), fresh_t(k, n, rest)))
    case STagEnd{k2}:
      String.eq(k2, k)
    case _:
      False{}

def wf(s: Schema) -> Bool:
  match s:
    case SOpt{+i}:
      Bool.and(Bool.not(nullable(i)), wf(i))
    case SOptional{+i}:
      Bool.and(Bool.not(opt_at(i)), wf(i))
    case SList{+e}:
      Bool.and(Bool.not(opt_at(e)), wf(e))
    case SListLen{lo_, hi_, +s2}:
      Bool.and(Bool.not(opt_at(s2)), wf(s2))
    case SStrLen{lo_, hi_, +s2}:
      Bool.and(Bool.not(opt_at(s2)), wf(s2))
    case SField{+n, fs, +rest}:
      Bool.and(wf(fs), Bool.and(fresh_f(n, rest), wf(rest)))
    case SRule{+s2, tag}:
      Bool.and(Bool.not(opt_at(s2)), wf(s2))
    case SStrict{+s2}:
      Bool.and(is_keyed(s2), Bool.and(Bool.not(opt_at(s2)), wf(s2)))
    case STagged{+k, +n, +cs, +rest}:
      Bool.and(Bool.not(opt_at(cs)), Bool.and(wf(cs), Bool.and(no_key(k, cs), Bool.and(fresh_t(k, n, rest), wf(rest)))))
    case SVariant{+n, +vs, +rest}:
      Bool.and(Bool.not(opt_at(vs)), Bool.and(wf(vs), Bool.and(fresh_v(n, rest), wf(rest))))
    case STuple{+ts, +rest}:
      Bool.and(Bool.not(opt_at(ts)), Bool.and(wf(ts), Bool.and(Bool.not(opt_at(rest)), wf(rest))))
    case _:
      True{}

# Every enum value in x is one of its names (encode_conforms' premise).
def names_ok(s: Schema, x: Meaning(s)) -> Bool:
  match s x:
    case SOpt{i} None{}:
      True{}
    case SOpt{i} Some{v}:
      names_ok(i, v)
    case SList{e} Nil{}:
      True{}
    case SList{+e} h <> t:
      Bool.and(names_ok(e, h), names_ok(SList{e}, t))
    case SField{n, fs, rest} Both{a, b}:
      Bool.and(names_ok(fs, a), names_ok(rest, b))
    case SRule{s2, tag} v:
      names_ok(s2, v)
    case SStrict{s2} v:
      names_ok(s2, v)
    case SStrLen{lo_, hi_, s2} v:
      names_ok(s2, v)
    case SListLen{lo_, hi_, s2} v:
      names_ok(s2, v)
    case SOptional{i} None{}:
      True{}
    case SOptional{i} Some{v}:
      names_ok(i, v)
    case STagged{k, n, cs, rest} Inl{a}:
      names_ok(cs, a)
    case STagged{k, n, cs, rest} Inr{b}:
      names_ok(rest, b)
    case SEnum{names} x:
      in_names(x, names)
    case SVariant{n, vs, rest} Inl{a}:
      names_ok(vs, a)
    case SVariant{n, vs, rest} Inr{b}:
      names_ok(rest, b)
    case STuple{ts, rest} Both{a, b}:
      Bool.and(names_ok(ts, a), names_ok(rest, b))
    case _ _:
      True{}

# Every bound a constructor states holds of the value that will be written, at
# every place one sits in the schema (encode_conforms' second premise, beside
# names_ok). The encoder writes the meaning unchanged, so a value outside a
# bound is written out as it is and refused by check on the way back: the host
# that built it is at fault, and this is where it says so. An SStrLen's bound
# is read off the string its own schema writes, and an SListLen's count off the
# list it writes, which is why enc appears here.
def bounds_ok(s: Schema, x: Meaning(s)) -> Bool:
  match s x:
    case SOpt{i} None{}:
      True{}
    case SOpt{i} Some{v}:
      bounds_ok(i, v)
    case SList{e} Nil{}:
      True{}
    case SList{+e} h <> t:
      Bool.and(bounds_ok(e, h), bounds_ok(SList{e}, t))
    case SField{n, fs, rest} Both{a, b}:
      Bool.and(bounds_ok(fs, a), bounds_ok(rest, b))
    case SRule{s2, tag} v:
      bounds_ok(s2, v)
    case SStrict{s2} v:
      bounds_ok(s2, v)
    case STagged{k, n, cs, rest} Inl{a}:
      bounds_ok(cs, a)
    case STagged{k, n, cs, rest} Inr{b}:
      bounds_ok(rest, b)
    case SNatIn{+lo, +hi} n:
      num_ok(lo, hi, n)
    case SStrLen{+lo, +hi, +s2} +v:
      Bool.and(bounds_ok(s2, v), len_ok(lo, hi, enc(s2, v)))
    case SListLen{+lo, +hi, +s2} +v:
      Bool.and(bounds_ok(s2, v), list_len_ok(lo, hi, enc(s2, v)))
    case SOptional{i} None{}:
      True{}
    case SOptional{i} Some{v}:
      bounds_ok(i, v)
    case SVariant{n, vs, rest} Inl{a}:
      bounds_ok(vs, a)
    case SVariant{n, vs, rest} Inr{b}:
      bounds_ok(rest, b)
    case STuple{ts, rest} Both{a, b}:
      Bool.and(bounds_ok(ts, a), bounds_ok(rest, b))
    case _ _:
      True{}
