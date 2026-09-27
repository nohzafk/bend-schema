import Base
import ./core.bend as C

# The laws of bend-schema, for every schema, every value and every rule:
# proved once, and every schema built from these combinators has them.
#
#   check_exact     check finds nothing exactly when the value conforms: it
#                   neither lets a bad value through nor refuses a good one.
#                   At an SRule the value must conform to the rule's schema,
#                   and the rule must report nothing.
#   check_accurate  what check reports is there: following its path, every
#                   value passed on the way conforms, and at the end the value
#                   is wrong in the way it says. At an SRule, the schema's
#                   shape was not the defect and the rule itself reported
#                   this error at the path it names.
#   enum_accepts    every name in an SEnum's list is accepted.
#   enum_admits     a string SEnum accepts is one of its names, and here is
#                   where. Together they pin in_names, which check and
#                   conforms share.
#   variant_meaning for a chain of SVariant keys ending in SVEnd, a value
#                   conforms exactly when it is an object, exactly one of the
#                   keys is in it, and the value under that key conforms: a
#                   second reading by counting, which pins none_present.
#   too_large_reported
#                   a node the codec refused to build is reported where it
#                   stands, with TooLarge: the one thing the core can be told
#                   about a size.
#   sbool_meaning   SBool accepts a boolean and nothing else.
#   sstr_len_meaning
#                   SStrLen{lo, hi, s} accepts a string whose length is in the
#                   bounds and that also satisfies s -- str_len_in_meaning,
#                   restated for the constructor.
#   snat_in_meaning SNatIn{lo, hi} accepts a number in the bounds --
#                   nat_in_meaning, restated for the constructor.
#                   A lo past hi is an empty range, not an error: nothing is in
#                   bounds, and each of these laws holds for every lo and hi.
#   slist_len_meaning
#                   SListLen{lo, hi, s} accepts a list whose element count is
#                   in the bounds and that also satisfies s -- str_len_in_meaning
#                   over elements. A value that is not a list is not in bounds
#                   here either (the count is a list's), and it is the inner
#                   schema's to refuse, exactly as check reports it.
#   soptional_meaning
#                   SOptional{inner} accepts an absent value (RMissing), and
#                   every other value exactly as the inner schema accepts it:
#                   the constructor adds absence and nothing else.
#
# bounds_meaning died with SBounds: the bounded list is billing's rule now,
# and its meaning is billing's law.
#
# Decided by the human with these laws (acl, 2026-09-24): an SVariant object
# with none of its keys, or with two of them, is an error, and a key's value
# is checked by its own schema (so {any: false} is refused by STrue).
#
# Decided by the human with these laws: a key the schema names must be
# present, and an optional value is written null; keys the schema does not
# name are ignored; the first error is depth first, by position. A rule runs
# only after the shape it refines holds, and its error's path is relative to
# the value it was given. (With a key repeated in an object, lookup reads the
# first: a JSON object has no repeated keys, and a value that repeats one is
# refused before any lookup is trusted -- repeated_key_refused.)

law check_exact:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +s: C.Schema
  for +r: C.Raw
  for +prev: Maybe<&2, Nat>
  {Maybe.is_none(&2, C.Err, C.check(~rule, s, r, prev)) == C.conforms(~rule, s, r, prev) : Bool}

law check_accurate:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +s: C.Schema
  for +r: C.Raw
  for +prev: Maybe<&2, Nat>
  for +path: List<&2, C.Step>
  for +why: C.Why
  for h: {C.check(~rule, s, r, prev) == Some{C.Err{path, why}} : Maybe<&2, C.Err>}
  {C.defect(~rule, s, r, prev, path) == Some{why} : Maybe<&2, C.Why>}

law enum_accepts:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +pre: List<&2, String>
  for +n: String
  for +post: List<&2, String>
  {C.conforms(~rule, C.SEnum{List.append(&2, String, pre, n <> post)}, C.RStr{n}, None{}) == True{} : Bool}

def OneOf(ns: List<&2, String>, x: String) -> Type:
  &pre: List<&2, String> -> &n: String -> &post: List<&2, String> ->
    {ns == List.append(&2, String, pre, n <> post) : List<&2, String>} & {String.eq(x, n) == True{} : Bool}

law enum_admits:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +ns: List<&2, String>
  for +x: String
  for h: {C.conforms(~rule, C.SEnum{ns}, C.RStr{x}, None{}) == True{} : Bool}
  OneOf(ns, x)

law variant_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +s: C.Schema
  for +r: C.Raw
  for hc: {C.is_chain(s) == True{} : Bool}
  {C.conforms(~rule, s, r, None{}) == Bool.and(C.is_object(r), Bool.and(Nat.is_eq(C.count_present(s, r), 1n), C.present_conform(~rule, s, r))) : Bool}

# ---- a key the schema reads, taken twice ----
#
# A key the schema READS as a field key (SField) or as a variant key
# (SVariant) must appear at most once in the value: with the key repeated,
# lookup reads the first one and the second is unreachable, so the value says
# something the schema cannot mean, and it is refused. Both halves of that are
# stated, and stated at explicit constructors and nothing else: the value does
# not conform, and check reports RepeatedKey at that key's own name with no
# step after it. Nothing else in the gate can catch a key_once that is wrong:
# check_exact is a consistency law, which a key_once wrong in the same
# direction on both sides satisfies, and the mutant has key_err stop
# reporting, which leaves key_once itself untested.
#
# Known hole, deliberately left. The TAG key of a tagged case is not checked,
# here or in conforms, check or defect. A case that names its own tag key
# encodes to a document holding that key twice -- enc writes the tag, and the
# case's own field writes it again -- so requiring a tag key to appear once
# would make encode_conforms false for a schema wf accepts. A tag key
# repeated in the value is therefore still accepted.
def Refused(s: C.Schema, r: C.Raw, +p: List<&2, C.Step>, +w: C.Why) -> Type:
  {C.conforms(~C.no_rule, s, r, None{}) == False{} : Bool} & {C.check(~C.no_rule, s, r, None{}) == Some{C.Err{p, w}} : Maybe<&2, C.Err>}

law repeated_key_refused:
  Refused(C.SField{"a", C.SNat{}, C.SEnd{}}, C.RKey{"a", C.RNum{1n}, C.RKey{"a", C.RNum{2n}, C.REnd{}}}, C.AtField{0n, "a"} <> Nil{}, C.RepeatedKey{"a"}) & Refused(C.SVariant{"a", C.SNat{}, C.SVEnd{}}, C.RKey{"a", C.RNum{1n}, C.RKey{"a", C.RNum{2n}, C.REnd{}}}, C.AtField{0n, "a"} <> Nil{}, C.RepeatedKey{"a"})

# ---- a key the schema does not name ----
#
# A key the schema does not name is ignored, so adding one to an object that
# already conforms leaves the answer alone -- before the keys the schema reads,
# or after them. Stated at explicit constructors, like repeated_key_refused,
# and that is the point of it (D3): the general form is FALSE. key_names names
# the keys of a chain and nothing else -- the SField and the SVariant it walks,
# not the wrappers a chain may sit in -- so its list says nothing about a
# wrapper, and a key outside that list can still be one the schema needs. The
# counterexample, which is why this law is at literals: with
# s = SOpt{SField{"a", SNat{}, SEnd{}}}, k = "a" and r = REnd{}, the premise
# Bool.not(in_names(k, key_names(s))) holds, because key_names(SOpt{i}) is Nil{}
# and Nil{} names no key at all, yet conforms(SOpt{i}, r) is False while
# conforms(SOpt{i}, RKey{"a", RNum{1}, REnd{}}) is True: the key is not extra
# at all, it is the one the wrapper's own schema asks for. A variant chain
# stands beside the record in the law because at literals it costs the same
# computation: none_present over a concrete chain reduces, and no skip lemma is
# wanted for it.
#
# What is deliberately not here. The reordering half of "non-canonical still
# decodes" is unproved: no def in the core reorders an object's keys -- lookup,
# drop_key, has_key and no_extra read them, and none of them moves one -- so a
# permuted value has nothing here to be an instance of. And a key the schema
# does not name that appears TWICE is left alone as well (core.bend, "a key the
# schema does not name"): a key nothing reads is unobservable however often it
# is written, so it is not refused, unlike the repeated key of
# repeated_key_refused. Neither is stated as a law: the first has no code to be
# false about, the second is unobservable by construction.

law unnamed_key_ignored:
  {C.conforms(~C.no_rule, C.SField{"a", C.SNat{}, C.SEnd{}}, C.RKey{"z", C.RNum{9n}, C.RKey{"a", C.RNum{1n}, C.REnd{}}}, None{}) == C.conforms(~C.no_rule, C.SField{"a", C.SNat{}, C.SEnd{}}, C.RKey{"a", C.RNum{1n}, C.REnd{}}, None{}) : Bool} &
  {C.conforms(~C.no_rule, C.SField{"a", C.SNat{}, C.SEnd{}}, C.RKey{"a", C.RNum{1n}, C.RKey{"z", C.RNum{9n}, C.REnd{}}}, None{}) == C.conforms(~C.no_rule, C.SField{"a", C.SNat{}, C.SEnd{}}, C.RKey{"a", C.RNum{1n}, C.REnd{}}, None{}) : Bool} &
  {C.conforms(~C.no_rule, C.SVariant{"a", C.SNat{}, C.SVEnd{}}, C.RKey{"z", C.RNum{9n}, C.RKey{"a", C.RNum{1n}, C.REnd{}}}, None{}) == C.conforms(~C.no_rule, C.SVariant{"a", C.SNat{}, C.SVEnd{}}, C.RKey{"a", C.RNum{1n}, C.REnd{}}, None{}) : Bool}

# A tuple conforms exactly when the value is a list, as long as the tuple,
# and each position conforms. Without it, a bug shared by check and conforms
# (both skipping a position) passes the two laws above.
law tuple_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +ss: List<&2, C.Schema>
  for +r: C.Raw
  {C.conforms(~rule, C.tuple_of(ss), r, None{}) == Bool.and(C.raw_list(r), Bool.and(Nat.is_eq(C.raw_len(r), List.length(&2, C.Schema, ss)), C.each_pos(~rule, ss, r, 0n))) : Bool}

# ---- a strict object ----
#
# SStrict{s} is s, and no key but the ones s names. The right side counts
# the unknown keys (count_unknown), a second walk that shares only in_names
# with the core, and in_names is pinned by the enum laws.

law strict_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +s: C.Schema
  for +r: C.Raw
  {C.conforms(~rule, C.SStrict{s}, r, None{}) == Bool.and(C.conforms(~rule, s, r, None{}), Nat.is_eq(C.count_unknown(C.key_names(s), r), 0n)) : Bool}

# ---- a tagged union ----
#
# tagged_meaning: at a case, a value whose tag is the case's name conforms
# exactly when the object without the tag conforms to the case; any other
# value is the rest's to decide. At the chain's end nothing conforms.
# drop_meaning pins drop_key, which conforms, check and dec share: what it
# leaves under k is what was under k after the first one (so a single tag
# key is gone), and every other key reads as before.

law tagged_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +k: String
  for +n: String
  for +cs: C.Schema
  for +rest: C.Schema
  for +r: C.Raw
  {C.conforms(~rule, C.STagged{k, n, cs, rest}, r, None{}) == C.pick_bool(C.is_tag(k, n, r), C.conforms(~rule, cs, C.drop_key(k, r), None{}), C.conforms(~rule, rest, r, None{})) : Bool}

law tag_end_refuses:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +k: String
  for +r: C.Raw
  {C.conforms(~rule, C.STagEnd{k}, r, None{}) == False{} : Bool}

law drop_first:
  for +k: String
  for +v: C.Raw
  for +o: C.Raw
  {C.drop_key(k, C.RKey{k, v, o}) == o : C.Raw}

law drop_other:
  for +k: String
  for +j: String
  for +r: C.Raw
  for h: {False{} == String.eq(k, j) : Bool}
  {C.lookup(j, C.drop_key(k, r)) == C.lookup(j, r) : C.Raw}

# ---- ready-made rules ----
#
# Each pins its rule to what it means: on the value it is about, it reports
# nothing exactly when the value is in the bounds (both ends included).

law str_len_in_meaning:
  for +lo: Nat
  for +hi: Nat
  for +x: String
  {Maybe.is_none(&2, C.Err, C.str_len_in(lo, hi, C.RStr{x})) == Bool.and(Nat.is_le(lo, String.length(x)), Nat.is_le(String.length(x), hi)) : Bool}

law nat_in_meaning:
  for +lo: Nat
  for +hi: Nat
  for +n: Nat
  {Maybe.is_none(&2, C.Err, C.nat_in(lo, hi, C.RNum{n})) == Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi)) : Bool}

# ---- a bound is a constructor ----
#
# Approved with these constructors (D4): a bound belongs to the schema, not to
# a rule's tag, so a host can build "a number from 1 to 6" or "a string of 1 to
# 64 characters" without a Bend program. Each one keeps the meaning of the rule
# it comes from -- str_len_in_meaning and nat_in_meaning restated -- and adds a
# shape of its own. lo > hi is an empty range: nothing is in bounds, and the
# laws still hold for every lo and hi (nothing in the core refuses the schema
# itself, it just accepts no value).
#
# Every other law covers them too: check_exact, check_accurate,
# too_large_reported, decode_encode, checked_decodes and encode_conforms are
# stated for every schema, so the new constructors are cases of them (see
# encode_conforms: a value outside a bound is written out unchanged, which is
# why it is a premise of that law rather than something the encoder can know).

# SBool accepts a boolean and nothing else: any b, and no other value.
law sbool_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +r: C.Raw
  {C.conforms(~rule, C.SBool{}, r, None{}) == C.is_bool(r) : Bool}

# SStrLen{lo, hi, s} accepts a string whose length is in the bounds, and that
# also satisfies s: the length part is str_len_in_meaning's, restated for the
# constructor (both ends included).
law sstr_len_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +lo: Nat
  for +hi: Nat
  for +s: C.Schema
  for +x: String
  {C.conforms(~rule, C.SStrLen{lo, hi, s}, C.RStr{x}, None{}) == Bool.and(C.conforms(~rule, s, C.RStr{x}, None{}), Bool.and(Nat.is_le(lo, String.length(x)), Nat.is_le(String.length(x), hi))) : Bool}

# SNatIn{lo, hi} accepts a number in the bounds, both ends included:
# nat_in_meaning's, restated for the constructor.
law snat_in_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +lo: Nat
  for +hi: Nat
  for +n: Nat
  {C.conforms(~rule, C.SNatIn{lo, hi}, C.RNum{n}, None{}) == Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi)) : Bool}

# SListLen{lo, hi, s} accepts a list whose element count is in the bounds, and
# that also satisfies s. The count is spelled out here rather than left to the
# helper the core reads, so that a bound off by one is the law's business too:
# a list of exactly lo or exactly hi elements is in, and one of any other count
# is not, for every lo and hi (lo > hi accepts no list at all). A value that is
# not a list is not in bounds, and the inner schema decides it.
law slist_len_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +lo: Nat
  for +hi: Nat
  for +s: C.Schema
  for +r: C.Raw
  {C.conforms(~rule, C.SListLen{lo, hi, s}, r, None{}) == Bool.and(Bool.and(C.raw_list(r), Bool.and(Nat.is_le(lo, C.raw_len(r)), Nat.is_le(C.raw_len(r), hi))), C.conforms(~rule, s, r, None{})) : Bool}

# SOptional{inner} accepts an absent value, and every other value exactly as
# the inner schema accepts it: the constructor adds absence and nothing else.
# enc writes None as RMissing (no key at all, in the host's JSON) and dec reads
# RMissing back as None; null is not absent, so it is refused unless the inner
# is nullable itself.
law soptional_meaning:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +i: C.Schema
  for +r: C.Raw
  {C.conforms(~rule, C.SOptional{i}, r, None{}) == Bool.or(C.is_missing(r), C.conforms(~rule, i, r, None{})) : Bool}

# ---- a value too big to walk ----

# The codec refuses to build a value past its budget and puts one RTooBig in
# place of the list or object that ran past it (codec.ts); nothing else in the
# core knows a size. So the claim about that node is local: it conforms to
# nothing, and the walk that reaches it reports it right there (the empty
# path, for the value it was given) with TooLarge -- never the schema kind's
# own reason, which would say the host sent the wrong shape when what it sent
# was too much of the right one. A node further down is reported one step
# along by check's own step machinery, which check_accurate covers, and the
# codec's budget (that a value inside it converts unchanged) is a run-time
# test, since the codec is TypeScript.
law too_large_reported:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +s: C.Schema
  for +prev: Maybe<&2, Nat>
  {C.check(~rule, s, C.RTooBig{}, prev) == Some{C.Err{Nil{}, C.TooLarge{}}} : Maybe<&2, C.Err>}

# ---- a schema's meaning: the decoder, derived from the schema ----
#
# Meaning, enc and dec are written once for every schema (core.bend), so a
# project stops writing its reader and its round trip. The three laws below
# were approved with the design: wf is a premise (a schema is the
# programmer's, not the wire's), and an enum means its string.

# What was written reads back as itself.
law decode_encode:
  for +s: C.Schema
  for +x: C.Meaning(s)
  for hw: {C.wf(s) == True{} : Bool}
  {C.dec(s, C.enc(s, x)) == Some{x} : Maybe<&2, C.Meaning(s)>}


# A value check accepts can be read: a project's reader needs no
# "cannot happen" default.
law checked_decodes:
  for ~rule: Nat -> C.Raw -> Maybe<&2, C.Err>
  for +s: C.Schema
  for +r: C.Raw
  for hc: {C.conforms(~rule, s, r, None{}) == True{} : Bool}
  {Maybe.is_some(&2, C.Meaning(s), C.dec(s, r)) == True{} : Bool}


# What is written is accepted by the schema (with no rule: a rule is the
# project's, and not the encoder's to satisfy), as long as each enum value is
# one of its names and each bound a constructor states holds of the value. A
# bound is a subset of the encoding's own shape, so the encoder -- which
# writes the meaning unchanged -- can write a value outside one; the host that
# built that value is the one at fault, and check refuses it on the way back.
law encode_conforms:
  for +s: C.Schema
  for +x: C.Meaning(s)
  for hw: {C.wf(s) == True{} : Bool}
  for hn: {C.names_ok(s, x) == True{} : Bool}
  for hb: {C.bounds_ok(s, x) == True{} : Bool}
  {C.conforms(~C.no_rule, s, C.enc(s, x), None{}) == True{} : Bool}
