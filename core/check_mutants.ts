// bend-schema's mutants: for each law, a change to core.bend that makes it
// false, an instance of that law the change turns false -- its counterexample,
// at tiny literals -- and the def the proof must then fail in. The harness is
// bend-falsify's runMutants, which also runs the counterexample: it must check
// on the core and fail on the mutant, so the law is shown false and not merely
// asserted. test.sh runs this.
//
// The instance is named by `at`, which gives a value for each of the law's
// binders: the tool reads the law's statement out of LAWS.bend and builds the
// instance from it, so a row cannot state something that is not the law. One
// law shape `at` cannot express keeps a hand-written `counter` -- enum_admits,
// whose claim is the witness type OneOf(ns, x) rather than an equation; the
// run prints "(counter not tied to the law)" for it.
//
// Two decode_encode rows are instances the core's own premise leaves out: the
// mutants strengthen wf, so wf is false on the core there, check 1 is vacuous
// and the claim is checked against the mutant alone -- which is what makes
// them counterexamples rather than restatements of the premise. check_accurate's
// later_f_path mutant moves the path check reports, and defect reads the path
// it is given, so that one builds the path with the core's own later_f_path --
// what check reports, on each core. Both mutants still have to fail the proof,
// in `de` and `field_path_end`.

import { type Mutant, runMutants } from "bend-falsify";

const EXACT = "check finds nothing exactly when the value conforms";

const MUTANTS: Mutant[] = [
  { law: "tagged_meaning", section: "a tagged case reads the object without its tag",
    from: "      pick_bool(is_tag(k, n, x), conforms(~rule, cs, drop_key(k, x), None{}), conforms(~rule, rest, x, None{}))",
    to: "      pick_bool(is_tag(k, n, x), conforms(~rule, cs, x, None{}), conforms(~rule, rest, x, None{}))",
    at: { rule: "C.no_rule", k: "\"t\"", n: "\"a\"", cs: "C.SStrict{C.SEnd{}}", rest: "C.STagEnd{\"t\"}", r: "C.RKey{\"t\", C.RStr{\"a\"}, C.REnd{}}" },
    why: "a case sees the tag, so a strict case refuses a good value", failsIn: "LAWS.tagged_meaning" },
  { law: "tag_end_refuses", section: "the end of a tagged chain accepts nothing",
    from: "      False{}  # the end of a tagged chain: no case matched", to: "      True{}",
    at: { rule: "C.no_rule", k: "\"t\"", r: "C.REnd{}" },
    why: "the end of a chain accepts anything", failsIn: "LAWS.tag_end_refuses" },
  { law: "drop_first", section: "drop_key takes out the first key it names",
    from: "      pick_raw(String.eq(j, k), o, RKey{j, v, drop_key(k, o)})", to: "      pick_raw(String.eq(j, k), RKey{j, v, o}, RKey{j, v, drop_key(k, o)})",
    at: { k: "\"k\"", v: "C.RNum{1n}", o: "C.REnd{}" },
    why: "drop_key keeps the tag, so the case sees it", failsIn: "drop_self" },
  { law: "drop_other", section: "drop_key leaves every other key as it was",
    from: "      pick_raw(String.eq(j, k), o, RKey{j, v, drop_key(k, o)})", to: "      pick_raw(String.eq(j, k), o, drop_key(k, o))",
    at: { k: "\"k\"", j: "\"j\"", r: "C.RKey{\"j\", C.RNum{1n}, C.REnd{}}" },
    why: "drop_key drops every key up to the tag (drop_self, which the section uses through the decoder tools, sees it first)", failsIn: "drop_self" },
  { law: "strict_meaning", section: "a strict object has no other key",
    from: "      Bool.and(in_names(k, ns), no_extra(ns, o))", to: "      in_names(k, ns)",
    at: { rule: "C.no_rule", s: "C.SField{\"a\", C.SNat{}, C.SEnd{}}", r: "C.RKey{\"a\", C.RNum{1n}, C.RKey{\"x\", C.RNum{2n}, C.REnd{}}}" },
    why: "no_extra looks at the first key only, so a later unknown key conforms", failsIn: "strict_count" },
  { law: "check_exact", section: EXACT,
    from: "      pick_err(in_names(k, ns), extra_err(ns, o), Some{Err{AtKey{k} <> Nil{}, UnknownKey{}}})", to: "      pick_err(in_names(k, ns), None{}, Some{Err{AtKey{k} <> Nil{}, UnknownKey{}}})",
    at: { rule: "C.no_rule", s: "C.SStrict{C.SField{\"a\", C.SNat{}, C.SEnd{}}}", r: "C.RKey{\"a\", C.RNum{1n}, C.RKey{\"x\", C.RNum{2n}, C.REnd{}}}", prev: "None{}" },
    why: "check stops after the first known key, so a later unknown key passes check though it does not conform", failsIn: "extra_exact" },
  { law: "check_accurate", section: "what check reports is there", with: [EXACT],
    from: "      guard(Bool.and(has_key(k, r), Bool.not(in_names(k, ns))), Some{UnknownKey{}})", to: "      guard(Bool.not(in_names(k, ns)), Some{NotObject{}})",
    at: { rule: "C.no_rule", s: "C.SStrict{C.SField{\"a\", C.SNat{}, C.SEnd{}}}", r: "C.RKey{\"a\", C.RNum{1n}, C.RKey{\"x\", C.RNum{2n}, C.REnd{}}}", prev: "None{}", path: "C.AtKey{\"x\"} <> Nil{}", why: "C.UnknownKey{}" },
    why: "defect replays an unknown key as the wrong reason", failsIn: "extra_lift" },
  { law: "str_len_in_meaning", section: "a string's length is in its bounds",
    from: "  Bool.and(Nat.is_le(lo, String.length(x)), Nat.is_le(String.length(x), hi))",
    to: "  Bool.and(Nat.is_le(lo, String.length(x)), Nat.is_lt(String.length(x), hi))",
    at: { lo: "0n", hi: "1n", x: "\"a\"" },
    why: "a string exactly hi long is refused (str_len_ok is the test str_len_in reports, and what an SStrLen means)", failsIn: "LAWS.str_len_in_meaning" },
  { law: "nat_in_meaning", section: "a number is in its bounds",
    from: "  Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi))",
    to: "  Nat.is_le(lo, n)",
    at: { lo: "0n", hi: "1n", n: "2n" },
    why: "a number past hi is let through (num_ok is the test nat_in reports, and what an SNatIn means)", failsIn: "LAWS.nat_in_meaning" },
  { law: "sbool_meaning", section: "a boolean, and nothing else",
    from: "      True{}  # any boolean is a boolean, and nothing else is",
    to: "      False{}  # any boolean is a boolean, and nothing else is",
    at: { rule: "C.no_rule", r: "C.RBool{True{}}" },
    why: "a boolean is refused, so SBool accepts nothing", failsIn: "sbool_go" },
  { law: "snat_in_meaning", section: "a number's bounds, as a constructor",
    from: "      num_ok(lo, hi, n)",
    to: "      Nat.is_le(lo, n)",
    at: { rule: "C.no_rule", lo: "0n", hi: "1n", n: "2n" }, nth: 1,
    why: "SNatIn drops its upper bound, so a number past hi conforms (the first of the two lines that read num_ok: conforms', not bounds_ok's)", failsIn: "LAWS.snat_in_meaning" },
  { law: "sstr_len_meaning", section: "a string's length, as a constructor",
    from: "      Bool.and(conforms(~rule, s2, x, prev), len_ok(lo, hi, x))",
    to: "      Bool.and(conforms(~rule, s2, x, prev), True{})",
    at: { rule: "C.no_rule", lo: "1n", hi: "3n", s: "C.SStr{}", x: "\"\"" },
    why: "SStrLen drops its bounds, so a string of any length conforms", failsIn: "LAWS.sstr_len_meaning" },
  { law: "slist_len_meaning", section: "a list's element count, as a constructor",
    from: "      Bool.and(list_len_ok(lo, hi, r), conforms(~rule, s2, r, None{}))",
    to: "      conforms(~rule, s2, r, None{})",
    at: { rule: "C.no_rule", lo: "1n", hi: "3n", s: "C.SList{C.SNat{}}", r: "C.RNil{}" },
    why: "SListLen drops its bounds, so a list of any element count conforms", failsIn: "LAWS.slist_len_meaning" },
  { law: "soptional_meaning", section: "an optional field, as a constructor",
    from: "      Bool.or(is_missing(x), conforms(~rule, inner, x, None{}))",
    to: "      Bool.or(is_missing(x), True{})",
    at: { rule: "C.no_rule", i: "C.SNat{}", r: "C.RStr{\"a\"}" },
    why: "SOptional accepts every value that is not absent, whatever the inner says", failsIn: "LAWS.soptional_meaning" },
  { law: "check_exact", section: EXACT,
    from: "      here(missing_or(x, NotNat{}))", to: "      None{}",
    at: { rule: "C.no_rule", s: "C.SNat{}", r: "C.RStr{\"a\"}", prev: "None{}" }, nth: 1,
    why: "a value that is not a number passes check, though it does not conform (the first of the two lines: the SNat arm, not the SNatIn one)", failsIn: "exact" },
  { law: "check_accurate", section: "what check reports is there", with: [EXACT],
    from: "      AtField{1n+k, n} <> q", to: "      AtField{k, n} <> q",
    at: { rule: "C.no_rule", s: "C.SField{\"a\", C.SNat{}, C.SField{\"b\", C.SNat{}, C.SEnd{}}}", r: "C.RKey{\"a\", C.RNum{1n}, C.RKey{\"b\", C.RStr{\"x\"}, C.REnd{}}}", prev: "None{}", path: "C.later_f_path(C.AtField{0n, \"b\"} <> Nil{})", why: "C.NotNat{}" },
    why: "an error in a later field names the field before it", failsIn: "field_path_end" },
  { law: "check_exact", section: EXACT,
    from: "      first(check(~rule, s2, x, prev), rule(tag, x))", to: "      check(~rule, s2, x, prev)",
    at: { rule: "(t => r => C.nat_in(1n, 2n, r))", s: "C.SRule{C.SNat{}, 0n}", r: "C.RNum{0n}", prev: "None{}" },
    why: "check forgets the rule, so a value the rule refuses passes", failsIn: "exact" },
  { law: "check_accurate", section: "what check reports is there", with: [EXACT],
    from: "      pick_why(conforms(~rule, s2, x, prev), rule_defect(rule(tag, x), q), defect(~rule, s2, x, prev, q))", to: "      defect(~rule, s2, x, prev, q)",
    at: { rule: "(t => r => C.nat_in(1n, 2n, r))", s: "C.SRule{C.SNat{}, 0n}", r: "C.RNum{0n}", prev: "None{}", path: "Nil{}", why: "C.NotIn{1n, 2n}" },
    why: "defect never replays the rule, so a rule's error is not found there", failsIn: "acc" },
  { law: "too_large_reported", section: "a too big value is reported where it stands",
    from: "      TooLarge{}", to: "      NotNat{}",
    at: { rule: "C.no_rule", s: "C.SNat{}", prev: "None{}" },
    why: "a node the codec refused to build is reported as the schema kind's own reason, so a value too big to walk reads as a value of the wrong shape", failsIn: "too_large_go" },
  { law: "enum_accepts", section: "every listed name is accepted",
    from: "      Bool.or(String.eq(x, n), in_names(x, t))", to: "      Bool.and(String.eq(x, n), in_names(x, t))",
    at: { rule: "C.no_rule", pre: "\"a\" <> Nil{}", n: "\"b\"", post: "Nil{}" },
    why: "a name is found only if it is every name, so listed names are refused", failsIn: "names_has" },
  // enum_admits' claim is the witness type OneOf(ns, x), not an equation, and
  // `at` reads only a claim of the form {... : T}: it refuses this law by name.
  // So this one row keeps a counter of its own, and the run says so.
  { law: "enum_admits", section: "an accepted string is one of the names",
    from: "      Bool.or(String.eq(x, n), in_names(x, t))", to: "      Bool.or(True{}, in_names(x, t))",
    counter: "{C.conforms(~C.no_rule, C.SEnum{\"a\" <> Nil{}}, C.RStr{\"b\"}, None{}) == False{} : Bool}",
    why: "any string is accepted by a non-empty list", failsIn: "one_of" },
  { law: "variant_meaning", section: "a variant chain, read by counting",
    from: "      pick_bool(is_missing(lookup(name, RKey{k, v, o})), conforms(~rule, rest, RKey{k, v, o}, None{}), Bool.and(key_once(name, RKey{k, v, o}), Bool.and(conforms(~rule, vs, lookup(name, RKey{k, v, o}), None{}), none_present(rest, RKey{k, v, o}))))",
    to: "      pick_bool(is_missing(lookup(name, RKey{k, v, o})), conforms(~rule, rest, RKey{k, v, o}, None{}), Bool.and(key_once(name, RKey{k, v, o}), conforms(~rule, vs, lookup(name, RKey{k, v, o}), None{})))",
    at: { rule: "C.no_rule", s: "C.SVariant{\"a\", C.SNat{}, C.SVariant{\"b\", C.SNat{}, C.SVEnd{}}}", r: "C.RKey{\"a\", C.RNum{1n}, C.RKey{\"b\", C.RNum{2n}, C.REnd{}}}" },
    why: "conforms stops at the first key it finds, so two keys conform", failsIn: "vm_raw" },
  { law: "check_exact", section: EXACT,
    from: "      here(TooLong{})", to: "      None{}",
    at: { rule: "C.no_rule", s: "C.STuple{C.SNat{}, C.STEnd{}}", r: "C.RCons{C.RNum{1n}, C.RCons{C.RNum{2n}, C.RNil{}}}", prev: "None{}" },
    why: "check lets a tuple with an extra element through, though it does not conform", failsIn: "exact" },
  { law: "check_accurate", section: "what check reports is there", with: [EXACT],
    from: "      at_end(TooShort{}, q)", to: "      at_end(TooLong{}, q)",
    at: { rule: "C.no_rule", s: "C.STuple{C.SNat{}, C.STEnd{}}", r: "C.RNil{}", prev: "None{}", path: "Nil{}", why: "C.TooShort{}" },
    why: "defect replays a missing position as an extra one", failsIn: "acc" },
  { law: "tuple_meaning", section: "a tuple means its positions", with: ["a variant chain, read by counting"],
    from: "      Bool.and(conforms(~rule, ts, h, None{}), conforms(~rule, rest, t, None{}))", to: "      conforms(~rule, rest, t, None{})",
    at: { rule: "C.no_rule", ss: "C.SNat{} <> Nil{}", r: "C.RCons{C.RStr{\"a\"}, C.RNil{}}" },
    why: "conforms skips a tuple's position (check would have to agree, and then exact and accurate still hold)", failsIn: "tm" },
  { law: "decode_encode", section: "what was written reads back as itself",
    from: "      Bool.and(wf(fs), Bool.and(fresh_f(n, rest), wf(rest)))", to: "      Bool.and(wf(fs), wf(rest))",
    at: { s: "C.SField{\"a\", C.SNat{}, C.SField{\"a\", C.SNat{}, C.SEnd{}}}", x: "C.Both{0n, C.Both{1n, Unit{}}}" },
    why: "wf lets a record name a key twice, and the second field reads the first one's value", failsIn: "de" },
  { law: "decode_encode", section: "what was written reads back as itself",
    from: "      Bool.and(Bool.not(nullable(i)), wf(i))", to: "      wf(i)",
    at: { s: "C.SOpt{C.SOpt{C.SNat{}}}", x: "Some{None{}}" },
    why: "wf lets an optional value be optional, and Some{None} is written null, read back as None", failsIn: "de" },
  { law: "checked_decodes", section: "a value check accepts can be read",
    from: "      Some{x <> xs}", to: "      None{}",
    at: { rule: "C.no_rule", s: "C.SList{C.SNat{}}", r: "C.RCons{C.RNum{1n}, C.RNil{}}" },
    why: "dec refuses every non-empty list, though a list of conforming elements conforms", failsIn: "some_cons" },
  { law: "encode_conforms", section: "what is written is accepted", with: ["every listed name is accepted"],
    from: "      RBool{True{}}", to: "      RBool{False{}}",
    at: { s: "C.STrue{}", x: "Unit{}" },
    why: "enc writes false where the schema accepts only true (dec reads either, so the round trip holds)", failsIn: "ec" },
  { law: "check_exact", section: EXACT,
    from: "      Some{Err{AtField{0n, name} <> Nil{}, RepeatedKey{name}}}", to: "      None{}",
    at: { rule: "C.no_rule", s: "C.SField{\"a\", C.SNat{}, C.SEnd{}}", r: "C.RKey{\"a\", C.RNum{1n}, C.RKey{\"a\", C.RNum{2n}, C.REnd{}}}", prev: "None{}" },
    // With the report gone, the proof dies in the lemma that reads the report
    // as the test's absence, not in the test itself (the def this row used to
    // name, key_err_none, has never existed): a report that stops is not a
    // key_once that is wrong.
    why: "a key the schema reads twice is reported as nothing, so check passes a value that does not conform", failsIn: "none_key_err" },
];

runMutants(import.meta.dir, MUTANTS);
