// bend-schema's mutants: for each law, a change to core.bend that makes it
// false, an instance of that law the change turns false -- its counterexample,
// at tiny literals -- and the def the proof must then fail in. The harness is
// bend-falsify's runMutants, which also runs the counterexample: it must check
// on the core and fail on the mutant, so the law is shown false and not merely
// asserted. test.sh runs this.
//
// The instance is named by `at`, which gives a value for each of the law's
// binders: the tool reads the law's statement out of LAWS.bend and builds the
// instance from it, so a row cannot state something that is not the law. Two
// claim shapes `at` cannot express keep a hand-written `counter` instead --
// enum_admits, whose claim is the witness type OneOf(ns, x) rather than an
// equation, and unnamed_key_ignored's second and third readings, which are the
// 2nd and 3rd conjunct of a law whose claim `at` reads only the first of; the
// run prints "(counter not tied to the law)" for each.
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
  // at binds the approved payload conjunct of this two-equation law. The
  // installed falsifier reads only the first conjunct; the literal selector
  // separately checks both equations. Every encoder mutant loses a payload.
  ...[
    { to: "      RBad{}", v: 'C.JArray{[C.JObject{[C.JMember{"z", C.JNumber{C.NumberBits{2147483648, 1}}}]}]}', why: "JSON encoder drops a nested payload" },
    { to: "      RJson{JNull{}}", v: 'C.JObject{[C.JMember{"z", C.JArray{[C.JNull{}]}}, C.JMember{"a", C.JNumber{C.NumberBits{1072693248, 7}}}]}', why: "JSON encoder replaces an ordered payload with null" },
    { to: "      RBool{True{}}", v: "C.JNull{}", why: "JSON encoder uses the wrong Raw wrapper" },
    { to: "      +v = value\n      RJson{Bool.pick(Json, valid_json(v), v, JNull{})}", v: "C.JNumber{C.NumberBits{2146959360, 1}}", why: "JSON encoder repairs a NaN payload to null" },
    { to: "      +v = value\n      RJson{Bool.pick(Json, valid_json(v), v, JNull{})}", v: 'C.JObject{[C.JMember{"a", C.JNull{}}, C.JMember{"a", C.JBool{True{}}}]}', why: "JSON encoder repairs repeated names to null" },
  ].map(({ to, v, why }): Mutant => ({
    law: "json_enc_preserves", section: "json_enc_preserves",
    with: ["number_spec: finite binary64 exponent", "json_valid_spec"],
    from: "      RJson{value}", to, at: { v }, why,
    failsIn: "Laws.json_enc_preserves",
  })),
  // Acceptance counters bind both approved law parameters. Validation stays
  // unchanged; each proof failure must name the acceptance law itself.
  ...[
    { to: "      True{}", r: "C.RJson{C.JNumber{C.NumberBits{2146435072, 0}}}", rule: "C.no_rule", why: "SJson ignores validity and accepts infinity" },
    { to: "      True{}", r: 'C.RJson{C.JObject{[C.JMember{"a", C.JNull{}}, C.JMember{"a", C.JNull{}}]}}', rule: "C.no_rule", why: "SJson ignores validity and accepts repeated names" },
    { to: "      False{}", r: "C.RJson{C.JNull{}}", rule: "C.no_rule", why: "SJson rejects valid JSON null" },
    { to: "      valid_json(value)\n    case SJson{} RTooBig{}:\n      True{}", r: "C.RTooBig{}", rule: "C.no_rule", why: "SJson admits a size marker" },
    { to: "      valid_json(value)\n    case SJson{} RBool{b}:\n      True{}", r: "C.RBool{True{}}", rule: "C.no_rule", why: "SJson admits a non-RJson boolean" },
    { to: "      +v = value\n      Bool.and(valid_json(v), Maybe.is_none(&2, Err, rule(0n, RJson{v})))", r: "C.RJson{C.JNull{}}", rule: "(t => r => Some{C.Err{Nil{}, C.NotNat{}}})", why: "SJson wrongly invokes a refusing caller rule" },
  ].map(({ to, r, rule, why }): Mutant => ({
    law: "json_accept_exact", section: "json_accept_exact",
    with: ["number_spec: finite binary64 exponent", "json_valid_spec"],
    from: "      valid_json(value)", nth: 1, to,
    at: { rule, r }, why, failsIn: "Laws.json_accept_exact",
  })),
  // Decoder preservation is independent of validation. Every counter is the
  // approved law at r, and failure must be in that law's own universal proof.
  { law: "json_dec_preserves", section: "json_dec_preserves",
    from: "      Some{value}", to: "      None{}",
    at: { r: "C.RJson{C.JArray{[C.JObject{[C.JMember{\"z\", C.JNumber{C.NumberBits{2147483648, 1}}}]}]}}" },
    why: "JSON decoder drops a nonempty nested payload", failsIn: "Laws.json_dec_preserves" },
  { law: "json_dec_preserves", section: "json_dec_preserves",
    from: "      Some{value}", to: "      Some{JNull{}}",
    at: { r: "C.RJson{C.JObject{[C.JMember{\"z\", C.JArray{[C.JNull{}]}}, C.JMember{\"a\", C.JNumber{C.NumberBits{1072693248, 7}}}]}}" },
    why: "JSON decoder replaces a nested ordered payload with null", failsIn: "Laws.json_dec_preserves" },
  { law: "json_dec_preserves", section: "json_dec_preserves",
    from: "      Some{value}",
    to: "      +v = value\n      pick_m(Maybe<&2, Json>, valid_json(v), Some{v}, None{})",
    at: { r: "C.RJson{C.JNumber{C.NumberBits{2146959360, 1}}}" },
    why: "JSON decoder rechecks validity and discards a NaN payload", failsIn: "Laws.json_dec_preserves" },
  { law: "json_dec_preserves", section: "json_dec_preserves",
    from: "      Some{value}",
    to: "      +v = value\n      pick_m(Maybe<&2, Json>, valid_json(v), Some{v}, None{})",
    at: { r: "C.RJson{C.JObject{[C.JMember{\"a\", C.JNull{}}, C.JMember{\"a\", C.JBool{True{}}}]}}" },
    why: "JSON decoder rechecks validity and discards repeated names", failsIn: "Laws.json_dec_preserves" },
  { law: "json_dec_preserves", section: "json_dec_preserves",
    from: "      Some{value}",
    to: "      Some{value}\n    case SJson{} RTooBig{}:\n      Some{JNull{}}",
    at: { r: "C.RTooBig{}" },
    why: "JSON decoder treats a size marker as JSON null", failsIn: "Laws.json_dec_preserves" },
  { law: "json_dec_preserves", section: "json_dec_preserves",
    from: "      Some{value}",
    to: "      Some{value}\n    case SJson{} RBool{b}:\n      Some{JBool{b}}",
    at: { r: "C.RBool{True{}}" },
    why: "JSON decoder admits a non-RJson scalar", failsIn: "Laws.json_dec_preserves" },
  // Independent JSON paths: each counter is the approved law at v,
  // and each proof must fail inside the JSON law, not a shared helper.
  { law: "json_valid_spec", section: "json_valid_spec", with: ["number_spec: finite binary64 exponent"],
    from: "      Bool.and(valid_json(head), valid_json(JArray{tail}))",
    to: "      valid_json(head)",
    at: { v: "C.JArray{[C.JNull{}, C.JNumber{C.NumberBits{2146435072, 0}}]}" },
    why: "array validation skips its tail and accepts a later infinity", failsIn: "Laws.json_valid_spec" },
  { law: "json_valid_spec", section: "json_valid_spec", with: ["number_spec: finite binary64 exponent"],
    from: "      Bool.and(valid_json(val), Bool.and(Bool.not(key_in(key, tail)), valid_json(JObject{tail})))",
    to: "      Bool.and(Bool.not(key_in(key, tail)), valid_json(JObject{tail}))",
    at: { v: "C.JObject{[C.JMember{\"a\", C.JNumber{C.NumberBits{2146435072, 0}}}]}" },
    why: "object validation skips its value and accepts infinity", failsIn: "Laws.json_valid_spec" },
  { law: "json_valid_spec", section: "json_valid_spec", with: ["number_spec: finite binary64 exponent"],
    from: "      Bool.and(valid_json(val), Bool.and(Bool.not(key_in(key, tail)), valid_json(JObject{tail})))",
    to: "      Bool.and(valid_json(val), Bool.not(key_in(key, tail)))",
    at: { v: "C.JObject{[C.JMember{\"a\", C.JNull{}}, C.JMember{\"b\", C.JNumber{C.NumberBits{2146435072, 0}}}]}" },
    why: "object validation skips its tail and accepts a later infinity", failsIn: "Laws.json_valid_spec" },
  { law: "json_valid_spec", section: "json_valid_spec", with: ["number_spec: finite binary64 exponent"],
    from: "      Bool.and(valid_json(val), Bool.and(Bool.not(key_in(key, tail)), valid_json(JObject{tail})))",
    to: "      Bool.and(valid_json(val), valid_json(JObject{tail}))",
    at: { v: "C.JObject{[C.JMember{\"a\", C.JNull{}}, C.JMember{\"a\", C.JNull{}}]}" },
    why: "object validation accepts repeated names", failsIn: "Laws.json_valid_spec" },
  // number_spec is a specification def, not a law block in LAWS.bend.
  // These counters expand its frozen comparison; the harness reports that
  // they are not tied to a law. The universal helper is checked in its own
  // section, and each mutation must fail in number_spec itself.
  { law: "number_spec", section: "number_spec: finite binary64 exponent",
    from: "      Bool.not(U32.is_eq(U32.and(hi, 2146435072), 2146435072))",
    to: "      True{}",
    counter: "{C.finite_number(C.NumberBits{2146435072, 0}) == Cmp.is_lt(U32.cmp(U32.and(2146435072, 2147483647), 2146435072)) : Bool}",
    why: "finite_number always accepts, including positive infinity", failsIn: "number_spec" },
  { law: "number_spec", section: "number_spec: finite binary64 exponent",
    from: "      Bool.not(U32.is_eq(U32.and(hi, 2146435072), 2146435072))",
    to: "      Bool.not(U32.is_eq(U32.and(hi, 2145386496), 2145386496))",
    counter: "{C.finite_number(C.NumberBits{2145386496, 0}) == Cmp.is_lt(U32.cmp(U32.and(2145386496, 2147483647), 2146435072)) : Bool}",
    why: "finite_number tests one fewer exponent bit, refusing a finite exponent of 0x7FE", failsIn: "number_spec" },
  { law: "number_spec", section: "number_spec: finite binary64 exponent",
    from: "      Bool.not(U32.is_eq(U32.and(hi, 2146435072), 2146435072))",
    to: "      Bool.not(U32.is_eq(U32.and(hi, 2147483648), 2147483648))",
    counter: "{C.finite_number(C.NumberBits{2147483648, 0}) == Cmp.is_lt(U32.cmp(U32.and(2147483648, 2147483647), 2146435072)) : Bool}",
    why: "finite_number tests the sign bit, refusing negative zero", failsIn: "number_spec" },
  { law: "tagged_meaning", section: "a tagged case reads the object without its tag",
    from: "      pick_bool(is_tag(k, n, x), Bool.and(key_once(k, x), conforms(~rule, cs, drop_key(k, x), None{})), conforms(~rule, rest, x, None{}))",
    to: "      pick_bool(is_tag(k, n, x), Bool.and(key_once(k, x), conforms(~rule, cs, x, None{})), conforms(~rule, rest, x, None{}))",
    at: { rule: "C.no_rule", k: "\"t\"", n: "\"a\"", cs: "C.SStrict{C.SEnd{}}", rest: "C.STagEnd{\"t\"}", r: "C.RKey{\"t\", C.RStr{\"a\"}, C.REnd{}}" },
    why: "a case sees the tag, so a strict case refuses a good value", failsIn: "Laws.tagged_meaning" },
  { law: "tag_end_refuses", section: "the end of a tagged chain accepts nothing",
    from: "      False{}  # the end of a tagged chain: no case matched", to: "      True{}",
    at: { rule: "C.no_rule", k: "\"t\"", r: "C.REnd{}" },
    why: "the end of a chain accepts anything", failsIn: "Laws.tag_end_refuses" },
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
    why: "a string exactly hi long is refused (str_len_ok is the test str_len_in reports, and what an SStrLen means)", failsIn: "Laws.str_len_in_meaning" },
  { law: "nat_in_meaning", section: "a number is in its bounds",
    from: "  Bool.and(Nat.is_le(lo, n), Nat.is_le(n, hi))",
    to: "  Nat.is_le(lo, n)",
    at: { lo: "0n", hi: "1n", n: "2n" },
    why: "a number past hi is let through (num_ok is the test nat_in reports, and what an SNatIn means)", failsIn: "Laws.nat_in_meaning" },
  { law: "sbool_meaning", section: "a boolean, and nothing else",
    from: "      True{}  # any boolean is a boolean, and nothing else is",
    to: "      False{}  # any boolean is a boolean, and nothing else is",
    at: { rule: "C.no_rule", r: "C.RBool{True{}}" },
    why: "a boolean is refused, so SBool accepts nothing", failsIn: "sbool_go" },
  { law: "snat_in_meaning", section: "a number's bounds, as a constructor",
    from: "      num_ok(lo, hi, n)",
    to: "      Nat.is_le(lo, n)",
    at: { rule: "C.no_rule", lo: "0n", hi: "1n", n: "2n" }, nth: 1,
    why: "SNatIn drops its upper bound, so a number past hi conforms (the first of the two lines that read num_ok: conforms', not bounds_ok's)", failsIn: "Laws.snat_in_meaning" },
  { law: "sstr_len_meaning", section: "a string's length, as a constructor",
    from: "      Bool.and(conforms(~rule, s2, x, prev), len_ok(lo, hi, x))",
    to: "      Bool.and(conforms(~rule, s2, x, prev), True{})",
    at: { rule: "C.no_rule", lo: "1n", hi: "3n", s: "C.SStr{}", x: "\"\"" },
    why: "SStrLen drops its bounds, so a string of any length conforms", failsIn: "Laws.sstr_len_meaning" },
  { law: "slist_len_meaning", section: "a list's element count, as a constructor",
    from: "      Bool.and(list_len_ok(lo, hi, r), conforms(~rule, s2, r, None{}))",
    to: "      conforms(~rule, s2, r, None{})",
    at: { rule: "C.no_rule", lo: "1n", hi: "3n", s: "C.SList{C.SNat{}}", r: "C.RNil{}" },
    why: "SListLen drops its bounds, so a list of any element count conforms", failsIn: "Laws.slist_len_meaning" },
  { law: "soptional_meaning", section: "an optional field, as a constructor",
    from: "      Bool.or(is_missing(x), conforms(~rule, inner, x, None{}))",
    to: "      Bool.or(is_missing(x), True{})",
    at: { rule: "C.no_rule", i: "C.SNat{}", r: "C.RStr{\"a\"}" },
    why: "SOptional accepts every value that is not absent, whatever the inner says", failsIn: "Laws.soptional_meaning" },
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
  // The D3 law is a conjunction of three readings: an unnamed key stands
  // before the keys the schema reads, after them, and before a variant key.
  // One row per reading, because the three break independently and a single
  // row's failure would not say which one is load-bearing.
  //
  // `at` can only state the FIRST reading. The tool reads a law's claim as its
  // first `{...}`, and this law's claim is a three-way conjunction, so an `at`
  // instance here is the reading-1 equation and no other -- the two rows for
  // readings 2 and 3 carry a `counter` instead, the tool's own escape for a
  // claim shape `at` cannot express, and its line says the counter is not tied
  // to the law. The cost is real and is the reason the text of each counter is
  // the law's own conjunct, copied character for character: nothing checks
  // that it still is, so an edit to LAWS.bend's second or third reading must
  // be carried here by hand.
  //
  // Each mutation was measured against one reading at a time (a scratch core
  // per mutation, one def per reading): under the mutation its own reading's
  // equation goes false and the other two still check.
  //
  // Reading 1 -- a key standing BEFORE the field the schema reads. conforms
  // reads the object's first key as the field's name.
  { law: "unnamed_key_ignored", section: "unnamed_key_ignored",
    from: "      Bool.and(key_once(name, RKey{k, v, o}), Bool.and(conforms(~rule, fs, lookup(name, RKey{k, v, o}), None{}), conforms(~rule, rest, RKey{k, v, o}, None{})))",
    to: "      Bool.and(String.eq(k, name), Bool.and(key_once(name, RKey{k, v, o}), Bool.and(conforms(~rule, fs, lookup(name, RKey{k, v, o}), None{}), conforms(~rule, rest, RKey{k, v, o}, None{}))))",
    at: {},
    why: "conforms reads an object's first key as the field's name, so a key the schema does not name changes the answer when it stands before the one the schema reads",
    failsIn: "Laws.unnamed_key_ignored" },
  // Reading 2 -- a key standing AFTER the field the schema reads. Nothing in
  // conforms refuses a later key: SEnd ignores whatever keys are left over, so
  // the two sides of the equation reach the same True and the unnamed key is
  // unobservable. The mutation is what makes it reachable-and-refused: a key
  // counts as read once the field's key has gone by, so key_once refuses every
  // key standing after it -- which is what "and nothing after it" would mean.
  // The "z" after "a" then flips the left side to False while the value with
  // no "z" stays True.
  { law: "unnamed_key_ignored", section: "unnamed_key_ignored",
    from: "      Bool.and(Bool.not(Bool.and(b, String.eq(k, name))), key_once_at(o, Bool.or(b, String.eq(k, name)), name))",
    to: "      Bool.and(Bool.not(b), key_once_at(o, Bool.or(b, String.eq(k, name)), name))",
    counter: "{C.conforms(~C.no_rule, C.SField{\"a\", C.SNat{}, C.SEnd{}}, C.RKey{\"a\", C.RNum{1n}, C.RKey{\"z\", C.RNum{9n}, C.REnd{}}}, None{}) == C.conforms(~C.no_rule, C.SField{\"a\", C.SNat{}, C.SEnd{}}, C.RKey{\"a\", C.RNum{1n}, C.REnd{}}, None{}) : Bool}",
    why: "key_once refuses every key that stands after the one the schema reads, so a key the schema does not name changes the answer when it stands after it",
    failsIn: "Laws.unnamed_key_ignored" },
  // Reading 3 -- a key standing BEFORE a variant key. The variant's key is
  // looked up wherever it stands, so a key in front of it is skipped and the
  // same two branches are taken as without it. The mutation asks instead
  // whether the object's FIRST key is the variant's: an unnamed key in front
  // of the variant key now hides it, the chain moves on to SVEnd, and SVEnd
  // conforms to nothing.
  { law: "unnamed_key_ignored", section: "unnamed_key_ignored",
    from: "      pick_bool(is_missing(lookup(name, RKey{k, v, o})), conforms(~rule, rest, RKey{k, v, o}, None{}), Bool.and(key_once(name, RKey{k, v, o}), Bool.and(conforms(~rule, vs, lookup(name, RKey{k, v, o}), None{}), none_present(rest, RKey{k, v, o}))))",
    to: "      pick_bool(Bool.not(String.eq(k, name)), conforms(~rule, rest, RKey{k, v, o}, None{}), Bool.and(key_once(name, RKey{k, v, o}), Bool.and(conforms(~rule, vs, lookup(name, RKey{k, v, o}), None{}), none_present(rest, RKey{k, v, o}))))",
    counter: "{C.conforms(~C.no_rule, C.SVariant{\"a\", C.SNat{}, C.SVEnd{}}, C.RKey{\"z\", C.RNum{9n}, C.RKey{\"a\", C.RNum{1n}, C.REnd{}}}, None{}) == C.conforms(~C.no_rule, C.SVariant{\"a\", C.SNat{}, C.SVEnd{}}, C.RKey{\"a\", C.RNum{1n}, C.REnd{}}, None{}) : Bool}",
    why: "a variant key counts only where it stands first, so a key the schema does not name changes the answer when it stands before the variant key",
    failsIn: "Laws.unnamed_key_ignored" },
  // The tag key's own test. The law is a Refused -- a conjunction of two
  // claims -- so the instance is a counter: the half that stops holding is the
  // one this counter states, and the def the proof must fail in is the law's
  // own, whose two halves are decided by evaluation and nothing else. The
  // mutation drops the test, and the case's own schema (SEnd{}) accepts the
  // object the tag key was taken out of, so the value the law refuses is
  // accepted; with the test in place the same reading is False.
  { law: "repeated_tag_refused", section: "repeated_tag_refused",
    from: "      pick_bool(is_tag(k, n, x), Bool.and(key_once(k, x), conforms(~rule, cs, drop_key(k, x), None{})), conforms(~rule, rest, x, None{}))",
    to: "      pick_bool(is_tag(k, n, x), conforms(~rule, cs, drop_key(k, x), None{}), conforms(~rule, rest, x, None{}))",
    counter: "{C.conforms(~C.no_rule, C.STagged{\"t\", \"a\", C.SEnd{}, C.STagEnd{\"t\"}}, C.RKey{\"t\", C.RStr{\"a\"}, C.RKey{\"t\", C.RStr{\"a\"}, C.REnd{}}}, None{}) == False{} : Bool}",
    why: "the tag key's own test is gone, so a value holding the tag key twice conforms",
    failsIn: "Laws.repeated_tag_refused" },
  // ---- SInt and SIntIn ----
  //
  // int_le_complete and int_le_sound pin int_le from the two sides: the walk up
  // from a never leaves it, and nothing reaches a number below it. Both are
  // stated for the pair (a, b); int_le_sound's claim is the witness type
  // Reaches(a, b), which `at` cannot read, so its rows keep a counter of their
  // own (the literal int_le the law forbids), and the run says so. Every row
  // fails in a def of the law's own section, not in a shared lemma.
  { law: "int_le_complete", section: "int_le_complete",
    from: "      True{}", to: "      False{}", nth: 10,
    at: { k: "1n", a: "C.INeg{0n}" },
    why: "int_le puts a negative above no non-negative, so one step from -1 reaches 0 and 0 is not at least -1", failsIn: "int_le_succ" },
  { law: "int_le_complete", section: "int_le_complete",
    from: "      Nat.is_le(n, m)", to: "      Nat.is_lt(n, m)",
    at: { k: "0n", a: "C.INeg{0n}" },
    why: "between negatives the comparison is strict, so -1 is not at least -1", failsIn: "int_le_refl" },
  { law: "int_le_complete", section: "int_le_complete",
    from: "      Nat.is_le(n, m)", to: "      Nat.is_le(m, n)",
    at: { k: "1n", a: "C.INeg{1n}" },
    why: "between negatives the offsets are compared the wrong way round, so one step up from -2 (to -1) is below -2", failsIn: "int_le_succ" },
  { law: "int_le_complete", section: "int_le_complete",
    from: "      Nat.is_le(m, n)", to: "      Nat.is_lt(m, n)",
    at: { k: "0n", a: "C.IPos{0n}" },
    why: "between non-negatives the comparison is strict, so 0 is not at least 0", failsIn: "int_le_refl" },
  { law: "int_le_sound", section: "int_le_sound",
    from: "      False{}", to: "      True{}", nth: 6,
    counter: "{C.int_le(C.IPos{0n}, C.INeg{0n}) == False{} : Bool}",
    why: "int_le puts a non-negative below a negative, which no number of steps up reaches", failsIn: "Laws.int_le_sound" },
  { law: "int_le_sound", section: "int_le_sound",
    from: "      False{}", to: "      Nat.is_le(m, n)", nth: 6,
    counter: "{C.int_le(C.IPos{0n}, C.INeg{5n}) == False{} : Bool}",
    why: "int_le compares a non-negative with a negative by their offsets, as if both had the same sign", failsIn: "Laws.int_le_sound" },
  { law: "int_le_sound", section: "int_le_sound",
    from: "      Nat.is_le(n, m)", to: "      Nat.is_le(m, n)",
    counter: "{C.int_le(C.INeg{0n}, C.INeg{1n}) == False{} : Bool}",
    why: "between negatives the offsets are compared the wrong way round, so -1 is at most -2 and is not reached from it by steps up", failsIn: "Laws.int_le_sound" },
  { law: "int_le_sound", section: "int_le_sound",
    from: "      Nat.is_le(m, n)", to: "      Nat.is_le(n, m)",
    counter: "{C.int_le(C.IPos{1n}, C.IPos{0n}) == False{} : Bool}",
    why: "between non-negatives the comparison is swapped, so 1 is at most 0 and 0 is not reached from 1 by steps up", failsIn: "Laws.int_le_sound" },
  // sint_meaning: SInt accepts RNum and RNeg and nothing else.
  { law: "sint_meaning", section: "sint_meaning",
    from: "      True{}", to: "      False{}", nth: 19,
    at: { rule: "C.no_rule", r: "C.RNeg{0n}" },
    why: "SInt refuses a negative number", failsIn: "sint_go" },
  { law: "sint_meaning", section: "sint_meaning",
    from: "      True{}", to: "      False{}", nth: 18,
    at: { rule: "C.no_rule", r: "C.RNum{0n}" },
    why: "SInt refuses a non-negative number", failsIn: "sint_go" },
  { law: "sint_meaning", section: "sint_meaning",
    from: "      True{}", to: "      True{}\n    case SInt{} RBad{}:\n      True{}", nth: 19,
    at: { rule: "C.no_rule", r: "C.RBad{}" },
    why: "SInt admits a number the codec could not hold (RBad: a fraction or past the bound)", failsIn: "sint_go" },
  { law: "sint_meaning", section: "sint_meaning",
    from: "      True{}", to: "      True{}\n    case SInt{} RTooBig{}:\n      True{}", nth: 19,
    at: { rule: "C.no_rule", r: "C.RTooBig{}" },
    why: "SInt admits a size marker", failsIn: "sint_go" },
  { law: "sint_meaning", section: "sint_meaning",
    from: "      True{}", to: "      True{}\n    case SInt{} RBool{b}:\n      True{}", nth: 19,
    at: { rule: "C.no_rule", r: "C.RBool{True{}}" },
    why: "SInt admits a boolean", failsIn: "sint_go" },
  // sint_in_meaning: SIntIn{lo, hi} accepts an integer from lo to hi, both
  // ends included. int_ok is what conforms reads; the law's right side reads
  // int_le itself, so a bound off at one end is the two sides disagreeing.
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "  Bool.and(int_le(lo, i), int_le(i, hi))", to: "  Bool.and(int_le(lo, i), Bool.not(int_le(hi, i)))",
    at: { rule: "C.no_rule", lo: "C.IPos{0n}", hi: "C.IPos{0n}", r: "C.RNum{0n}" },
    why: "the upper bound is excluded, so hi itself is refused", failsIn: "sint_in_go" },
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "  Bool.and(int_le(lo, i), int_le(i, hi))", to: "  Bool.and(Bool.not(int_le(i, lo)), int_le(i, hi))",
    at: { rule: "C.no_rule", lo: "C.INeg{0n}", hi: "C.IPos{2n}", r: "C.RNeg{0n}" },
    why: "the lower bound is excluded, so lo itself is refused", failsIn: "sint_in_go" },
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "  Bool.and(int_le(lo, i), int_le(i, hi))", to: "  int_le(lo, i)",
    at: { rule: "C.no_rule", lo: "C.INeg{2n}", hi: "C.INeg{0n}", r: "C.RNum{3n}" },
    why: "the upper bound is not read, so a number past hi is accepted", failsIn: "sint_in_go" },
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "  Bool.and(int_le(lo, i), int_le(i, hi))", to: "  int_le(i, hi)",
    at: { rule: "C.no_rule", lo: "C.IPos{0n}", hi: "C.IPos{2n}", r: "C.RNeg{0n}" },
    why: "the lower bound is not read, so a number below lo is accepted", failsIn: "sint_in_go" },
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "      int_ok(lo, hi, INeg{n})", to: "      int_ok(lo, hi, INeg{1n+n})",
    at: { rule: "C.no_rule", lo: "C.INeg{0n}", hi: "C.INeg{0n}", r: "C.RNeg{0n}" },
    why: "a negative number is read one further down than it is: RNeg{0n} is -2, not -1", failsIn: "sint_in_go" },
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "      int_ok(lo, hi, INeg{n})", to: "      int_ok(lo, hi, IPos{n})",
    at: { rule: "C.no_rule", lo: "C.INeg{2n}", hi: "C.INeg{0n}", r: "C.RNeg{1n}" },
    why: "a negative number is read as the non-negative with the same offset", failsIn: "sint_in_go" },
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "      int_ok(lo, hi, IPos{n})", to: "      int_ok(lo, hi, INeg{n})",
    at: { rule: "C.no_rule", lo: "C.IPos{0n}", hi: "C.IPos{0n}", r: "C.RNum{0n}" },
    why: "a non-negative number is read as the negative with the same offset", failsIn: "sint_in_go" },
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "      int_ok(lo, hi, IPos{n})", to: "      int_ok(hi, lo, IPos{n})",
    at: { rule: "C.no_rule", lo: "C.IPos{0n}", hi: "C.IPos{2n}", r: "C.RNum{1n}" },
    why: "the bounds are swapped, so a range with lo below hi is empty", failsIn: "sint_in_go" },
  { law: "sint_in_meaning", section: "sint_in_meaning",
    from: "      int_ok(lo, hi, INeg{n})", to: "      int_ok(lo, hi, INeg{n})\n    case SIntIn{+lo, +hi} RBad{}:\n      True{}",
    at: { rule: "C.no_rule", lo: "C.INeg{2n}", hi: "C.IPos{2n}", r: "C.RBad{}" },
    why: "SIntIn admits a number the codec could not hold", failsIn: "sint_in_go" },
  // The constructors in the laws that were already proved. enc and dec are a
  // round trip, so an offset wrong on both sides is invisible to it; the rows
  // below put it wrong on one side, which decode_encode and encode_conforms see.
  { law: "decode_encode", section: "what was written reads back as itself",
    from: "      RNeg{n}", to: "      RNeg{1n+n}",
    at: { s: "C.SInt{}", x: "C.INeg{0n}" },
    why: "enc writes -(n+1) one further down (RNeg{n+1}), so -1 is read back as -2", failsIn: "de" },
  { law: "decode_encode", section: "what was written reads back as itself",
    from: "      RNeg{n}", to: "      RNum{n}",
    at: { s: "C.SInt{}", x: "C.INeg{0n}" },
    why: "enc writes a negative as the non-negative with the same offset, so -1 is read back as 0", failsIn: "de" },
  { law: "decode_encode", section: "what was written reads back as itself",
    from: "      Some{INeg{n}}", to: "      Some{INeg{1n+n}}", nth: 1,
    at: { s: "C.SInt{}", x: "C.INeg{0n}" },
    why: "dec reads RNeg{n} as -(n+2), so what enc wrote as -1 is read back as -2", failsIn: "de" },
  { law: "decode_encode", section: "what was written reads back as itself",
    from: "      Some{INeg{n}}", to: "      Some{IPos{n}}", nth: 2,
    at: { s: "C.SIntIn{C.INeg{2n}, C.IPos{2n}}", x: "C.INeg{0n}" },
    why: "dec reads RNeg{n} under SIntIn as the non-negative n", failsIn: "de" },
  { law: "encode_conforms", section: "what is written is accepted", with: ["every listed name is accepted"],
    from: "      RNeg{n}", to: "      RNum{n}",
    at: { s: "C.SIntIn{C.INeg{2n}, C.INeg{0n}}", x: "C.INeg{0n}" },
    why: "enc writes -1 as 0, which the bounds [-3, -1] refuse (dec reads either, so the round trip holds only for SInt)", failsIn: "ec" },
  // A shift that enc and dec share is invisible to decode_encode (measured on
  // a scratch core with enc writing RNeg{n+1} and dec reading it back as
  // INeg{n}: the round trip holds at -1 and -4). What pins the offset is that
  // the bound reads RNeg{n} as -(n+1): encode_conforms, on a bounded schema.
  { law: "encode_conforms", section: "what is written is accepted", with: ["every listed name is accepted"],
    from: "      RNeg{n}", to: "      RNeg{1n+n}",
    at: { s: "C.SIntIn{C.INeg{0n}, C.INeg{0n}}", x: "C.INeg{0n}" },
    why: "enc writes -(n+1) as RNeg{n+1}, one further down, which the bounds [-1, -1] refuse", failsIn: "ec" },
  { law: "checked_decodes", section: "a value check accepts can be read",
    from: "      Some{INeg{n}}", to: "      None{}", nth: 1,
    at: { rule: "C.no_rule", s: "C.SInt{}", r: "C.RNeg{0n}" },
    why: "dec refuses a negative number that SInt accepts", failsIn: "cd" },
  { law: "check_exact", section: EXACT,
    from: "      in_err(int_ok(lo, hi, INeg{n}), IntNotIn{lo, hi})", to: "      None{}",
    at: { rule: "C.no_rule", s: "C.SIntIn{C.INeg{2n}, C.INeg{0n}}", r: "C.RNeg{5n}", prev: "None{}" },
    why: "check lets a negative number past the bounds through, though it does not conform", failsIn: "exact" },
  { law: "check_exact", section: EXACT,
    from: "      in_err(int_ok(lo, hi, IPos{n}), IntNotIn{lo, hi})", to: "      None{}",
    at: { rule: "C.no_rule", s: "C.SIntIn{C.INeg{2n}, C.INeg{0n}}", r: "C.RNum{0n}", prev: "None{}" },
    why: "check lets a non-negative number past the bounds through, though it does not conform", failsIn: "exact" },
  { law: "check_exact", section: EXACT,
    from: "      here(missing_or(x, NotInt{}))", to: "      None{}", nth: 1,
    at: { rule: "C.no_rule", s: "C.SInt{}", r: "C.RBad{}", prev: "None{}" },
    why: "a value that is not an integer passes check at SInt, though it does not conform (the first of the two lines: the SInt arm, not the SIntIn one)", failsIn: "exact" },
  { law: "check_accurate", section: "what check reports is there", with: [EXACT],
    from: "      guard(Bool.not(int_ok(lo, hi, INeg{n})), Some{IntNotIn{lo, hi}})", to: "      guard(Bool.not(int_ok(lo, hi, INeg{n})), Some{NotInt{}})",
    at: { rule: "C.no_rule", s: "C.SIntIn{C.INeg{2n}, C.INeg{0n}}", r: "C.RNeg{5n}", prev: "None{}", path: "Nil{}", why: "C.IntNotIn{C.INeg{2n}, C.INeg{0n}}" },
    why: "defect replays an out-of-bounds negative as the wrong reason", failsIn: "acc_int_in_neg" },
  { law: "check_accurate", section: "what check reports is there", with: [EXACT],
    from: "      Some{missing_or(x, NotInt{})}",
    to: "      Some{missing_or(x, NotNat{})}", nth: 1,
    at: { rule: "C.no_rule", s: "C.SInt{}", r: "C.RStr{\"x\"}", prev: "None{}", path: "Nil{}", why: "C.NotInt{}" },
    why: "defect replays a value that is not an integer as not a number", failsIn: "acc" },
  // SIntIn's copies of the lines above: the same mutation at the second
  // occurrence, which the SInt rows leave unread.
  { law: "check_exact", section: EXACT,
    from: "      here(missing_or(x, NotInt{}))", to: "      None{}", nth: 2,
    at: { rule: "C.no_rule", s: "C.SIntIn{C.INeg{2n}, C.IPos{2n}}", r: "C.RBad{}", prev: "None{}" },
    why: "a value that is not an integer passes check at SIntIn, though it does not conform (the SIntIn arm, the second of the two lines)", failsIn: "exact" },
  { law: "check_accurate", section: "what check reports is there", with: [EXACT],
    from: "      Some{missing_or(x, NotInt{})}",
    to: "      Some{missing_or(x, NotNat{})}", nth: 2,
    at: { rule: "C.no_rule", s: "C.SIntIn{C.INeg{2n}, C.IPos{2n}}", r: "C.RStr{\"x\"}", prev: "None{}", path: "Nil{}", why: "C.NotInt{}" },
    why: "defect replays a value that is not an integer as not a number at SIntIn (int_in_defect's line, the second of the two)", failsIn: "acc" },
  { law: "check_accurate", section: "what check reports is there", with: [EXACT],
    from: "      guard(Bool.not(int_ok(lo, hi, IPos{n})), Some{IntNotIn{lo, hi}})", to: "      guard(Bool.not(int_ok(lo, hi, IPos{n})), Some{NotInt{}})",
    at: { rule: "C.no_rule", s: "C.SIntIn{C.INeg{2n}, C.INeg{0n}}", r: "C.RNum{3n}", prev: "None{}", path: "Nil{}", why: "C.IntNotIn{C.INeg{2n}, C.INeg{0n}}" },
    why: "defect replays an out-of-bounds non-negative as the wrong reason", failsIn: "acc_int_in_num" },
  { law: "encode_conforms", section: "what is written is accepted", with: ["every listed name is accepted"],
    from: "      int_ok(lo, hi, i)", to: "      True{}",
    at: { s: "C.SIntIn{C.INeg{2n}, C.INeg{0n}}", x: "C.INeg{5n}" },
    why: "bounds_ok drops SIntIn's bound, so a value outside it passes the premise and is written, and check refuses it", failsIn: "ec" },
];

runMutants(import.meta.dir, MUTANTS);
