// Literal instances of the laws, for the falsifier (bend-falsify). One LAW
// value checks one law: LAW=exact|accurate|enum_accepts|enum_admits|variant|
// strict|tuple|tagged|too_large|rules|sbool_meaning|snat_in_meaning|
// sstr_len_meaning|soptional_meaning|slist_len_meaning|unnamed_key|number_spec|json_valid_spec|json_dec_preserves|json_accept_exact|json_enc_preserves|
// int_le_complete|int_le_sound|sint_meaning|sint_in_meaning|kinds_table|kind_sound|union_exact|union_disjoint.
//   bunx bend-falsify spec.ts
// CORE=<path as C> and HELPERS=<file> point it at a mutated copy (the control).
// The two generic laws on small schemas and values built around them, with
// no rules and with a rule that dispatches on the tag.
type R = string; // a Bend Raw literal
const N = (n: number) => `C.RNum{${n}n}`, NUL = "C.RNull{}", BAD = "C.RBad{}", STR = 'C.RStr{"x"}';
const list = (xs: R[]) => xs.reduceRight((t, h) => `C.RCons{${h}, ${t}}`, "C.RNil{}");
const obj = (kv: [string, R][]) => kv.reduceRight((t, [k, v]) => `C.RKey{"${k}", ${v}, ${t}}`, "C.REnd{}");
const S = {
  nat: "C.SNat{}", str: "C.SStr{}", opt: "C.SOpt{C.SNat{}}", lnat: "C.SList{C.SNat{}}", lopt: "C.SList{C.SOpt{C.SNat{}}}",
  rec: 'C.SField{"a", C.SNat{}, C.SField{"b", C.SOpt{C.SNat{}}, C.SEnd{}}}',
};
const lrec = `C.SList{${S.rec}}`;
const BIG = "C.RTooBig{}"; // a node the codec refused to build
const scalars = [N(0), N(3), NUL, BAD, BIG, STR, "C.RMissing{}", list([]), obj([])];
const recs = [obj([["a", N(1)], ["b", NUL]]), obj([["b", N(2)], ["a", N(0)]]), obj([["a", N(1)]]), obj([["a", NUL], ["b", N(1)]]),
  obj([["a", N(1)], ["b", BAD], ["z", N(9)]]), obj([["z", N(1)], ["a", N(5)], ["b", N(5)]]), N(1), list([])];
const pairs: [string, R][] = [];
for (const r of scalars) for (const s of [S.nat, S.str, S.opt, S.lnat, S.rec]) pairs.push([s, r]);
for (const xs of [[], [N(1)], [N(1), NUL], [NUL, N(2), BAD], [N(1), N(2), N(3)], [STR]]) for (const s of [S.lnat, S.lopt]) pairs.push([s, list(xs)]);
for (const r of recs) { pairs.push([S.rec, r]); pairs.push([lrec, list([r, recs[0]])]); pairs.push([lrec, list([recs[0], r])]); }
pairs.push([S.lnat, `C.RCons{${N(1)}, ${NUL}}`]); // improper tail
// the choices: true, one of some names, one of some keys
const TRUE = "C.RBool{True{}}", FALSE = "C.RBool{False{}}";
const enumS = 'C.SEnum{["allow", "deny"]}';
const target = 'C.SVariant{"any", C.STrue{}, C.SVariant{"only", C.SNat{}, C.SVEnd{}}}';
const rule = `C.SField{"role", ${target}, C.SField{"effect", ${enumS}, C.SEnd{}}}`;
const choiceVals: R[] = [TRUE, FALSE, 'C.RStr{"allow"}', 'C.RStr{"deny"}', 'C.RStr{"Allow"}', N(1), NUL, obj([]),
  obj([["any", TRUE]]), obj([["any", FALSE]]), obj([["only", N(3)]]), obj([["only", 'C.RStr{"3"}']]), obj([["any", TRUE], ["only", N(3)]]),
  obj([["only", N(3)], ["any", TRUE]]), obj([["x", N(1)]]), obj([["x", N(1)], ["only", N(2)]]), obj([["any", NUL]])];
for (const r of choiceVals) for (const s of ["C.STrue{}", enumS, target, "C.SVEnd{}", 'C.SVariant{"any", C.STrue{}, C.SVEnd{}}']) pairs.push([s, r]);
for (const role of choiceVals.slice(8)) for (const eff of ['C.RStr{"allow"}', 'C.RStr{"nope"}', TRUE]) pairs.push([rule, obj([["role", role], ["effect", eff]])]);
// A key the schema reads, taken twice. A second field key, a second variant
// key and a second tag key are each refused (RepeatedKey at that key's own
// name, with no step after it), and check and conforms must still agree on it.
// The tag key's test sits at the case the tag names, so the case here is one
// whose own schema does not read the key: an SField ignores it, and the object
// the case is checked against has the first one taken out.
// Both rules read the same pairs, so these run under exact and accurate.
const twice: [string, R][] = [
  ['C.SField{"a", C.SNat{}, C.SEnd{}}', obj([["a", N(1)], ["a", N(2)]])],
  [S.rec, obj([["a", N(1)], ["a", N(2)], ["b", NUL]])],
  [S.rec, obj([["a", N(1)], ["b", NUL], ["b", NUL]])],
  [target, obj([["any", TRUE], ["any", FALSE]])],
  [target, obj([["only", N(3)], ["only", N(4)]])],
  [target, obj([["any", TRUE], ["only", N(3)], ["any", FALSE]])],
  ['C.STagged{"type", "b", C.SField{"y", C.SStr{}, C.SEnd{}}, C.STagEnd{"type"}}', obj([["type", 'C.RStr{"b"}'], ["type", 'C.RStr{"b"}'], ["y", 'C.RStr{"s"}']])],
];
for (const [s, r] of twice) { pairs.push([s, r]); pairs.push([`C.SList{${s}}`, list([r])]); }
pairs.push([`C.SList{${rule}}`, list([obj([["role", obj([["any", TRUE]])], ["effect", 'C.RStr{"deny"}']]), obj([["role", obj([["any", TRUE], ["only", N(1)]])], ["effect", 'C.RStr{"deny"}']])])]);
// SRule: the value must conform to the rule's schema, then the rule decides.
// r_any: tag 0 wants positive numbers, tag 1 wants the value to be the tag.
const ruled = (tag: number) => `C.SRule{${S.nat}, ${tag}n}`;
const lruled = (tag: number) => `C.SList{${ruled(tag)}}`;
const fruled = (tag: number) => `C.SField{"a", ${ruled(tag)}, C.SEnd{}}`;
const lfruled = (tag: number) => `C.SList{${fruled(tag)}}`;
const ruledVals: R[] = [N(0), N(1), N(3), NUL, BAD, STR, list([]), list([N(0), N(2)]), list([N(2), N(0)]),
  list([STR]), list([N(1), STR]), obj([["a", N(1)]]), obj([["a", NUL]])];
for (const tag of [0, 1]) for (const r of ruledVals) {
  pairs.push([ruled(tag), r]);
  pairs.push([lruled(tag), list([r, r])]);
  pairs.push([fruled(tag), r]);
  pairs.push([lfruled(tag), list([r, r])]);
}
// tuples: a fixed-length list, each position its own schema
const tup = (ss: string[]) => ss.reduceRight((t, h) => `C.STuple{${h}, ${t}}`, "C.STEnd{}");
const tuples = [tup([]), tup([S.nat]), tup([S.nat, S.nat]), tup([S.nat, S.opt, S.rec]), tup([ruled(0), S.nat]), tup([S.nat, tup([S.nat, S.nat])])];
const tupVals: R[] = [list([]), list([N(1)]), list([N(1), N(2)]), list([N(1), N(2), N(3)]), list([N(0), NUL, recs[0]]),
  list([NUL, N(2)]), list([N(1), STR]), list([N(1), list([N(2), N(3)])]), list([N(1), list([N(2)])]), list([N(1), list([N(2), N(3), N(4)])]),
  `C.RCons{${N(1)}, ${NUL}}`, N(1), NUL, obj([]), "C.RMissing{}"];
for (const t of tuples) for (const r of tupVals) { pairs.push([t, r]); pairs.push([`C.SList{${t}}`, list([r, r])]); }
const tupSS = [[], [S.nat], [S.nat, S.nat], [S.nat, S.opt, S.rec], [ruled(0), S.nat], [S.nat, tup([S.nat, S.nat])]];
const lst = (xs: string[]) => "[" + xs.join(", ") + "]";
// Integers, as this file knows them: v >= 0 is IPos{v}, v < 0 is INeg{-v-1}
// (so -1 is INeg{0n}). The laws on SInt and SIntIn are checked against bounds
// and orders computed here, never read off the core.
const I = (v: number) => (v >= 0 ? `C.IPos{${v}n}` : `C.INeg{${-v - 1}n}`);
const tag = (v: number) => (v < 0 ? `m${-v}` : `${v}`); // a name cannot hold a minus sign
const IR = (v: number) => (v >= 0 ? N(v) : `C.RNeg{${-v - 1}n}`);
// check and conforms on the new schemas must agree, and check's report must be
// there, over every kind of raw value.
const intS = ["C.SInt{}", `C.SIntIn{${I(-3)}, ${I(1)}}`, `C.SIntIn{${I(1)}, ${I(-1)}}`, "C.SList{C.SInt{}}", 'C.SField{"a", C.SInt{}, C.SEnd{}}'];
const intRaws: R[] = [IR(0), IR(-1), IR(1), IR(-2), IR(-3), IR(-4), IR(2), BAD, BIG, STR, NUL, "C.RMissing{}", list([]), obj([]), TRUE, list([IR(-1), IR(1)]), list([IR(-1), STR]), obj([["a", IR(-2)]]), obj([["a", STR]])];
for (const sc of intS) for (const r of intRaws) pairs.push([sc, r]);
// The union: well-formed ones of every kind pairing, nested, under a rule and
// a wrapper, and ill-formed ones (overlapping kinds, an absent field, s.json())
// that the generic laws must still cover, since they have no wf premise.
const E = (l: string, r: string) => `C.SEither{${l}, ${r}}`;
const TAGGED = 'C.STagged{"t", "a", C.SField{"y", C.SStr{}, C.SEnd{}}, C.STagEnd{"t"}}';
const unionS = [E(S.nat, S.str), E("C.SInt{}", S.str), E(S.str, S.lnat), E(S.rec, S.nat), E(S.opt, S.str), E(S.str, S.opt),
  E(S.nat, E(S.str, "C.SBool{}")), E(E(S.nat, S.str), "C.STrue{}"), E(ruled(0), S.str), E(TAGGED, S.nat), E(enumS, tup([S.nat, S.nat])),
  `C.SStrLen{1n, 2n, ${E(S.str, S.nat)}}`, `C.SList{${E(S.nat, S.str)}}`, `C.SField{"a", ${E(S.nat, S.str)}, C.SEnd{}}`, `C.SOpt{${E(S.nat, S.str)}}`,
  E("C.SNatIn{0n, 1n}", S.nat), E(`C.SOptional{${S.nat}}`, S.str), E("C.SJson{}", S.nat), E(S.opt, `C.SOpt{${S.str}}`), E(S.str, S.str)];
const unionRaws: R[] = [N(0), N(3), IR(-1), STR, 'C.RStr{"allow"}', TRUE, FALSE, NUL, BAD, BIG, "C.RMissing{}", list([]), list([N(1)]), list([N(1), N(2)]),
  list([STR]), list([N(1), STR, NUL]), obj([]), recs[0], obj([["a", STR]]), obj([["t", 'C.RStr{"a"}'], ["y", STR]]), "C.RJson{C.JNull{}}"];
for (const sc of unionS) for (const r of unionRaws) pairs.push([sc, r]);
const law = process.env.LAW;
const instances: { name: string; claim: string }[] = [];
// a strict object: the core against a count of unknown keys written here
const strictS = [S.rec, 'C.SField{"a", C.SStr{}, C.SEnd{}}', "C.SEnd{}", 'C.SVariant{"any", C.STrue{}, C.SVariant{"only", C.SNat{}, C.SVEnd{}}}'];
const strictNames = [["a", "b"], ["a"], [], ["any", "only"]];
const strictVals: [string, R][] = [["a1b", obj([["a", N(1)], ["b", NUL]])], ["a1", obj([["a", N(1)]])], ["as", obj([["a", 'C.RStr{"s"}']])], ["z", obj([["z", N(1)]])],
  ["a1z", obj([["a", N(1)], ["z", N(2)]])], ["za1", obj([["z", N(2)], ["a", N(1)]])], ["any", obj([["any", TRUE]])], ["anyz", obj([["any", TRUE], ["z", TRUE]])],
  ["e", obj([])], ["n", N(3)], ["l", list([])]];
strictS.forEach((sc, si) => strictVals.forEach(([nm, r]) => {
  const keys = nm === "n" || nm === "l" ? [] : [...r.matchAll(/C\.RKey\{"(\w+)"/g)].map((m) => m[1]);
  const unknown = keys.filter((k) => !strictNames[si].includes(k)).length;
  const st = `C.SStrict{${sc}}`;
  if (!law || law === "strict") instances.push({ name: `strict_${si}_${nm}`, claim: `{C.conforms(~H.no_rule, ${st}, ${r}, None{}) == Bool.and(C.conforms(~H.no_rule, ${sc}, ${r}, None{}), ${unknown === 0 ? "True{}" : "False{}"}) : Bool}` });
  pairs.push([st, r]);
}));
for (const rule of ["no_rule", "r_any"]) {
  instances.push(...pairs.flatMap(([s, r], i) => [
    ...(!law || law === "exact" ? [{ name: `exact_${rule}_${i}`, claim: `{Maybe.is_none(&2, C.Err, C.check(~H.${rule}, ${s}, ${r}, None{})) == C.conforms(~H.${rule}, ${s}, ${r}, None{}) : Bool}` }] : []),
    ...(!law || law === "accurate" ? [{ name: `accurate_${rule}_${i}`, claim: `{H.acc_ok(~H.${rule}, ${s}, ${r}, C.check(~H.${rule}, ${s}, ${r}, None{})) == True{} : Bool}` }] : []),
  ]));
}
// the choice laws
const names = [[], ["allow"], ["allow", "deny"], ["a", "b", "c"], ["x", "x"]];
const strList = (xs: string[]) => "[" + xs.map((x) => `"${x}"`).join(", ") + "]";
for (const ns of names) for (let i = 0; i < ns.length; i++)
  instances.push(...(!law || law === "enum_accepts" ? [{ name: `enum_accepts_${names.indexOf(ns)}_${i}`, claim: `{C.conforms(~H.no_rule, C.SEnum{List.append(&2, String, ${strList(ns.slice(0, i))}, "${ns[i]}" <> ${strList(ns.slice(i + 1))})}, C.RStr{"${ns[i]}"}, None{}) == True{} : Bool}` }] : []));
for (const ns of names) for (const x of ["allow", "deny", "a", "c", "z", ""])
  instances.push(...(!law || law === "enum_admits" ? [{ name: `enum_admits_${names.indexOf(ns)}_${x || "empty"}`, claim: `{Bool.or(Bool.not(C.conforms(~H.no_rule, C.SEnum{${strList(ns)}}, C.RStr{"${x}"}, None{})), ${ns.includes(x) ? "True{}" : "False{}"}) == True{} : Bool}` }] : []));
const chains = ["C.SVEnd{}", 'C.SVariant{"any", C.STrue{}, C.SVEnd{}}', target, 'C.SVariant{"a", C.SNat{}, C.SVariant{"b", C.SOpt{C.SNat{}}, C.SVariant{"c", C.STrue{}, C.SVEnd{}}}}'];
const chainVals = [...choiceVals, obj([["a", N(1)]]), obj([["b", NUL]]), obj([["a", N(1)], ["c", TRUE]]), obj([["c", FALSE]]), obj([["b", N(2)], ["z", N(0)]])];
chains.forEach((c, ci) => chainVals.forEach((r, ri) =>
  instances.push(...(!law || law === "variant" ? [{ name: `variant_${ci}_${ri}`, claim: `{C.conforms(~H.no_rule, ${c}, ${r}, None{}) == Bool.and(C.is_object(${r}), Bool.and(Nat.is_eq(C.count_present(${c}, ${r}), 1n), C.present_conform(~H.no_rule, ${c}, ${r}))) : Bool}` }] : []))));
for (const rule of ["no_rule", "r_any"]) tupSS.forEach((ss, si) => tupVals.forEach((r, ri) =>
  instances.push(...(!law || law === "tuple" ? [{ name: `tuple_${rule}_${si}_${ri}`, claim: `{C.conforms(~H.${rule}, C.tuple_of(${lst(ss)}), ${r}, None{}) == Bool.and(C.raw_list(${r}), Bool.and(Nat.is_eq(C.raw_len(${r}), List.length(&2, C.Schema, ${lst(ss)})), C.each_pos(~H.${rule}, ${lst(ss)}, ${r}, 0n))) : Bool}` }] : []))));
// a tagged union: the case sees the object without its tag
const tagged = 'C.STagged{"type", "a", C.SStrict{C.SField{"x", C.SNat{}, C.SEnd{}}}, C.STagged{"type", "b", C.SField{"y", C.SStr{}, C.SEnd{}}, C.STagEnd{"type"}}}';
const T = (t: string) => `C.RStr{"${t}"}`;
const tagVals: R[] = [obj([["type", T("a")], ["x", N(1)]]), obj([["x", N(1)], ["type", T("a")]]), obj([["type", T("a")], ["x", N(1)], ["z", N(0)]]),
  obj([["type", T("a")]]), obj([["type", T("b")], ["y", T("s")]]), obj([["type", T("b")], ["y", N(1)]]), obj([["type", T("c")]]), obj([["type", N(1)]]),
  obj([["x", N(1)]]), obj([]), N(1), NUL, obj([["type", T("a")], ["type", T("b")], ["x", N(1)]]),
  obj([["type", T("b")], ["type", T("b")], ["y", T("s")]])];
tagVals.forEach((r, i) => {
  pairs.push([tagged, r]);
  pairs.push([`C.SList{${tagged}}`, list([r, r])]);
  if (!law || law === "tagged") {
    // the case under tag "a" sees r without its first "type" key, and so on
    instances.push({ name: `tagged_${i}`, claim: `{C.conforms(~H.no_rule, ${tagged}, ${r}, None{}) == H.tagged_spec(${r}) : Bool}` });
    instances.push({ name: `tagged_drop_${i}`, claim: `{C.lookup("type", C.drop_key("type", ${r})) == H.second_type(${r}) : C.Raw}` });
  }
});
// a value too big to walk: the core reports the node where it stands, with
// TooLarge, whatever the schema is
const bigS = [S.nat, S.str, S.opt, S.lnat, S.rec, lrec, "C.SEnd{}", "C.STrue{}", enumS, target, "C.STagEnd{\"type\"}", tup([S.nat]),
  'C.SRule{C.SNat{}, 0n}', 'C.SStrict{C.SField{"a", C.SNat{}, C.SEnd{}}}', tagged];
for (const s of bigS)
  instances.push(...(!law || law === "too_large" ? [{ name: `too_large_${instances.length}`, claim: `{C.check(~H.no_rule, ${s}, ${BIG}, None{}) == Some{C.Err{Nil{}, C.TooLarge{}}} : Maybe<&2, C.Err>}` }] : []));
for (const s of [S.nat, S.lnat, S.rec])
  instances.push(...(!law || law === "too_large" ? [{ name: `too_large_defect_${instances.length}`, claim: `{C.defect(~H.no_rule, ${s}, ${BIG}, None{}, Nil{}) == Some{C.TooLarge{}} : Maybe<&2, C.Why>}` }] : []));

// the ready-made rules, against bounds computed here, not by Bend
const bounds = [[0, 0], [0, 3], [1, 3], [2, 2], [3, 1], [5, 9]];
for (const [lo, hi] of bounds) for (const x of ["", "a", "ab", "abc", "abcd", "日本"]) {
  const ok = lo <= [...x].length && [...x].length <= hi;
  instances.push(...(!law || law === "rules" ? [{ name: `str_len_${lo}_${hi}_${instances.length}`, claim: `{Maybe.is_none(&2, C.Err, C.str_len_in(${lo}n, ${hi}n, C.RStr{"${x}"})) == ${ok ? "True{}" : "False{}"} : Bool}` }] : []));
}
for (const [lo, hi] of bounds) for (const n of [0, 1, 2, 3, 4, 9, 10]) {
  const ok = lo <= n && n <= hi;
  instances.push(...(!law || law === "rules" ? [{ name: `nat_in_${lo}_${hi}_${n}`, claim: `{Maybe.is_none(&2, C.Err, C.nat_in(${lo}n, ${hi}n, C.RNum{${n}n})) == ${ok ? "True{}" : "False{}"} : Bool}` }] : []));
}
for (const r of [STR, NUL, BAD, list([]), obj([])])
  instances.push(...(!law || law === "rules" ? [{ name: `nat_in_other_${instances.length}`, claim: `{Maybe.is_none(&2, C.Err, C.nat_in(1n, 2n, ${r})) == True{} : Bool}` }] : []));
// ---- the meaning laws of the three constructors that carry their bound ----
//
// Each is that law's statement at literals: conforms must agree with what the
// constructor's name claims. Edge cases come first, since the checker stops at
// the first failing instance: a lo past hi is an empty range, not an error, so
// lo > hi is a case here, and so are the empty string and n = 0.
const meaningBounds = [[0, 0], [3, 1], [0, 3], [1, 3], [2, 2], [5, 9]];
// sbool_meaning: SBool accepts a boolean and nothing else. No rule is read at
// an SBool, so one rule stands for all of them.
const sboolRaws: R[] = [TRUE, FALSE, BAD, BIG, "C.RMissing{}", N(0), STR, NUL, list([]), obj([])];
sboolRaws.forEach((r, i) => instances.push(...(!law || law === "sbool_meaning" ? [{
  name: `sbool_meaning_${i}`,
  claim: `{C.conforms(~H.no_rule, C.SBool{}, ${r}, None{}) == C.is_bool(${r}) : Bool}`,
}] : [])));
// snat_in_meaning: SNatIn{lo, hi} accepts a number in the bounds, both ends
// included -- and nothing else.
const meaningNums = [0, 1, 2, 3, 4, 9, 10];
const notNums: R[] = [STR, NUL, BAD, BIG, "C.RMissing{}", list([]), obj([]), TRUE];
meaningBounds.forEach(([lo, hi], bi) => meaningNums.forEach((n, ni) => instances.push(...(!law || law === "snat_in_meaning" ? [{
  name: `snat_in_meaning_${bi}_${ni}`,
  claim: `{C.conforms(~H.no_rule, C.SNatIn{${lo}n, ${hi}n}, C.RNum{${n}n}, None{}) == Bool.and(Nat.is_le(${lo}n, ${n}n), Nat.is_le(${n}n, ${hi}n)) : Bool}`,
}] : []))));
notNums.forEach((r, i) => instances.push(...(!law || law === "snat_in_meaning" ? [{
  name: `snat_in_meaning_other_${i}`,
  claim: `{C.conforms(~H.no_rule, C.SNatIn{0n, 3n}, ${r}, None{}) == False{} : Bool}`,
}] : [])));
// sstr_len_meaning: SStrLen{lo, hi, s} accepts a string whose length is in the
// bounds and that also satisfies s. SStr, SNat and SEnum under it read both
// halves: the inner check, and the length.
const meaningStrs = ["", "a", "ab", "abc", "abcd", "日本"];
const meaningInner = [S.str, S.nat, enumS];
const notStrs: R[] = [BIG, "C.RMissing{}", NUL, BAD, TRUE, FALSE, N(1), list([]), obj([])];
meaningBounds.forEach(([lo, hi], bi) => meaningStrs.forEach((x, xi) => meaningInner.forEach((s, si) => instances.push(...(!law || law === "sstr_len_meaning" ? [{
  name: `sstr_len_meaning_${bi}_${xi}_${si}`,
  claim: `{C.conforms(~H.no_rule, C.SStrLen{${lo}n, ${hi}n, ${s}}, C.RStr{"${x}"}, None{}) == Bool.and(C.conforms(~H.no_rule, ${s}, C.RStr{"${x}"}, None{}), Bool.and(Nat.is_le(${lo}n, String.length("${x}")), Nat.is_le(String.length("${x}"), ${hi}n))) : Bool}`,
}] : [])))));
notStrs.forEach((r, i) => meaningInner.forEach((s, si) => instances.push(...(!law || law === "sstr_len_meaning" ? [{
  name: `sstr_len_meaning_other_${i}_${si}`,
  claim: `{C.conforms(~H.no_rule, C.SStrLen{0n, 3n, ${s}}, ${r}, None{}) == False{} : Bool}`,
}] : []))));
// ---- SListLen: a list whose element count is in the bounds ----
//
// slist_len_meaning: SListLen{lo, hi, s} accepts a list whose element count is
// in the bounds and that s also accepts. The count is computed here, not by
// Bend, so a bound off by one is this file's business too. Edge cases first:
// the empty list, a count of exactly lo, exactly hi, and lo > hi.
const lenBounds = [[0, 0], [1, 3], [2, 2], [3, 1], [0, 2], [2, 4]];
// elems: the list's elements, or null when the raw is not a proper list at all
const lenVals: { r: R; elems: R[] | null }[] = [
  { r: list([]), elems: [] },
  { r: list([N(1)]), elems: [N(1)] },
  { r: list([N(1), N(2)]), elems: [N(1), N(2)] },
  { r: list([N(1), N(2), N(3)]), elems: [N(1), N(2), N(3)] },
  { r: list([N(1), N(2), N(3), N(4)]), elems: [N(1), N(2), N(3), N(4)] },
  { r: list([N(1), STR]), elems: [N(1), STR] },
  { r: `C.RCons{${N(1)}, ${NUL}}`, elems: null },
  { r: N(1), elems: null },
  { r: STR, elems: null },
  { r: NUL, elems: null },
  { r: BAD, elems: null },
  { r: BIG, elems: null },
  { r: "C.RMissing{}", elems: null },
  { r: obj([]), elems: null },
];
const numRaw = (r: R) => r.startsWith("C.RNum{");
const lenInner = S.lnat; // a list of numbers, so an element decides the other half
lenBounds.forEach(([lo, hi], bi) => lenVals.forEach(({ r, elems }, vi) => {
  const expected = elems !== null && elems.every(numRaw) && lo <= elems.length && elems.length <= hi;
  instances.push(...(!law || law === "slist_len_meaning" ? [{
    name: `slist_len_meaning_${bi}_${vi}`,
    claim: `{C.conforms(~H.no_rule, C.SListLen{${lo}n, ${hi}n, ${lenInner}}, ${r}, None{}) == ${expected ? "True{}" : "False{}"} : Bool}`,
  }] : []));
}));
// the law's own statement at literals, with the count read in Bend: a second
// reading of the same values, against the raw_len the core walks.
const lenLawBounds = [[0, 0], [1, 3], [3, 1], [0, 2]];
lenLawBounds.forEach(([lo, hi], bi) => lenVals.forEach(({ r }, vi) => instances.push(...(!law || law === "slist_len_meaning" ? [{
  name: `slist_len_law_${bi}_${vi}`,
  claim: `{C.conforms(~H.no_rule, C.SListLen{${lo}n, ${hi}n, ${lenInner}}, ${r}, None{}) == Bool.and(Bool.and(C.raw_list(${r}), Bool.and(Nat.is_le(${lo}n, C.raw_len(${r})), Nat.is_le(C.raw_len(${r}), ${hi}n))), C.conforms(~H.no_rule, ${lenInner}, ${r}, None{})) : Bool}`,
}] : []))));
// ---- SOptional: a field that may be absent ----
//
// soptional_meaning: an absent value is accepted, and every other value is the
// inner schema's to decide. The law's own statement at literals, edge cases
// first: the absent value itself, the two nodes the codec refused to build,
// then null (refused unless the inner is an SOpt) and a wrong kind.
const soptInners: [string, string][] = [
  ["nat", S.nat], ["str", S.str], ["bool", "C.SBool{}"], ["opt", "C.SOpt{C.SNat{}}"], ["lnat", S.lnat], ["rec", S.rec],
];
const soptRaws: R[] = ["C.RMissing{}", BIG, BAD, NUL, N(0), STR, TRUE, FALSE, list([]), obj([]), "C.REnd{}"];
soptInners.forEach(([nm, i], si) => soptRaws.forEach((r, ri) => instances.push(...(!law || law === "soptional_meaning" ? [{
  name: `soptional_meaning_${nm}_${ri}`,
  claim: `{C.conforms(~H.no_rule, C.SOptional{${i}}, ${r}, None{}) == Bool.or(C.is_missing(${r}), C.conforms(~H.no_rule, ${i}, ${r}, None{})) : Bool}`,
}] : []))));
// the same edges with the answer written here rather than read off the inner:
// absent is accepted whatever the inner is; null only where the inner is an
// SOpt; a node the codec refused to build is refused here too.
const soptEdges: [string, R, boolean][] = [
  ["C.SOptional{C.SNat{}}", "C.RMissing{}", true],
  ["C.SOptional{C.SNat{}}", NUL, false],
  ["C.SOptional{C.SNat{}}", BIG, false],
  ["C.SOptional{C.SNat{}}", BAD, false],
  ["C.SOptional{C.SNat{}}", N(0), true],
  ["C.SOptional{C.SNat{}}", STR, false],
  ["C.SOptional{C.SOpt{C.SNat{}}}", "C.RMissing{}", true],
  ["C.SOptional{C.SOpt{C.SNat{}}}", NUL, true],
  ["C.SOptional{C.SOpt{C.SNat{}}}", N(1), true],
  ["C.SOptional{C.SBool{}}", TRUE, true],
  ["C.SOptional{C.SBool{}}", FALSE, true],
  ["C.SOptional{C.SBool{}}", N(1), false],
  ["C.SOptional{C.SList{C.SNat{}}}", list([]), true],
  ["C.SOptional{C.SList{C.SNat{}}}", list([N(1)]), true],
  ["C.SOptional{C.SList{C.SNat{}}}", list([STR]), false],
  ["C.SOptional{C.SList{C.SNat{}}}", BIG, false],
];
soptEdges.forEach(([s, r, ok], i) => instances.push(...(!law || law === "soptional_meaning" ? [{
  name: `soptional_edge_${i}`,
  claim: `{C.conforms(~H.no_rule, ${s}, ${r}, None{}) == ${ok ? "True{}" : "False{}"} : Bool}`,
}] : [])));
// ---- a key the schema does not name (D3) ----
//
// The law's three readings at literals: an unnamed key before the keys the
// schema reads, after them, and before a variant key. Edge cases first, since
// the checker stops at the first failing instance: the key the schema DOES
// name is not a key it does not name -- repeated, it is refused, and that is
// repeated_key_refused's law -- and a value the schema refuses stays refused
// however many keys stand around it. A repeat of a key nothing reads is here
// too: nothing in the core reads an unnamed key, so a second one leaves the
// answer alone. Both claims are checked on the values that conform: the
// answer written here, and the law's own reading, that conforms at the value
// with the extra key is conforms at the value without it.
const d3Rec = 'C.SField{"a", C.SNat{}, C.SEnd{}}';
const d3Var = 'C.SVariant{"a", C.SNat{}, C.SVEnd{}}';
const d3Named = obj([["a", N(1)]]);
const d3Cases: [string, string, R, boolean][] = [
  ["rec_named", d3Rec, d3Named, true],
  ["rec_before", d3Rec, obj([["z", N(9)], ["a", N(1)]]), true],
  ["rec_after", d3Rec, obj([["a", N(1)], ["z", N(9)]]), true],
  ["rec_before_twice", d3Rec, obj([["z", N(9)], ["z", N(9)], ["a", N(1)]]), true],
  ["rec_before_bool", d3Rec, obj([["z", TRUE], ["a", N(1)]]), true],
  ["var_named", d3Var, d3Named, true],
  ["var_before", d3Var, obj([["z", N(9)], ["a", N(1)]]), true],
  ["var_after", d3Var, obj([["a", N(1)], ["z", N(9)]]), true],
  ["rec_named_twice", d3Rec, obj([["a", N(1)], ["a", N(2)]]), false],
  ["rec_named_absent", d3Rec, obj([["z", N(9)]]), false],
  ["rec_named_wrong", d3Rec, obj([["z", N(9)], ["a", STR]]), false],
  ["rec_empty", d3Rec, obj([]), false],
  ["var_named_absent", d3Var, obj([["z", N(9)]]), false],
  ["var_empty", d3Var, obj([]), false],
];
d3Cases.forEach(([nm, s, r, ok], i) => instances.push(...(!law || law === "unnamed_key" ? [{
  name: `unnamed_key_${i}_${nm}`,
  claim: `{C.conforms(~H.no_rule, ${s}, ${r}, None{}) == ${ok ? "True{}" : "False{}"} : Bool}`,
}, ...(ok ? [{
  name: `unnamed_key_law_${i}_${nm}`,
  claim: `{C.conforms(~H.no_rule, ${s}, ${r}, None{}) == C.conforms(~H.no_rule, ${s}, ${d3Named}, None{}) : Bool}`,
}] : [])] : [])));

// The number clause of json_valid_spec, with the approved comparison
// specification expanded so that the falsifier imports no open laws.
for (const hi of [0x7FF00000, 0xFFF00000, 0x7FF80000, 0x7FEFFFFF, 0x80000000, 0, 0xFFFFFFFF])
  for (const lo of [0, 1]) if (!law || law === "number_spec") instances.push({
    name: `number_spec_${hi.toString(16)}_${lo}`,
    claim: `{C.finite_number(C.NumberBits{${hi}, ${lo}}) == Cmp.is_lt(U32.cmp(U32.and(${hi}, 2147483647), 2146435072)) : Bool}`,
  });

// json_valid_spec: the frozen specification at nested valid and invalid values.
const jnum = (hi: number, lo = 0) => `C.JNumber{C.NumberBits{${hi}, ${lo}}}`;
const jarr = (vs: string[]) => `C.JArray{[${vs.join(", ")}]}`;
const jobj = (ms: [string, string][]) => `C.JObject{[${ms.map(([k, v]) => `C.JMember{"${k}", ${v}}`).join(", ")}]}`;
const jnull = "C.JNull{}", jbad = jnum(0x7ff00000);
const jsonCases: [string, string, boolean][] = [
  ["null", jnull, true], ["bool", "C.JBool{False{}}", true], ["string", 'C.JString{"x"}', true],
  ["empty_array", jarr([]), true], ["empty_object", jobj([]), true],
  ["finite", jnum(0x7fefffff, 0xffffffff), true], ["negative_zero", jnum(0x80000000), true],
  ["infinity", jbad, false], ["negative_infinity", jnum(0xfff00000), false], ["nan", jnum(0x7ff80000, 1), false],
  ["array_later_bad", jarr([jnull, jbad]), false],
  ["object_value_bad", jobj([["a", jbad]]), false],
  ["object_later_bad", jobj([["a", jnull], ["b", jbad]]), false],
  // a repeated name is JSON (RFC 8259: names should be unique, not must)
  ["repeated", jobj([["a", jnull], ["a", jnull]]), true],
  ["distinct", jobj([["a", jnull], ["b", jnull]]), true],
  ["later_repeated", jobj([["a", jnull], ["b", jnull], ["b", jnull]]), true],
  ["nested_valid", jarr([jobj([["a", jarr([jnull, jnum(0)])], ["b", jobj([])]])]), true],
  ["nested_bad", jobj([["a", jarr([jnull, jobj([["b", jnull], ["c", jbad]])])]]), false],
  ["nested_repeated", jarr([jnull, jobj([["a", jnull], ["a", jarr([])]])]), true],
];
for (const [name, v, valid] of jsonCases) if (!law || law === "json_valid_spec") {
  instances.push({ name: `json_valid_spec_${name}`, claim: `{C.valid_json(${v}) == H.json_spec(${v}) : Bool}` });
  instances.push({ name: `json_valid_expected_${name}`, claim: `{H.json_spec(${v}) == ${valid ? "True{}" : "False{}"} : Bool}` });
}

// json_dec_preserves: all Raw constructors and exact payload equality, not
// validity. Invalid numbers, and the repeated names valid_json does not
// refuse, must be returned unchanged.
const jsonDecCases: [string, R][] = [
  ["bad", BAD], ["too_big", BIG], ["missing", "C.RMissing{}"],
  ["number", N(3)], ["bool_true", TRUE], ["bool_false", FALSE],
  ["null", NUL], ["string", STR], ["nil", list([])],
  ["cons", list([N(1)])], ["end", obj([])], ["key", obj([["a", N(1)]])],
  ...jsonCases.map(([name, v]): [string, R] => [`json_${name}`, `C.RJson{${v}}`]),
  ["ordered_nested", `C.RJson{${jobj([["z", jarr([jnum(0x80000000, 1), jobj([["b", jnum(0x3ff00000, 7)], ["a", jnull]])])], ["a", jnum(0x7fefffff, 0xffffffff)]])}}`],
  ["ordered_nested_reverse", `C.RJson{${jobj([["a", jnum(0x7fefffff, 0xffffffff)], ["z", jarr([jobj([["a", jnull], ["b", jnum(0x3ff00000, 7)]]), jnum(0x80000000, 1)])]])}}`],
];
for (const [name, r] of jsonDecCases) if (!law || law === "json_dec_preserves") {
  instances.push({ name: `json_dec_preserves_${name}`, claim: `{C.dec(C.SJson{}, ${r}) == H.raw_json_value(${r}) : Maybe<&2, C.Json>}` });
  const expected = r.startsWith("C.RJson{") ? `Some{${r.slice(8, -1)}}` : "None{}";
  instances.push({ name: `json_dec_expected_${name}`, claim: `{H.raw_json_value(${r}) == ${expected} : Maybe<&2, C.Json>}` });
}

// json_accept_exact: all Raw constructors under both an accepting rule and a
// rule that refuses JSON. Both readings use the independent frozen spec.
const jsonAcceptCases: [string, R, boolean][] = [
  ...jsonDecCases.filter(([, r]) => !r.startsWith("C.RJson{")).map(([name, r]): [string, R, boolean] => [name, r, false]),
  ...jsonCases.map(([name, v, valid]): [string, R, boolean] => [`json_${name}`, `C.RJson{${v}}`, valid]),
];
for (const rule of ["no_rule", "r_any"]) for (const [name, r, valid] of jsonAcceptCases) if (!law || law === "json_accept_exact") {
  instances.push({ name: `json_accept_exact_${rule}_${name}`, claim: `{C.conforms(~H.${rule}, C.SJson{}, ${r}, None{}) == H.raw_json_spec(${r}) : Bool}` });
  instances.push({ name: `json_accept_expected_${rule}_${name}`, claim: `{C.conforms(~H.${rule}, C.SJson{}, ${r}, None{}) == ${valid ? "True{}" : "False{}"} : Bool}` });
  instances.push({ name: `json_accept_spec_expected_${rule}_${name}`, claim: `{H.raw_json_spec(${r}) == ${valid ? "True{}" : "False{}"} : Bool}` });
}

// json_enc_preserves: both approved equations, plus explicit payload and
// validity expectations. Encoding never repairs invalid payloads.
const jsonEncCases: [string, string, boolean][] = [
  ...jsonCases,
  ["bool_true", "C.JBool{True{}}", true],
  ["positive_zero", jnum(0), true],
  ["empty_string", 'C.JString{""}', true],
  ["unicode_string", 'C.JString{"日本"}', true],
  ["negative_finite", jnum(0xffefffff, 0xffffffff), true],
  ["negative_nan", jnum(0xfff80000, 0xffffffff), false],
  ["signaling_nan", jnum(0x7ff00000, 1), false],
  ["ordered_nested", jobj([["z", jarr([jnum(0x80000000, 1), jobj([["b", jnum(0x3ff00000, 7)], ["a", jnull]])])], ["a", jnum(0x7fefffff, 0xffffffff)]]), true],
  ["ordered_nested_reverse", jobj([["a", jnum(0x7fefffff, 0xffffffff)], ["z", jarr([jobj([["a", jnull], ["b", jnum(0x3ff00000, 7)]]), jnum(0x80000000, 1)])]]), true],
  ["repeated_different_values", jobj([["a", jnull], ["a", "C.JBool{True{}}"]]), true],
];
for (const [name, v, valid] of jsonEncCases) if (!law || law === "json_enc_preserves") {
  const encoded = `C.enc(C.SJson{}, ${v})`;
  instances.push({ name: `json_enc_payload_${name}`, claim: `{${encoded} == C.RJson{${v}} : C.Raw}` });
  instances.push({ name: `json_enc_validation_${name}`, claim: `{C.conforms(~C.no_rule, C.SJson{}, ${encoded}, None{}) == H.json_spec(${v}) : Bool}` });
  instances.push({ name: `json_enc_expected_${name}`, claim: `{C.conforms(~C.no_rule, C.SJson{}, ${encoded}, None{}) == ${valid ? "True{}" : "False{}"} : Bool}` });
  instances.push({ name: `json_enc_spec_expected_${name}`, claim: `{H.json_spec(${v}) == ${valid ? "True{}" : "False{}"} : Bool}` });
}

// ---- SInt: a whole number of either sign ----
//
// The four laws at literals. Edge cases come first, since the checker stops at
// the first failing instance: 0, -1 (INeg{0n}), then the integers on either
// side of zero. -1 is INeg{0n}, -2 is INeg{1n}: an offset read as -n instead
// of -(n+1) is wrong at -1 and -2 first.
const ints = [0, -1, 1, -2, 2, -3, 3, -4, 4];
const walk = [0, 1, 2, 3, 4, 5];

// int_le_complete: every number reached from a by k steps of +1 is at least a.
// The reached number is computed here (a + k) as well as by the walk.
for (const a of ints) for (const k of walk) if (!law || law === "int_le_complete") {
  instances.push({ name: `int_le_complete_${tag(a)}_${k}`, claim: `{C.int_le(${I(a)}, H.int_add(${k}n, ${I(a)})) == True{} : Bool}` });
  instances.push({ name: `int_le_complete_sum_${tag(a)}_${k}`, claim: `{H.int_add(${k}n, ${I(a)}) == ${I(a + k)} : C.Int}` });
}

// int_le_sound: a number at least a is reached from a by steps of +1 -- so a
// number below a is not at least a. The distance is computed here. Both
// readings: the reachable pairs are reached in exactly b - a steps, and int_le
// holds of them; the unreachable pairs (b below a) are refused by int_le.
for (const a of ints) for (const b of ints) if (!law || law === "int_le_sound") {
  if (a <= b) {
    instances.push({ name: `int_le_sound_reach_${tag(a)}_${tag(b)}`, claim: `{H.int_add(${b - a}n, ${I(a)}) == ${I(b)} : C.Int}` });
    instances.push({ name: `int_le_sound_le_${tag(a)}_${tag(b)}`, claim: `{C.int_le(${I(a)}, ${I(b)}) == True{} : Bool}` });
  } else {
    instances.push({ name: `int_le_sound_below_${tag(a)}_${tag(b)}`, claim: `{C.int_le(${I(a)}, ${I(b)}) == False{} : Bool}` });
  }
}

// sint_meaning: SInt accepts a whole number of either sign and nothing else.
// No rule is read at an SInt, so a rule that refuses everything stands in too.
const intKinds: [string, R, boolean][] = [
  ["zero", IR(0), true], ["minus_one", IR(-1), true], ["one", IR(1), true], ["minus_two", IR(-2), true], ["minus_big", IR(-1000), true],
  ["bad", BAD, false], ["too_big", BIG, false], ["missing", "C.RMissing{}", false], ["null", NUL, false], ["string", STR, false],
  ["true", TRUE, false], ["false", FALSE, false], ["nil", list([]), false], ["cons", list([IR(-1)]), false], ["end", obj([]), false],
  ["key", obj([["a", IR(-1)]]), false], ["json", "C.RJson{C.JNull{}}", false],
];
for (const rl of ["no_rule", "r_any"]) for (const [nm, r, ok] of intKinds) if (!law || law === "sint_meaning") {
  instances.push({ name: `sint_meaning_${rl}_${nm}`, claim: `{C.conforms(~H.${rl}, C.SInt{}, ${r}, None{}) == H.is_int_spec(H.raw_int_spec(${r})) : Bool}` });
  instances.push({ name: `sint_meaning_expected_${rl}_${nm}`, claim: `{C.conforms(~H.${rl}, C.SInt{}, ${r}, None{}) == ${ok ? "True{}" : "False{}"} : Bool}` });
}

// sint_in_meaning: SIntIn{lo, hi} accepts an integer from lo to hi, both ends
// included. lo == hi, lo > hi (an empty range, not an error), and bounds that
// straddle zero come first; every integer from -4 to 4 is tried at each.
const intBounds: [number, number][] = [[0, 0], [-1, -1], [-1, 0], [0, -1], [-2, 1], [1, -2], [-3, -3], [2, 2], [1, 3], [-4, -2], [-4, 4]];
intBounds.forEach(([lo, hi], bi) => ints.forEach((v) => {
  if (law && law !== "sint_in_meaning") return;
  const ok = lo <= v && v <= hi;
  const sc = `C.SIntIn{${I(lo)}, ${I(hi)}}`;
  instances.push({ name: `sint_in_meaning_${bi}_${tag(v)}`, claim: `{C.conforms(~H.no_rule, ${sc}, ${IR(v)}, None{}) == H.int_in_spec(${I(lo)}, ${I(hi)}, H.raw_int_spec(${IR(v)})) : Bool}` });
  instances.push({ name: `sint_in_meaning_expected_${bi}_${tag(v)}`, claim: `{C.conforms(~H.no_rule, ${sc}, ${IR(v)}, None{}) == ${ok ? "True{}" : "False{}"} : Bool}` });
}));
for (const [nm, r] of intKinds.filter(([, , ok]) => !ok)) if (!law || law === "sint_in_meaning") {
  instances.push({ name: `sint_in_meaning_other_${nm}`, claim: `{C.conforms(~H.r_any, C.SIntIn{${I(-2)}, ${I(2)}}, ${r}, None{}) == False{} : Bool}` });
  instances.push({ name: `sint_in_meaning_other_wide_${nm}`, claim: `{C.conforms(~H.no_rule, C.SIntIn{${I(-1000)}, ${I(1000)}}, ${r}, None{}) == H.int_in_spec(${I(-1000)}, ${I(1000)}, H.raw_int_spec(${r})) : Bool}` });
}

// The union's own laws. A schema list wide enough to reach every row of the
// kind table, and every kind.
const kinds = ["C.KNum{}", "C.KStr{}", "C.KBool{}", "C.KList{}", "C.KObj{}", "C.KNull{}", "C.KAbsent{}", "C.KJson{}", "C.KOther{}"];
const tableS = [...new Set([S.nat, S.str, S.opt, S.lnat, S.rec, "C.SNatIn{0n, 1n}", "C.SInt{}", `C.SIntIn{${I(-1)}, ${I(1)}}`, enumS, "C.SBool{}", "C.STrue{}",
  tup([]), tup([S.nat]), "C.SEnd{}", TAGGED, 'C.STagEnd{"t"}', target, "C.SVEnd{}", "C.SJson{}", `C.SOptional{${S.nat}}`, `C.SStrLen{1n, 2n, ${S.str}}`,
  `C.SListLen{0n, 2n, ${S.lnat}}`, ruled(0), `C.SStrict{${S.rec}}`, ...unionS])];
tableS.forEach((sc, si) => kinds.forEach((k, ki) => {
  if (!law || law === "kinds_table") instances.push({ name: `kinds_table_${si}_${ki}`, claim: `{C.has_kind(${sc}, ${k}) == H.in_kinds(${k}, H.kinds_spec(${sc})) : Bool}` });
}));
// The table at literals, read off D2 here rather than off either function.
const expectKinds: [string, number[]][] = [[S.nat, [0]], [S.str, [1]], [S.opt, [5, 0]], [S.lnat, [3]], [S.rec, [4]], [enumS, [1]], ["C.STrue{}", [2]],
  ["C.SJson{}", [7]], [`C.SOptional{${S.nat}}`, [6, 0]], [E(S.nat, E(S.str, "C.SBool{}")), [0, 1, 2]], [E(S.opt, S.str), [5, 0, 1]], [TAGGED, [4]], [tup([]), [3]]];
expectKinds.forEach(([sc, ks], si) => kinds.forEach((k, ki) => {
  if (!law || law === "kinds_table") instances.push({ name: `kinds_table_expected_${si}_${ki}`, claim: `{C.has_kind(${sc}, ${k}) == ${ks.includes(ki) ? "True{}" : "False{}"} : Bool}` });
}));
pairs.forEach(([sc, r], i) => { for (const rl of ["no_rule", "r_any"]) {
  if (!law || law === "kind_sound") instances.push({ name: `kind_sound_${rl}_${i}`, claim: `{Bool.or(Bool.not(C.conforms(~H.${rl}, ${sc}, ${r}, None{})), C.has_kind(${sc}, C.kind_of(${r}))) == True{} : Bool}` });
} });
// union_exact and union_disjoint hold under wf; that wf really holds of the
// well-formed ones (and refuses the rest) is checked too, or both would be
// vacuous.
const altS = [S.nat, S.str, S.opt, S.lnat, S.rec, "C.SNatIn{0n, 1n}", "C.SInt{}", enumS, "C.STrue{}", "C.SBool{}", tup([S.nat]), TAGGED, ruled(0), `C.SStrict{${S.rec}}`,
  `C.SOptional{${S.nat}}`, "C.SJson{}", E(S.str, "C.SBool{}"), `C.SOpt{${S.str}}`];
const kindsOf = (a: string): number[] => expectKinds.find(([s]) => s === a)?.[1] ?? ({ [S.nat]: [0], "C.SNatIn{0n, 1n}": [0], "C.SInt{}": [0], "C.SBool{}": [2], [tup([S.nat])]: [3], [ruled(0)]: [0], [`C.SStrict{${S.rec}}`]: [4], [E(S.str, "C.SBool{}")]: [1, 2], [`C.SOpt{${S.str}}`]: [5, 1] } as Record<string, number[]>)[a]!;
altS.forEach((a, ai) => altS.forEach((b, bi) => {
  const u = E(a, b);
  const ka = kindsOf(a), kb = kindsOf(b);
  const wfOk = !ka.some((k) => kb.includes(k)) && ![...ka, ...kb].some((k) => k === 6 || k === 7);
  if (!law || law === "union_exact" || law === "union_disjoint") instances.push({ name: `union_wf_${ai}_${bi}`, claim: `{C.wf(${u}) == ${wfOk ? "True{}" : "False{}"} : Bool}` });
  unionRaws.forEach((r, ri) => { for (const rl of ["no_rule", "r_any"]) {
    const lc = `C.conforms(~H.${rl}, ${a}, ${r}, None{})`, rc = `C.conforms(~H.${rl}, ${b}, ${r}, None{})`;
    if (!law || law === "union_exact") instances.push({ name: `union_exact_${rl}_${ai}_${bi}_${ri}`, claim: `{Bool.or(Bool.not(C.wf(${u})), H.bool_eq(C.conforms(~H.${rl}, ${u}, ${r}, None{}), Bool.or(${lc}, ${rc}))) == True{} : Bool}` });
    if (!law || law === "union_disjoint") instances.push({ name: `union_disjoint_${rl}_${ai}_${bi}_${ri}`, claim: `{Bool.or(Bool.not(C.wf(${u})), Bool.not(Bool.and(${lc}, ${rc}))) == True{} : Bool}` });
  } });
}));

// Which reason a union reports. err_eq compares two reports by value; the
// NoAlternative reasons are written out here from D2's table, not from no_alt.
const NA = (ks: number[]) => `C.NoAlternative{${[0, 1, 2, 3, 4, 5].map((k) => (ks.includes(k) ? "True{}" : "False{}")).join(", ")}}`;
altS.forEach((a, ai) => altS.forEach((b, bi) => unionRaws.forEach((r, ri) => {
  const u = E(a, b), ka = kindsOf(a), kb = kindsOf(b);
  const k = r.startsWith("C.RNum") || r.startsWith("C.RNeg") ? 0 : r.startsWith("C.RStr") ? 1 : r.startsWith("C.RBool") ? 2 : r.startsWith("C.RNil") || r.startsWith("C.RCons") ? 3
    : r.startsWith("C.REnd") || r.startsWith("C.RKey") ? 4 : r === NUL ? 5 : r === "C.RMissing{}" ? 6 : r.startsWith("C.RJson") ? 7 : 8;
  const chk = (s: string) => `C.check(~H.no_rule, ${s}, ${r}, None{})`;
  if (ka.includes(k)) { if (!law || law === "union_reports_alternative") instances.push({ name: `union_reports_${ai}_${bi}_${ri}`, claim: `{H.err_eq(${chk(u)}, ${chk(a)}) == True{} : Bool}` }); }
  else if (kb.includes(k)) { if (!law || law === "union_reports_right") instances.push({ name: `union_reports_right_${ai}_${bi}_${ri}`, claim: `{H.err_eq(${chk(u)}, ${chk(b)}) == True{} : Bool}` }); }
  else if (!kb.includes(k) && (!law || law === "union_no_alternative")) {
    const why = r === "C.RMissing{}" ? "C.Missing{}" : r === BIG ? "C.TooLarge{}" : NA([...ka, ...kb]);
    instances.push({ name: `union_no_alt_${ai}_${bi}_${ri}`, claim: `{H.err_eq(${chk(u)}, Some{C.Err{[], ${why}}}) == True{} : Bool}` });
  }
})));

export default { imports: [process.env.CORE ?? "../core.bend as C", `./${process.env.HELPERS ?? "helpers.bend"} as H`], instances };
