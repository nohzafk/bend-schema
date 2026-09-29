// The universal codec: any JS value, as the schema check takes it.
//
// It knows no schema, so it decides nothing about shapes: a whole number from 0
// to the runtime's Nat bound (2^48-1) is RNum, a boolean RBool, null RNull, a
// string RStr, an array a chain of RCons, an object a chain of RKey in its own
// key order, and anything else (a fraction, a negative, NaN, undefined) is
// RBad, for check to report where it sits. Every rule about shapes is the
// proved core's (LAWS.bend).
//
// Size is the one thing it decides, because it is the one thing the core
// cannot: the compiled JS walks a list or an object with one native JS frame
// per element or key, so a long value throws RangeError. So the codec counts
// what such a walk would cost -- see BUDGET -- and puts one RTooBig in place of
// the array or object that runs past the budget, which the core reports as
// TooLarge at that node's path. Nothing here is a rule about values: a size is
// not a shape, and a host cannot choose the sizes it is sent.

import type { BendList, BendMaybe, Err, Raw, Step, Why } from "../dist-core/core.mjs";

// The largest Nat the runtime holds: bend's own Nat.add(Nat.mul(65535,
// 4294967295 + 1), 4294967295). A number past it is not a Nat at all, so it
// is not a value the core can be given.
export const NAT_MAX = 2 ** 48 - 1;

// One rule, two ways out: the runtime holds v as a Nat, or it does not.
const natFit = (v: number): boolean => Number.isSafeInteger(v) && v >= 0 && v <= NAT_MAX;

// `nat(name, v)` is v when the runtime can hold it as a Nat, and an Error
// otherwise. It is toRaw's RNum rule, thrown instead of reported: a host that
// must refuse a number before building anything -- billing's `units`, which is
// not part of the plan it checks -- needs the refusal here, and the message
// names the field, the bound and the value.
export function nat(name: string, v: number): number {
  if (!natFit(v)) {
    throw new Error(`${name} must be a whole number from 0 to ${NAT_MAX} (${name}=${v})`);
  }
  return v;
}

// The most list elements and object keys one value may hold, counted over
// every level of nesting and summed: `[[1,2],[3]]` is 2 + 3 = 5. Past it, a
// node becomes RTooBig.
//
// Measured, not guessed (with bend 2.0.34 on a macOS arm64 Mac, each shape in
// its own process). Each shape below is the largest count where toRaw, check0,
// conforms0, enc and dec all return in bun, and what the next step throws:
//
//   flat list       19949   check0: RangeError
//   nested object    8192   check0: RangeError
//   nested list     18777   converting: RangeError
//   list of lists  >199000  (not the binding shape)
//   list of objects >199000 (not the binding shape)
//   mixed          >100000  (not the binding shape)
//   flat object     not measured: past 600 s, and KEYS_MAX (below) caps it
//
// The binding shape is the nested object, at 8192, and a value at the budget
// keeps some 2.7x of margin under it. (On bend 2.0.27 the nested object reached
// about 10,600 and a flat object bound first, at 6144, which is why KEYS_MAX
// exists; the budget was set to half of that, 3072, and is kept.) One budget
// covers lists, objects and nesting alike, and what makes it enough is the
// invariant: toRaw never builds a value whose count is past it, so the walk
// that follows is bounded by it.

export const BUDGET = 3072;

// The most keys one object may hold. A second limit, on time rather than
// stack: the core finds each field by scanning the object from the front, so
// walking an object costs about keys^2 lookups. At 3072 keys that was about
// 8 s for each of check0, conforms0 and dec -- a small request that holds a
// server for seconds. At 256 keys it is about 65,000 lookups. An object with
// more keys than this is RTooBig, like a value past the budget; a set that
// large belongs in a list.
export const KEYS_MAX = 256;

export function toRaw(v: unknown): Raw {
  let left = BUDGET;
  const build = (v: unknown): Raw => {
    if (v === null) return { $: "RNull" };
    if (typeof v === "number") return natFit(v) ? { $: "RNum", n: BigInt(v) } : { $: "RBad" };
    if (typeof v === "boolean") return { $: "RBool", b: v };
    if (typeof v === "string") return { $: "RStr", s: v };
    if (Array.isArray(v)) {
      if (v.length > left) return { $: "RTooBig" };
      left -= v.length;
      // Elements are built first to last, so the budget runs out where a
      // reader would expect: at the first node past it, not at the start.
      const heads = v.map(build);
      return heads.reduceRight<Raw>((tail, head) => ({ $: "RCons", head, tail }), { $: "RNil" });
    }
    if (typeof v === "object") {
      const entries = Object.entries(v as object);
      if (entries.length > KEYS_MAX || entries.length > left) return { $: "RTooBig" };
      left -= entries.length;
      const vals = entries.map(([key, val]) => [key, build(val)] as const);
      return vals.reduceRight<Raw>((rest, [key, val]) => ({ $: "RKey", key, val, rest }), { $: "REnd" });
    }
    return { $: "RBad" };
  };
  return build(v);
}

export const NONE: BendMaybe<bigint> = { $: "None" };

function steps(p: BendList<Step>): Step[] {
  const out: Step[] = [];
  for (let x = p; x.$ === "Con"; x = x.tail) out.push(x.head);
  return out;
}

// A path as text: "[2].upTo". A field step counts the schema fields it
// skipped, for the proofs; the text shows only its name.
export function pathText(p: BendList<Step>): string {
  return steps(p).map((s) => (s.$ === "AtIndex" ? `[${s.i}]` : s.$ === "AtField" ? `.${s.name}` : s.$ === "AtKey" ? `.${s.key}` : `[${s.i}].${s.key}`)).join("");
}

// What is wrong, in words. tsc checks every reason is here.
export function whyText(w: Why): string {
  switch (w.$) {
    case "Missing":
      return "missing";
    case "NotNat":
      return `must be a whole number from 0 to ${NAT_MAX}`;
    case "NotString":
      return "must be a string";
    case "NotBool":
      return "must be a boolean";
    case "NotList":
      return "must be a list";
    case "NotObject":
      return "must be an object";
    case "NoElements":
      return "must not be empty";
    case "OpenNotLast":
      return "only the last may be null";
    case "LastNotOpen":
      return "the last must be null";
    case "NotIncreasing":
      return `must be past ${w.prev} (got ${w.got})`;
    case "NotTrue":
      return "must be true";
    case "NotOneOf":
      return "is not one of the allowed names";
    case "NoVariant":
      return "must have one of its keys";
    case "TwoVariants":
      return "is a second key, where only one is allowed";
    case "TooShort":
      return "has too few elements";
    case "TooLong":
      return "has too many elements";
    case "LengthNotIn":
      return `must be ${w.lo} to ${w.hi} characters long`;
    case "CountNotIn":
      return `must have ${w.lo} to ${w.hi} elements`;
    case "UnknownKey":
      return "is not a key this object allows";
    case "RepeatedKey":
      return `is a second ${w.key}`;
    case "NotIn":
      return `must be from ${w.lo} to ${w.hi}`;
    case "TooLarge":
      return "too large";
  }
}

// An error in words, its path after `where` (the name the host gives the
// value): errText(e, "tiers") is "tiers[0].upTo: missing". With no `where`
// and an empty path, the value itself is named: "the value: must be a list".
export function errText(e: Err, where = ""): string {
  return `${where + pathText(e.path) || "the value"}: ${whyText(e.why)}`;
}
