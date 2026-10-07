// The universal codec: any JS value, as the schema check takes it.
//
// It knows no schema, so it decides nothing about shapes: a whole number from 0
// to the runtime's Nat bound (2^48-1) is RNum, a boolean RBool, null RNull, a
// string RStr, an array a chain of RCons, a plain object a chain of RKey in its
// own key order, and anything else (a fraction, a negative, NaN, undefined, a
// Date or any other non-plain object) is RBad, for check to report where it
// sits. Every rule about shapes is the proved core's (LAWS.bend).
//
// Size is the one thing it decides, because it is the one thing the core
// cannot: the compiled JS walks a list or an object with one native JS frame
// per element or key, so a long value throws RangeError. So the codec counts
// what such a walk would cost -- see BUDGET -- and puts one RTooBig in place of
// the array or object that runs past the budget, which the core reports as
// TooLarge at that node's path. Nothing here is a rule about values: a size is
// not a shape, and a host cannot choose the sizes it is sent.

import type { BendList, BendMap, BendMaybe, Err, Json, NumberBits, Raw, Step, Why } from "../dist-core/core.mjs";

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
// Measured, not guessed (with bend 2.0.35 on a macOS arm64 Mac, each shape in
// its own process). Each shape below is the largest count where toRaw, check0,
// conforms0, enc and dec all return in bun, and what the next step throws:
//
//   flat list       30000   check0: RangeError
//   nested object    6257   check0: RangeError
//   nested list      6257   check0: RangeError
//   list of lists   29929   survived the largest count tried
//   list of objects 29929   survived the largest count tried
//   mixed           15224   survived the largest count tried
//   flat object      6656   check0: RangeError (25 probes, 903 s)
//
// The binding shapes are the nested object and the nested list, both at 6257,
// and a value at the budget keeps about 2.0x of margin under them. (On bend
// 2.0.27 the nested object reached about 10,600 and a flat object bound first,
// at 6144, which is why KEYS_MAX exists; the budget was set to half of that,
// 3072, and is kept.) One budget covers lists, objects and nesting alike, and
// what makes it enough is the invariant: toRaw never builds a value whose count
// is past it, so the walk that follows is bounded by it.

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
      // A plain object, and nothing else. A Date, Map, Set or class instance is
      // not JSON, and carries no own enumerable keys, so it would otherwise
      // become an empty REnd -- a value the core would accept as conforming to
      // any object schema with no required key.
      const proto = Object.getPrototypeOf(v);
      if (proto !== Object.prototype && proto !== null) return { $: "RBad" };
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

const numberView = new DataView(new ArrayBuffer(8));

function numberBits(v: number): NumberBits | null {
  if (!Number.isFinite(v)) return null;
  numberView.setFloat64(0, v, false);
  const bits = { $: "NumberBits" as const, hi: numberView.getUint32(0, false), lo: numberView.getUint32(4, false) };
  return Object.is(bitsNumber(bits), v) ? bits : null;
}

function bitsNumber(bits: NumberBits): number {
  numberView.setUint32(0, bits.hi, false);
  numberView.setUint32(4, bits.lo, false);
  return numberView.getFloat64(0, false);
}

// Internal seam for the JSON branch of host input. Failures retain the same
// boundary markers as toRaw, so index can attach them without accepting an
// invalid Json value.
export function toJsonRaw(v: unknown): Raw {
  let left = BUDGET;
  const active = new WeakSet<object>();
  const build = (value: unknown): Json | Raw => {
    if (value === null) return { $: "JNull" };
    if (typeof value === "boolean") return { $: "JBool", value };
    if (typeof value === "number") {
      const bits = numberBits(value);
      return bits === null || !Number.isFinite(bitsNumber(bits)) ? { $: "RBad" } : { $: "JNumber", value: bits };
    }
    if (typeof value === "string") return { $: "JString", value };
    if (Array.isArray(value)) {
      if (value.length > left || active.has(value)) return value.length > left ? { $: "RTooBig" } : { $: "RBad" };
      left -= value.length;
      active.add(value);
      const items = Array.from(value, build);
      active.delete(value);
      if (items.some((item) => item.$ === "RBad" || item.$ === "RTooBig")) {
        return items.find((item) => item.$ === "RTooBig") ?? { $: "RBad" };
      }
      let values: BendList<Json> = { $: "Nil" };
      for (let i = items.length - 1; i >= 0; i--) values = { $: "Con", head: items[i] as Json, tail: values };
      return { $: "JArray", values };
    }
    if (typeof value === "object") {
      const proto = Object.getPrototypeOf(value);
      if (proto !== Object.prototype && proto !== null) return { $: "RBad" };
      if (active.has(value)) return { $: "RBad" };
      const entries = Object.entries(value as object);
      if (entries.length > KEYS_MAX || entries.length > left) return { $: "RTooBig" };
      left -= entries.length;
      active.add(value);
      const values = entries.map(([key, child]) => [key, build(child)] as const);
      active.delete(value);
      const bad = values.find(([, child]) => child.$ === "RTooBig" || child.$ === "RBad");
      if (bad) return bad[1].$ === "RTooBig" ? bad[1] : { $: "RBad" };
      const leaves: BendMap<Json>[] = values.map(([key, child]) => ({ $: "MLeaf", key, val: child as Json }));
      const mapTree = (lo: number, hi: number): BendMap<Json> => {
        if (lo >= hi) return { $: "MTip" };
        if (hi - lo === 1) return leaves[lo];
        const mid = lo + Math.floor((hi - lo) / 2);
        return { $: "MNode", pos: BigInt(mid), lo: mapTree(lo, mid), hi: mapTree(mid, hi) };
      };
      return { $: "JObject", values: mapTree(0, leaves.length) };
    }
    return { $: "RBad" };
  };
  const result = build(v);
  return result.$ === "RBad" || result.$ === "RTooBig" ? result : { $: "RJson", value: result as Json };
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
    case "NotJson":
      return "must be a JSON value";
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
