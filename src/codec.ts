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
// cannot: how long a walk takes grows with the value, and how deep it nests
// costs one native JS frame per level. So the codec counts what a walk would
// cost -- see BUDGET and DEPTH_MAX -- and puts one RTooBig in place of the
// array or object that runs past either, which the core reports as TooLarge at
// that node's path. Nothing here is a rule about values: a size is
// not a shape, and a host cannot choose the sizes it is sent.

import type { BendList, BendMaybe, Err, Json, JMember, NumberBits, Raw, Step, Why } from "../dist-core/core.mjs";

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
// The budget caps the time one message can cost. The stack does not bound the
// total: the core walks a list or an object in a loop, and nesting is capped at
// DEPTH_MAX. Cost is roughly linear in the count, except in objects, where each
// key is looked up by a scan and a walk costs about keys^2; so the worst case
// is many objects at KEYS_MAX keys, and costs about count x KEYS_MAX lookups.
//
// Measured with `bun src/measure_budget.ts` (bend 2.0.35, bend-emit 0.3.4, bun
// 1.4.2, macOS 27.0 arm64, Apple M3 Max, one run each), at a count of about
// 100,000 -- milliseconds:
//
//   shape                  count   check0  conforms0   enc   dec
//   flat list             100000       29         27    15    25
//   list of lists          99856       16         16    14    15
//   list of objects        99994      100         96    15    60   (16 keys each)
//   list of wide objects   99973     1173       1211    13   518   (256 keys each)
//   mixed                  99856       14         14    12    14
//   deep and wide         100000       18         18    11    20
//
// and through the public API, the same wide objects (parse / encode, ms):
//
//   s.json()                   316 / 382
//   256-field schema          1784 / 2024
//   256-field, .strict()      2608 / 2784
//
// So a message at the budget costs tens of milliseconds in the usual shapes and
// at most a few seconds in the worst one. A typed schema costs more than
// s.json() because each of its fields is looked up in each object; the sender
// controls the keys, the developer the fields.

export const BUDGET = 100_000;

// The most keys one object may hold. A limit on time: the core finds each field
// by scanning the object from the front, so walking one object costs about
// keys^2 lookups -- about 65,000 at 256 keys, a couple of milliseconds. Under
// the budget, the objects of one value cost at most about count x KEYS_MAX
// lookups in all (see BUDGET). An object with more keys than this is RTooBig,
// like a value past the budget; a set that large belongs in a list.
export const KEYS_MAX = 256;

// The deepest a list or object may nest: the outermost container is level 1.
// The core and this codec walk the elements of a container in a loop, but go
// one level down by a JavaScript call, so nesting is what still uses the stack.
// A container below this level is RTooBig. 128 is serde_json's default, a
// little above the 100 of protobufjs and protobuf-es; a protocol message nests
// a few dozen levels at most.
export const DEPTH_MAX = 128;

export function toRaw(v: unknown): Raw {
  let left = BUDGET;
  let depth = 0;
  const build = (v: unknown): Raw => {
    if (v === null) return { $: "RNull" };
    if (typeof v === "number") return natFit(v) ? { $: "RNum", n: BigInt(v) } : { $: "RBad" };
    if (typeof v === "boolean") return { $: "RBool", b: v };
    if (typeof v === "string") return { $: "RStr", s: v };
    if (Array.isArray(v)) {
      if (v.length > left || depth >= DEPTH_MAX) return { $: "RTooBig" };
      left -= v.length;
      // Elements are built first to last, so the budget runs out where a
      // reader would expect: at the first node past it, not at the start.
      depth++;
      const heads = v.map(build);
      depth--;
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
      if (entries.length > KEYS_MAX || entries.length > left || depth >= DEPTH_MAX) return { $: "RTooBig" };
      left -= entries.length;
      depth++;
      const vals = entries.map(([key, val]) => [key, build(val)] as const);
      depth--;
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
  let depth = 0;
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
      if (active.has(value)) return { $: "RBad" };
      if (value.length > left || depth >= DEPTH_MAX) return { $: "RTooBig" };
      left -= value.length;
      active.add(value);
      depth++;
      const items = Array.from(value, build);
      depth--;
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
      if (entries.length > KEYS_MAX || entries.length > left || depth >= DEPTH_MAX) return { $: "RTooBig" };
      left -= entries.length;
      active.add(value);
      depth++;
      const values = entries.map(([key, child]) => [key, build(child)] as const);
      depth--;
      active.delete(value);
      const bad = values.find(([, child]) => child.$ === "RTooBig" || child.$ === "RBad");
      if (bad) return bad[1].$ === "RTooBig" ? bad[1] : { $: "RBad" };
      let members: BendList<JMember> = { $: "Nil" };
      for (let i = values.length - 1; i >= 0; i--) {
        const [key, child] = values[i]!;
        members = { $: "Con", head: { $: "JMember", key, value: child as Json }, tail: members };
      }
      return { $: "JObject", members };
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
