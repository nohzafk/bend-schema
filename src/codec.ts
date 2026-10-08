// The universal codec: any JS value, as the schema check takes it.
//
// It knows no schema, so it decides nothing about shapes: a whole number from 0
// to the runtime's Nat bound (2^48-1) is RNum, a whole number from -(2^48-1)
// to -1 is RNeg{n} with n = -v-1, a boolean RBool, null RNull, a
// string RStr, an array a chain of RCons, a plain object a chain of RKey in its
// own key order, and anything else (a fraction, a number past either bound, NaN, undefined, a
// Date or any other non-plain object) is RBad, for check to report where it
// sits. Every rule about shapes is the proved core's (LAWS.bend).
//
// Depth is the one thing it decides, because it is the one thing the core
// cannot: nesting costs one native JS frame per level. So the codec counts the
// level of each container -- see DEPTH_MAX -- and puts one RTooBig in place of
// the array or object that nests too deep, which the core reports as TooLarge
// at that node's path. Width is not limited: the core and this codec walk the
// elements of a container in a loop, and the time grows with the input, which
// the host's body-size limit bounds. Nothing here is a rule about values: a
// size is not a shape, and a host cannot choose the sizes it is sent.

import type { BendList, BendMaybe, Err, Int, Json, JMember, NumberBits, Raw, Step, Why } from "../dist-core/core.mjs";

// The largest Nat the runtime holds: bend's own Nat.add(Nat.mul(65535,
// 4294967295 + 1), 4294967295). A number past it is not a Nat at all, so it
// is not a value the core can be given.
export const NAT_MAX = 2 ** 48 - 1;

// One rule, two ways out: the runtime holds v as a Nat, or it does not.
const natFit = (v: number): boolean => Number.isSafeInteger(v) && v >= 0 && v <= NAT_MAX;

// The smallest integer SInt reads: the negatives mirror the Nat bound, RNeg{n}
// holding -(n+1) for n from 0 to NAT_MAX-1.
export const INT_MIN = -NAT_MAX;
const negFit = (v: number): boolean => Number.isSafeInteger(v) && v < 0 && v >= INT_MIN;

/** A JS integer as the core's Int, or null when SInt cannot hold it. */
export function intOf(v: number): Int | null {
  if (natFit(v)) return { $: "IPos", n: BigInt(v) };
  if (negFit(v)) return { $: "INeg", n: BigInt(-v - 1) };
  return null;
}

/** The core's Int as a JS number. */
export const intNumber = (i: Int): number => (i.$ === "IPos" ? Number(i.n) : -Number(i.n) - 1);

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

// The deepest a list or object may nest: the outermost container is level 1.
// The core and this codec walk the elements of a container in a loop, but go
// one level down by a JavaScript call, so nesting is what uses the stack.
// A container below this level is RTooBig. 128 is serde_json's default, a
// little above the 100 of protobufjs and protobuf-es; a protocol message nests
// a few dozen levels at most.
//
// Width costs time, not stack, and the time is linear in the input for a given
// schema: the core finds each field by a scan of the object, so one object
// costs fields x keys lookups, and the sender controls only the keys; an
// s.json() position is one pass over its value. Measured with
// `bun src/measure.ts` (bend 2.0.36, bend-emit 0.3.5, bun 1.4.2, Apple M3 Max,
// one run each): one object of 1,000,000 keys checks in about 0.85 s against a
// 16-field schema and 0.33 s through s.json(); a flat list of 1,000,000
// numbers in 0.19 s. A limit on width would only restate the host's body-size
// limit, so there is none.
export const DEPTH_MAX = 128;

export function toRaw(v: unknown): Raw {
  let depth = 0;
  const build = (v: unknown): Raw => {
    if (v === null) return { $: "RNull" };
    if (typeof v === "number") return natFit(v) ? { $: "RNum", n: BigInt(v) } : negFit(v) ? { $: "RNeg", n: BigInt(-v - 1) } : { $: "RBad" };
    if (typeof v === "boolean") return { $: "RBool", b: v };
    if (typeof v === "string") return { $: "RStr", s: v };
    if (Array.isArray(v)) {
      if (depth >= DEPTH_MAX) return { $: "RTooBig" };
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
      if (depth >= DEPTH_MAX) return { $: "RTooBig" };
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
// `depth0` is the level v sits at: encode passes it, so that one value's
// s.json() positions share its depth with the rest of it.
export function toJsonRaw(v: unknown, depth0 = 0): Raw {
  let depth = depth0;
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
      if (depth >= DEPTH_MAX) return { $: "RTooBig" };
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
      if (depth >= DEPTH_MAX) return { $: "RTooBig" };
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

// "a, b or c"; "a or b"; "a".
function kindList(kinds: [boolean, string][]): string {
  const names = kinds.filter(([on]) => on).map(([, name]) => name);
  return names.length < 2 ? names.join("") : `${names.slice(0, -1).join(", ")} or ${names[names.length - 1]}`;
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
    case "NotInt":
      return `must be a whole number from ${INT_MIN} to ${NAT_MAX}`;
    case "IntNotIn":
      return `must be from ${intNumber(w.lo)} to ${intNumber(w.hi)}`;
    case "NoAlternative":
      return `must be ${kindList([[w.num, "a whole number"], [w.str, "a string"], [w.bool, "a boolean"], [w.list, "a list"], [w.obj, "an object"], [w.null, "null"]])}`;
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
