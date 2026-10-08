// bend-schema's TypeScript face: build a schema with `s`, then call
// `.parse`, `.check` or `.encode` on it. What is proved is the core's
// (core/LAWS.bend): which values a schema accepts, the first error and its
// path, and that dec reads what enc writes. What is NOT proved lives here: the
// builder (a mirror of the core's Schema constructors), the conversion between
// the core's Meaning values and plain JS, and `.refine()` predicates, whose
// errors say `proved: false`.

import * as core from "../dist-core/core.mjs";
import type { BendList, Json as CoreJson, Schema as Node, Step } from "../dist-core/core.mjs";
import { BUDGET, DEPTH_MAX, INT_MIN, NAT_MAX, intNumber, intOf, toJsonRaw, toRaw, whyText } from "./codec";

// enc and dec return a type computed from the schema (Meaning(s)), which
// bend-emit cannot write as a TS signature; they are untyped here.
const { enc, dec } = core as unknown as { enc: (s: Node, m: unknown) => core.Raw; dec: (s: Node, r: core.Raw) => core.BendMaybe<unknown> };

export { BUDGET, DEPTH_MAX, INT_MIN, KEYS_MAX, NAT_MAX, nat, toRaw } from "./codec";
export type { Raw } from "../dist-core/core.mjs";

/** JSON values exposed by the builder are ordinary JavaScript values. */
export type Json = null | boolean | number | string | Json[] | { [key: string]: Json };

// ------------------------------------------------------------------ issues

export type PathPart = string | number;

/** The first error: where it is, and why. `proved: true` came from the core;
 * `proved: false` from a `.refine()` predicate. */
export class Issue {
  constructor(
    readonly path: PathPart[],
    readonly message: string,
    readonly proved: boolean,
  ) {}

  /** "plan.tiers[3].up: must be ..." -- `where` names the value. */
  text(where = ""): string {
    const p = this.path.map((x) => (typeof x === "number" ? `[${x}]` : `.${x}`)).join("");
    const at = (where + p).replace(/^\./, "") || "the value";
    return `${at}: ${this.message}`;
  }

  toString(): string {
    return this.text();
  }
}

export type Result<T> = { ok: true; value: T } | { ok: false; error: Issue };

// ---------------------------------------------------------------- the builder

type Kind =
  | { k: "nat" }
  | { k: "natIn"; lo: number; hi: number }
  | { k: "int" }
  | { k: "intIn"; lo: number; hi: number }
  | { k: "str" }
  | { k: "strLen"; lo: number; hi: number; inner: Schema<string> }
  | { k: "bool" }
  | { k: "true" }
  | { k: "json" }
  | { k: "nullable"; inner: Schema<any> }
  | { k: "optional"; inner: Schema<any> }
  | { k: "list"; elem: Schema<any> }
  | { k: "listLen"; lo: number; hi: number; inner: Schema<any[]> }
  | { k: "tuple"; items: Schema<any>[] }
  | { k: "object"; fields: [string, Schema<any>][] }
  | { k: "strict"; obj: Schema<any> }
  | { k: "enum"; names: string[] }
  | { k: "oneKey"; cases: [string, Schema<any>][] }
  | { k: "tagged"; key: string; cases: [string, Schema<any>][] };

type Refinement = { fn: (x: any) => boolean; why: string };

export class Schema<T> {
  declare readonly _T: T;
  /** @internal */ readonly kind: Kind;
  /** @internal */ readonly refines: Refinement[];
  private cached?: Node;

  /** @internal */ constructor(kind: Kind, refines: Refinement[] = []) {
    this.kind = kind;
    this.refines = refines;
  }

  /** A host-side predicate, run after the proved check passes. Not proved:
   * its error carries `proved: false`. Keeps the schema's own methods. */
  refine(fn: (x: T) => boolean, why: string): this {
    const Ctor = this.constructor as new (k: Kind, r: Refinement[]) => this;
    return new Ctor(this.kind, [...this.refines, { fn, why }]);
  }

  /** null or this. The key must still be present. */
  nullable(): Schema<T | null> {
    return new Schema<T | null>({ k: "nullable", inner: this });
  }

  /** The key may be absent. Only valid as an object field. */
  optional(): Optional<T> {
    return new Optional<T>({ k: "optional", inner: this });
  }

  /** Check v, then read it as T. */
  parse(v: unknown): Result<T> {
    const node = this.node;
    const raw = rawFor(this, v, toRaw(v));
    const e = core.check0(node, raw);
    if (e.$ === "Some") return { ok: false, error: new Issue(pathOf(e.value.path), whyText(e.value.why), true) };
    const m = dec(node, raw);
    if (m.$ !== "Some") throw new Error("bend-schema: dec refused a value check0 accepted (a bug in the core)");
    const value = toJs(this, m.value) as T;
    const r = refineAt(this, value, []);
    return r ? { ok: false, error: r } : { ok: true, value };
  }

  /** The first error, or null. */
  check(v: unknown): Issue | null {
    const r = this.parse(v);
    return r.ok ? null : r.error;
  }

  /** Write x as plain JSON-ready JS; parse reads it back. Throws when x breaks
   * a bound or a refinement, which its type cannot rule out. */
  encode(x: T): unknown {
    const out = rawToJs(enc(this.node, toMeaning(this, x, { left: BUDGET, depth: 0, path: [] })));
    // An absent top-level value is legitimate for an Optional schema, and
    // JSON has no way to write it, so it stays undefined rather than throwing.
    if (out === undefined) return undefined;
    const e = this.check(out);
    if (e) throw new Error(`bend-schema: encode: ${e.text()}`);
    return out;
  }

  /** The core's Schema value. Throws if the core finds it ill-formed. */
  get node(): Node {
    if (!this.cached) {
      const n = toNode(this);
      if (!core.wf(n)) {
        throw new Error(
          "bend-schema: ill-formed schema (a duplicate key, a nullable inside a nullable, " +
            ".optional() outside an object field, or .strict() on a non-object)",
        );
      }
      this.cached = n;
    }
    return this.cached;
  }
}

/** A field that may be absent. */
export class Optional<T> extends Schema<T | undefined> {
  declare readonly _optional: true;
}

export class NatSchema extends Schema<number> {
  /** lo <= n <= hi, both ends included. */
  in(lo: number, hi: number): NatSchema {
    return new NatSchema({ k: "natIn", lo: whole(lo), hi: whole(hi) }, this.refines);
  }
}

export class IntSchema extends Schema<number> {
  /** lo <= n <= hi, both ends included; either may be negative. */
  in(lo: number, hi: number): IntSchema {
    return new IntSchema({ k: "intIn", lo: bound(lo), hi: bound(hi) }, this.refines);
  }
}

export class StrSchema extends Schema<string> {
  /** lo <= length <= hi, both ends included. */
  len(lo: number, hi: number): StrSchema {
    return new StrSchema({ k: "strLen", lo: whole(lo), hi: whole(hi), inner: this });
  }
}

export class ListSchema<T> extends Schema<T[]> {
  /** lo <= element count <= hi, both ends included. */
  len(lo: number, hi: number): ListSchema<T> {
    return new ListSchema<T>({ k: "listLen", lo: whole(lo), hi: whole(hi), inner: this });
  }
}

export class ObjectSchema<T> extends Schema<T> {
  /** Refuse keys this object does not name (by default they are dropped). */
  strict(): ObjectSchema<T> {
    return new ObjectSchema<T>({ k: "strict", obj: this });
  }
}

// An integer bound: one SInt can hold, so that the schema says what it means.
function bound(n: number): number {
  if (intOf(n) === null) throw new Error(`bend-schema: an integer bound must be a whole number from ${INT_MIN} to ${NAT_MAX}, got ${n}`);
  return n;
}

// A value written at an SInt. One SInt cannot hold is a host's mistake its type
// cannot rule out, like a bound broken, so encode refuses it.
function intMeaning(v: number): core.Int {
  const i = typeof v === "number" ? intOf(v) : null;
  if (i === null) throw new Error(`bend-schema: encode: ${String(v)} is not a whole number from ${INT_MIN} to ${NAT_MAX}`);
  return i;
}

function whole(n: number): number {
  if (!Number.isSafeInteger(n) || n < 0) throw new Error(`bend-schema: a bound must be a whole number >= 0, got ${n}`);
  return n;
}

type Shape = Record<string, Schema<any>>;
type Simplify<T> = { [K in keyof T]: T[K] } & {};
type OptKeys<S extends Shape> = { [K in keyof S]: S[K] extends Optional<any> ? K : never }[keyof S];
type ObjOf<S extends Shape> = Simplify<
  { [K in Exclude<keyof S, OptKeys<S>>]: Infer<S[K]> } & { [K in OptKeys<S>]?: Exclude<Infer<S[K]>, undefined> }
>;
type Union<S extends Shape> = { [K in keyof S]: { [P in K]: Infer<S[K]> } }[keyof S];
type TaggedUnion<K extends string, S extends Record<string, ObjectSchema<any>>> = {
  [N in keyof S]: Simplify<{ [P in K]: N } & Infer<S[N]>>;
}[keyof S];

export type Infer<X> = X extends Schema<infer T> ? T : never;

export const s = {
  nat: () => new NatSchema({ k: "nat" }),
  int: () => new IntSchema({ k: "int" }),
  str: () => new StrSchema({ k: "str" }),
  bool: () => new Schema<boolean>({ k: "bool" }),
  true: () => new Schema<true>({ k: "true" }),
  json: () => new Schema<Json>({ k: "json" }),
  list: <T>(elem: Schema<T>) => new ListSchema<T>({ k: "list", elem }),
  tuple: <A extends Schema<any>[]>(...items: A) =>
    new Schema<{ [I in keyof A]: Infer<A[I]> }>({ k: "tuple", items }),
  object: <S extends Shape>(shape: S) => new ObjectSchema<ObjOf<S>>({ k: "object", fields: Object.entries(shape) }),
  enum: <const N extends readonly [string, ...string[]]>(names: N) => new Schema<N[number]>({ k: "enum", names: [...names] }),
  oneKey: <S extends Shape>(cases: S) => new Schema<Union<S>>({ k: "oneKey", cases: Object.entries(cases) }),
  tagged: <K extends string, S extends Record<string, ObjectSchema<any>>>(key: K, cases: S) =>
    new Schema<TaggedUnion<K, S>>({ k: "tagged", key, cases: Object.entries(cases) }),
};

// `s.Infer<typeof x>` reads as `Infer<typeof x>`.
export declare namespace s {
  type Infer<X> = X extends Schema<infer T> ? T : never;
}

function toNode(x: Schema<any>): Node {
  const k = x.kind;
  switch (k.k) {
    case "nat": return { $: "SNat" };
    case "natIn": return { $: "SNatIn", lo: BigInt(k.lo), hi: BigInt(k.hi) };
    case "int": return { $: "SInt" };
    case "intIn": return { $: "SIntIn", lo: intOf(k.lo)!, hi: intOf(k.hi)! };
    case "str": return { $: "SStr" };
    case "strLen": return { $: "SStrLen", lo: BigInt(k.lo), hi: BigInt(k.hi), s: toNode(k.inner) };
    case "bool": return { $: "SBool" };
    case "true": return { $: "STrue" };
    case "json": return { $: "SJson" };
    case "nullable": return { $: "SOpt", inner: toNode(k.inner) };
    case "optional": return { $: "SOptional", inner: toNode(k.inner) };
    case "listLen": return { $: "SListLen", lo: BigInt(k.lo), hi: BigInt(k.hi), s: toNode(k.inner) };
    case "list": return { $: "SList", elem: toNode(k.elem) };
    case "tuple": return k.items.reduceRight<Node>((rest, it) => ({ $: "STuple", s: toNode(it), rest }), { $: "STEnd" });
    case "object": return k.fields.reduceRight<Node>((rest, [name, f]) => ({ $: "SField", name, s: toNode(f), rest }), { $: "SEnd" });
    case "strict": return { $: "SStrict", s: toNode(k.obj) };
    case "enum": return { $: "SEnum", names: k.names.reduceRight<BendList<string>>((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" }) };
    case "oneKey": return k.cases.reduceRight<Node>((rest, [name, c]) => ({ $: "SVariant", name, s: toNode(c), rest }), { $: "SVEnd" });
    case "tagged": return k.cases.reduceRight<Node>((rest, [name, c]) => ({ $: "STagged", key: k.key, name, s: toNode(c), rest }), { $: "STagEnd", key: k.key });
  }
}

function rawAtKey(raw: core.Raw, name: string): core.Raw {
  for (let r = raw; r.$ === "RKey"; r = r.rest) if (r.key === name) return r.val;
  return { $: "RMissing" };
}

// toRaw owns the single whole-value budget and the depth limit. This pass only
// replaces values at SJson positions, and a size marker from that first pass
// anywhere inside one must not be hidden by toJsonRaw's own count, which starts
// afresh: a JSON value carries no marker inside it, so the whole position is
// too large. A value that is not JSON at all (a cycle, NaN) still says so.
function rawFor(x: Schema<any>, v: any, raw: core.Raw): core.Raw {
  const k = x.kind;
  switch (k.k) {
    case "json": {
      if (raw.$ === "RTooBig") return raw;
      const j = toJsonRaw(v);
      return j.$ !== "RBad" && hasTooBig(raw) ? { $: "RTooBig" } : j;
    }
    case "strLen": return rawFor(k.inner, v, raw);
    case "listLen": return rawFor(k.inner, v, raw);
    case "nullable": return v === null ? raw : rawFor(k.inner, v, raw);
    case "optional": return v === undefined ? { $: "RMissing" } : rawFor(k.inner, v, raw);
    case "strict": return rawFor(k.obj, v, raw);
    case "list": {
      if (!Array.isArray(v) || raw.$ !== "RCons" && raw.$ !== "RNil") return raw;
      let r: core.Raw = raw;
      const heads: core.Raw[] = [];
      for (let i = 0; i < v.length; i++) {
        if (r.$ !== "RCons") return raw;
        heads.push(rawFor(k.elem, v[i], r.head));
        r = r.tail;
      }
      if (r.$ !== "RNil") return raw;
      return heads.reduceRight<core.Raw>((tail, head) => ({ $: "RCons", head, tail }), { $: "RNil" });
    }
    case "tuple": {
      if (!Array.isArray(v)) return raw;
      let r: core.Raw = raw;
      const heads: core.Raw[] = [];
      for (const item of k.items) {
        if (r.$ !== "RCons") return raw;
        heads.push(rawFor(item, v[heads.length], r.head));
        r = r.tail;
      }
      if (r.$ !== "RNil") return raw;
      return heads.reduceRight<core.Raw>((tail, head) => ({ $: "RCons", head, tail }), { $: "RNil" });
    }
    case "object": {
      if (raw.$ !== "REnd" && raw.$ !== "RKey") return raw;
      const fields = new Map(k.fields.map(([name, field]) => [name, field]));
      const entries: [string, core.Raw][] = [];
      for (let r: core.Raw = raw; r.$ === "RKey"; r = r.rest) {
        const field = fields.get(r.key);
        entries.push([r.key, field ? rawFor(field, v?.[r.key], r.val) : r.val]);
      }
      return entries.reduceRight<core.Raw>((rest, [key, val]) => ({ $: "RKey", key, val, rest }), { $: "REnd" });
    }
    case "oneKey": {
      if (v === null || typeof v !== "object") return raw;
      const selected = k.cases.find(([name]) => name in v);
      if (!selected) return raw;
      return replaceRawKey(raw, selected[0], rawFor(selected[1], v[selected[0]], rawAtKey(raw, selected[0])));
    }
    case "tagged": {
      if (v === null || typeof v !== "object") return raw;
      const selected = k.cases.find(([name]) => v[k.key] === name);
      if (!selected) return raw;
      return rawFor(selected[1], v, raw);
    }
    default: return raw;
  }
}

// The first key `name` holds `value`; the keys before it are copied, the rest
// shared. A loop: an object's width must not cost stack.
function replaceRawKey(raw: core.Raw, name: string, value: core.Raw): core.Raw {
  const before: core.Raw[] = [];
  let r = raw;
  while (r.$ === "RKey" && r.key !== name) { before.push(r); r = r.rest; }
  if (r.$ !== "RKey") return raw;
  let out: core.Raw = { ...r, val: value };
  for (let i = before.length - 1; i >= 0; i--) out = { ...before[i]!, rest: out } as core.Raw;
  return out;
}

// Whether a size marker sits anywhere in raw. A stack, not recursion: raw's
// depth is bounded by DEPTH_MAX, its width is not.
function hasTooBig(raw: core.Raw): boolean {
  const todo: core.Raw[] = [raw];
  while (todo.length > 0) {
    const r = todo.pop()!;
    if (r.$ === "RTooBig") return true;
    if (r.$ === "RCons") todo.push(r.head, r.tail);
    else if (r.$ === "RKey") todo.push(r.val, r.rest);
  }
  return false;
}


type M = any; // a core Meaning(s) value: number (a Nat), string, boolean, Unit, Both, Either, Maybe, List

const unit = { $: "Unit" };
const both = (a: M, b: M) => ({ $: "Both", a, b });

function bitsToNumber(bits: { hi: number; lo: number }): number {
  const view = new DataView(new ArrayBuffer(8));
  view.setUint32(0, bits.hi, false);
  view.setUint32(4, bits.lo, false);
  return view.getFloat64(0, false);
}

function jsonToJs(value: CoreJson): Json {
  switch (value.$) {
    case "JNull": return null;
    case "JBool": return value.value;
    case "JNumber": return bitsToNumber(value.value);
    case "JString": return value.value;
    case "JArray": {
      const out: Json[] = [];
      for (let xs = value.values; xs.$ === "Con"; xs = xs.tail) out.push(jsonToJs(xs.head));
      return out;
    }
    case "JObject": {
      const out: Record<string, Json> = {};
      for (let xs = value.members; xs.$ === "Con"; xs = xs.tail) put(out, xs.head.key, jsonToJs(xs.head.value));
      return out;
    }
  }
}

function toJs(x: Schema<any>, m: M): unknown {
  const k = x.kind;
  switch (k.k) {
    case "nat": case "natIn": return Number(m);
    case "int": case "intIn": return intNumber(m);
    case "str": case "bool": case "enum": return m;
    case "strLen": return toJs(k.inner, m);
    case "true": return true;
    case "json": return jsonToJs(m as CoreJson);
    case "nullable": return m.$ === "None" ? null : toJs(k.inner, m.value);
    case "optional": return m.$ === "None" ? undefined : toJs(k.inner, m.value);
    case "listLen": return toJs(k.inner, m);
    case "list": { const out = []; for (let l = m; l.$ === "Con"; l = l.tail) out.push(toJs(k.elem, l.head)); return out; }
    case "tuple": { const out = []; let b = m; for (const it of k.items) { out.push(toJs(it, b.a)); b = b.b; } return out; }
    case "object": { const out: Record<string, unknown> = {}; let b = m; for (const [n, f] of k.fields) { const x = toJs(f, b.a); if (x !== undefined) put(out, n, x); b = b.b; } return out; }
    case "strict": return toJs(k.obj, m);
    case "oneKey": { let e = m; for (const [n, c] of k.cases) { if (e.$ === "Inl") return { [n]: toJs(c, e.value) }; e = e.value; } throw new Error("unreachable: Empty"); }
    case "tagged": { let e = m; for (const [n, c] of k.cases) { if (e.$ === "Inl") return { [k.key]: n, ...(toJs(c, e.value) as object) }; e = e.value; } throw new Error("unreachable: Empty"); }
  }
}

// What encode is about to write, within the limits parse applies to it. Every
// container the schema writes is counted before it is walked -- its length,
// or the keys it will write -- against one budget for the whole value, and its
// level against DEPTH_MAX; s.json() positions draw on the same budget. Only
// what is written counts: a property the schema does not name is never seen.
// So the work is bounded by the limits, however far shared references in the
// input would expand, and a sparse array is refused by its length.
type Limit = { left: number; depth: number; path: PathPart[] };

function tooLarge(lim: Limit): never {
  throw new Error(`bend-schema: encode: ${new Issue([...lim.path], "too large", true).text()}`);
}

function enter(lim: Limit, n: number): void {
  if (n > lim.left || lim.depth >= DEPTH_MAX) tooLarge(lim);
  lim.left -= n;
}

function at<R>(lim: Limit, step: PathPart, f: () => R): R {
  lim.path.push(step);
  try { return f(); } finally { lim.path.pop(); }
}

function inside<R>(lim: Limit, f: () => R): R {
  lim.depth++;
  try { return f(); } finally { lim.depth--; }
}

const written = (f: Schema<any>, x: unknown) => !(f.kind.k === "optional" && x === undefined);

function toMeaning(x: Schema<any>, v: any, lim: Limit): M {
  const k = x.kind;
  switch (k.k) {
    case "nat": case "natIn": return BigInt(whole(v));
    case "int": case "intIn": return intMeaning(v);
    case "str": case "bool": case "enum": return v;
    case "strLen": return toMeaning(k.inner, v, lim);
    case "true": return unit;
    case "json": return jsonFromRaw(toJsonRaw(v, lim, lim.depth), lim);
    case "nullable": return v === null ? { $: "None" } : { $: "Some", value: toMeaning(k.inner, v, lim) };
    case "optional": return v === undefined ? { $: "None" } : { $: "Some", value: toMeaning(k.inner, v, lim) };
    case "listLen": return toMeaning(k.inner, v, lim);
    case "list": {
      const xs = v as any[];
      enter(lim, xs.length);
      const heads = inside(lim, () => Array.from(xs, (h, i) => at(lim, i, () => toMeaning(k.elem, h, lim))));
      let out: M = { $: "Nil" };
      for (let i = heads.length - 1; i >= 0; i--) out = { $: "Con", head: heads[i], tail: out };
      return out;
    }
    case "tuple": {
      enter(lim, k.items.length);
      const ms = inside(lim, () => k.items.map((it, i) => at(lim, i, () => toMeaning(it, v[i], lim))));
      return ms.reduceRight((rest: M, m) => both(m, rest), unit);
    }
    case "object": {
      enter(lim, k.fields.filter(([n, f]) => written(f, v[n])).length);
      const ms = inside(lim, () => k.fields.map(([n, f]) => at(lim, n, () => toMeaning(f, v[n], lim))));
      return ms.reduceRight((rest: M, m) => both(m, rest), unit);
    }
    case "strict": return toMeaning(k.obj, v, lim);
    case "oneKey": {
      const i = k.cases.findIndex(([n]) => n in v);
      if (i < 0) throw new Error("bend-schema: encode: no case key present");
      const [n, c] = k.cases[i]!;
      enter(lim, 1);
      return inj(i, inside(lim, () => at(lim, n, () => toMeaning(c, v[n], lim))));
    }
    case "tagged": {
      const i = k.cases.findIndex(([n]) => v[k.key] === n);
      if (i < 0) throw new Error(`bend-schema: encode: unknown tag ${String(v[k.key])}`);
      // The tag key is written beside the case's own fields, in the same
      // object. The case is an object schema that reads only the fields it
      // names, and wf refuses one naming the tag key, so it is given v itself:
      // copying v's other properties would cost work no limit counts.
      enter(lim, 1);
      return inj(i, toMeaning(k.cases[i]![1], v, lim));
    }
  }
}

function jsonFromRaw(raw: core.Raw, lim: Limit): CoreJson {
  if (raw.$ === "RJson") return raw.value;
  // The same two reasons parse gives for an s.json() position, at its path.
  const why = raw.$ === "RTooBig" ? "too large" : "must be a JSON value";
  throw new Error(`bend-schema: encode: ${new Issue([...lim.path], why, true).text()}`);
}

const inj = (i: number, m: M): M => (i === 0 ? { $: "Inl", value: m } : { $: "Inr", value: inj(i - 1, m) });

// `out[n] = x` is a prototype setter for a field named `__proto__`, which would
// silently drop it -- a required field gone from a value parse calls valid, and
// an encode whose own re-check then fails. defineProperty has no such case.
function put(out: Record<string, unknown>, n: string, x: unknown): void {
  Object.defineProperty(out, n, { value: x, enumerable: true, writable: true, configurable: true });
}

function rawToJs(r: core.Raw): unknown {
  switch (r.$) {
    case "RNum": return Number(r.n);
    case "RNeg": return -Number(r.n) - 1;
    case "RBool": return r.b;
    case "RNull": return null;
    case "RStr": return r.s;
    case "RNil": case "RCons": { const out = []; for (let l: core.Raw = r; l.$ === "RCons"; l = l.tail) out.push(rawToJs(l.head)); return out; }
    case "REnd": case "RKey": { const out: Record<string, unknown> = {}; for (let l: core.Raw = r; l.$ === "RKey"; l = l.rest) if (l.val.$ !== "RMissing") put(out, l.key, rawToJs(l.val)); return out; }
    // An absent value is legitimate at the top level of an Optional schema. JSON
    // cannot write it, so it reads as undefined; a nested one never reaches
    // here, because the RKey arm drops it.
    case "RMissing": return undefined;
    case "RJson": return jsonToJs(r.value);
    default: throw new Error(`bend-schema: encode produced ${r.$}`);
  }
}

// --------------------------------------------------------------- issues' paths

function pathOf(p: BendList<Step>): PathPart[] {
  const out: PathPart[] = [];
  for (let x = p; x.$ === "Con"; x = x.tail) {
    const st = x.head;
    if (st.$ === "AtIndex") out.push(Number(st.i));
    else if (st.$ === "AtField") out.push(st.name);
    else if (st.$ === "AtKey") out.push(st.key);
    else out.push(Number(st.i), st.key);
  }
  return out;
}

// Run refinements bottom-up over the parsed value, first failure in reading order.
function refineAt(x: Schema<any>, v: any, path: PathPart[]): Issue | null {
  const k = x.kind;
  const sub = (c: Schema<any>, cv: any, p: PathPart) => refineAt(c, cv, [...path, p]);
  let e: Issue | null = null;
  switch (k.k) {
    case "strLen": e = refineAt(k.inner, v, path); break;
    case "nullable": if (v !== null) e = refineAt(k.inner, v, path); break;
    case "optional": if (v !== undefined) e = refineAt(k.inner, v, path); break;
    case "listLen": e = refineAt(k.inner, v, path); break;
    case "list": for (let i = 0; i < v.length && !e; i++) e = sub(k.elem, v[i], i); break;
    case "tuple": for (let i = 0; i < k.items.length && !e; i++) e = sub(k.items[i]!, v[i], i); break;
    case "object": for (const [n, f] of k.fields) if (!e && !(f.kind.k === "optional" && v[n] === undefined)) e = sub(f, v[n], n); break;
    case "strict": e = refineAt(k.obj, v, path); break;
    case "oneKey": for (const [n, c] of k.cases) if (!e && n in v) e = sub(c, v[n], n); break;
    case "tagged": for (const [n, c] of k.cases) if (!e && v[k.key] === n) e = refineAt(c, v, path); break;
  }
  if (e) return e;
  for (const r of x.refines) if (!r.fn(v)) return new Issue(path, r.why, false);
  return null;
}
