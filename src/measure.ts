// What one message costs in time, measured rather than guessed.
//
// Nothing limits the width of a value: the core walks a list or an object in a
// loop, nesting is capped at DEPTH_MAX, so the stack bounds nothing, and what
// is left is how long check0, conforms0, enc and dec take. This runs every
// shape at two scales and prints how long each call took, then shows that the
// time is linear in the input for a fixed schema: one object of more and more
// keys against 16 fields, and a flat list of more and more numbers.
//
//   bun src/measure.ts
//
// The shapes are exported for codec.test.ts, which holds the codec against them
// (a large value converts whole and every walk returns), so the numbers in
// codec.ts, the README and the gate are one set of shapes. The timing is not
// run by the tests.
//
// Each time is one run, in milliseconds, from the converted value to the
// walk's return. toRaw is the codec's own conversion.

import * as kernel from "../dist-core/core.mjs";
import { check0, conforms0, type BendMaybe, type Raw, type Schema } from "../dist-core/core.mjs";
import { DEPTH_MAX, toRaw } from "./codec";
import { s } from "./index";

// enc and dec compute a type from a value (Meaning(s)), so bend-emit
// leaves them undeclared in dist-core/core.d.mts: these are their run-time types.
const { enc, dec } = kernel as unknown as {
  enc: (s: Schema, x: unknown) => unknown;
  dec: (s: Schema, r: unknown) => BendMaybe<unknown>;
};

const nat: Schema = { $: "SNat" };
const end: Schema = { $: "SEnd" };

// A list as the module encodes one, built from the tail so the stack stays flat.
function bList<T>(xs: T[]): unknown {
  let out: unknown = { $: "Nil" };
  for (let i = xs.length - 1; i >= 0; i--) out = { $: "Con", head: xs[i], tail: out };
  return out;
}

// A record of n fields, all SNat: the schema, the object, and its meaning.
function record(n: number) {
  let schema: Schema = end;
  let meaning: unknown = { $: "Unit" };
  const obj: Record<string, number> = {};
  for (let i = n - 1; i >= 0; i--) {
    schema = { $: "SField", name: "k" + i, s: nat, rest: schema };
    meaning = { $: "Both", a: 0n, b: meaning };
    obj["k" + i] = 0;
  }
  return { schema, obj, meaning };
}

export type Case = { schema: Schema; value: unknown; meaning: unknown; count: number };

// rows of `width` keys each, `rows` as many as n counts allow (a row counts
// width + 1: its key count and itself as an element).
function objects(n: number, width: number): Case {
  const cols = Math.max(1, Math.min(width, n - 1));
  const rows = Math.max(1, Math.floor(n / (cols + 1)));
  const one = record(cols);
  return {
    schema: { $: "SList", elem: one.schema },
    value: Array.from({ length: rows }, () => ({ ...one.obj })),
    meaning: bList(Array.from({ length: rows }, () => one.meaning)),
    count: rows * (cols + 1),
  };
}

// Each shape takes one scale -- its own unit: elements, rows -- and reports the
// count the codec would make of it.
export const SHAPES: Record<string, (n: number) => Case> = {
  "flat list": (n) => ({
    schema: { $: "SList", elem: nat },
    value: Array.from({ length: n }, () => 0),
    meaning: bList(Array.from({ length: n }, () => 0n)),
    count: n,
  }),
  "flat object": (n) => {
    const r = record(n);
    return { schema: r.schema, value: r.obj, meaning: r.meaning, count: n };
  },
  "list of lists": (n) => {
    const rows = Math.max(1, Math.round(Math.sqrt(n)));
    const cols = Math.max(1, Math.floor(n / rows) - 1);
    return {
      schema: { $: "SList", elem: { $: "SList", elem: nat } },
      value: Array.from({ length: rows }, () => Array.from({ length: cols }, () => 0)),
      meaning: bList(Array.from({ length: rows }, () => bList(Array.from({ length: cols }, () => 0n)))),
      count: rows * (cols + 1),
    };
  },
  // objects of 16 keys: a typical record
  "list of objects": (n) => objects(n, 16),
  // objects of 256 keys, against a schema of 256 fields: fields x keys
  // lookups per object, the most a typed schema costs per key
  "list of wide objects": (n) => objects(n, 256),
  mixed: (n) => {
    const rows = Math.max(1, Math.round(Math.sqrt(n)));
    const cols = Math.max(1, Math.floor(n / rows) - 2);
    const inner: Schema = { $: "SList", elem: nat };
    return {
      schema: { $: "SList", elem: { $: "SField", name: "a", s: inner, rest: end } },
      value: Array.from({ length: rows }, () => ({ a: Array.from({ length: cols }, () => 0) })),
      meaning: bList(Array.from({ length: rows }, () => ({ $: "Both", a: bList(Array.from({ length: cols }, () => 0n)), b: { $: "Unit" } }))),
      count: rows * (cols + 2),
    };
  },
  // DEPTH_MAX levels of lists, one element each down to the last level, which
  // is wide: the deepest value, with the most breadth at the bottom.
  "deep and wide": (n) => {
    const m = Math.max(1, n - (DEPTH_MAX - 1));
    let schema: Schema = { $: "SList", elem: nat };
    let value: unknown = Array.from({ length: m }, () => 0);
    let meaning: unknown = bList(Array.from({ length: m }, () => 0n));
    for (let i = 1; i < DEPTH_MAX; i++) {
      schema = { $: "SList", elem: schema };
      value = [value];
      meaning = bList([meaning]);
    }
    return { schema, value, meaning, count: m + DEPTH_MAX - 1 };
  },
};

// The codec's conversion with no depth check: the walk the codec made before
// it had one. codec.test.ts compares toRaw against this, for the claim that
// nothing inside DEPTH_MAX changed.
export function unbudgeted(v: unknown): Raw {
  const NAT_MAX = 2 ** 48 - 1;
  if (v === null) return { $: "RNull" };
  if (typeof v === "number") {
    if (!Number.isSafeInteger(v) || Math.abs(v) > NAT_MAX) return { $: "RBad" };
    return v >= 0 ? { $: "RNum", n: BigInt(v) } : { $: "RNeg", n: BigInt(-v - 1) };
  }
  if (typeof v === "boolean") return { $: "RBool", b: v };
  if (typeof v === "string") return { $: "RStr", s: v };
  if (Array.isArray(v)) return v.reduceRight<Raw>((tail, h) => ({ $: "RCons", head: unbudgeted(h), tail }), { $: "RNil" });
  if (typeof v === "object") return Object.entries(v as object).reduceRight<Raw>((rest, [key, val]) => ({ $: "RKey", key, val: unbudgeted(val), rest }), { $: "REnd" });
  return { $: "RBad" };
}

const ms = (f: () => unknown): number => {
  const t = performance.now();
  f();
  return performance.now() - t;
};

// The five calls on a case, each in milliseconds.
function time(c: Case): Record<string, number> {
  let r: Raw = { $: "RNil" };
  const out: Record<string, number> = {};
  out.toRaw = ms(() => (r = toRaw(c.value)));
  out.check0 = ms(() => check0(c.schema, r));
  out.conforms0 = ms(() => conforms0(c.schema, r));
  out.enc = ms(() => enc(c.schema, c.meaning));
  out.dec = ms(() => dec(c.schema, r));
  return out;
}

const cols = ["toRaw", "check0", "conforms0", "enc", "dec"];
const row = (name: string, count: number, t: Record<string, number>) =>
  console.log(name.padEnd(30) + String(count).padStart(9) + cols.map((k) => (t[k] === undefined ? "-" : t[k]!.toFixed(0)).padStart(11)).join(""));

if (import.meta.main) {
  console.log(`depth ${DEPTH_MAX}; milliseconds, one run each`);
  for (const scale of [100_000, 1_000_000]) {
    console.log("\nscale " + scale + "\n" + "shape".padEnd(30) + "count".padStart(9) + cols.map((k) => k.padStart(11)).join(""));
    for (const [name, shape] of Object.entries(SHAPES)) {
      // a flat object of n keys against n fields is n^2 lookups: the one shape
      // whose schema grows with the value, so the linearity table below
      // covers objects instead
      if (name === "flat object") continue;
      const c = shape(scale);
      row(name, c.count, time(c));
    }
  }

  // Linear in the input for a fixed schema: the sender controls the keys, the
  // developer the fields, and each key costs about `fields` lookups.
  const f16 = record(16).schema;
  console.log("\none object against 16 fields" + "\n" + "keys".padEnd(12) + "check0 ms".padStart(11) + "us/key".padStart(11));
  for (const k of [1_000, 10_000, 100_000, 1_000_000]) {
    const r = toRaw(record(k).obj);
    const t = ms(() => check0(f16, r));
    console.log(String(k).padEnd(12) + t.toFixed(0).padStart(11) + ((t / k) * 1000).toFixed(2).padStart(11));
  }

  // The worst case through the public API, which is what a host calls: a list
  // of 256-key objects against s.json(), against a schema of 256 fields, and
  // against the same schema made strict.
  const wide = SHAPES["list of wide objects"]!(100_000);
  const fields: Record<string, ReturnType<typeof s.nat>> = {};
  for (let i = 0; i < 256; i++) fields["k" + i] = s.nat();
  const typed = s.list(s.object(fields));
  const rows: [string, any][] = [
    ["s.json()", s.json()],
    ["s.list(256 fields)", typed],
    ["... .strict()", s.list(s.object(fields).strict())],
  ];
  console.log("\nwide objects, public API: " + wide.count + " counted\n" + "schema".padEnd(30) + "parse".padStart(11) + "encode".padStart(11));
  for (const [name, schema] of rows) {
    let parsed: any;
    const p = ms(() => (parsed = schema.parse(wide.value)));
    if (!parsed.ok) throw new Error(`${name}: ${parsed.error}`);
    const e = ms(() => schema.encode(parsed.value));
    console.log(name.padEnd(30) + p.toFixed(0).padStart(11) + e.toFixed(0).padStart(11));
  }
}
