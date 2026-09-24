// How large a value the walks survive, measured rather than guessed.
//
// The compiled JS of check0, conforms0, enc and dec costs one native JS frame
// per list element, per object key and per level of nesting, so a long value
// throws RangeError. The budget the codec enforces (BUDGET in codec.ts) is half
// the largest total this reports, where the total is what the codec counts:
// list elements plus object keys, summed over the whole value.
//
//   bun measure_budget.ts
//
// This measures the backend, so it converts values with the codec's walk and
// none of its counting (unbudgeted, below): through the codec itself every
// value past the budget would come back as one RTooBig, and the walks' own
// limit could never be reached. The codec's budget is a policy about that
// limit, and this is what the limit is.
//
// Per shape, the largest scale where all five calls return, and what the next
// step throws. A shape that survives the cap says nothing about the budget:
// the budget is half the smallest of these, and the smallest is the shape with
// the most nesting per counted element.
//
// codec.test.ts imports the shapes from here and holds the budget against
// them, so the number in codec.ts, the table in the README and the gate cannot
// drift apart: they are one set of shapes and one measurement.
//
// The search is per shape, on the shape's own scale, and a shape reports the
// count it actually built. The cap keeps a shape that is nowhere near the
// limit (a list of short objects, say) from being searched to millions: what
// such a shape survives is not the budget's business.
//
// A full run takes a few minutes, and the flat object is nearly all of it: a
// walk over an object costs one lookup per field and each lookup scans from
// the front, so probing near its edge costs half a minute per probe. The
// per-shape probe count and time go to stderr, the table to stdout.

import * as kernel from "../dist-core/core.js";
import { check0, conforms0, type BendMaybe, type Raw, type Schema } from "../dist-core/core.js";
import { BUDGET } from "./codec";

// enc and dec compute a type from a value (Meaning(s)), so tools/bend_lib.ts
// leaves them undeclared in dist-core/core.d.ts: these are their run-time types.
const { enc, dec } = kernel as unknown as {
  enc: (s: Schema, x: unknown) => unknown;
  dec: (s: Schema, r: unknown) => BendMaybe<unknown>;
};

const CAP = 30_000; // past every shape's edge; the smallest edge is what counts
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

// Each shape takes one scale -- its own unit: elements, rows, depth -- and
// reports the count the codec would make of it.
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
  "list of objects": (n) => {
    const rows = Math.max(1, Math.round(Math.sqrt(n)));
    const cols = Math.max(1, Math.floor(n / rows) - 1);
    const one = record(cols);
    return {
      schema: { $: "SList", elem: one.schema },
      value: Array.from({ length: rows }, () => ({ ...one.obj })),
      meaning: bList(Array.from({ length: rows }, () => one.meaning)),
      count: rows * (cols + 1),
    };
  },
  mixed: (n) => {
    const rows = Math.max(1, Math.round(Math.sqrt(n)));
    const cols = Math.max(1, Math.floor(n / (2 * rows)));
    const inner: Schema = { $: "SList", elem: nat };
    return {
      schema: { $: "SList", elem: { $: "SField", name: "a", s: inner, rest: end } },
      value: Array.from({ length: rows }, () => ({ a: Array.from({ length: cols }, () => 0) })),
      meaning: bList(Array.from({ length: rows }, () => ({ $: "Both", a: bList(Array.from({ length: cols }, () => 0n)), b: { $: "Unit" } }))),
      count: 2 * rows + rows * cols,
    };
  },
  "nested object": (n) => {
    let schema: Schema = nat;
    let value: unknown = 0;
    let meaning: unknown = 0n;
    for (let i = 0; i < n; i++) {
      schema = { $: "SField", name: "a", s: schema, rest: end };
      value = { a: value };
      meaning = { $: "Both", a: meaning, b: { $: "Unit" } };
    }
    return { schema, value, meaning, count: n };
  },
  "nested list": (n) => {
    let schema: Schema = nat;
    let value: unknown = 0;
    let meaning: unknown = 0n;
    for (let i = 0; i < n; i++) {
      schema = { $: "SList", elem: schema };
      value = [value];
      meaning = bList([meaning]);
    }
    return { schema, value, meaning, count: n };
  },
};

// The codec's conversion with none of its counting: the walk the codec made
// before it had a budget. codec.test.ts compares toRaw against this, for the
// claim that nothing below the budget changed.
export function unbudgeted(v: unknown): Raw {
  const NAT_MAX = 2 ** 48 - 1;
  if (v === null) return { $: "RNull" };
  if (typeof v === "number") return Number.isSafeInteger(v) && v >= 0 && v <= NAT_MAX ? { $: "RNum", n: BigInt(v) } : { $: "RBad" };
  if (typeof v === "boolean") return { $: "RBool", b: v };
  if (typeof v === "string") return { $: "RStr", s: v };
  if (Array.isArray(v)) return v.reduceRight<Raw>((tail, h) => ({ $: "RCons", head: unbudgeted(h), tail }), { $: "RNil" });
  if (typeof v === "object") return Object.entries(v as object).reduceRight<Raw>((rest, [key, val]) => ({ $: "RKey", key, val: unbudgeted(val), rest }), { $: "REnd" });
  return { $: "RBad" };
}

// Which of the five throws, and with what. null when all of them return.
function walk(c: Case): string | null {
  let r: Raw;
  try {
    r = unbudgeted(c.value);
  } catch (e) {
    return `converting: ${e instanceof RangeError ? "RangeError" : String(e)}`;
  }
  const calls: [string, () => unknown][] = [
    ["check0", () => check0(c.schema, r)],
    ["conforms0", () => conforms0(c.schema, r)],
    ["enc", () => enc(c.schema, c.meaning as never)],
    ["dec", () => dec(c.schema, r)],
  ];
  for (const [name, f] of calls) {
    try {
      f();
    } catch (e) {
      return `${name}: ${e instanceof RangeError ? "RangeError" : String(e)}`;
    }
  }
  return null;
}

// The largest scale where all five return, and the count it built.
function edge(name: string, shape: (n: number) => Case): { count: number; over: string } {
  const t0 = Date.now();
  let probes = 0;
  const ok = (n: number) => {
    probes += 1;
    return walk(shape(n)) === null;
  };
  let lo = 1;
  let hi = 2;
  while (hi <= CAP && ok(hi)) {
    lo = hi;
    hi *= 2;
  }
  if (hi <= CAP) {
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (ok(mid)) lo = mid;
      else hi = mid - 1;
    }
  } else lo = CAP;
  const over = walk(shape(lo + 1)) ?? "nothing (at the cap)";
  const secs = ((Date.now() - t0) / 1000).toFixed(1);
  console.error(`  ${name}: ${probes} probes, ${secs} s`);
  console.log(`${name.padEnd(16)} ${String(shape(lo).count).padStart(7)} counted, next throws ${over}`);
  return { count: shape(lo).count, over };
}

// codec.test.ts imports the shapes above; only a run measures.
if (import.meta.main) {
  let worst = Infinity;
  for (const [name, shape] of Object.entries(SHAPES)) worst = Math.min(worst, edge(name, shape).count);
  console.log(`\nsmallest count a shape survives: ${worst}; half of it is ${Math.floor(worst / 2)}`);
  console.log(`the codec's budget: ${BUDGET}`);
}
