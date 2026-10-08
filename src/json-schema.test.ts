import { describe, expect, test } from "bun:test";
import Ajv2020 from "ajv/dist/2020";
import { INT_MIN, NAT_MAX, s, type Schema } from "./index";
import { DIALECT, toJsonSchema } from "./json-schema";

// ownProperties: ajv otherwise reads `required: ["k"]` as satisfied by an
// inherited property. A key named "__proto__" is still out of ajv's reach: it
// drops that entry of `properties` without a word (ajv 8.20), so the random
// tests below leave that key out, and its own test reads the document instead.
const ajv = new Ajv2020({ strict: true, ownProperties: true });
const def = (o: object, k: string, value: unknown) =>
  Object.defineProperty(o, k, { value, enumerable: true, writable: true, configurable: true });
const passes = (x: Schema<any>, v: unknown): boolean => ajv.validate(toJsonSchema(x), v) as boolean;

// ------------------------------------------------------------ a seeded PRNG

function rng(seed: number) {
  let a = seed >>> 0;
  const next = () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const int = (n: number) => Math.floor(next() * n);
  const pick = <T>(xs: readonly T[]): T => xs[int(xs.length)]!;
  return { next, int, pick };
}
type R = ReturnType<typeof rng>;

// Keys are drawn from a small pool so that fields, tags, oneKey cases and
// stray keys collide often.
const KEYS = ["a", "b", "c", "kind"];
const STRS = ["", "a", "ab", "x", "😀", "😀😀", "\ud800", "kind"];
const NUMS = [0, 1, 2, 5, -1, -5, 0.5, -0, NAT_MAX, NAT_MAX + 1, INT_MIN, INT_MIN - 1, 1e300];

// A random well-formed schema without .refine(): the builder refuses an
// ill-formed one at first use, so a refused draw is drawn again.
function genSchema(r: R, depth: number): Schema<any> {
  for (;;) {
    const x = draw(r, depth);
    try {
      void x.node;
      return x;
    } catch {}
  }
}

function draw(r: R, depth: number): Schema<any> {
  const leaf = depth <= 0 || r.next() < 0.35;
  if (leaf) {
    switch (r.int(9)) {
      case 0: return s.nat();
      case 1: { const lo = r.int(4); return s.nat().in(lo, lo + r.int(4)); }
      case 2: return s.int();
      case 3: { const lo = r.int(8) - 6; return s.int().in(lo, lo + r.int(6)); }
      case 4: return r.next() < 0.5 ? s.str() : s.str().len(r.int(2), 1 + r.int(2));
      case 5: return s.bool();
      case 6: return s.true();
      case 7: return s.enum(["a", r.pick(["x", "ab", "😀"])] as const);
      default: return s.json();
    }
  }
  switch (r.int(7)) {
    case 0: return genSchema(r, depth - 1).nullable();
    case 1: { const l = s.list(genSchema(r, depth - 1)); return r.next() < 0.5 ? l : l.len(r.int(2), 1 + r.int(2)); }
    case 2: return s.tuple(...Array.from({ length: r.int(3) }, () => genSchema(r, depth - 1)));
    case 3: { const o = s.object(fields(r, depth)); return r.next() < 0.4 ? o.strict() : o; }
    case 4: return s.oneKey(Object.fromEntries(distinct(r, 1 + r.int(2)).map((k) => [k, genSchema(r, depth - 1)])));
    default: {
      const cases = Object.fromEntries(["a", "b"].slice(0, 1 + r.int(2)).map((n) => {
        const o = s.object(fields(r, depth));
        return [n, r.next() < 0.4 ? o.strict() : o];
      }));
      return s.tagged("kind", cases as any);
    }
  }
}

function distinct(r: R, n: number): string[] {
  const out = new Set<string>();
  while (out.size < n) out.add(r.pick(KEYS));
  return [...out];
}

function fields(r: R, depth: number): Record<string, Schema<any>> {
  const out: Record<string, Schema<any>> = {};
  for (const k of distinct(r, r.int(3))) {
    const f = genSchema(r, depth - 1);
    def(out, k, r.next() < 0.3 ? f.optional() : f);
  }
  return out;
}

// A JSON value shaped like x often enough to land inside it, and off it often
// enough to land outside.
function genValue(r: R, x: Schema<any>, depth: number): unknown {
  if (depth <= 0 || r.next() < 0.15) return anyJson(r, 1);
  const k = x.kind;
  switch (k.k) {
    case "nat": case "natIn": case "int": case "intIn": return r.next() < 0.7 ? r.int(12) - 6 : r.pick(NUMS);
    case "str": case "strLen": case "enum": return r.pick(STRS);
    case "bool": case "true": return r.next() < 0.5;
    case "json": return anyJson(r, 2);
    case "nullable": return r.next() < 0.3 ? null : genValue(r, k.inner, depth);
    case "optional": return genValue(r, k.inner, depth);
    case "list": case "listLen": {
      const elem = k.k === "list" ? k.elem : (k.inner.kind as { elem: Schema<any> }).elem;
      return Array.from({ length: r.int(4) }, () => genValue(r, elem, depth - 1));
    }
    case "tuple": {
      const n = r.next() < 0.8 ? k.items.length : r.int(4);
      return Array.from({ length: n }, (_, i) => (k.items[i] ? genValue(r, k.items[i]!, depth - 1) : anyJson(r, 1)));
    }
    case "object": case "strict": {
      const fs = k.k === "object" ? k.fields : (k.obj.kind as { fields: [string, Schema<any>][] }).fields;
      return objValue(r, fs, depth);
    }
    case "oneKey": {
      const out: Record<string, unknown> = {};
      for (const [n, c] of k.cases) if (r.next() < 0.6) def(out, n, genValue(r, c, depth - 1));
      if (r.next() < 0.2) out[r.pick(["z", "q"])] = 1;
      return out;
    }
    case "tagged": {
      const [n, c] = r.pick(k.cases);
      const ck = c.kind as any;
      const fs = ck.k === "object" ? ck.fields : ck.obj.kind.fields;
      const out = objValue(r, fs, depth) as Record<string, unknown>;
      if (r.next() < 0.9) def(out, k.key, r.next() < 0.85 ? n : r.pick(["z", 1, null]));
      return out;
    }
  }
}

function objValue(r: R, fs: [string, Schema<any>][], depth: number): unknown {
  const out: Record<string, unknown> = {};
  for (const [n, f] of fs) if (r.next() < 0.85) def(out, n, genValue(r, f, depth - 1));
  if (r.next() < 0.2) def(out, r.pick([...KEYS, "z"]), anyJson(r, 1));
  return out;
}

function anyJson(r: R, depth: number): unknown {
  switch (depth <= 0 ? r.int(4) : r.int(6)) {
    case 0: return null;
    case 1: return r.next() < 0.5;
    case 2: return r.pick(NUMS);
    case 3: return r.pick(STRS);
    case 4: return Array.from({ length: r.int(3) }, () => anyJson(r, depth - 1));
    default: {
      const out: Record<string, unknown> = {};
      for (const k of distinct(r, r.int(3))) def(out, k, anyJson(r, depth - 1));
      return out;
    }
  }
}

// --------------------------------------------------------------------- tests

describe("toJsonSchema", () => {
  test("is a draft 2020-12 document ajv compiles in strict mode", () => {
    const doc = toJsonSchema(s.object({ id: s.nat(), name: s.str().optional() }));
    expect(doc.$schema).toBe(DIALECT);
    expect(() => ajv.compile(doc)).not.toThrow();
  });

  test("an object names its fields; an optional one is not required", () => {
    expect(toJsonSchema(s.object({ id: s.nat(), name: s.str().optional() }))).toEqual({
      $schema: DIALECT,
      type: "object",
      properties: { id: { type: "integer", minimum: 0, maximum: NAT_MAX }, name: { type: "string" } },
      required: ["id"],
      additionalProperties: true,
    });
  });

  test("a JSON-RPC error code: a negative integer range", () => {
    const code = s.int().in(-32768, -32000);
    expect(passes(code, -32601)).toBe(true);
    expect(passes(code, 32601)).toBe(false);
    expect(passes(code, -32600.5)).toBe(false);
  });

  test("a strict tagged case admits its tag and nothing else", () => {
    const x = s.tagged("method", { ping: s.object({ n: s.nat() }).strict() });
    expect(passes(x, { method: "ping", n: 1 })).toBe(true);
    expect(passes(x, { method: "ping", n: 1, extra: 0 })).toBe(false);
    expect(passes(x, { method: "pong", n: 1 })).toBe(false);
  });

  test("a field named __proto__ is a property, not a prototype", () => {
    const x = s.object({ ["__proto__"]: s.nat() } as Record<string, Schema<number>>);
    const doc = toJsonSchema(x) as { properties: object; required: string[] };
    expect(Object.keys(doc.properties)).toEqual(["__proto__"]);
    expect(doc.required).toEqual(["__proto__"]);
  });

  test("an ill-formed schema is refused, as parse refuses it", () => {
    expect(() => toJsonSchema(s.str().nullable().nullable())).toThrow(/ill-formed/);
  });

  test("what JSON Schema cannot say is left out: refine and the size limits", () => {
    const even = s.nat().refine((n) => n % 2 === 0, "must be even");
    expect(passes(even, 3)).toBe(true);
    expect(even.parse(3).ok).toBe(false);
  });
});

describe("toJsonSchema against parse, on random schemas", () => {
  const SCHEMAS = 400;
  const VALUES = 60;

  // The contract: never stricter than parse.
  // Without .refine(), and inside the size limits, also never looser: the
  // document says exactly what parse accepts.
  test(`${SCHEMAS} schemas x ${VALUES} values: accepted by parse <=> passes the document`, () => {
    const r = rng(20261008);
    let accepted = 0;
    let checked = 0;
    for (let i = 0; i < SCHEMAS; i++) {
      const x = genSchema(r, 3);
      const validate = ajv.compile(toJsonSchema(x));
      for (let j = 0; j < VALUES; j++) {
        const v = genValue(r, x, 4);
        const p = x.parse(v).ok;
        const a = validate(v) as boolean;
        if (p !== a) {
          throw new Error(`disagree: parse=${p} jsonschema=${a}\nschema=${JSON.stringify(toJsonSchema(x))}\nvalue=${JSON.stringify(v)}`);
        }
        if (p) accepted++;
        checked++;
      }
    }
    // The generator must land inside often enough for the test to mean something.
    expect(accepted).toBeGreaterThan(checked / 5);
  });

  test("every value encode writes passes the document", () => {
    const r = rng(7);
    let n = 0;
    for (let i = 0; i < SCHEMAS; i++) {
      const x = genSchema(r, 3);
      const validate = ajv.compile(toJsonSchema(x));
      for (let j = 0; j < VALUES; j++) {
        const v = genValue(r, x, 4);
        const p = x.parse(v);
        if (!p.ok) continue;
        const out = x.encode(p.value);
        if (out === undefined) continue;
        expect(validate(out)).toBe(true);
        n++;
      }
    }
    expect(n).toBeGreaterThan(1000);
  });
});
