describe("the JSON host codec", () => {
  const jsonValue = (raw: Raw) => raw.$ === "RJson" ? raw.value : null;

  test("encodes finite numbers as binary64 bits without losing negative zero", () => {
    for (const value of [-0, -12, 1.5, 2 ** 48, 2 ** 53 + 1]) {
      const raw = toJsonRaw(value);
      expect(raw.$).toBe("RJson");
      const json = jsonValue(raw);
      expect(json?.$).toBe("JNumber");
      if (json?.$ === "JNumber") {
        const view = new DataView(new ArrayBuffer(8));
        view.setFloat64(0, value, false);
        expect(json.value).toEqual({ $: "NumberBits", hi: view.getUint32(0, false), lo: view.getUint32(4, false) });
      }
    }
    expect(Object.is(-0, 0)).toBe(false);
    expect(toJsonRaw(NaN)).toEqual({ $: "RBad" });
    expect(toJsonRaw(Infinity)).toEqual({ $: "RBad" });
    expect(toJsonRaw(-Infinity)).toEqual({ $: "RBad" });
  });

  test("builds empty and nested JSON containers, including __proto__ safely", () => {
    expect(toJsonRaw([])).toEqual({ $: "RJson", value: { $: "JArray", values: { $: "Nil" } } });
    expect(toJsonRaw({})).toEqual({ $: "RJson", value: { $: "JObject", members: { $: "Nil" } } });
    const proto = JSON.parse('{"__proto__":{"safe":true}}') as unknown;
    const raw = toJsonRaw(proto);
    expect(raw.$).toBe("RJson");
    const json = jsonValue(raw);
    expect(json?.$).toBe("JObject");
    if (json?.$ === "JObject") expect(json.members).toEqual({ $: "Con", head: { $: "JMember", key: "__proto__", value: { $: "JObject", members: { $: "Con", head: { $: "JMember", key: "safe", value: { $: "JBool", value: true } }, tail: { $: "Nil" } } } }, tail: { $: "Nil" } });
    const nullProto = Object.create(null) as Record<string, unknown>;
    nullProto.x = [null, "s"];
    expect(toJsonRaw(nullProto).$).toBe("RJson");
  });

  test("the core refuses an object that holds a name twice, and a non-finite number", () => {
    const num = { $: "JNumber" as const, value: { $: "NumberBits" as const, hi: 0, lo: 0 } };
    const member = (key: string) => ({ $: "JMember" as const, key, value: num });
    const list = (...xs: ReturnType<typeof member>[]): BendList<ReturnType<typeof member>> =>
      xs.reduceRight<BendList<ReturnType<typeof member>>>((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });
    const json: Schema = { $: "SJson" };
    const at = (members: BendList<ReturnType<typeof member>>): Raw => ({ $: "RJson", value: { $: "JObject", members } });
    expect(check(json, at(list(member("a"), member("b"))))).toEqual({ $: "None" });
    expect(check(json, at(list(member("a"), member("b"), member("a")))).$).toBe("Some");
    expect(conforms0(json, at(list(member("a"), member("a"))))).toBe(false);
    const nan: Raw = { $: "RJson", value: { $: "JNumber", value: { $: "NumberBits", hi: 0x7ff80000, lo: 0 } } };
    expect(check(json, nan).$).toBe("Some");
  });

  test("preserves the codec size and non-JSON boundaries", () => {
    expect(toJsonRaw(Array.from({ length: BUDGET + 1 }, () => null))).toEqual({ $: "RTooBig" });
    expect(toJsonRaw(Object.fromEntries(Array.from({ length: KEYS_MAX + 1 }, (_, i) => [`k${i}`, null])))).toEqual({ $: "RTooBig" });
    expect(toJsonRaw({ value: undefined })).toEqual({ $: "RBad" });
    expect(toJsonRaw(new Date())).toEqual({ $: "RBad" });
    const cyclic: { self?: unknown } = {};
    cyclic.self = cyclic;
    expect(toJsonRaw(cyclic)).toEqual({ $: "RBad" });
  });
});

// The codec and the proved check, at run time: what reaches the core, and what
// comes back.
//
// The budget is the part of this file that is not just a test: nothing in the
// proved core knows a size, so the codec's counting is what keeps a message's
// cost bounded, and the gate has to fail if a value at the budget no longer
// converts whole and walks. The shapes come from measure_budget.ts, so the
// numbers in codec.ts and the gate cannot drift.

import { describe, expect, test } from "bun:test";
import * as kernel from "../dist-core/core.mjs";
import { check0 as check, conforms0, type BendList, type BendMaybe, type Raw, type Schema } from "../dist-core/core.mjs";
import { BUDGET, DEPTH_MAX, KEYS_MAX, NAT_MAX, errText, nat as hostNat, toJsonRaw, toRaw } from "./codec";
import { s } from "./index";
import { SHAPES, unbudgeted as before, type Case } from "./measure_budget";

// enc and dec compute a type from a value (Meaning(s)), so bend-emit
// leaves them undeclared in dist-core/core.d.mts: these are their run-time types.
const { enc, dec } = kernel as unknown as {
  enc: (s: Schema, x: unknown) => Raw;
  dec: (s: Schema, r: Raw) => BendMaybe<unknown>;
};

const nat: Schema = { $: "SNat" };
const end: Schema = { $: "SEnd" };
const first = (s: Schema, v: unknown) => {
  const r = check(s, toRaw(v));
  return r.$ === "None" ? null : errText(r.value);
};

// What the budget counts, read back from a Raw: one per element, one per key,
// over every level (RTooBig holds nothing). It also says whether the codec
// gave up on a node.
function measure(r: Raw): { count: number; tooBig: boolean } {
  let count = 0;
  let tooBig = false;
  const stack: Raw[] = [r];
  while (stack.length > 0) {
    const x = stack.pop() as Raw;
    if (x.$ === "RCons") {
      count += 1;
      stack.push(x.head, x.tail);
    } else if (x.$ === "RKey") {
      count += 1;
      stack.push(x.val, x.rest);
    } else if (x.$ === "RTooBig") {
      tooBig = true;
    }
  }
  return { count, tooBig };
}

// The largest scale a shape builds within the budget, and that case: a count is
// what the budget counts, so "one past" is a count, not a scale.
function atBudget(shape: (n: number) => Case): { scale: number; c: Case } {
  let lo = 1;
  let hi = BUDGET;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (shape(mid).count <= BUDGET) lo = mid;
    else hi = mid - 1;
  }
  return { scale: lo, c: shape(lo) };
}

describe("the codec decides nothing about shapes", () => {
  test("numbers the Nat cannot hold are RBad, for check to place", () => {
    expect(toRaw(1.5)).toEqual({ $: "RBad" });
    expect(toRaw(-1)).toEqual({ $: "RBad" });
    expect(toRaw(2 ** 48)).toEqual({ $: "RBad" });
    expect(toRaw(true)).toEqual({ $: "RBool", b: true });
    expect(toRaw(undefined)).toEqual({ $: "RBad" });
    expect(toRaw(2 ** 48 - 1)).toEqual({ $: "RNum", n: 2n ** 48n - 1n });
  });
});

describe("the budget", () => {
  // Every shape but the flat object, which KEYS_MAX caps long before the
  // budget; it has its own test below.
  const BUDGETED = Object.entries(SHAPES).filter(([name]) => name !== "flat object");
  test("a value at the budget converts whole and walks, for every measured shape", () => {
    for (const [name, shape] of BUDGETED) {
      const { c } = atBudget(shape);
      const r = toRaw(c.value);
      // Nothing was given up on, and what the codec built is the count the
      // budget counts: the codec's own number and the value's agree.
      expect({ name, ...measure(r) }).toEqual({ name, count: c.count, tooBig: false });
      expect(conforms0(c.schema, r)).toBe(true);
      expect(check(c.schema, r)).toEqual({ $: "None" });
      expect(dec(c.schema, r).$).toBe("Some");
      expect(enc(c.schema, c.meaning)).toBeDefined();
    }
  });

  test("a value past the budget still walks: nothing over the budget is built", () => {
    for (const [name, shape] of BUDGETED) {
      let n = atBudget(shape).scale + 1;
      while (shape(n).count <= BUDGET) n += 1;
      const c = shape(n);
      const r = toRaw(c.value);
      const m = measure(r);
      // The codec gave up on a node, and what it did build is within the
      // budget: that, not the input, is what the walks are bounded by.
      expect({ name, over: m.count <= BUDGET, gaveUp: m.tooBig }).toEqual({ name, over: true, gaveUp: true });
      // and the core reports it rather than crashing
      const res = check(c.schema, r);
      expect(res.$ === "None" ? "nothing" : res.value.why.$).toBe("TooLarge");
    }
  });

  test("one past the budget is TooLarge at the node's path", () => {
    const list: Schema = { $: "SList", elem: nat };
    const lists: Schema = { $: "SList", elem: list };
    const field: Schema = { $: "SField", name: "a", s: list, rest: end };
    // the value itself, an element, the element of a list of lists, a field's
    const zeros = (n: number) => Array.from({ length: n }, () => 0);
    expect(first(list, zeros(BUDGET + 1))).toBe("the value: too large");
    expect(first(list, [...zeros(BUDGET - 1), [0, 0, 0]])).toBe(`[${BUDGET - 1}]: too large`);
    expect(first(lists, [zeros(BUDGET)])).toBe("[0]: too large");
    const inField = check(field, toRaw({ a: zeros(BUDGET + 1) }));
    expect(inField.$ === "None" ? "nothing" : errText(inField.value, "req")).toBe("req.a: too large");
  });

  test("the budget runs out at the first node past it, in reading order", () => {
    const lists: Schema = { $: "SList", elem: { $: "SList", elem: nat } };
    const half = Array.from({ length: BUDGET / 2 }, () => 0);
    // [half, half] counts 2 + BUDGET: the second list is the one past it
    expect(first(lists, [half, half])).toBe("[1]: too large");
  });

  test("an object past KEYS_MAX is TooLarge, and one at it walks fast", () => {
    const at = SHAPES["flat object"](KEYS_MAX);
    const r = toRaw(at.value);
    const t = performance.now();
    expect(conforms0(at.schema, r)).toBe(true);
    expect(check(at.schema, r)).toEqual({ $: "None" });
    expect(dec(at.schema, r).$).toBe("Some");
    expect(performance.now() - t).toBeLessThan(1000);
    const over = SHAPES["flat object"](KEYS_MAX + 1);
    const res = check(over.schema, toRaw(over.value));
    expect(res.$ === "None" ? "nothing" : errText(res.value)).toBe("the value: too large");
    expect(first({ $: "SList", elem: nat }, [0, 0])).toBe(null);
  });

  test("below the budget the conversion is the one it always was", () => {
    let deep: unknown = 0;
    // 60 rounds of an object and a list: 120 levels, inside DEPTH_MAX
    for (let i = 0; i < DEPTH_MAX / 2 - 4; i++) deep = { a: [deep] };
    const values: unknown[] = [null, true, false, 0, 1.5, -1, 2 ** 48, 2 ** 48 - 1, "", "hi", [], {}, [[]], [[[[]]]], undefined, { a: { b: [1, "x", null] } }, deep];
    for (const v of values) expect(toRaw(v)).toEqual(before(v));
    // And at the budget's own size, where the counting is doing the most work:
    // the flat list is one element per count, so its at-budget value is the
    // longest one a single call can build.
    const at = Array.from({ length: BUDGET }, () => 1);
    expect(measure(toRaw(at))).toEqual({ count: BUDGET, tooBig: false });
    // toEqual recurses down the chain, so the comparison is made on a prefix
    const some = at.slice(0, 3000);
    expect(toRaw(some)).toEqual(before(some));
    // one level past DEPTH_MAX is where the conversion stops
    expect(toRaw(nest(DEPTH_MAX))).toEqual(before(nest(DEPTH_MAX)));
    expect(JSON.stringify(toRaw(nest(DEPTH_MAX + 1)))).toContain("RTooBig");
  });
});

// A list nested d levels: the outermost is level 1, the empty innermost level d.
function nest(d: number): unknown {
  let v: unknown = [];
  for (let i = 1; i < d; i++) v = [v];
  return v;
}

function nestSchema(d: number) {
  let sc: any = s.list(s.nat());
  for (let i = 1; i < d; i++) sc = s.list(sc);
  return sc as ReturnType<typeof s.list<any>>;
}

const zeros = (n: number) => Array.from({ length: n }, () => 0);
const issue = (r: { ok: boolean; error?: { text(): string } }) => (r.ok ? "ok" : r.error!.text());

describe("the depth limit", () => {
  test("a value DEPTH_MAX deep converts whole, and one level more is TooLarge at the first too-deep container", () => {
    expect(measure(toRaw(nest(DEPTH_MAX)))).toEqual({ count: DEPTH_MAX - 1, tooBig: false });
    expect(measure(toRaw(nest(DEPTH_MAX + 1))).tooBig).toBe(true);
    const lists = nestSchema(DEPTH_MAX);
    expect(first(lists.node as never, nest(DEPTH_MAX))).toBe(null);
    // the container at level DEPTH_MAX + 1 sits behind DEPTH_MAX indexes
    expect(first(lists.node as never, nest(DEPTH_MAX + 1))).toBe("[0]".repeat(DEPTH_MAX) + ": too large");
  });

  test("an object counts as a level too", () => {
    let v: unknown = {};
    for (let i = 1; i < DEPTH_MAX; i++) v = { a: v };
    expect(measure(toRaw(v)).tooBig).toBe(false);
    expect(measure(toRaw({ a: v })).tooBig).toBe(true);
  });

  test("through parse: a typed schema and s.json() accept DEPTH_MAX and refuse one more", () => {
    const typed = nestSchema(DEPTH_MAX);
    expect(issue(typed.parse(nest(DEPTH_MAX)))).toBe("ok");
    expect(issue(typed.parse(nest(DEPTH_MAX + 1)))).toBe("[0]".repeat(DEPTH_MAX) + ": too large");
    expect(issue(s.json().parse(nest(DEPTH_MAX)))).toBe("ok");
    // a JSON success value carries no marker inside it, so the error sits at
    // the s.json() position
    expect(issue(s.json().parse(nest(DEPTH_MAX + 1)))).toBe("the value: too large");
    expect(issue(s.object({ a: s.json() }).parse({ a: nest(DEPTH_MAX) }))).toBe("a: too large");
  });
});

describe("the budget over s.json() positions", () => {
  test("two s.json() fields do not each get a fresh budget (W3.g)", () => {
    const o = s.object({ l: s.list(s.nat()), a: s.json(), b: s.json() });
    const big = [zeros(BUDGET - 2)]; // BUDGET - 1 counted: nested one level down
    const r = o.parse({ l: zeros(BUDGET - 3000), a: big, b: big });
    expect(r.ok).toBe(false);
    expect(issue(r)).toBe("a: too large");
    // alone, a value of that size fits
    expect(issue(o.parse({ l: [], a: [zeros(BUDGET - 10)], b: [] }))).toBe("ok");
  });

  test("a cycle at an s.json() position is not JSON, not too large", () => {
    const cyc: unknown[] = [];
    cyc.push(cyc);
    expect(issue(s.object({ a: s.json() }).parse({ a: cyc }))).toBe("a: must be a JSON value");
    expect(issue(s.json().parse(cyc))).toBe("the value: must be a JSON value");
  });

  test("a non-JSON leaf beside a size marker in one s.json() position is not JSON", () => {
    // toRaw marks the inner array too large (the list took the budget), and
    // the NaN makes the position not JSON: not-JSON is what parse reports.
    const o = s.object({ l: s.list(s.nat()), a: s.json() });
    expect(issue(o.parse({ l: zeros(BUDGET - 5), a: [zeros(10), NaN] }))).toBe("a: must be a JSON value");
  });
});

describe("encode applies the same limits (W3.c)", () => {
  // What encode writes is checked as parse would check it; nothing is walked
  // one JavaScript call per element, and nesting is only as deep as the schema.
  const throwsSize = (f: () => unknown, msg: string) => {
    let err: unknown;
    try { f(); } catch (e) { err = e; }
    expect(err instanceof RangeError).toBe(false);
    expect(String(err)).toContain(msg);
  };
  test("a value past the budget or DEPTH_MAX throws the size error, never RangeError", () => {
    throwsSize(() => s.list(s.nat()).encode(zeros(BUDGET + 1)), "bend-schema: encode: the value: too large");
    throwsSize(() => s.list(s.nat()).encode(zeros(1_000_000)), "bend-schema: encode: the value: too large");
    throwsSize(() => nestSchema(DEPTH_MAX + 1).encode(nest(DEPTH_MAX + 1) as never), "too large");
    throwsSize(() => s.json().encode(nest(DEPTH_MAX + 1) as never), "bend-schema: encode: the value: too large");
    throwsSize(() => s.json().encode(zeros(BUDGET + 1) as never), "bend-schema: encode: the value: too large");
    // at the limits it writes
    expect(() => s.list(s.nat()).encode(zeros(BUDGET))).not.toThrow();
    expect(() => nestSchema(DEPTH_MAX).encode(nest(DEPTH_MAX) as never)).not.toThrow();
    expect(() => s.json().encode(nest(DEPTH_MAX) as never)).not.toThrow();
  });

  test("what the schema does not write is not counted: encode accepts what parse accepts", () => {
    const o = s.object({ a: s.nat() });
    const extra = { a: 1, deep: nest(DEPTH_MAX + 50), wide: zeros(BUDGET + 1) };
    expect(issue(o.parse(extra))).toBe("ok");
    expect(o.encode(extra as never)).toEqual({ a: 1 });
  });

  test("work is bounded by the limits, not by what shared references expand to", () => {
    // n^3 nodes from three n-slot arrays: refused at the budget, fast.
    for (const n of [200, 1000]) {
      const v = Array(n).fill(Array(n).fill(Array(n).fill(0)));
      const t = performance.now();
      throwsSize(() => s.list(s.list(s.list(s.nat()))).encode(v), "too large");
      expect(performance.now() - t).toBeLessThan(500);
    }
    // s.json() positions share the value's one budget
    const t = performance.now();
    throwsSize(() => s.list(s.json()).encode(Array(100).fill(zeros(BUDGET - 1)) as never), "bend-schema: encode: [0]: too large");
    expect(performance.now() - t).toBeLessThan(500);
  });

  test("a sparse array is refused by its length, not written as []", () => {
    const t = performance.now();
    throwsSize(() => s.list(s.nat()).encode(new Array(1e9)), "bend-schema: encode: the value: too large");
    throwsSize(() => s.list(s.nat()).encode(new Array(BUDGET + 1)), "bend-schema: encode: the value: too large");
    expect(performance.now() - t).toBeLessThan(500);
  });

  test("a tagged value's unwritten properties cost nothing, however many", () => {
    const o: Record<string, unknown> = { t: "a" };
    for (let i = 0; i < 20000; i++) o["k" + i] = i;
    const t = performance.now();
    const out = s.list(s.tagged("t", { a: s.object({}) })).encode(Array(50000).fill(o) as never);
    expect((out as unknown[]).length).toBe(50000);
    expect(performance.now() - t).toBeLessThan(1000);
  });

  test("the tag key counts toward the budget", () => {
    // each element writes one key, its tag: BUDGET/2 elements + BUDGET/2 keys
    const tg = s.list(s.tagged("t", { a: s.object({}) }));
    expect(() => tg.encode(Array(BUDGET / 2).fill({ t: "a" }) as never)).not.toThrow();
    throwsSize(() => tg.encode(Array(BUDGET / 2 + 1).fill({ t: "a" }) as never), "too large");
  });

  test("an optional field left undefined is not counted", () => {
    const o = s.list(s.object({ a: s.nat().optional() }));
    expect(() => o.encode(Array(BUDGET).fill({}) as never)).not.toThrow();
    throwsSize(() => o.encode(Array(BUDGET / 2 + 1).fill({ a: 1 }) as never), "too large");
  });

  test("an s.json() position shares the budget with its typed siblings, and is named", () => {
    const tp = s.tuple(s.list(s.nat()), s.json());
    // 2 (tuple) + 50000 + 49998 = 100000
    expect(() => tp.encode([zeros(50000), zeros(49998)] as never)).not.toThrow();
    expect(tp.parse([zeros(50000), zeros(49998)]).ok).toBe(true);
    throwsSize(() => tp.encode([zeros(50000), zeros(49999)] as never), "bend-schema: encode: [1]: too large");
    expect(tp.parse([zeros(50000), zeros(49999)]).ok).toBe(false);
  });

  test("depth through tagged and oneKey: 128 levels encode and parse, 129 do not", () => {
    const deepTagged = (d: number): { schema: any; value: any } => {
      let schema: any = s.tagged("t", { a: s.object({}) });
      let value: any = { t: "a" };
      for (let i = 1; i < d; i++) {
        schema = s.tagged("t", { a: s.object({ c: schema }) });
        value = { t: "a", c: value };
      }
      return { schema, value };
    };
    const deepOneKey = (d: number): { schema: any; value: any } => {
      let schema: any = s.oneKey({ k: s.nat() });
      let value: any = { k: 1 };
      for (let i = 1; i < d; i++) {
        schema = s.oneKey({ k: schema });
        value = { k: value };
      }
      return { schema, value };
    };
    for (const mk of [deepTagged, deepOneKey]) {
      const at = mk(DEPTH_MAX);
      expect(issue(at.schema.parse(at.value))).toBe("ok");
      expect(() => at.schema.encode(at.value)).not.toThrow();
      const past = mk(DEPTH_MAX + 1);
      expect(issue(past.schema.parse(past.value))).toContain("too large");
      throwsSize(() => past.schema.encode(past.value), "too large");
    }
  });

  test("the size error names where it was hit", () => {
    throwsSize(() => s.object({ a: s.list(s.nat()) }).encode({ a: zeros(BUDGET + 1) }), "bend-schema: encode: a: too large");
  });

  test("a cycle at an s.json() position is not JSON on encode too", () => {
    const cyc: unknown[] = [];
    cyc.push(cyc);
    throwsSize(() => s.json().encode(cyc as never), "bend-schema: encode: the value: must be a JSON value");
  });
});

describe("oneKey with a long object", () => {
  test("the chosen key after 250 others still yields its value", () => {
    const sch = s.oneKey({ a: s.nat(), pick: s.json() });
    const v: Record<string, unknown> = {};
    for (let i = 0; i < 250; i++) v["x" + i] = i;
    v.pick = { n: [1, { m: null }] };
    expect(sch.parse(v)).toEqual({ ok: true, value: { pick: { n: [1, { m: null }] } } });
    // the replaced value is the one checked: 1.5 is JSON, and parses
    v.pick = 1.5;
    expect(sch.parse(v)).toEqual({ ok: true, value: { pick: 1.5 } });
  });
});

describe("the check at run time", () => {
  test("a list of numbers reports the element that is wrong", () => {
    const r = check({ $: "SList", elem: nat }, toRaw([1, 2, -3]));
    expect(r.$ === "None" ? null : errText(r.value)).toBe("[2]: must be a whole number from 0 to 281474976710655");
  });
});

// The three constructors a host can build without a Bend program: SBool,
// SNatIn{lo, hi} and SStrLen{lo, hi, s}. Each one's laws are in LAWS.bend
// (sbool_meaning, snat_in_meaning, sstr_len_meaning), so what is tested here
// is the run-time side: the reason a value is refused, and what enc writes.
describe("a bound a host can write", () => {
  const bool: Schema = { $: "SBool" };
  const inSix: Schema = { $: "SNatIn", lo: 1n, hi: 6n };
  const three: Schema = { $: "SStrLen", lo: 1n, hi: 3n, s: { $: "SStr" } };
  const names = (...ns: string[]): Schema => {
    let l: BendList<string> = { $: "Nil" };
    for (let i = ns.length - 1; i >= 0; i--) l = { $: "Con", head: ns[i], tail: l };
    return { $: "SEnum", names: l };
  };

  test("SBool accepts both booleans, and says so of anything else", () => {
    expect(conforms0(bool, toRaw(true))).toBe(true);
    expect(conforms0(bool, toRaw(false))).toBe(true);
    expect(first(bool, true)).toBe(null);
    expect(first(bool, false)).toBe(null);
    expect(first(bool, 0)).toBe("the value: must be a boolean");
    expect(first(bool, "true")).toBe("the value: must be a boolean");
    expect(first(bool, null)).toBe("the value: must be a boolean");
    expect(first({ $: "SList", elem: bool }, [true, 1])).toBe("[1]: must be a boolean");
    expect(conforms0({ $: "SList", elem: bool }, toRaw([true, false]))).toBe(true);
  });

  test("SNatIn accepts the numbers in its bounds, both ends included", () => {
    expect(conforms0(inSix, toRaw(1))).toBe(true);
    expect(conforms0(inSix, toRaw(6))).toBe(true);
    expect(conforms0(inSix, toRaw(0))).toBe(false);
    expect(first(inSix, 0)).toBe("the value: must be from 1 to 6");
    expect(first(inSix, 7)).toBe("the value: must be from 1 to 6");
    // a value that is not a number at all is refused as one
    expect(first(inSix, "3")).toBe("the value: must be a whole number from 0 to 281474976710655");
    expect(first({ $: "SField", name: "n", s: inSix, rest: end }, {})).toBe(".n: missing");
  });

  test("lo past hi is an empty range, not an error: nothing is in bounds", () => {
    const none: Schema = { $: "SNatIn", lo: 3n, hi: 1n };
    expect(conforms0(none, toRaw(0))).toBe(false);
    expect(conforms0(none, toRaw(1))).toBe(false);
    expect(conforms0(none, toRaw(2))).toBe(false);
    expect(first(none, 2)).toBe("the value: must be from 3 to 1");
    // and the same for a string
    const noLength: Schema = { $: "SStrLen", lo: 2n, hi: 1n, s: { $: "SStr" } };
    expect(conforms0(noLength, toRaw("a"))).toBe(false);
    expect(first(noLength, "a")).toBe("the value: must be 2 to 1 characters long");
  });

  test("SStrLen is a string in the bounds that also satisfies its schema", () => {
    expect(conforms0(three, toRaw("a"))).toBe(true);
    expect(conforms0(three, toRaw("abc"))).toBe(true);
    expect(conforms0(three, toRaw(""))).toBe(false);
    expect(first(three, "")).toBe("the value: must be 1 to 3 characters long");
    expect(first(three, "abcd")).toBe("the value: must be 1 to 3 characters long");
    // the shape comes first, as at every kind
    expect(first(three, 1)).toBe("the value: must be a string");
    // the schema it wraps is checked too
    const named: Schema = { $: "SStrLen", lo: 2n, hi: 2n, s: names("ab", "cd") };
    expect(first(named, "ab")).toBe(null);
    expect(first(named, "cd")).toBe(null);
    expect(first(named, "ef")).toBe("the value: is not one of the allowed names");
    // the schema the value must satisfy is checked first, as at a rule
    expect(first(named, "a")).toBe("the value: is not one of the allowed names");
  });

  test("the three constructors round-trip through enc and dec", () => {
    expect(dec(bool, enc(bool, true))).toEqual({ $: "Some", value: true });
    expect(dec(bool, enc(bool, false))).toEqual({ $: "Some", value: false });
    // A Nat is a number on this side of the door -- nat(name, v), NAT_MAX and
    // toJs all take one, and only the wire (Raw) holds a BigInt -- so the round
    // trip is stated over a number, and it is exact.
    expect(dec(inSix, enc(inSix, 6))).toEqual({ $: "Some", value: 6 });
    // A Nat that went in as a BigInt comes back as a number, and this line says
    // so: dec's return type is the type family Meaning(s), which bend's marshal
    // has no type to convert by, so the runtime's own value leaves unchanged
    // (bendlang/bend#1150). The value is exact either way -- a Nat is at most
    // 2^48-1 < 2^53 -- and when upstream converts it, this line is what fails.
    expect(dec(inSix, enc(inSix, 6n))).toEqual({ $: "Some", value: 6 });
    expect(dec(three, enc(three, "abc"))).toEqual({ $: "Some", value: "abc" });
  });

  test("a value outside a bound is written out as it is, and check refuses it", () => {
    // encode_conforms carries the bound as a premise (LAWS.bend): the encoder
    // writes the meaning unchanged, and a host that holds a value past a bound
    // is the one at fault -- parse reports it, with the bound's own reason.
    expect(dec(three, enc(three, "abcd"))).toEqual({ $: "Some", value: "abcd" });
    const r = check(three, enc(three, "abcd"));
    expect(r.$ === "None" ? null : errText(r.value)).toBe("the value: must be 1 to 3 characters long");
  });
});

describe("the host-side Nat guard", () => {
  // nat is toRaw's RNum rule thrown rather than reported, so the two must
  // agree on where the bound is: the same numbers, one as RNum/RBad, one as v
  // or a refusal. A host that writes a number into the core's input needs the
  // refusal before it builds anything, and the message must name the field,
  // the bound and the value.
  test("it returns the value where toRaw says RNum, and refuses where it says RBad", () => {
    for (const v of [0, 1, 2 ** 48 - 1, NAT_MAX]) {
      expect(hostNat("units", v)).toBe(v);
      expect(toRaw(v)).toEqual({ $: "RNum", n: BigInt(v) });
    }
    for (const v of [2 ** 48, -1, 1.5, NaN, Infinity, 2 ** 53]) {
      expect(toRaw(v)).toEqual({ $: "RBad" });
      expect(() => hostNat("units", v)).toThrow();
    }
  });

  test("NAT_MAX is the largest the runtime holds, and the refusal names all three", () => {
    expect(NAT_MAX).toBe(2 ** 48 - 1);
    expect(hostNat("units", NAT_MAX)).toBe(NAT_MAX);
    expect(() => hostNat("units", NAT_MAX + 1)).toThrow(`units must be a whole number from 0 to ${NAT_MAX} (units=${NAT_MAX + 1})`);
  });
});
