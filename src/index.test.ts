// The TS face: builder -> core node, Meaning <-> JS, refinements, paths.
// None of this is proved, so every constructor is round-tripped here.

import { describe, expect, test } from "bun:test";
import { INT_MIN, NAT_MAX, s, type Infer, type Json } from "./index.ts";

const Plan = s.object({
    name: s.str().len(1, 20),
    seats: s.nat().in(1, 500),
    active: s.bool(),
    beta: s.true(),
    tier: s.enum(["free", "pro"]),
    note: s.str().nullable(),
    tags: s.list(s.str()),
    pair: s.tuple(s.nat(), s.str()),
    pay: s.oneKey({ card: s.object({ last4: s.str().len(4, 4) }), invoice: s.object({ days: s.nat() }) }),
    event: s.tagged("type", { open: s.object({ at: s.nat() }), close: s.object({ why: s.str() }) }),
  }).strict();
type Plan = Infer<typeof Plan>;

const good: Plan = {
  name: "acme",
  seats: 10,
  active: false,
  beta: true,
  tier: "pro",
  note: null,
  tags: ["a", "b"],
  pair: [3, "x"],
  pay: { invoice: { days: 30 } },
  event: { type: "close", why: "done" },
};

describe("parse", () => {
  test("a valid value parses to itself", () => {
    expect(Plan.parse(good)).toEqual({ ok: true, value: good });
  });

  test("encode then parse is the identity, every constructor", () => {
    const alt: Plan = { ...good, note: "n", tags: [], pay: { card: { last4: "1234" } }, event: { type: "open", at: 7 } };
    for (const v of [good, alt]) expect(Plan.parse(Plan.encode(v))).toEqual({ ok: true, value: v });
  });

  test("a nullable field must be present: absent is missing", () => {
    const { note: _, ...rest } = good;
    expect<unknown>(Plan.check(rest)).toEqual({ path: ["note"], message: "missing", proved: true });
  });

  test("a non-strict object drops extra keys", () => {
    const P = s.object({ a: s.nat() });
    expect(P.parse({ a: 1, b: 2 })).toEqual({ ok: true, value: { a: 1 } });
  });

  test("strict refuses an extra key, at its path", () => {
    const r = Plan.parse({ ...good, zzz: 1 });
    expect(r.ok).toBe(false);
    if (!r.ok) expect<unknown>(r.error).toEqual({ path: ["zzz"], message: "is not a key this object allows", proved: true });
  });

  test("errors carry the path and the core's reason", () => {
    const e = Plan.check({ ...good, pair: [3, 4] });
    expect<unknown>(e).toEqual({ path: ["pair", 1], message: "must be a string", proved: true });
    expect(e!.text("plan")).toBe("plan.pair[1]: must be a string");
    expect((Plan.check({ ...good, seats: 0 })!).text()).toBe("seats: must be from 1 to 500");
    expect((Plan.check({ ...good, name: "" })!).text()).toBe("name: must be 1 to 20 characters long");
    expect((s.nat().check("x")!).text()).toMatch(/^the value: must be a whole number/);
  });

  // A non-plain object has no own enumerable keys, so without this it converted
  // to an empty object and the core accepted it against any object schema with
  // no required key. A host can be handed one; parsing must not claim it fits.
  test("a value that is not JSON is refused, not read as an empty object", () => {
    for (const v of [new Date(), new Map([["a", 1]]), new Set([1]), new (class {})()]) {
      const r = s.object({ a: s.nat().optional() }).strict().parse(v);
      expect(r.ok).toBe(false);
    }
    expect(s.object({}).parse(new Date()).ok).toBe(false);
  });

  test("a plain object and Object.create(null) are still objects", () => {
    expect(s.object({ a: s.nat() }).parse({ a: 1 }).ok).toBe(true);
    const bare = Object.create(null);
    bare.a = 1;
    expect(s.object({ a: s.nat() }).parse(bare).ok).toBe(true);
  });

  // `out["__proto__"] = x` hits the prototype setter, so the field vanished
  // from a value parse called valid.
  test("a field named __proto__ survives parse and encode", () => {
    const P = s.object({ ["__proto__"]: s.str() }).strict();
    const r = P.parse(JSON.parse('{"__proto__":"hello"}'));
    expect(r.ok).toBe(true);
    expect(JSON.stringify((r as { ok: true; value: unknown }).value)).toBe('{"__proto__":"hello"}');
    expect(P.encode({ ["__proto__"]: "hello" })).toEqual({ ["__proto__"]: "hello" });
  });

  test("encoding an absent top-level optional is undefined", () => {
    expect(s.str().optional().encode(undefined)).toBe(undefined);
  });
});

describe("refine", () => {
  const Email = s.str().refine((x) => x.includes("@"), "must be an email");
  const User = s.object({ email: Email, friends: s.list(Email) });

  test("runs after the proved check, and says it is not proved", () => {
    expect<unknown>(User.check({ email: "a@b", friends: ["c@d", "nope"] })).toEqual({ path: ["friends", 1], message: "must be an email", proved: false });
  });

  test("a proved error comes first", () => {
    expect(User.check({ email: 3, friends: ["nope"] })?.proved).toBe(true);
  });

  test("cross-field rule on an object", () => {
    const Range = s.object({ lo: s.nat(), hi: s.nat() }).refine((r) => r.lo <= r.hi, "lo must not exceed hi");
    expect<unknown>(Range.check({ lo: 5, hi: 2 })).toEqual({ path: [], message: "lo must not exceed hi", proved: false });
    expect(Range.check({ lo: 1, hi: 2 })).toBeNull();
  });
});

describe("encode", () => {
  test("refuses a value outside a bound (its type cannot)", () => {
    expect(() => Plan.encode({ ...good, seats: 501 })).toThrow("seats: must be from 1 to 500");
  });
});

describe("the builder", () => {
  test("an ill-formed schema is refused at first use", () => {
    expect(() => s.nat().nullable().nullable().parse(null)).toThrow(/ill-formed/);
  });

  test("a bound must be whole", () => {
    expect(() => s.nat().in(-1, 3)).toThrow();
    expect(() => s.str().len(0, 1.5)).toThrow();
  });
});

describe("json schema", () => {
  const Json = s.json();

  test("accepts JSON numbers and preserves IEEE-754 identity", () => {
    for (const value of [0, -0, 0.1, -12.5, Number.MAX_VALUE, Number.MIN_VALUE]) {
      const parsed = Json.parse(value);
      expect(parsed.ok).toBe(true);
      if (parsed.ok) expect(Object.is(parsed.value, value)).toBe(true);
      expect(Object.is(Json.encode(value), value)).toBe(true);
    }
    expect(Json.check(Infinity)?.message).toBe("must be a JSON value");
  });

  test("round-trips containers, ordering, empty values and __proto__", () => {
    const value = JSON.parse('{"first":[],"__proto__":{"x":-0},"last":[null,true,1.25]}');
    const parsed = Json.parse(value);
    expect(parsed.ok).toBe(true);
    if (parsed.ok) {
      expect(Object.keys(parsed.value as object)).toEqual(["first", "__proto__", "last"]);
      expect(Object.is((parsed.value as any).__proto__.x, -0)).toBe(true);
      expect(parsed.value).toEqual(value);
    }
    expect(Json.encode(value)).toEqual(value);
    expect(Json.parse([])).toEqual({ ok: true, value: [] });
    expect(Json.parse({})).toEqual({ ok: true, value: {} });
  });

  test("uses JSON conversion recursively inside ordinary schemas", () => {
    const Nested = s.object({
      values: s.list(s.json()),
      pair: s.tuple(s.str(), s.json()),
      choice: s.oneKey({ payload: s.json() }),
      tagged: s.tagged("kind", { item: s.object({ value: s.json() }) }),
    });
    const value: Infer<typeof Nested> = { values: [0.5, { a: -0 }], pair: ["x", null], choice: { payload: [true] }, tagged: { kind: "item", value: { n: 2.25 } } };
    const parsed = Nested.parse(value);
    expect(parsed.ok).toBe(true);
    if (parsed.ok) expect(Object.is((parsed.value.values[1] as Record<string, Json>).a, -0)).toBe(true);
    expect(Nested.encode(value)).toEqual(value);
  });

  test("does not turn ordinary schema numbers into JSON numbers", () => {
    expect(s.nat().parse(4)).toEqual({ ok: true, value: 4 });
    expect(s.nat().check(0.5)?.message).toMatch(/whole number/);
  });
});

// Compile-time: tsc checks these lines; they never run.
function _types() {
  const T = s.tuple(s.nat(), s.enum(["a", "b"]));
  const t: [number, "a" | "b"] = null as unknown as Infer<typeof T>;
  const u: Infer<typeof Plan>["event"] = { type: "open", at: 1 };
  // @ts-expect-error a wrong tag is a type error
  const w: Infer<typeof Plan>["event"] = { type: "shut", at: 1 };
  return [t, u, w];
}

describe("optional and list length", () => {
  const P = s.object({ id: s.nat(), nick: s.str().len(1, 8).optional(), tags: s.list(s.str()).len(1, 3) });

  test("an optional key may be absent, and stays absent", () => {
    expect(P.parse({ id: 1, tags: ["a"] })).toEqual({ ok: true, value: { id: 1, tags: ["a"] } });
    expect(P.parse({ id: 1, nick: "x", tags: ["a"] })).toEqual({ ok: true, value: { id: 1, nick: "x", tags: ["a"] } });
  });

  test("present, it is checked", () => {
    expect(P.check({ id: 1, nick: "", tags: ["a"] })?.text()).toBe("nick: must be 1 to 8 characters long");
  });

  test("encode leaves an absent key out", () => {
    expect(P.encode({ id: 1, tags: ["a"] })).toEqual({ id: 1, tags: ["a"] });
  });

  test("list length is checked", () => {
    expect(P.check({ id: 1, tags: [] })?.text()).toBe("tags: must have 1 to 3 elements");
  });

  test("optional outside a field is refused", () => {
    expect(() => s.list(s.nat().optional()).parse([])).toThrow(/ill-formed/);
  });

  test("refine keeps the builder's methods", () => {
    const N = s.nat().refine((n) => n % 2 === 0, "must be even").in(0, 10);
    expect(N.check(12)?.proved).toBe(true);
    expect(N.check(3)?.text()).toBe("the value: must be even");
  });
});

function _optTypes() {
  const O = s.object({ a: s.nat(), b: s.str().optional() });
  const x: Infer<typeof O> = { a: 1 };
  const y: Infer<typeof O> = { a: 1, b: "z" };
  return [x, y];
}

describe("int", () => {
  // JSON-RPC's error codes: the reason s.int() exists.
  const Code = s.int().in(-32768, -32000);
  const Resp = s.object({ code: s.int(), message: s.str(), data: s.json().optional() });

  test("accepts a whole number of either sign, and reads it back", () => {
    for (const v of [0, 1, -1, -32700, INT_MIN, NAT_MAX]) expect(s.int().parse(v)).toEqual({ ok: true, value: v });
    expect(s.int().parse(-0)).toEqual({ ok: true, value: 0 });
    expect(Resp.parse({ code: -32601, message: "Method not found" })).toEqual({ ok: true, value: { code: -32601, message: "Method not found" } });
  });

  test("refuses a fraction, a number past either bound, and anything not a number", () => {
    for (const v of [1.5, -0.5, INT_MIN - 1, NAT_MAX + 1, NaN, Infinity, "1", null, true]) {
      const e = s.int().check(v);
      expect(e?.message).toBe(`must be a whole number from ${INT_MIN} to ${NAT_MAX}`);
      expect(e?.proved).toBe(true);
    }
    expect(s.int().check(undefined)?.message).toBe(`must be a whole number from ${INT_MIN} to ${NAT_MAX}`);
    expect(s.object({ code: s.int() }).check({})?.message).toBe("missing");
  });

  test("a range has both ends included, either of them negative", () => {
    for (const v of [-32768, -32700, -32000]) expect(Code.parse(v).ok).toBe(true);
    for (const v of [-32769, -31999, 0, 32700]) {
      expect(Code.check(v)?.message).toBe("must be from -32768 to -32000");
    }
    expect(s.int().in(-2, 3).parse(3).ok).toBe(true);
    expect(s.int().in(-2, 3).parse(-3).ok).toBe(false);
    // lo past hi is an empty range, not an error
    expect(s.int().in(1, -1).parse(0).ok).toBe(false);
  });

  test("the paths and the reason are the core's", () => {
    const e = s.object({ error: s.object({ code: Code }) }).check({ error: { code: 1 } })!;
    expect(e.path).toEqual(["error", "code"]);
    expect(e.text()).toBe("error.code: must be from -32768 to -32000");
  });

  test("SNat still refuses a negative, as before", () => {
    expect(s.nat().check(-1)?.message).toBe(`must be a whole number from 0 to ${NAT_MAX}`);
  });

  test("encode then parse is the identity, and encode refuses what SInt cannot hold", () => {
    for (const v of [0, -1, 7, -32603, INT_MIN, NAT_MAX]) {
      expect(s.int().encode(v)).toBe(v);
      expect(s.int().parse(s.int().encode(v))).toEqual({ ok: true, value: v });
    }
    expect(Resp.encode({ code: -32700, message: "Parse error" })).toEqual({ code: -32700, message: "Parse error" });
    for (const v of [1.5, NaN, INT_MIN - 1, NAT_MAX + 1]) expect(() => s.int().encode(v)).toThrow();
    expect(() => Code.encode(5)).toThrow("must be from -32768 to -32000");
  });

  test("a bound must be one SInt can hold", () => {
    expect(() => s.int().in(-1.5, 3)).toThrow();
    expect(() => s.int().in(INT_MIN - 1, 0)).toThrow();
    expect(() => s.int().in(INT_MIN, NAT_MAX)).not.toThrow();
  });

  test("a refinement keeps the builder's methods", () => {
    const Even = s.int().refine((n) => n % 2 === 0, "must be even").in(-10, 10);
    expect(Even.check(-3)?.message).toBe("must be even");
    expect(Even.check(-12)?.message).toBe("must be from -10 to 10");
  });
});
