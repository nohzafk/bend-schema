// The TS face: builder -> core node, Meaning <-> JS, refinements, paths.
// None of this is proved, so every constructor is round-tripped here.

import { describe, expect, test } from "bun:test";
import { check, encode, errText, parse, s, type Infer } from "./index.ts";

const Plan = s.strict(
  s.object({
    name: s.str().len(1, 20),
    seats: s.nat().in(1, 500),
    active: s.bool(),
    beta: s.true(),
    tier: s.enum(["free", "pro"]),
    note: s.nullable(s.str()),
    tags: s.list(s.str()),
    pair: s.tuple(s.nat(), s.str()),
    pay: s.oneKey({ card: s.object({ last4: s.str().len(4, 4) }), invoice: s.object({ days: s.nat() }) }),
    event: s.tagged("type", { open: s.object({ at: s.nat() }), close: s.object({ why: s.str() }) }),
  }),
);
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
    expect(parse(Plan, good)).toEqual({ ok: true, value: good });
  });

  test("encode then parse is the identity, every constructor", () => {
    const alt: Plan = { ...good, note: "n", tags: [], pay: { card: { last4: "1234" } }, event: { type: "open", at: 7 } };
    for (const v of [good, alt]) expect(parse(Plan, encode(Plan, v))).toEqual({ ok: true, value: v });
  });

  test("a nullable field must be present: absent is missing", () => {
    const { note: _, ...rest } = good;
    expect(check(Plan, rest)).toEqual({ path: ["note"], message: "missing", proved: true });
  });

  test("a non-strict object drops extra keys", () => {
    const P = s.object({ a: s.nat() });
    expect(parse(P, { a: 1, b: 2 })).toEqual({ ok: true, value: { a: 1 } });
  });

  test("strict refuses an extra key, at its path", () => {
    const r = parse(Plan, { ...good, zzz: 1 });
    expect(r.ok).toBe(false);
    if (!r.ok) expect(r.error).toEqual({ path: ["zzz"], message: "is not a key this object allows", proved: true });
  });

  test("errors carry the path and the core's reason", () => {
    const e = check(Plan, { ...good, pair: [3, 4] });
    expect(e).toEqual({ path: ["pair", 1], message: "must be a string", proved: true });
    expect(errText(e!, "plan")).toBe("plan.pair[1]: must be a string");
    expect(errText(check(Plan, { ...good, seats: 0 })!)).toBe("seats: must be from 1 to 500");
    expect(errText(check(Plan, { ...good, name: "" })!)).toBe("name: must be 1 to 20 characters long");
    expect(errText(check(s.nat(), "x")!)).toMatch(/^the value: must be a whole number/);
  });
});

describe("refine", () => {
  const Email = s.str().refine((x) => x.includes("@"), "must be an email");
  const User = s.object({ email: Email, friends: s.list(Email) });

  test("runs after the proved check, and says it is not proved", () => {
    expect(check(User, { email: "a@b", friends: ["c@d", "nope"] })).toEqual({ path: ["friends", 1], message: "must be an email", proved: false });
  });

  test("a proved error comes first", () => {
    expect(check(User, { email: 3, friends: ["nope"] })?.proved).toBe(true);
  });

  test("cross-field rule on an object", () => {
    const Range = s.object({ lo: s.nat(), hi: s.nat() }).refine((r) => r.lo <= r.hi, "lo must not exceed hi");
    expect(check(Range, { lo: 5, hi: 2 })).toEqual({ path: [], message: "lo must not exceed hi", proved: false });
    expect(check(Range, { lo: 1, hi: 2 })).toBeNull();
  });
});

describe("encode", () => {
  test("refuses a value outside a bound (its type cannot)", () => {
    expect(() => encode(Plan, { ...good, seats: 501 })).toThrow("seats: must be from 1 to 500");
  });
});

describe("the builder", () => {
  test("an ill-formed schema is refused at first use", () => {
    expect(() => parse(s.nullable(s.nullable(s.nat())), null)).toThrow(/ill-formed/);
  });

  test("a bound must be whole", () => {
    expect(() => s.nat().in(-1, 3)).toThrow();
    expect(() => s.str().len(0, 1.5)).toThrow();
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
