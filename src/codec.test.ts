// The codec and the proved check, at run time: what reaches the core, and what
// comes back.
//
// The budget is the part of this file that is not just a test: nothing in the
// proved core knows a size, so the codec's counting is what keeps the walks
// inside the stack, and the gate has to fail if the budget is raised past what
// the runtime can walk or the walk gets deeper. The shapes come from
// measure_budget.ts, so the numbers in codec.ts and the gate cannot drift.

import { describe, expect, test } from "bun:test";
import * as kernel from "../dist-core/core.mjs";
import { check0 as check, conforms0, type BendList, type BendMaybe, type Raw, type Schema } from "../dist-core/core.mjs";
import { BUDGET, KEYS_MAX, NAT_MAX, errText, nat as hostNat, toRaw } from "./codec";
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
    for (let i = 0; i < 200; i++) deep = { a: [deep] };
    const values: unknown[] = [null, true, false, 0, 1.5, -1, 2 ** 48, 2 ** 48 - 1, "", "hi", [], {}, [[]], [[[[]]]], undefined, { a: { b: [1, "x", null] } }, deep];
    for (const v of values) expect(toRaw(v)).toEqual(before(v));
    // And at the budget's own size, where the counting is doing the most work:
    // the flat list is one element per count, so its at-budget value is the
    // longest one a single call can build.
    const at = Array.from({ length: BUDGET }, () => 1);
    expect(measure(toRaw(at))).toEqual({ count: BUDGET, tooBig: false });
    expect(toRaw(at)).toEqual(before(at));
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
