// The codec and the proved check, at run time: what reaches the core, and what
// comes back.
//
// The budget is the part of this file that is not just a test: nothing in the
// proved core knows a size, so the codec's counting is what keeps the walks
// inside the stack, and the gate has to fail if the budget is raised past what
// the runtime can walk or the walk gets deeper. The shapes come from
// measure_budget.ts, so the numbers in codec.ts and the gate cannot drift.

import { describe, expect, test } from "bun:test";
import * as kernel from "../dist-core/core.js";
import { check0 as check, conforms0, type BendMaybe, type Raw, type Schema } from "../dist-core/core.js";
import { BUDGET, KEYS_MAX, errText, toRaw } from "./codec";
import { SHAPES, unbudgeted as before, type Case } from "./measure_budget";

// enc and dec compute a type from a value (Meaning(s)), so tools/bend_lib.ts
// leaves them undeclared in dist-core/core.d.ts: these are their run-time types.
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
