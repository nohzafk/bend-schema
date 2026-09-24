// The event log as a user of it: every case in and out through a file, a
// generated batch, a bad value refused at the writer, a corrupt line named.

import { afterAll, describe, expect, test } from "bun:test";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Event, append, readAll } from "./log.ts";

const dir = mkdtempSync(join(tmpdir(), "event-log-"));
afterAll(() => rmSync(dir, { recursive: true, force: true }));

let n = 0;
const file = () => join(dir, `log-${n++}.jsonl`);

// One event per case, edge values where the schema allows them: the shortest
// and longest allowed `user`, an empty `sku`, `qty` at both ends, `coupon`
// null and a string, empty `text`, an empty tag, and a newline in text (it
// must stay one line).
const cases: Event[] = [
  { kind: "signup", user: "a", plan: "free" },
  { kind: "signup", user: "x".repeat(32), plan: "pro" },
  { kind: "purchase", user: "bob", sku: "", qty: 1, coupon: null },
  { kind: "purchase", user: "bob", sku: "SKU-9", qty: 99, coupon: "" },
  { kind: "note", text: "", tags: [], at: [0, 0] },
  { kind: "note", text: "hi\nthere", tags: [""], at: [1, 281474976710655] },
];

describe("every case", () => {
  test("written and read back, one line each", () => {
    const p = file();
    for (const e of cases) append(p, e);
    expect(readFileSync(p, "utf8").split("\n").filter(Boolean)).toHaveLength(cases.length);
    expect(readAll(p)).toEqual(cases);
  });
});

describe("the writer", () => {
  test("refuses a value outside a bound, so a bad event never reaches the file", () => {
    const p = file();
    const bad = { kind: "purchase", user: "bob", sku: "x", qty: 100, coupon: null } as unknown as Event;
    expect(() => append(p, bad)).toThrow("qty: must be from 1 to 99");
    expect(existsSync(p)).toBe(false);

    append(p, cases[0]!);
    expect(() => append(p, bad)).toThrow();
    expect(readAll(p)).toEqual([cases[0]!]);
  });
});

describe("a generated batch", () => {
  test("200 events round-trip exactly", () => {
    const events = generate(200);
    const p = file();
    for (const e of events) append(p, e);
    expect(readAll(p)).toEqual(events);

    const kinds = new Set(events.map((e) => e.kind));
    expect([...kinds].sort()).toEqual(["note", "purchase", "signup"]);
  });
});

describe("the reader", () => {
  test("names the line and the field of a hand-corrupted one", () => {
    const good: Event[] = [
      { kind: "signup", user: "a", plan: "free" },
      { kind: "note", text: "n", tags: [], at: [0, 1] },
      { kind: "purchase", user: "b", sku: "s", qty: 3, coupon: null },
    ];
    const p = file();
    for (const e of good) append(p, e);

    const text = readFileSync(p, "utf8");
    const torn = text.replace('"qty":3', '"qty":100');
    expect(torn).not.toBe(text); // the corruption the next line relies on
    writeFileSync(p, torn);

    expect(() => readAll(p)).toThrow("line 3.qty: must be from 1 to 99");
  });

  test("names a line that is not JSON", () => {
    const p = file();
    append(p, cases[0]!);
    writeFileSync(p, readFileSync(p, "utf8") + "{oops\n");
    expect(() => readAll(p)).toThrow("line 2: not JSON");
  });
});

// ---- a deterministic batch: a seeded PRNG, so a failure is reproducible ----

function mulberry32(seed: number): () => number {
  let a = seed;
  return () => {
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function generate(count: number): Event[] {
  const rnd = mulberry32(20260925);
  const pick = <T>(xs: T[]): T => xs[Math.floor(rnd() * xs.length)]!;
  const users = ["a", "bob", "Randall", "x".repeat(32), "ü"];
  const skus = ["", "SKU-1", "a".repeat(64)];
  const texts = ["", "hello", "line\nbreak", "unicode ✓ 中文", "x".repeat(200)];
  const tagsets = [[], [""], ["a", "bb"], ["tag1", "tag2", "tag3"]];
  const stamps: [number, number][] = [[0, 0], [1, 2], [281474976710655, 281474976710655], [0, 42]];
  const coupons = [null, "", "SAVE10", "a".repeat(40)];
  const qtys = [1, 2, 50, 99];

  const out: Event[] = [];
  for (let i = 0; i < count; i++) {
    switch (pick(["signup", "purchase", "note"] as const)) {
      case "signup":
        out.push({ kind: "signup", user: pick(users), plan: pick(["free", "pro"] as const) });
        break;
      case "purchase":
        out.push({ kind: "purchase", user: pick(users), sku: pick(skus), qty: pick(qtys), coupon: pick(coupons) });
        break;
      case "note":
        out.push({ kind: "note", text: pick(texts), tags: pick(tagsets), at: pick(stamps) });
        break;
    }
  }
  return out;
}
