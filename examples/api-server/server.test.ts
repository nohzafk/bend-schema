// The API over a real Request — handle() is called directly, no port, no
// server. `bun test` from the repo root globs this file.

import { describe, expect, test } from "bun:test";
import { BUDGET, type Infer } from "../../src/index.ts";
import { handle, Order as OrderSchema } from "./server.ts";

type Order = Infer<typeof OrderSchema>;

const item = (qty: number): Order["items"][number] => ({ sku: "sku-1", qty, price: 250 });

const base: Order = { id: "o-1", currency: "usd", note: null, totalQty: 1, items: [item(1)] };
const order = (over: Partial<Order>): Order => ({ ...base, ...over });

const post = (raw: string): Promise<Response> =>
  handle(new Request("http://localhost/orders", { method: "POST", body: raw }));

const postOrder = async (v: unknown) => {
  const res = await post(JSON.stringify(v));
  return { status: res.status, body: await res.json() };
};

describe("POST /orders", () => {
  test("a valid order is 201 with the parsed order", async () => {
    const o = order({ items: [item(2), item(3)], totalQty: 5 });
    expect(await postOrder(o)).toEqual({ status: 201, body: o });
  });

  test("a wrong type deep in the line items names its exact path, proved", async () => {
    const o = order({ totalQty: 3 });
    const r = await postOrder({ ...o, items: [item(1), item(1), { ...item(1), qty: "3" }] });
    expect(r.status).toBe(400);
    expect(r.body.path).toEqual(["items", 2, "qty"]);
    expect(r.body.proved).toBe(true);
    expect(r.body.text).toMatch(/^order\.items\[2\]\.qty: must be a whole number/);
  });

  test("the cross-field refine fails with proved: false", async () => {
    const r = await postOrder(order({ items: [item(2), item(2)], totalQty: 5 }));
    expect(r).toEqual({
      status: 400,
      body: {
        path: [],
        message: "totalQty must equal the sum of the item quantities",
        proved: false,
        text: "order: totalQty must equal the sum of the item quantities",
      },
    });
  });

  test("a body past the size budget is a 400, not a stack overflow", async () => {
    const items = Array.from({ length: 5000 }, () => item(1));
    expect(items.length).toBeGreaterThan(BUDGET); // BUDGET is 3072
    const r = await postOrder(order({ items, totalQty: 5000 }));
    expect(r).toEqual({
      status: 400,
      body: { path: ["items"], message: "too large", proved: true, text: "order.items: too large" },
    });
  });

  test("malformed JSON is a 400", async () => {
    const res = await post('{"id": "o-1",');
    expect(res.status).toBe(400);
    expect(await res.json()).toEqual({
      path: [],
      message: "body must be valid JSON",
      proved: false,
      text: "order: body must be valid JSON",
    });
  });
});
