// A small orders API: Bun.serve, one file, no dependencies.
//
// The body is checked by bend-schema, so the path and the reason in a 400 are
// the proved core's (core/LAWS.bend, law check_accurate). The one part that is
// a plain TS function is the `.refine()` at the bottom: it runs only after the
// proved check passes, and its 400 says `proved: false`.

import { Issue, s, type Infer } from "../../src/index.ts";

const LineItem = s.object({
    sku: s.str().len(1, 32),
    qty: s.nat().in(1, 999),
    price: s.nat().in(0, 1_000_000), // whole cents: the schema has no float
  }).strict();

export const Order = s.object({
      id: s.str().len(1, 40),
      currency: s.enum(["usd", "eur"]),
      note: s.str().len(0, 200).nullable(), // the key must be present, as null
      totalQty: s.nat().in(1, 10_000),
      items: s.list(LineItem),
    }).strict()
  .refine(
    (o) => o.items.reduce((n, it) => n + it.qty, 0) === o.totalQty,
    "totalQty must equal the sum of the item quantities",
  );

export type Order = Infer<typeof Order>;

const json = (status: number, body: unknown): Response =>
  new Response(JSON.stringify(body), { status, headers: { "content-type": "application/json" } });

// Every 400 has one shape: the issue, plus its wording from errText.
const reject = (e: Issue): Response =>
  json(400, { path: e.path, message: e.message, proved: e.proved, text: e.text("order") });

export async function handle(req: Request): Promise<Response> {
  const { pathname } = new URL(req.url);
  if (pathname !== "/orders" || req.method !== "POST") return json(404, { error: "not found" });

  let body: unknown;
  try {
    body = JSON.parse(await req.text());
  } catch {
    // JSON.parse is the host's, so this 400 is not proved either.
    return reject(new Issue([], "body must be valid JSON", false));
  }

  const r = Order.parse(body);
  if (!r.ok) return reject(r.error); // a value nested past the codec's depth limit is TooLarge here
  return json(201, r.value);
}

if (import.meta.main) {
  const port = Number(process.env.PORT ?? 3000);
  Bun.serve({ port, fetch: handle });
  console.log(`orders api: POST http://localhost:${port}/orders`);
}
