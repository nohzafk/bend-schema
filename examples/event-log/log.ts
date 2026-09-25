// An append-only event log: one JSON line per event.
//
// The writer and the reader are the same schema value. `append` encodes with
// `Event` and writes the line; `readAll` parses every line against `Event`
// and reports the first bad one, with its line number.

import { appendFileSync, readFileSync } from "node:fs";
import { s, type Infer } from "../../src/index.ts";

const User = s.str().len(1, 32);

/** The log's format, in full. */
export const Event = s.tagged("kind", {
  signup: s.object({
    user: User,
    plan: s.enum(["free", "pro"]),
  }),
  purchase: s.object({
    user: User,
    sku: s.str(),
    qty: s.nat().in(1, 99),
    coupon: s.str().nullable(),
  }),
  note: s.object({
    text: s.str(),
    tags: s.list(s.str()),
    at: s.tuple(s.nat(), s.nat()),
  }),
});

export type Event = Infer<typeof Event>;

/** Append one event as a JSON line. `encode` refuses a value outside a bound,
 * so a bad event never reaches the file. */
export function append(path: string, event: Event): void {
  appendFileSync(path, JSON.stringify(Event.encode(event)) + "\n");
}

/** Every event in the file, in order. Throws on the first line that is not a
 * JSON object of a known kind, naming the line and, inside it, the field. */
export function readAll(path: string): Event[] {
  const lines = readFileSync(path, "utf8").split("\n");
  if (lines[lines.length - 1] === "") lines.pop(); // append writes a trailing "\n"

  const events: Event[] = [];
  for (let i = 0; i < lines.length; i++) {
    const n = i + 1;
    let v: unknown;
    try {
      v = JSON.parse(lines[i]);
    } catch {
      throw new Error(`line ${n}: not JSON`);
    }
    const r = Event.parse(v);
    if (!r.ok) throw new Error(r.error.text(`line ${n}`));
    events.push(r.value);
  }
  return events;
}
