// A JSON Schema (draft 2020-12) for the JSON a bend-schema schema accepts.
//
// The contract is one-sided: every value `parse` accepts passes the JSON
// Schema, never the other way round. Three things a JSON Schema cannot say are
// left out, so the document is looser there and only there: `.refine()`
// predicates, the size and depth limits (BUDGET, KEYS_MAX, DEPTH_MAX), and a
// key repeated in one object, which a parsed JSON object cannot hold anyway.
// `parse` stays the authority; this document is for client authors and tools.
//
// Not proved: it reads the builder's kinds, not the core.

import type { Schema } from "./index";
import { INT_MIN, NAT_MAX } from "./codec";

export type JsonSchema = { [k: string]: unknown };

export const DIALECT = "https://json-schema.org/draft/2020-12/schema";

/** The JSON Schema document for `schema`. Throws on an ill-formed schema, as
 * `parse` would. */
export function toJsonSchema(schema: Schema<any>): JsonSchema {
  void schema.node; // the core's well-formedness check, the same refusal parse gives
  return { $schema: DIALECT, ...body(schema) };
}

// A key set with defineProperty: `out["__proto__"] = x` would set the
// prototype and drop the field.
function put(out: JsonSchema, k: string, v: unknown): void {
  Object.defineProperty(out, k, { value: v, enumerable: true, writable: true, configurable: true });
}

function obj(entries: [string, unknown][]): JsonSchema {
  const out: JsonSchema = {};
  for (const [k, v] of entries) put(out, k, v);
  return out;
}

// Both a and b: their keywords side by side when none is shared, allOf otherwise.
function both(a: JsonSchema, b: JsonSchema): JsonSchema {
  return Object.keys(b).some((k) => k in a) ? { allOf: [a, b] } : { ...a, ...b };
}

// The schema no value passes.
const NOTHING: JsonSchema = { not: {} };

function body(x: Schema<any>): JsonSchema {
  const k = x.kind;
  switch (k.k) {
    case "nat": return { type: "integer", minimum: 0, maximum: NAT_MAX };
    case "natIn": return { type: "integer", minimum: k.lo, maximum: k.hi };
    case "int": return { type: "integer", minimum: INT_MIN, maximum: NAT_MAX };
    case "intIn": return { type: "integer", minimum: k.lo, maximum: k.hi };
    case "str": return { type: "string" };
    case "strLen": return both(body(k.inner), { minLength: k.lo, maxLength: k.hi });
    case "bool": return { type: "boolean" };
    case "true": return { const: true };
    case "json": return {};
    case "enum": return { type: "string", enum: [...k.names] };
    // The key must be present; a nested nullable is ill-formed, so one null branch.
    case "nullable": return { anyOf: [body(k.inner), { type: "null" }] };
    // Absence is not a JSON value: an object leaves the key out of `required`,
    // and at the top level the present case is all a document can describe.
    case "optional": return body(k.inner);
    case "list": return { type: "array", items: body(k.elem) };
    case "listLen": return both(body(k.inner), { minItems: k.lo, maxItems: k.hi });
    // The metaschema requires prefixItems to be non-empty: the empty tuple is [].
    case "tuple": return k.items.length === 0
      ? { type: "array", maxItems: 0 }
      : { type: "array", prefixItems: k.items.map(body), items: false, minItems: k.items.length };
    case "object": return objectBody(k.fields, true, []);
    case "strict": return strictBody(k.obj);
    // With no case, parse accepts nothing, and oneOf may not be empty.
    case "oneKey": return k.cases.length === 0 ? NOTHING : { oneOf: k.cases.map(([n, c]) => oneKeyCase(n, c, k.cases.map(([m]) => m))) };
    case "tagged": return k.cases.length === 0 ? NOTHING : { oneOf: k.cases.map(([n, c]) => taggedCase(k.key, n, c)) };
  }
}

// An object's fields; `extra` names keys the enclosing schema adds (a tag).
function objectBody(fields: [string, Schema<any>][], open: boolean, extra: [string, JsonSchema][]): JsonSchema {
  const props = obj([...extra, ...fields.map(([n, f]) => [n, body(f)] as [string, JsonSchema])]);
  const required = [...extra.map(([n]) => n), ...fields.filter(([, f]) => f.kind.k !== "optional").map(([n]) => n)];
  return { type: "object", properties: props, required, additionalProperties: open };
}

function strictBody(o: Schema<any>): JsonSchema {
  const k = o.kind;
  if (k.k !== "object") throw new Error(`bend-schema: toJsonSchema: .strict() on ${k.k}`);
  return objectBody(k.fields, false, []);
}

// One case of a tagged union: the case's own object, with the tag key fixed to
// its name. The tag joins the case's properties (not an allOf), so a strict
// case still admits it.
function taggedCase(key: string, name: string, c: Schema<any>): JsonSchema {
  const k = c.kind;
  const tag: [string, JsonSchema] = [key, { const: name }];
  if (k.k === "object") return objectBody(k.fields, true, [tag]);
  if (k.k === "strict" && k.obj.kind.k === "object") return objectBody(k.obj.kind.fields, false, [tag]);
  throw new Error(`bend-schema: toJsonSchema: a tagged case must be an object, got ${k.k}`);
}

// One case of oneKey: its own key present and checked, every other case's key
// absent. Keys no case names are allowed, as the core allows them.
function oneKeyCase(name: string, c: Schema<any>, all: string[]): JsonSchema {
  const others = all.filter((m) => m !== name).map((m) => [m, false] as [string, unknown]);
  return { type: "object", properties: obj([[name, body(c)], ...others]), required: [name] };
}
