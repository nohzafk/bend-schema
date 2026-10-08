import { expect, test } from "bun:test";
import { mkdtempSync, mkdirSync, cpSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Schema as S, SchemaIssue, SchemaParser } from "effect";
import type { Effect } from "effect";
import { Rpc, RpcClient, RpcGroup } from "effect/rpc";
import { s, type Infer } from "bend-schema";
import { toEffect } from "bend-schema/effect";

const Payload = s.object({ name: s.str(), note: s.str().optional() });
const Event = s.tagged("type", {
  open: s.object({ at: s.nat() }),
  close: s.object({ why: s.str() }),
});
const Adapted = toEffect(Payload);
const AdaptedEvent = toEffect(Event);

type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends
  (<T>() => T extends B ? 1 : 2) ? true : false;
const inferred: Equal<typeof Adapted.Type, Infer<typeof Payload>> = true;
const inferredUnion: Equal<typeof AdaptedEvent.Type, Infer<typeof Event>> = true;
const encodedUnknown: Equal<typeof Adapted.Encoded, unknown> = true;
const noDecodeServices: Equal<typeof Adapted.DecodingServices, never> = true;
const noEncodeServices: Equal<typeof Adapted.EncodingServices, never> = true;
// @ts-expect-error The decoded field is string, not number.
const wrong: typeof Adapted.Type = { name: 1 };
void wrong;

const Nested = s.object({ items: s.list(s.object({ label: s.str() })) });
const AdaptedString = toEffect(s.str());
const taggedWire: Equal<typeof AdaptedEvent.Encoded, unknown> = true;
const stringWire: Equal<typeof AdaptedString.Encoded, unknown> = true;
void [taggedWire, stringWire];
const Calls = RpcGroup.make(
  Rpc.make("Object", { payload: Adapted, success: AdaptedEvent }),
  Rpc.make("Tagged", { payload: AdaptedEvent, success: Adapted }),
  Rpc.make("String", { payload: AdaptedString, success: AdaptedString }),
  Rpc.make("Nested", { payload: toEffect(Nested) }),
);

// Compile-only: exercise the actual client signatures, without a consumer cast.
function inferredClient(client: RpcClient.RpcClient<RpcGroup.Rpcs<typeof Calls>>) {
  const objectInput: Equal<Parameters<typeof client.Object>[0], Infer<typeof Payload>> = true;
  const taggedInput: Equal<Parameters<typeof client.Tagged>[0], Infer<typeof Event>> = true;
  const stringInput: Equal<Parameters<typeof client.String>[0], string> = true;
  const nestedInput: Equal<Parameters<typeof client.Nested>[0], Infer<typeof Nested>> = true;
  const call = client.Object({ name: "hello" });
  const result: Equal<Effect.Success<typeof call>, Infer<typeof Event>> = true;
  const services: Equal<Effect.Services<typeof call>, never> = true;
  client.Object({ name: "hello", note: "memo" });
  client.Tagged({ type: "open", at: 3 });
  client.Tagged({ type: "close", why: "done" });
  client.String("hello");
  client.Nested({ items: [{ label: "hello" }] });
  // @ts-expect-error Required name is missing.
  client.Object({});
  // @ts-expect-error Object field is a string.
  client.Object({ name: 1 });
  // @ts-expect-error Optional note is a string when present.
  client.Object({ name: "hello", note: 1 });
  // @ts-expect-error Nested labels are strings.
  client.Nested({ items: [{ label: false }] });
  // @ts-expect-error Only declared tags are allowed.
  client.Tagged({ type: "other", why: "done" });
  // @ts-expect-error The close variant requires why.
  client.Tagged({ type: "close" });
  // @ts-expect-error The open variant's at field is a number.
  client.Tagged({ type: "open", at: "bad" });
  // @ts-expect-error A string payload rejects numbers.
  client.String(1);
  return [objectInput, taggedInput, stringInput, nestedInput, result, services];
}
void inferredClient;

function failure(schema: S.Codec<unknown, unknown>, input: unknown) {
  const result = SchemaParser.decodeUnknownResult(schema)(input);
  if (result._tag !== "Failure") throw new Error("expected decode failure");
  return SchemaIssue.makeFormatterStandardSchemaV1()(result.failure).issues;
}

test("string decoding and inferred types", () => {
  expect(S.decodeUnknownSync(toEffect(s.str()))("hello")).toBe("hello");
  expect(failure(toEffect(s.str()), 1)).toEqual([
    { path: [], message: "must be a string" },
  ]);
  expect([inferred, inferredUnion, encodedUnknown, noDecodeServices, noEncodeServices]).toEqual([
    true, true, true, true, true,
  ]);
});

test("object decoding returns parse's transformed value, not the input", () => {
  const input = { name: "hello", extra: true };
  const output = S.decodeUnknownSync(Adapted)(input);
  expect(output).toEqual({ name: "hello" });
  expect(output).not.toBe(input);
  expect(input).toEqual({ name: "hello", extra: true });
  expect(S.decodeUnknownSync(S.toType(Adapted))(input)).toEqual({ name: "hello" });
  // RPC constructs payloads with make before encoding them.
  expect(Adapted.make(input)).toEqual({ name: "hello" });
});

test("strict objects refuse unknown keys with the original path and reason", () => {
  expect(failure(toEffect(Payload.strict()), { name: "hello", extra: true })).toEqual([
    { path: ["extra"], message: "is not a key this object allows" },
  ]);
});

test("optional fields are omitted or decoded when present", () => {
  const decode = S.decodeUnknownSync(Adapted);
  expect(decode({ name: "hello" })).toEqual({ name: "hello" });
  expect(decode({ name: "hello", note: "memo" })).toEqual({ name: "hello", note: "memo" });
  expect(failure(Adapted, { name: "hello", note: 4 })).toEqual([
    { path: ["note"], message: "must be a string" },
  ]);
});

test("tagged unions decode and encode both cases", () => {
  for (const value of [{ type: "open", at: 3 }, { type: "close", why: "done" }] as const) {
    const encoded = S.encodeSync(AdaptedEvent)(value);
    expect(encoded).toEqual(Event.encode(value));
    expect(S.decodeUnknownSync(AdaptedEvent)(encoded)).toEqual(value);
  }
  expect(S.decodeUnknownSync(AdaptedEvent)({ type: "open", at: 3, extra: true })).toEqual({ type: "open", at: 3 });
  expect(failure(AdaptedEvent, { type: "open", at: "bad" })).toEqual([
    { path: ["at"], message: "must be a whole number from 0 to 281474976710655" },
  ]);
});

test("nested failures retain field and index paths, including Effect struct context", () => {
  const core = s.object({ items: s.list(s.object({ name: s.str() })) });
  expect(failure(toEffect(core), { items: [{ name: 3 }] })).toEqual([
    { path: ["items", 0, "name"], message: "must be a string" },
  ]);
  expect(failure(S.Struct({ payload: toEffect(core) }), { payload: { items: [{ name: 3 }] } })).toEqual([
    { path: ["payload", "items", 0, "name"], message: "must be a string" },
  ]);
  expect(failure(Adapted, {})).toEqual([{ path: ["name"], message: "missing" }]);
});

test("refinement failures remain schema failures with their reason", () => {
  expect(failure(toEffect(s.str().refine((x) => x.length > 0, "must not be empty")), "")).toEqual([
    { path: [], message: "must not be empty" },
  ]);
});

test("encoding delegates to the existing encoder and round trips", () => {
  let calls = 0;
  const schema = s.object({ name: s.str(), note: s.str().optional() });
  const encode = schema.encode.bind(schema);
  schema.encode = (value) => { calls++; return encode(value); };
  const adapted = toEffect(schema);
  for (const value of [{ name: "hello" }, { name: "hello", note: "memo" }]) {
    const wire = S.encodeSync(adapted)(value);
    expect(wire).toEqual(encode(value));
    expect(S.decodeUnknownSync(adapted)(wire)).toEqual(value);
  }
  expect(calls).toBe(2);
  expect(() => S.encodeUnknownSync(toEffect(s.nat().in(1, 3)))(4)).toThrow();
});

test("encoder exceptions become Effect schema failures", () => {
  const schema = s.str();
  schema.encode = () => { throw new Error("encoder refused"); };
  const result = SchemaParser.encodeUnknownResult(toEffect(schema))("hello");
  if (result._tag !== "Failure") throw new Error("expected encode failure");
  expect(SchemaIssue.makeFormatterStandardSchemaV1()(result.failure).issues).toEqual([
    { path: [], message: "encoder refused" },
  ]);
});

test("adapted codecs work as Effect RPC payload and success schemas", () => {
  const rpc = Rpc.make("Open", { payload: Adapted, success: AdaptedEvent });
  expect(S.decodeUnknownSync(rpc.payloadSchema)({ name: "hello", extra: true })).toEqual({ name: "hello" });
  expect(S.encodeSync(rpc.successSchema)({ type: "open", at: 3 })).toEqual({ type: "open", at: 3 });
});

test("root entry runs in an isolated directory with Effect absent", () => {
  const dir = mkdtempSync(join(tmpdir(), "bend-schema-root-"));
  try {
    mkdirSync(join(dir, "src"));
    for (const file of ["index.ts", "codec.ts"]) {
      cpSync(new URL(file, import.meta.url), join(dir, "src", file));
    }
    cpSync(new URL("../dist-core", import.meta.url), join(dir, "dist-core"), { recursive: true });
    const entry = join(dir, "smoke.ts");
    writeFileSync(entry, `
      try { await import("effect"); process.exit(2); } catch {}
      const { s } = await import("./src/index.ts");
      const r = s.str().parse("hello");
      if (!r.ok || r.value !== "hello") process.exit(3);
    `);
    const result = Bun.spawnSync([process.execPath, "--no-install", entry], { cwd: dir });
    expect(result.stderr.toString()).toBe("");
    expect(result.exitCode).toBe(0);
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
});

// The InvalidValue leaf under a failure: Composite and Pointer nodes wrap it.
function leaf(schema: S.Codec<unknown, unknown>, input: unknown): SchemaIssue.InvalidValue {
  const result = SchemaParser.decodeUnknownResult(schema)(input);
  if (result._tag !== "Failure") throw new Error("expected decode failure");
  const walk = (i: any): any =>
    i._tag === "InvalidValue" ? i : [i.issue, ...(i.issues ?? [])].filter(Boolean).map(walk).find(Boolean);
  const found = walk(result.failure);
  if (!found) throw new Error("no InvalidValue leaf");
  return found;
}

test("proved rides on the InvalidValue annotations", () => {
  const core = leaf(toEffect(s.object({ a: s.nat() })), { a: "x" });
  expect(core.annotations).toEqual({ message: "must be a whole number from 0 to 281474976710655", proved: true });
  const host = leaf(toEffect(s.nat().refine((n) => n > 3, "too small")), 1);
  expect(host.annotations).toEqual({ message: "too small", proved: false });
});
