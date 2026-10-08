// Optional Effect v4 bridge. The root entry does not import Effect.
import { Effect, Schema as S, SchemaGetter, SchemaIssue } from "effect";
import type { Schema } from "./index";

/** Decode with bend-schema's parse (including transformations), and encode
 * with its encode. The encoded representation is unknown; T is inferred.
 * Keep the concrete schema type: Codec<T, unknown> erases RPC's make input. */
export function toEffect<T>(schema: Schema<T>): S.decodeTo<
  S.declareConstructor<T, T, readonly []>, typeof S.Unknown
> {
  const value = S.declareConstructor<T>()([], () => (input) => {
    const result = schema.parse(input);
    return result.ok
      ? Effect.succeed(result.value)
      : Effect.fail(new SchemaIssue.Pointer(
          result.error.path,
          new SchemaIssue.InvalidValue({ message: result.error.message, proved: result.error.proved }),
        ));
  });

  return S.Unknown.pipe(S.decodeTo(value, {
    // The declaration validates this unknown value and returns parse's T.
    decode: SchemaGetter.transform((input: unknown) => input as T),
    encode: SchemaGetter.transformEffect((input: T) => Effect.try({
      try: () => schema.encode(input),
      catch: (error) => new SchemaIssue.InvalidValue({
        message: error instanceof Error ? error.message : String(error),
      }),
    })),
  }));
}
