// The printer's tests. The fixture lives in gen.schemas.ts, because the gate
// runs the real command on that file and the command executes what it reads.

import { describe, expect, test } from "bun:test";
import { emit, printNode } from "./gen.ts";
import { Every, schemas } from "./gen.schemas.ts";

const FORMS = [
  "SStrict{", "SField{", "SEnd{}", "SStr{}", "SStrLen{", "SNat{}", "SNatIn{", "SBool{}",
  "STrue{}", "SJson{}", "SEnum{", "SOpt{", "SList{", "STuple{", "STEnd{}", "SVariant{", "SVEnd{}",
  "STagged{", "STagEnd{",
];

describe("the printer", () => {
  test("prints every constructor the builder can make", () => {
    const src = printNode(Every.node);
    for (const f of FORMS) expect(src).toContain(f);
  });

  test("emits one def per key, and imports the core where it is told to", () => {
    const src = emit(schemas, { libPath: "../core/core.bend", from: "x.ts" });
    expect(src).toContain("import ../core/core.bend as S");
    expect(src).toContain("def every_schema() -> S.Schema:");
    expect(src).toContain("def workers_schema() -> S.Schema:");
    expect(src.match(/^def /gm)?.length).toBe(2);
  });

  test("refuses a constructor it has no Bend form for", () => {
    expect(() => printNode({ $: "SNope" } as never)).toThrow("no Bend form for SNope");
  });

  test("refuses a key that is not a Bend name, and a value that is not a Schema", () => {
    expect(() => emit({ "no-good": Every }, { libPath: "x", from: "y" })).toThrow("not a Bend name");
    expect(() => emit({ x: 7 as never }, { libPath: "x", from: "y" })).toThrow("is not a Schema");
  });

  test("refuses to write an empty file", () => {
    expect(() => emit({}, { libPath: "x", from: "y" })).toThrow("nothing to print");
  });
});
