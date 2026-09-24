// case_arms: the generated arms of a proof's case table, on a fixture.
import { describe, expect, test } from "bun:test";
import { process as fill, readTypes } from "../case_arms.ts";

const core = `
type Shape is Data:
  Dot{}
  Pair{a: Nat, b: List<&2, Nat>}
  Box{inner: Shape}
`;

describe("readTypes", () => {
  test("a field's type may hold commas", () => {
    expect(readTypes(core).get("Shape")).toEqual([
      { name: "Dot", fields: [] },
      { name: "Pair", fields: ["a", "b"] },
      { name: "Box", fields: ["inner"] },
    ]);
  });
});

describe("one column", () => {
  const proof = [
    "# arms: s",
    "# arms leaf: {==}",
    "def p(s: C.Shape) -> {f(s) == g(s) : Bool}:",
    "  match s:",
    "    case C.Box{+i}:",
    "      p(i)",
    "",
  ].join("\n");

  test("the leaf fills every constructor the hand arms leave, in declared order", () => {
    expect(fill(proof, core)).toBe([
      "# arms: s",
      "# arms leaf: {==}",
      "def p(s: C.Shape) -> {f(s) == g(s) : Bool}:",
      "  match s:",
      "    case C.Dot{}:",
      "      {==}",
      "    case C.Pair{a_, b_}:",
      "      {==}",
      "    case C.Box{+i}:",
      "      p(i)",
      "",
    ].join("\n"));
  });

  test("filling is a fixed point", () => {
    const once = fill(proof, core);
    expect(fill(once, core)).toBe(once);
  });

  test("a new constructor gets its arm", () => {
    const more = core.replace("  Box{inner: Shape}", "  Box{inner: Shape}\n  Ring{r: Nat}");
    expect(fill(fill(proof, core), more)).toContain("    case C.Ring{r_}:\n      {==}");
  });
});

describe("two columns", () => {
  const proof = [
    "# arms: s t",
    "# arms leaf: why($S, $R, $W)",
    "# arms why: Dot=A Box=B Pair.Dot=C",
    "def q(s: C.Shape, t: C.Shape) -> {x == y : Bool}:",
    "  match s t:",
    "    case C.Pair{a, b} x:",
    "      hand(x)",
    "",
  ].join("\n");

  test("a variable column covers the rest of its row; a reason is the pair's, then the second column's", () => {
    const got = fill(proof, core);
    expect(got).toContain("    case C.Dot{} C.Dot{}:\n      why(C.Dot{}, C.Dot{}, A)");
    expect(got).toContain("    case C.Box{inner_} C.Dot{}:\n      why(C.Box{inner_}, C.Dot{}, A)");
    expect(got).toContain("    case C.Box{inner_} C.Box{inner__}:\n      why(C.Box{inner_}, C.Box{inner__}, B)");
    expect(got).not.toContain("case C.Pair{a, b} C.Dot{}");
    expect(got).toContain("    case C.Pair{a, b} x:\n      hand(x)");
  });

  test("a field two columns share binds apart", () => {
    expect(fill(proof, core)).toContain("    case C.Box{inner_} C.Box{inner__}:");
  });

  test("an arm with no reason is refused, by name", () => {
    const noWhy = proof.replace("# arms why: Dot=A Box=B Pair.Dot=C", "# arms why: Box=B");
    expect(() => fill(noWhy, core)).toThrow("q: no arm for Dot Dot, and no reason for a leaf");
  });
});

describe("refusals", () => {
  test("a column that is not a parameter", () => {
    expect(() => fill("# arms: z\n# arms leaf: {==}\ndef r(s: C.Shape) -> T:\n  match z:\n", core)).toThrow("r: no parameter z");
  });

  test("a type the core does not declare", () => {
    expect(() => fill("# arms: s\n# arms leaf: {==}\ndef r(s: C.Other) -> T:\n  match s:\n", core)).toThrow("r: no type Other");
  });
});
