// Falsify candidate laws on concrete inputs, with the Bend checker as the runner.
//
//   bun falsify.ts <spec.ts> [--each]
//
// <spec.ts> default-exports { imports, instances }:
//
//   export default {
//     imports: ["./core.bend as C"],                 // relative to the spec file
//     instances: [
//       { name: "covers_0", claim: "{C.covered(C.merge(C.Iv{0n, 2n} <> Nil{}), 1n) == C.covered(C.Iv{0n, 2n} <> Nil{}, 1n) : Bool}" },
//       ...
//     ],
//   };
//
// Each instance becomes `def <name>() -> <claim>: {==}` in one scratch file. The
// checker runs the code on the literals, so an instance closes exactly when the
// law holds there. The checker stops at the first failing def: without --each
// you get one counterexample, fast; with --each every instance is checked
// alone (in parallel) and every counterexample is listed.
//
// A falsifier that has never failed proves nothing: plant a bug in a copy of
// the core, point `imports` at it, and require a counterexample.

import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";

interface Spec {
  imports: string[];
  instances: { name: string; claim: string }[];
}

const [specPath, flag] = process.argv.slice(2);
if (!specPath) {
  console.error("usage: bun falsify.ts <spec.ts> [--each]");
  process.exit(2);
}
const spec: Spec = (await import(resolve(specPath))).default;
const base = dirname(resolve(specPath));
// "./core.bend as C" -> "import /abs/core.bend as C": the scratch file lives elsewhere.
const head = ["import Base", ...spec.imports.map((i) => {
  const [path, ...rest] = i.split(" ");
  return `import ${path.startsWith(".") ? resolve(base, path) : path} ${rest.join(" ")}`;
})].join("\n");
const body = (xs: Spec["instances"]) => xs.map((x) => `def ${x.name}() -> ${x.claim}:\n  {==}`).join("\n\n");

const dir = mkdtempSync(join(tmpdir(), "falsify-"));
function run(file: string, text: string): string {
  writeFileSync(join(dir, file), text);
  // 5 s: a check that runs longer is a problem to fix (a large constant, a
  // fuel loop, application code in a goal), not a limit to raise.
  const r = Bun.spawnSync(["bend", join(dir, file), "--check-only"], { stdout: "pipe", stderr: "pipe", timeout: 5000 });
  if (r.exitedDueToTimeout) { console.log(`TIMEOUT: the checker ran past 5 s: a problem to fix, not a limit to raise (see AGENTS.md)`); process.exit(1); }
  return r.stdout.toString() + r.stderr.toString();
}
function report(out: string): string {
  const pick = (k: string) => out.match(new RegExp(`^- ${k}\\s*: (.*)$`, "m"))?.[1] ?? "?";
  return `expected ${pick("expected")} / observed ${pick("observed")}`;
}

try {
  const t0 = performance.now();
  if (flag !== "--each") {
    const out = run("all.bend", `${head}\n\n${body(spec.instances)}\n`);
    const ms = Math.round(performance.now() - t0);
    if (out.includes("All terms check")) {
      console.log(`holds on all ${spec.instances.length} instances (${ms} ms)`);
    } else {
      const loc = out.match(/^Location: (\S+)/m)?.[1];
      if (!loc) { console.log(out); process.exit(1); }
      const inst = spec.instances.find((x) => x.name === loc);
      console.log(`COUNTEREXAMPLE ${loc}: ${report(out)}`);
      if (inst) console.log(`  claim: ${inst.claim}`);
      process.exitCode = 1;
    }
  } else {
    const bad: string[] = [];
    let next = 0;
    let done = 0;
    const step = Math.max(1, Math.floor(spec.instances.length / 10));
    // Each instance is a checker run of ~0.15 s, so --each on thousands takes minutes.
    console.error(`checking ${spec.instances.length} instances one by one...`);
    // A few checkers at a time: one per instance at once would swamp the machine.
    const worker = async () => {
      for (let i = next++; i < spec.instances.length; i = next++) {
        const x = spec.instances[i];
        const file = join(dir, `i${i}.bend`);
        writeFileSync(file, `${head}\n\n${body([x])}\n`);
        const p = Bun.spawn(["bend", file, "--check-only"], { stdout: "pipe", stderr: "pipe", timeout: 5000 });
        const out = (await new Response(p.stdout).text()) + (await new Response(p.stderr).text());
        await p.exited;
        if (p.signalCode) bad.push(`${x.name}: TIMEOUT, the checker ran past 5 s: a problem to fix, not a limit to raise (see AGENTS.md)\n  claim: ${x.claim}`);
        else if (!out.includes("All terms check")) bad.push(`${x.name}: ${report(out)}\n  claim: ${x.claim}`);
        done++;
        if (done % step === 0) console.error(`  ${done}/${spec.instances.length} checked, ${bad.length} failing`);
      }
    };
    await Promise.all(Array.from({ length: Math.max(1, navigator.hardwareConcurrency || 4) }, worker));
    const ms = Math.round(performance.now() - t0);
    if (bad.length === 0) console.log(`holds on all ${spec.instances.length} instances, each alone (${ms} ms)`);
    else { console.log(`${bad.length} of ${spec.instances.length} instances fail:\n${bad.sort().join("\n")}`); process.exitCode = 1; }
  }
} finally {
  rmSync(dir, { recursive: true, force: true });
}
