// Every law's proof has to fail when the law is made false.
//
// For each mutant: copy the project's core, laws and proof into a scratch tree,
// keep only the tools and one law's section of PROOF.bend, and check it twice --
// once as it is, where it must check, and once with the core mutated so the law
// no longer holds, where it must fail in the named def. A proof that still
// checks against a false law would be saying nothing about the core.
//
// Isolating one section per law matters: the checker stops at the first
// failing def, and proofs over the same definitions break together, so a mutant
// run against the whole file would be blamed on whichever proof comes first.
//
// The scratch tree mirrors the repository (<project>/ beside every sibling
// directory it imports -- base-facts/ and schema-lib/ next to it, or a
// directory inside it, like schema-lib's own base-facts/), because a relative
// import does not resolve from a bare temp directory.
//
// A project calls runMutants(projectDir, MUTANTS) from its own table file.
// It expects core.bend, LAWS.bend and PROOF.bend in projectDir, and a PROOF.bend
// whose shared lemmas sit under a header containing "tools".
//
// A law proved from other laws cannot be checked alone: its mutant names their
// sections in `with`, and the run keeps those sections and their laws too.
// meet-lib's merge_admits is proved from merge_covers and merge_separated.

import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { basename, dirname, join } from "node:path";

export interface Mutant {
  law: string;
  section: string; // the "# ---- <section> ----" header in PROOF.bend
  from: string; // a line of core.bend, replaced whole
  to: string;
  why: string; // why the law is false afterwards
  failsIn: string; // the def the checker must name
  // Other laws' sections this proof builds on, kept (with their laws) in the
  // run. A law proved from other laws cannot be checked alone.
  with?: string[];
}

// PROOF.bend as its head (imports) and its "# ---- name ----" sections.
function sections(text: string): { head: string; secs: [string, string][] } {
  const parts = text.split(/^(# ---- .* ----)$/m);
  const secs: [string, string][] = [];
  for (let i = 1; i < parts.length; i += 2) secs.push([parts[i], parts[i + 1]]);
  return { head: parts[0], secs };
}

// LAWS.bend with every law but the kept ones removed; its defs stay.
function onlyLaws(text: string, keep: string[]): string {
  return text
    .split(/^(?=law |# ---- |def )/m)
    .filter((b) => !b.startsWith("law ") || keep.some((k) => b.startsWith(`law ${k}:`)))
    .join("");
}

// Replace exactly one whole line of the core, or refuse: a mutation that does
// not apply would make the mutant identical to the control.
function mutate(text: string, from: string, to: string, law: string): string {
  const lines = text.split("\n");
  const hit = lines.indexOf(from);
  if (hit < 0) throw new Error(`${law}: the line to mutate is not in core.bend: ${JSON.stringify(from)}`);
  lines[hit] = to;
  return lines.join("\n");
}

export function runMutants(projectDir: string, mutants: Mutant[]): void {
  const core = readFileSync(join(projectDir, "core.bend"), "utf8");
  const laws = readFileSync(join(projectDir, "LAWS.bend"), "utf8");
  const proof = readFileSync(join(projectDir, "PROOF.bend"), "utf8");
  // Every directory the project imports relatively -- a sibling beside it
  // (../base-facts, ../schema-lib) or one inside it (./base-facts) -- is
  // copied to the matching place, so its relative imports resolve in the
  // scratch tree.
  const siblings = [...new Set([core, laws, proof].flatMap((text) =>
    [...text.matchAll(/^import (\.{1,2})\/([^/\s]+)\//gm)].map((m) => `${m[1]}/${m[2]}`)))];

  function check(coreText: string, lawName: string, section: string, withLaws: [string, string][]): { ok: boolean; location: string } {
    const root = mkdtempSync(join(tmpdir(), "bend-mutant-"));
    try {
      const dir = join(root, basename(projectDir));
      mkdirSync(dir);
      for (const sib of siblings) {
        const [up, name] = sib.split("/");
        const from = up === ".." ? join(dirname(projectDir), name) : join(projectDir, name);
        const to = up === ".." ? join(root, name) : join(dir, name);
        cpSync(from, to, { recursive: true, filter: (src) => !src.includes("node_modules") });
      }
      const { head, secs } = sections(proof);
      const wanted = [section, ...withLaws.map(([, sec]) => sec)].map((x) => `# ---- ${x} ----`);
      const kept = secs.filter(([h]) => h.includes("tools") || wanted.includes(h));
      if (!kept.some(([h]) => h === `# ---- ${section} ----`)) {
        throw new Error(`${lawName}: no section "${section}" in PROOF.bend`);
      }
      writeFileSync(join(dir, "core.bend"), coreText);
      writeFileSync(join(dir, "LAWS.bend"), onlyLaws(laws, [lawName, ...withLaws.map(([law]) => law)]));
      writeFileSync(join(dir, "PROOF.bend"), head + kept.map(([h, b]) => h + b).join(""));
      // 5 s, as tools/bend-check: a check that runs longer is a problem to fix.
      const r = Bun.spawnSync(["bend", "PROOF.bend"], { cwd: dir, timeout: 5000 });
      if (r.exitedDueToTimeout) throw new Error(`${lawName}: the checker ran past 5 s: a problem to fix, not a limit to raise (tools/bend-check, AGENTS.md)`);
      const out = r.stdout.toString() + r.stderr.toString();
      return { ok: out.includes("All terms check."), location: out.match(/^Location: (\S+)/m)?.[1] ?? "?" };
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  }

  let bad = 0;
  // A section named in `with` is kept with the law whose section it is.
  const lawOf = (sec: string): [string, string] => {
    const owner = mutants.find((x) => x.section === sec);
    if (!owner) throw new Error(`no mutant has the section "${sec}", so its law is unknown`);
    return [owner.law, sec];
  };
  for (const m of mutants) {
    const withLaws = (m.with ?? []).map(lawOf);
    const control = check(core, m.law, m.section, withLaws);
    const mutant = check(mutate(core, m.from, m.to, m.law), m.law, m.section, withLaws);
    const name = m.law.padEnd(26);
    if (!control.ok) {
      console.log(`  ${name} FAIL  the proof does not check even unmutated (${control.location})`);
      bad += 1;
    } else if (mutant.ok) {
      console.log(`  ${name} FAIL  still checks when ${m.why}`);
      bad += 1;
    } else if (mutant.location !== m.failsIn) {
      console.log(`  ${name} FAIL  failed in ${mutant.location}, not ${m.failsIn}, when ${m.why}`);
      bad += 1;
    } else {
      console.log(`  ${name} PASS  fails in ${m.failsIn} when ${m.why}`);
    }
  }
  if (bad > 0) {
    console.log(`FAIL: ${bad} of ${mutants.length} mutants did not break the proof they target`);
    process.exit(1);
  }
  console.log(`PASS: all ${mutants.length} mutants break the proof they target`);
}
