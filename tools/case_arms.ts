// case_arms: fill a proof's case table from its constructors.
//
// A proof over an abstract value enumerates its constructors: a `match s r:`
// on a Schema and a Raw has one arm per pair, and adding a constructor adds
// an arm to every such table. Most arms are the same leaf (`{==}`, or one
// rewrite pattern), so they are generated; the arms that say something are
// written by hand and kept as they are.
//
// A table is a def preceded by directives:
//
//   # arms: s r                      the match's columns (the def's parameters)
//   # arms leaf: {==}                the leaf; repeat the line for more lines
//   # arms why: SNat=C.NotNat{} RMissing=C.Missing{} SVEnd.REnd=C.NoVariant{}
//   # arms accept: SNat.RNum SOpt.RNull  pairs the leaf is not for: the value
//   # arms accept leaf: ...             is accepted, and these get this leaf
//
// In the leaf, $S and $R are the scrutinees' values for the arm (as
// expressions, binders unmarked) and $W the reason from `why`: a pair key
// (SVEnd.REnd) first, then the raw constructor, then the schema's. An arm
// written by hand is any arm that is not the leaf for its pair; a column
// pattern that is a variable covers the rest of its row.
//
//   bun tools/case_arms.ts --write PROOF.bend    fill every table
//   bun tools/case_arms.ts --check PROOF.bend    fail if a table is not filled
//
// The constructors come from the file PROOF.bend imports `as C` (the core).

import { readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";

type Ctor = { name: string; fields: string[] };

export function readTypes(core: string): Map<string, Ctor[]> {
  const types = new Map<string, Ctor[]>();
  const lines = core.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const m = lines[i].match(/^type (\w+)(?:<[^>]*>)? is Data:\s*$/);
    if (!m) continue;
    const ctors: Ctor[] = [];
    for (let j = i + 1; j < lines.length && /^\s+\S/.test(lines[j]); j++) {
      const c = lines[j].trim().match(/^(\w+)\{(.*)\}$/);
      if (!c) continue;
      // Fields are `name: Type`; a type may hold commas (`List<&2, String>`),
      // so a field starts at each `name:` rather than after each comma.
      const fields = [...c[2].matchAll(/(?:^|,)\s*(\w+)\s*:/g)].map((f) => f[1]);
      ctors.push({ name: c[1], fields });
    }
    types.set(m[1], ctors);
  }
  return types;
}

type Arm = { header: string; body: string[]; key: string[] | null };

// The constructor name of each column in an arm's pattern, or null for a
// variable. `C.SList{+e} C.RCons{h, t}` gives ["SList", "RCons"].
function patternKey(pat: string, n: number): (string | null)[] {
  const out: (string | null)[] = [];
  let i = 0;
  const s = pat.trim();
  while (out.length < n && i < s.length) {
    while (s[i] === " ") i++;
    let j = i, depth = 0;
    while (j < s.length && (depth > 0 || s[j] !== " ")) {
      if (s[j] === "{") depth++;
      if (s[j] === "}") depth--;
      j++;
    }
    const tok = s.slice(i, j);
    const m = tok.match(/^(?:\w+\.)?([A-Z]\w*)\{/);
    out.push(m ? m[1] : null);
    i = j;
  }
  return out;
}

function splitPattern(pat: string): string[] {
  const out: string[] = [];
  let i = 0;
  const s = pat.trim();
  while (i < s.length) {
    while (s[i] === " ") i++;
    let j = i, depth = 0;
    while (j < s.length && (depth > 0 || s[j] !== " ")) {
      if (s[j] === "{") depth++;
      if (s[j] === "}") depth--;
      j++;
    }
    out.push(s.slice(i, j));
    i = j;
  }
  return out;
}

const unmark = (p: string) => p.replace(/\+/g, "");

type Table = { name: string; cols: string[]; types: string[]; leaf: string[]; why: Map<string, string>; accept: Set<string>; acceptLeaf: string[] };

function fill(table: Table, arms: Arm[], types: Map<string, Ctor[]>, prefix: string): string[] {
  const colCtors = table.types.map((t) => {
    const cs = types.get(t);
    if (!cs) throw new Error(`${table.name}: no type ${t} in the core`);
    return cs;
  });
  // The pattern a column's constructor is written with: the one a hand arm
  // uses (marks included: arms of one constructor mark their binders alike),
  // else its fields with trailing underscores, one per column (so a field
  // name two columns share, like SRule.s and RStr.s, binds twice apart).
  const written = new Map<string, string>();
  for (const a of arms) {
    splitPattern(a.header).forEach((p, c) => {
      const k = patternKey(p, 1)[0];
      if (k && !written.has(`${c}:${k}`)) written.set(`${c}:${k}`, p);
    });
  }
  const pat = (c: number, ct: Ctor) =>
    written.get(`${c}:${ct.name}`) ?? `${prefix}${ct.name}{${ct.fields.map((f) => f + "_".repeat(c + 1)).join(", ")}}`;
  const reason = (ks: string[]) => {
    const w = table.why.get(ks.join(".")) ?? table.why.get(ks[ks.length - 1]) ?? table.why.get(ks[0]);
    return w;
  };
  const leafFor = (pats: string[], ks: string[]): string[] | null => {
    const sub = (ls: string[], w: string) => ls.map((l) => l.replaceAll("$S", unmark(pats[0])).replaceAll("$R", unmark(pats[1] ?? "")).replaceAll("$W", w));
    if (table.accept.has(ks.join("."))) return sub(table.acceptLeaf, "");
    let w = "";
    if (table.leaf.some((l) => l.includes("$W"))) {
      const r = reason(ks);
      if (!r) return null;
      w = r;
    }
    return sub(table.leaf, w);
  };
  const hand = arms.filter((a) => {
    const ks = patternKey(a.header, table.cols.length);
    if (ks.some((k) => k === null)) return true;
    const want = leafFor(splitPattern(a.header), ks as string[]);
    return !want || want.join("\n") !== a.body.map((l) => l.slice(6)).join("\n");
  });
  const handKey = (a: Arm) => patternKey(a.header, table.cols.length);
  const out: string[] = [];
  const emit = (pats: string[], body: string[]) => {
    out.push(`    case ${pats.join(" ")}:`);
    for (const l of body) out.push("      " + l);
  };
  const rows = colCtors[0];
  for (const sc of rows) {
    const inRow = hand.filter((a) => handKey(a)[0] === sc.name);
    if (table.cols.length === 1) {
      if (inRow.length) inRow.forEach((a) => out.push(a.header, ...a.body));
      else {
        const b = leafFor([pat(0, sc)], [sc.name]);
        if (!b) throw new Error(`${table.name}: no arm for ${sc.name}, and no reason for a leaf`);
        emit([pat(0, sc)], b);
      }
      continue;
    }
    // A variable in the second column covers what the row has not matched.
    const wild = inRow.find((a) => handKey(a)[1] === null);
    for (const rc of colCtors[1]) {
      const a = inRow.find((x) => handKey(x)[1] === rc.name);
      if (a) { out.push(a.header, ...a.body); continue; }
      if (wild) continue;
      const pats = [pat(0, sc), pat(1, rc)];
      const b = leafFor(pats, [sc.name, rc.name]);
      if (!b) throw new Error(`${table.name}: no arm for ${sc.name} ${rc.name}, and no reason for a leaf`);
      emit(pats, b);
    }
    if (wild) out.push(wild.header, ...wild.body);
  }
  return out;
}

export function process(proof: string, core: string, prefix = "C."): string {
  const types = readTypes(core);
  const lines = proof.split("\n");
  const out: string[] = [];
  const fresh = () => ({ leaf: [] as string[], why: new Map<string, string>(), accept: new Set<string>(), acceptLeaf: [] as string[] });
  let pending: { cols?: string[] } & ReturnType<typeof fresh> = fresh();
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    let m;
    if ((m = l.match(/^# arms: (.+)$/))) pending.cols = m[1].trim().split(/\s+/);
    else if ((m = l.match(/^# arms leaf: ?(.*)$/))) pending.leaf.push(m[1]);
    else if ((m = l.match(/^# arms accept leaf: ?(.*)$/))) pending.acceptLeaf.push(m[1]);
    else if ((m = l.match(/^# arms accept: (.+)$/))) for (const k of m[1].trim().split(/\s+/)) pending.accept.add(k);
    else if ((m = l.match(/^# arms why: (.+)$/))) for (const kv of m[1].trim().split(/\s+/)) { const [k, v] = kv.split("="); pending.why.set(k, v); }
    out.push(l);
    if (!pending.cols || !l.startsWith("def ")) continue;
    const name = l.match(/^def ([\w.]+)\(/)![1];
    const types_ = pending.cols.map((c) => {
      const t = l.match(new RegExp(`[(,]\\s*\\+?${c}: (?:\\w+\\.)?(\\w+)`));
      if (!t) throw new Error(`${name}: no parameter ${c} in its signature`);
      return t[1];
    });
    const table: Table = { name, cols: pending.cols, types: types_, leaf: pending.leaf, why: pending.why, accept: pending.accept, acceptLeaf: pending.acceptLeaf };
    pending = fresh();
    const mline = lines[++i];
    if (mline.trim() !== `match ${table.cols.join(" ")}:`) throw new Error(`${name}: expected "match ${table.cols.join(" ")}:" after the def`);
    out.push(mline);
    const arms: Arm[] = [];
    i++;
    while (i < lines.length && lines[i].startsWith("    ")) {
      const header = lines[i];
      if (!/^    case .*:$/.test(header)) throw new Error(`${name}: expected a case at "${header}"`);
      const body: string[] = [];
      i++;
      while (i < lines.length && lines[i].startsWith("      ")) body.push(lines[i++]);
      arms.push({ header, body, key: null });
    }
    i--;
    for (const a of arms) a.header = a.header.replace(/^    case (.*):$/, "$1");
    const armsFull = arms.map((a) => ({ ...a }));
    const filled = fill(table, armsFull, types, prefix);
    out.push(...filled.map((x) => (x.startsWith("    ") ? x : `    case ${x}:`)));
  }
  return out.join("\n");
}

if (import.meta.main) {
  const [mode, file] = process_argv();
  const proof = readFileSync(file, "utf8");
  const imp = proof.match(/^import (\S+) as C$/m);
  if (!imp) throw new Error(`${file}: no "import ... as C" to read the constructors from`);
  const core = readFileSync(join(dirname(file), imp[1]), "utf8");
  const got = process(proof, core);
  if (mode === "--write") {
    writeFileSync(file, got);
  } else if (got !== proof) {
    const a = proof.split("\n"), b = got.split("\n");
    let k = 0;
    while (k < a.length && a[k] === b[k]) k++;
    console.error(`FAIL: ${file} is not what case_arms fills (first difference at line ${k + 1}); run bun tools/case_arms.ts --write ${file}`);
    console.error(`  file:      ${a[k] ?? "(end)"}\n  generated: ${b[k] ?? "(end)"}`);
    globalThis.process.exit(1);
  }
}

function process_argv(): [string, string] {
  const [mode, file] = globalThis.process.argv.slice(2);
  if ((mode !== "--write" && mode !== "--check") || !file) {
    console.error("usage: bun tools/case_arms.ts --write|--check PROOF.bend");
    globalThis.process.exit(2);
  }
  return [mode, file];
}
