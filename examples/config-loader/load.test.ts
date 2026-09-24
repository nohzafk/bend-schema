// What the schema in load.ts buys: a good file parses to a typed value, and
// every way of getting it wrong is named at its path.

import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { loadConfig } from "./load.ts";

const read = (f: string) => readFileSync(new URL(`./${f}`, import.meta.url), "utf8");

const config = (json: unknown) => loadConfig(JSON.stringify(json));

describe("a good config", () => {
  test("parses, and the value is typed", () => {
    const r = loadConfig(read("good.json"));
    expect(r.ok).toBe(true);
    if (!r.ok) return;
    expect(r.value.name).toBe("assets-deploy");
    expect(r.value.notify).toBe("ops@example.com");
    expect(r.value.targets).toHaveLength(3);

    // The tag narrows: `t.type === "s3"` leaves t with bucket/region/prefix,
    // and the else branch with host/port/user. tsc checks this, not bun.
    const t = r.value.targets[2]!;
    if (t.type === "s3") {
      const bucket: string = t.bucket;
      const region: "eu-west-1" | "us-east-1" | "us-west-2" = t.region;
      const prefix: string | null = t.prefix;
      expect([bucket, region, prefix]).toEqual(["assets-us", "us-east-1", null]);
    } else {
      const port: number = t.port;
      expect(port).toBeNaN();
    }
  });
});

describe("a typo'd key", () => {
  test("is an error at its path, not ignored", () => {
    const r = loadConfig(read("typo.json"));
    expect(r.ok).toBe(false);
    if (r.ok) return;
    expect(r.error).toBe("config.targets[1].regoin: is not a key this object allows");
  });

  test("the same key is refused whether it is extra or alone", () => {
    // `regoin` where `regoin` belongs: with `region` gone too, the walk names
    // the absent field first -- a named key is checked before unknown ones.
    const r = config({
      name: "x",
      notify: null,
      targets: [{ type: "s3", bucket: "b", regoin: "us-east-1", prefix: null }],
    });
    expect(r.ok).toBe(false);
    if (!r.ok) expect(r.error).toBe("config.targets[0].region: missing");
  });
});

describe("other ways to be wrong", () => {
  test("a tag no case claims", () => {
    const r = loadConfig(read("wrong-tag.json"));
    expect(r.ok).toBe(false);
    if (!r.ok) expect(r.error).toBe("config.targets[1].type: is not one of the allowed names");
  });

  test("a port outside the bound", () => {
    const r = config({
      name: "x",
      notify: null,
      targets: [{ type: "ssh", host: "h", port: 70000, user: "u" }],
    });
    expect(r.ok).toBe(false);
    if (!r.ok) expect(r.error).toBe("config.targets[0].port: must be from 1 to 65535");
  });

  test("a nullable key that is absent, not null", () => {
    const r = loadConfig(read("missing.json"));
    expect(r.ok).toBe(false);
    if (!r.ok) expect(r.error).toBe("config.notify: missing");
  });

  test("a file that is not JSON", () => {
    const r = loadConfig("{ nope");
    expect(r.ok).toBe(false);
    if (!r.ok) expect(r.error).toMatch(/^config: not JSON: /);
  });
});

describe("the CLI", () => {
  test("prints the config, and exits 1 on an error", () => {
    const run = (f: string) => Bun.spawnSync(["bun", "load.ts", f], { cwd: import.meta.dir });
    const good = run("good.json");
    expect(good.exitCode).toBe(0);
    expect(JSON.parse(good.stdout.toString()).name).toBe("assets-deploy");

    const bad = run("typo.json");
    expect(bad.exitCode).toBe(1);
    expect(bad.stderr.toString().trim()).toBe("config.targets[1].regoin: is not a key this object allows");
  });
});
