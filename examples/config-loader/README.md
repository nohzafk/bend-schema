# config-loader — a deploy config, with one proved check

`load.ts` builds the schema for a small deploy config and reads a file into it.
`bun load.ts <file.json>` prints the parsed config, or one line saying what is
wrong, and exits 1.

```sh
bun load.ts good.json          # the config, as JSON; exit 0
bun load.ts typo.json          # config.targets[1].regoin: is not a key this object allows; exit 1
bun test .                     # 8 tests: the schema, the fixtures, the CLI
```

Fixtures: `good.json` (a valid file, both target kinds), `typo.json` (an s3
target that also carries the misspelled `regoin`), `wrong-tag.json`
(`"type": "ftp"`, which no case claims), `missing.json` (no `notify`, which is
`nullable` — a key the schema names must be present, as `null`; absent is
reported `missing`).

What this buys over a hand-written zod schema is one thing: **a key the schema
does not name is an error, at its path, and that is proved for every schema,
not for this one.** `.strict()` is the core's `SStrict`, whose law
`strict_meaning` states `conforms(~rule, SStrict{s}, r) ==
conforms(~rule, s, r) and count_unknown(key_names(s), r) == 0` — "it conforms
to s, and it has no key s does not name" — and the core reports the first such
key at `AtKey{key}`, which is where `config.targets[1].regoin` comes from. The
tag is the core's `STagged` too: `tagged_meaning` says a case conforms by the
object **without** its tag when the tag is the case's name, else by the rest,
and `tag_end_refuses` says the end of the chain accepts nothing — so
`"type": "ftp"` is `config.targets[1].type: is not one of the allowed names`
rather than a parsed value with no target, and an s3 case need not name `type`.
Both laws sit under `check_exact` (check finds nothing exactly when the value
conforms) and `check_accurate` (following the reported path, everything passed
on the way conforms, and the value at the end is wrong in the reported way), so
the error's path is not a convention here, it is the claim. zod's default
`z.object` does the opposite: it strips unknown keys silently, so `regoin`
disappears and the config looks fine. Two honest edges: the laws pin the core's
`check`/`conforms`, not this file's builder or the JS conversion (that is what
`src/index.test.ts` round-trips), and a field is checked before unknown keys are
counted, so if `regoin` is written *instead of* `region`, the first error is the
absent one — `config.targets[0].region: missing` — and `regoin` is not named
until `region` is back (both are errors; that one just comes first).
