# config-loader — read a config file, report the first mistake

`load.ts` reads a JSON deploy config and checks it against a schema.

- Valid file → prints the parsed config, exit code 0.
- Invalid file → prints **one line** saying where and what is wrong, exit code 1.

## Try it

Run these from this directory (`examples/config-loader`):

```sh
bun load.ts good.json          # prints the config; exit 0
bun load.ts typo.json          # config.targets[1].regoin: is not a key this object allows; exit 1
bun test .                     # 8 tests: the schema, the fixtures, the CLI
```

## Files

| File | What it is |
|---|---|
| `load.ts` | the `Config` schema, `loadConfig(text)`, and the CLI |
| `load.test.ts` | the tests |
| `good.json` | a valid config, with both target kinds |
| `typo.json` | an s3 target with a misspelled extra key, `regoin` |
| `wrong-tag.json` | a target with `"type": "ftp"`, which is not a known kind |
| `missing.json` | no `notify` key (see "nullable" below) |

## The schema

A config is a strict object (unknown keys are errors):

| Field | Rule |
|---|---|
| `name` | string, 1–64 characters |
| `notify` | string or `null`. The key must be present; write `null`, not nothing. |
| `targets` | list of targets. `"type"` picks the kind: |
| — `"type": "s3"` | `bucket` (1–63 chars), `region` (`eu-west-1`, `us-east-1`, `us-west-2`), `prefix` (string or `null`) |
| — `"type": "ssh"` | `host`, `port` (1–65535), `user` |

## Why this is better than a default zod schema

**Typos are caught, not ignored.** zod's default `z.object` silently drops keys it
does not know. So a misspelled `regoin` just disappears and the config looks fine.
Here, `.strict()` makes an unknown key an error, reported at its exact path:

```
config.targets[1].regoin: is not a key this object allows
```

**Unknown kinds are caught.** `"type": "ftp"` matches no case, so it is an error:

```
config.targets[1].type: is not one of the allowed names
```

— not a parsed value with no target.

**This behaviour is proved, not just tested.** It holds for every schema, not only
this one. The laws are in `core/LAWS.bend`:

- `strict_meaning` — a strict object is valid only if the inner object is valid
  *and* it has no key the schema does not name.
- `tagged_meaning` / `tag_end_refuses` — a tagged value is checked against the case
  its tag names; a tag that names no case is refused.
- `check_exact` — the checker finds no error exactly when the value is valid.
- `check_accurate` — when the checker reports an error at a path, the value at that
  path really is wrong in that way.

So the path in the error message is not a best guess; it is part of what is proved.

## Two things to know

1. **Order of errors.** Missing fields are checked before unknown keys. If you write
   `regoin` *instead of* `region`, the first error is
   `config.targets[0].region: missing`. `regoin` is only reported once `region` is
   back. Both are errors; one just comes first.
2. **What is not proved.** The laws cover the core checker. They do not cover the
   TypeScript builder in `load.ts` or the conversion between JS values and the
   core's values. That conversion is tested in `src/index.test.ts`.
