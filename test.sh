#!/bin/sh
# bend-schema's gate. Each step checks one claim, and each can fail:
#
#   1. the laws are proved, with no unsafe code, and each fails when made false
#   2. the core builds into a typed module, and what it builds is what is
#      committed in dist-core/
#   3. the tests pass: the codec, and the check at run time
#   4. the host typechecks
#   5. the Base facts this core's proofs import are proved, and one of them is
#      made false to show that check can fail
#
# Usage: sh test.sh
#
# bend is a build-time dependency of this repository alone: the package ships
# dist-core/, so a user of the package never installs bend. This is the one
# step that needs it, and it is why dist-core/ is committed (D8).

set -e
cd "$(dirname "$0")"

# The installed compiler, wherever it is; the recorded one is recorded, not
# required (a bump with the same output is not a change).
PATH="$HOME/.bend/bin:$PATH"
export PATH
BEND_NO_TELEMETRY=1
export BEND_NO_TELEMETRY

echo "== 1. the laws =="
# The case tables' leaf arms are generated (tools/case_arms.ts): a new
# constructor is one --write away, and a hand edit that drifts fails here.
bun tools/case_arms.ts --check core/PROOF.bend
OUT=$(tools/bend-check core/PROOF.bend 2>&1) || { echo "$OUT"; exit 1; }
echo "$OUT"
if echo "$OUT" | grep -q "rely on unsafe\|relies on unsafe"; then
  echo "FAIL: a proof relies on unsafe code, which proves anything"
  exit 1
fi
if ! bun core/check_mutants.ts > /tmp/bend-schema-mutants.log 2>&1; then
  cat /tmp/bend-schema-mutants.log
  echo "FAIL: a mutant check failed"
  exit 1
fi
cat /tmp/bend-schema-mutants.log

echo "== 2. the module =="
# dist-core/ is committed and pinned: build it fresh elsewhere and diff, so a
# compiler bump that changes the module is a visible change, not a surprise.
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
bun tools/bend_lib.ts core/core.bend "$TMP" > /dev/null
if ! cmp -s dist-core/core.js "$TMP/core.js" || ! cmp -s dist-core/core.d.ts "$TMP/core.d.ts"; then
  echo "FAIL: dist-core/ is not what $(cat dist-core/BEND-VERSION) builds here"
  diff -u dist-core/core.js "$TMP/core.js" | head -40
  diff -u dist-core/core.d.ts "$TMP/core.d.ts" | head -40
  echo "FAIL: rebuild and commit dist-core/ if the new module is wanted"
  exit 1
fi
echo "dist-core/ is what $(cat dist-core/BEND-VERSION) builds"

echo "== 3. the tests =="
if ! bun test > /tmp/bend-schema-tests.log 2>&1; then
  tail -20 /tmp/bend-schema-tests.log
  echo "FAIL: a test failed"
  exit 1
fi
tail -3 /tmp/bend-schema-tests.log

echo "== 4. the types =="
bunx tsc -p .

echo "== 5. the facts this core rests on =="
sh core/base-facts/test.sh

echo "PASS: bend-schema's gate"
