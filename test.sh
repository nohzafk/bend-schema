#!/bin/sh
# bend-schema's gate. Each step checks one claim, and each can fail:
#
#   1. the laws are proved, with no unsafe code, and each fails when made false
#   1b. and each law holds on the concrete instances of it that
#      core/falsify/spec.ts generates, edge cases first
#   2. the core builds into a typed module, and what it builds is what is
#      committed in dist-core/
#   3. the tools' fixtures build into modules, and the tests pass: the codec,
#      the two tools built on fixtures, and the check at run time
#   4. the hosts typecheck: this package's src/, and the tools' fixture host
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

echo "== 1b. the laws on concrete instances =="
# Before a proof is written, a law is falsified on literal instances of it
# (core/falsify/spec.ts): the checker runs the code on them, so an instance
# that holds is one the law really covers. Each law is checked alone, because
# the checker stops at the first failing instance and the one that fails names
# the law it belongs to. A falsifier that has never failed proves nothing:
# tools/falsify.ts takes CORE=<path> as C to point it at a mutated copy of the
# core, which is how that is shown.
for L in exact accurate enum_accepts enum_admits variant strict tuple tagged \
         too_large rules sbool_meaning snat_in_meaning sstr_len_meaning \
         soptional_meaning slist_len_meaning; do
  if ! OUT=$(LAW=$L bun tools/falsify.ts core/falsify/spec.ts 2>&1); then
    echo "$OUT"
    echo "FAIL: $L does not hold on the instances it is checked over"
    exit 1
  fi
  echo "  $L: $OUT"
done

echo "== 2. the module =="
# dist-core/ is committed and pinned: build it fresh elsewhere and diff, so a
# compiler bump that changes the module is a visible change, not a surprise.
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
bunx bend-emit core/core.bend "$TMP" > /dev/null
if ! cmp -s dist-core/core.js "$TMP/core.js" || ! cmp -s dist-core/core.d.ts "$TMP/core.d.ts"; then
  echo "FAIL: dist-core/ is not what $(cat dist-core/BEND-VERSION) builds here"
  diff -u dist-core/core.js "$TMP/core.js" | head -40
  diff -u dist-core/core.d.ts "$TMP/core.d.ts" | head -40
  echo "FAIL: rebuild and commit dist-core/ if the new module is wanted"
  exit 1
fi
echo "dist-core/ is what $(cat dist-core/BEND-VERSION) builds"

echo "== 3. the tests =="
# The module builder is the bend-emit dev dependency; its repository holds
# the five fixture cores it is tested on, and its test.sh gates the builder.
# What is left under tools/test/ is case_arms.ts's test, whose core is
# written in the test file itself -- nothing to build first.
if ! bun test > /tmp/bend-schema-tests.log 2>&1; then
  tail -20 /tmp/bend-schema-tests.log
  echo "FAIL: a test failed"
  exit 1
fi
tail -3 /tmp/bend-schema-tests.log

echo "== 4. the types =="
bunx tsc -p .

echo "== 4b. the printer =="
# Every constructor the builder has, printed by the real command and then
# compiled by bend. A constructor with no case throws; one printed wrongly is a
# Bend error. Neither can be a silent difference, which is the point: the core's
# constructors and this printer must agree on every one of them.
# Inside the package: the import the command writes is a path relative to the
# output file, so a file outside the tree has to climb out of it -- and /var is
# a symlink on macOS, so the climb lands where nothing exists.
GEN=$(mktemp -d "$PWD/tmp.gen.XXXXXX")
trap 'rm -rf "$TMP" "$GEN"' EXIT
bun src/gen-cli.ts src/gen.schemas.ts "$GEN/schemas.bend"
tools/bend-check "$GEN/schemas.bend"

echo "== 5. the facts this core rests on =="
sh core/base-facts/test.sh

echo "PASS: bend-schema's gate"
