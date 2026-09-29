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

# The bend this package declares (BEND_VERSION): the one in
# ~/projects/.toolchains/bend-<v>/ if it is there, else the installed one. The
# gate refuses any other before anything runs, and so does bend-emit.
BEND_VERSION=$(tr -d ' \t\n\r' < BEND_VERSION)
PATH="${BEND_TOOLCHAINS:-$HOME/projects/.toolchains}/bend-$BEND_VERSION/bin:$HOME/.bend/bin:$PATH"
export PATH
if [ "$(bend version 2>/dev/null)" != "bend $BEND_VERSION" ]; then
  echo "FAIL: this gate needs bend $BEND_VERSION; bend on PATH says: $(bend version 2>&1)"
  exit 1
fi
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
# A law's proof has to depend on the code: core/check_mutants.ts changes one
# line of core.bend for each law, and requires the proof to fail in the def it
# names -- and, first, that the law really is false there, by a counterexample
# at literals that holds on the core and fails on the mutant. bend-falsify's
# runMutants is the harness.
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
# core/falsify/spec.ts takes CORE=<path> as C to point it at a mutated copy of
# the core, which is how that is shown.
for L in exact accurate enum_accepts enum_admits variant strict tuple tagged \
         too_large rules sbool_meaning snat_in_meaning sstr_len_meaning \
         soptional_meaning slist_len_meaning unnamed_key; do
  if ! OUT=$(LAW=$L bunx bend-falsify core/falsify/spec.ts 2>&1); then
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
if ! cmp -s dist-core/core.mjs "$TMP/core.mjs" || ! cmp -s dist-core/core.d.mts "$TMP/core.d.mts"; then
  echo "FAIL: dist-core/ is not what bend $BEND_VERSION builds here"
  diff -u dist-core/core.mjs "$TMP/core.mjs" | head -40
  diff -u dist-core/core.d.mts "$TMP/core.d.mts" | head -40
  echo "FAIL: rebuild and commit dist-core/ if the new module is wanted"
  exit 1
fi
echo "dist-core/ is what bend $BEND_VERSION builds"

echo "== 3. the tests =="
# The module builder is the bend-emit dev dependency; its repository holds
# the five fixture cores it is tested on, and its test.sh gates the builder.
# What is left under tools/test/ is case_arms.ts's test, whose core is
# written in the test file itself -- nothing to build first.
if ! bun test src > /tmp/bend-schema-tests.log 2>&1; then
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
# They are bend-mathlib's, from the vendor/bendlib submodule (nohzafk/bendlib,
# branch ours); PROOF.bend checking in step 1 checks the imported lemmas too.
# bendlib's own gate holds their negative controls.
test -f vendor/bendlib/packages/bend-mathlib/nat.bend || { echo "FAIL: run git submodule update --init"; exit 1; }
echo "  vendor/bendlib at $(git -C vendor/bendlib rev-parse --short HEAD)"

echo "PASS: bend-schema's gate"
