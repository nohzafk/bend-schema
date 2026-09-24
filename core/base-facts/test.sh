#!/bin/sh
# Every def in these files returns an equation, so type checking is the
# proof: if a fact stopped being true, the file would not compile.
#
# A gate that has never rejected anything is not a gate, so this also takes
# one fact, makes it false, and requires the check to fail.
#
# These are the facts this core's proofs import (core/PROOF.bend). The list is
# the files this repository carries; a file added here is checked here too.
set -e
cd "$(dirname "$0")"

FILES="comparison.bend nat_le.bend string_eq.bend"
for f in $FILES; do
  if ../../tools/bend-check "$f" 2>&1 | grep -q "All terms check"; then
    echo "PASS $f"
  else
    echo "FAIL $f"
    ../../tools/bend-check "$f"
    exit 1
  fi
done

echo "== a false fact must be refused =="
W=$(mktemp -d)
sed 's/{True{} == String.eq(s, s) : Bool}/{False{} == String.eq(s, s) : Bool}/' \
  comparison.bend > "$W/comparison.bend"
if ! grep -q 'False{} == String.eq(s, s)' "$W/comparison.bend"; then
  echo "FAIL perturbation-did-not-apply"
  rm -rf "$W"
  exit 1
fi
if ../../tools/bend-check "$W/comparison.bend" 2>&1 | grep -q "All terms check"; then
  echo "FAIL false-fact-accepted"
  rm -rf "$W"
  exit 1
fi
rm -rf "$W"
echo "PASS false-fact-rejected"

echo "== an unsound string equality must be refused =="
W=$(mktemp -d)
sed 's/-> {a == b : Bool}:/-> {a == True{} : Bool}:/' string_eq.bend > "$W/string_eq.bend"
if ! grep -q '{a == True{} : Bool}' "$W/string_eq.bend"; then
  echo "FAIL perturbation-did-not-apply"
  rm -rf "$W"
  exit 1
fi
if ../../tools/bend-check "$W/string_eq.bend" 2>&1 | grep -q "All terms check"; then
  echo "FAIL unsound-equality-accepted"
  rm -rf "$W"
  exit 1
fi
rm -rf "$W"
echo "PASS unsound-equality-rejected"

echo "=== base-facts: all checks passed ==="
