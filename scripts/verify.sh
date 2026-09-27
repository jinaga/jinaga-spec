#!/usr/bin/env bash
# Everything that must hold, in one command. Exits non-zero on the first failure.
#
#   scripts/verify.sh                      # Lean, vectors, randomized check, TypeScript port
#   JINAGA_JS=/path/to/jinaga.js scripts/verify.sh
#
# The TypeScript step runs only if a jinaga.js checkout is found (JINAGA_JS, or a
# sibling directory named jinaga.js).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

echo "== Lean: definitions and proofs"
lake build

echo "== No sorry, no added axioms"
if grep -rnE "sorry|^axiom|native_decide" JinagaSpec; then
  echo "found a forbidden construct"; exit 1
fi
tmp="$(mktemp -d)"; printf 'import JinagaSpec\n#print axioms JinagaSpec.split_correct\n#print axioms JinagaSpec.isWellFormed_iff\n' > "$tmp/a.lean"
lake env lean "$tmp/a.lean" | tee "$tmp/out.txt"
if grep -q sorryAx "$tmp/out.txt"; then echo "split_correct depends on sorry"; exit 1; fi

echo "== Vectors are up to date"
lake build vectors
tmp="$(mktemp -d)"; lake exe vectors "$tmp" > /dev/null
for kind in split well-formed; do
  diff -r "$tmp/$kind" "vectors/$kind" || { echo "vectors/$kind is out of date: run lake exe vectors"; exit 1; }
done
echo "vectors match the oracle"

echo "== Randomized check"
lake build check
for seed in 1 2 3; do lake exe check "$seed" | grep -E "specs|cases"; done

jinaga="${JINAGA_JS:-../jinaga.js}"
if [ -d "$jinaga/src/specification" ]; then
  jinaga="$(cd "$jinaga" && pwd)"
  echo "== TypeScript port against $jinaga"
  (cd ports/typescript && npm ci --silent && JINAGA_JS="$jinaga" npm run --silent vectors | grep -E "vectors pass|FAIL"; npm run --silent audit | tail -2)
else
  echo "== TypeScript port skipped (no jinaga.js checkout at $jinaga)"
fi
echo "OK"
