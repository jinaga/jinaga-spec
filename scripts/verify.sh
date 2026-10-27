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
tmp="$(mktemp -d)"; printf 'import JinagaSpec\n#print axioms JinagaSpec.split_correct\n#print axioms JinagaSpec.isWellFormed_iff\n#print axioms JinagaSpec.store_correct\n#print axioms JinagaSpec.store_denies\n#print axioms JinagaSpec.maintain_correct\n#print axioms JinagaSpec.evaluate_perm\n#print axioms JinagaSpec.shakeTree_bound\n#print axioms JinagaSpec.candidates_complete\n#print axioms JinagaSpec.notify_correct\n#print axioms JinagaSpec.stream_correct\n#print axioms JinagaSpec.reorderOrSelf_correct\n#print axioms JinagaSpec.read_reduceGivenConditions\n#print axioms JinagaSpec.stream_correct_given\n' > "$tmp/a.lean"
lake env lean "$tmp/a.lean" | tee "$tmp/out.txt"
if grep -q sorryAx "$tmp/out.txt"; then echo "one of the checked theorems depends on sorry"; exit 1; fi

echo "== Vectors are up to date"
lake build vectors
tmp="$(mktemp -d)"; lake exe vectors "$tmp" > /dev/null
for kind in split well-formed inverse; do
  diff -r "$tmp/$kind" "vectors/$kind" || { echo "vectors/$kind is out of date: run lake exe vectors"; exit 1; }
done
echo "vectors match the oracle"

echo "== Randomized check"
lake build check
for seed in 1 2 3; do lake exe check "$seed" | grep -E "specs|cases|maintain"; done

echo "== Randomized check of inversion"
lake build check-inverse
lake exe check-inverse 1 | grep -E "^specifications|^complete|^sound|^by rule|^batches|caught"

jinaga="${JINAGA_JS:-../jinaga.js}"
if [ -d "$jinaga/src/specification" ]; then
  jinaga="$(cd "$jinaga" && pwd)"
  echo "== TypeScript port against $jinaga"
  # Each step is its own statement, not chained with && or ;: under set -e, a
  # failure partway through an && list (e.g. cd or npm ci) does not stop the
  # script, and a later, unrelated command succeeding can mask it.
  (
    cd ports/typescript
    npm ci --silent
    JINAGA_JS="$jinaga" npm run --silent vectors | grep -E "vectors pass|vectors agree|FAIL"
    dump="$(mktemp -d)/inverse-dump.json"
    (cd ../.. && lake exe check-inverse dump "$dump" 1 > /dev/null)
    JINAGA_JS="$jinaga" npx tsx inverse-diff.ts "$dump" | grep -E "specifications|FAIL"
    JINAGA_JS="$jinaga" npm run --silent inverse | grep -E "inverse vectors|FAIL|misses changes"
    # The reference TypeScript implementation, against the vectors and against
    # the Lean definition on random specifications.
    JINAGA_JS="$jinaga" PORT=./inverse-candidates.ts npm run --silent inverse | grep -E "inverse vectors|FAIL"
    cands="$(mktemp -d)/candidates-dump.json"
    (cd ../.. && lake exe check-inverse dump-candidates "$cands" 1 > /dev/null)
    npx tsx reference-diff.ts "$cands" | grep -E "specifications|FAIL"
    npm run --silent audit | tail -2
  )
else
  echo "== TypeScript port skipped (no jinaga.js checkout at $jinaga)"
fi
echo "OK"
