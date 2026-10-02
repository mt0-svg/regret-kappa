#!/bin/bash
# Runs the two piece programs of item (3) of Computation 3.13 (pieces.gp and pieces_lean.gp) twice each, compares
# each output with the recorded one (out/pieces.txt, out/pieces_lean.txt) and prints the wall time of each run.
# Run from this directory: bash pieces_rerun.sh > out/pieces_rerun.txt
set -u
cd "$(dirname "$0")" || exit 1
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
echo "pieces rerun, $(date -u +%Y-%m-%dT%H:%M:%SZ); pari $(echo 'print(version())' | gp -q 2>&1 | head -1)"
fail=0
for pass in 1 2; do
  for p in pieces pieces_lean; do
    t0=$(date +%s.%N)
    gp -q "$p.gp" < /dev/null > "$tmp/$p.txt" 2>&1
    rc=$?
    t=$(echo "$(date +%s.%N) - $t0" | bc)
    if cmp -s "$tmp/$p.txt" "out/$p.txt"; then same="SAME as recorded"; else same="DIFFERS from recorded"; fail=1; fi
    [ "$rc" -eq 0 ] || fail=1
    printf 'pass %s: %s.gp exit %s, %.1f s, out/%s.txt %s\n' "$pass" "$p" "$rc" "$t" "$p" "$same"
  done
done
if [ "$fail" -eq 0 ]; then echo "overall: every run exits 0 and reproduces its recorded output"; else echo "overall: FAILED"; fi
exit "$fail"
