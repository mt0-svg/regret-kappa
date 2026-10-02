#!/bin/sh
# Regenerates every output of out/ from scratch, each script under cap, and writes out/run.log
# (Sage version, commit, exit status, RESULT line and wall time of each script).
# Exits nonzero unless every script exits 0 with exactly one "RESULT <name> PASS" line.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
cd "$here" || exit 1
mkdir -p out
log=out/run.log
dirty=$(git status --porcelain -- . ":!out/run.log" | wc -l)
rm -f "$log"
{
  echo "sage: $(sage --version)"
  echo "commit: $(git rev-parse HEAD)"
  echo "uncommitted changes in this directory (out/run.log aside): $dirty"
} > "$log"
status=0
for s in drift_rational drift_arb phase1_constants phase2 total_bound identities negative_controls; do
  rm -f "out/$s.out"
  t0=$(date +%s)
  sage "$s.sage" > "out/$s.out" 2>&1
  rc=$?
  t1=$(date +%s)
  res=$(grep -c "^RESULT $s PASS$" "out/$s.out")
  echo "$s: exit $rc, RESULT PASS lines $res, $((t1 - t0)) s" >> "$log"
  if [ "$rc" -ne 0 ] || [ "$res" -ne 1 ]; then status=1; fi
done
if [ "$status" -eq 0 ]; then echo "overall: PASS" >> "$log"; else echo "overall: FAIL" >> "$log"; fi
cat "$log"
exit "$status"
