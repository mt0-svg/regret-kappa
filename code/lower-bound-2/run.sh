#!/bin/sh
# Second programs of the lower bound (Section 7.3 of the paper). Run from anywhere; complete outputs go to out/.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
run() { # name, then the command
  name=$1; shift
  start=$(date +%s)
  "$@" < /dev/null > "out/$name.txt" 2>&1 || true
  echo "elapsed: $(( $(date +%s) - start )) s" >> "out/$name.txt"
}
run drift gp -q -s 1G gp/drift.gp
CEX=1 run cex1 gp -q -s 1G gp/cex.gp
CEX=2 run cex2 gp -q -s 1G gp/cex.gp
run constants gp -q -s 1G gp/constants.gp
run phase2 gp -q -s 1G gp/phase2.gp
run identities gp -q -s 1G gp/identities.gp
run kstar gp -q -s 1G gp/kstar.gp
run mc_phase1 gp -q -s 1G gp/mc_phase1.gp
# the author's certificate on the two counterexample tables (one table entry replaced; the copy lives in a temp dir)
tmp=$(mktemp -d)
src="$here/../lower-bound/drift_check.gp"
line='tab = vector(28, j, round(5/8 * exp(-((j-1)/10 + 1/20)^2 / 2) * 10^4) / 10^4);'
grep -qF "$line" "$src"
for c in 1 2; do
  if [ "$c" = 1 ]; then edit='tab[17] = 1852/10000;'; else edit='tab[28] = 50/10000;'; fi
  awk -v l="$line" -v e="$edit" '{ print } $0 == l { print e }' "$src" > "$tmp/author_cex$c.gp"
  grep -qF "$edit" "$tmp/author_cex$c.gp"
  run "author_cert_on_cex$c" gp -q -s 1G "$tmp/author_cex$c.gp"
done
rm -r "$tmp"
# the author's scripts rerun, compared with their recorded outputs
: > out/author_rerun.txt
for s in drift_check total_bound phase2_check; do
  (cd ../lower-bound && gp -q -s 1G "$s.gp" < /dev/null 2>&1) > "out/author_rerun_$s.txt"
  if diff -q "out/author_rerun_$s.txt" "../lower-bound/$s.out" > /dev/null; then
    echo "$s: rerun identical to the recorded output" >> out/author_rerun.txt
  else
    echo "$s: rerun DIFFERS from the recorded output" >> out/author_rerun.txt
  fi
  rm "out/author_rerun_$s.txt"
done
grep -h "PASS\|FAIL\|VIOLATION\|identical\|DIFFERS" out/*.txt
