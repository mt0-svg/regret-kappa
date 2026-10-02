#!/bin/bash
# Reruns, in a temporary copy of code/, every program of code/ outside formal-proof/ and compares each output file it
# writes with the recorded one, apart from the running times, dates and names of temporary files inside its lines.
# The committed outputs are not touched. The recorded pass:
#   bash code/rerun/layout.sh 1 > code/rerun/out/layout-pass1.txt
# A second argument, an extended regular expression, keeps only the programs whose name it matches: the job pari-gp of
# .github/workflows/ci.yml runs bash code/rerun/layout.sh ci '^(lower-bound|lean-upper-sharp)'.
# Not compared: upper-bound-certificate/out/run.txt, the log of the recorded run with its date and running times.
set -u
pass=${1:?usage: layout.sh N [NAMES]}
names=${2:-}
code=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp -r "$code" "$tmp/code"
mkdir -p "$tmp/RegretKappa/LowerSharp"    # drift_cells.gp writes ../../RegretKappa/LowerSharp/DriftCells.lean
echo "layout rerun, pass $pass, $(date -u +%Y-%m-%dT%H:%M:%SZ)"
sage=$(sage --version 2>/dev/null | head -1)
echo "pari: $(echo 'print(version())' | gp -q 2>&1 | head -1); ${sage:-no sage}"
# Running times, dates and names of temporary files are masked inside the lines; no line is dropped. The running
# times appear as "time 0.8 s", "elapsed: 3 s", ", 11.3 s" at the end of a line, "secs 1.1", and the last column of
# a table whose header ends with the column secs.
norm() {
  sed -E -e 's/(elapsed|time|wall)[: ]*[0-9]+(\.[0-9]+)? ?s\b/\1 <T>/gI' -e 's/, [0-9]+(\.[0-9]+)? s$/, <T> s/' \
    -e 's/\bsecs [0-9]+(\.[0-9]+)?$/secs <T>/' \
    -e 's/20[0-9]{2}-[0-9]{2}-[0-9]{2}[T ][0-9:]+Z?/<DATE>/g' -e 's#/tmp/[A-Za-z0-9._/-]*#/tmp/<temporary>#g' "$1" |
    awk -F '\t' -v OFS='\t' '$NF == "secs" { t = 1; print; next } t && NF > 1 && $1 ~ /^[0-9]+$/ { $NF = "<T>" } { print }'
}
fail=0
# name | directory (relative to code/) | command | outputs compared (relative to the directory; @F: the command's
# standard output, compared with F)
jobs='
upper-bound-certificate run|upper-bound-certificate|bash run.sh|out/t0_tools.txt out/c1_gamma.txt out/c2_small_steps.txt out/c3_large_steps.txt out/c4_terminal.txt out/c5_final.txt out/neg_fail.txt out/neg_raise.txt out/neg_fake.txt
lower-bound drift certificate|lower-bound|gp -q drift_check.gp|@drift_check.out
lower-bound negative controls|lower-bound|sh neg_tables.sh|out/neg_s16.txt out/neg_s27.txt
lean-upper-sharp pieces|lean-upper-sharp|gp -q pieces_lean.gp|@out/pieces_lean.txt
lean-upper-sharp quartic|lean-upper-sharp|gp -q quartic.gp|@out/quartic.txt
lean-upper-sharp K0|lean-upper-sharp|gp -q k0.gp|@out/k0.txt
lean-upper-sharp margins|lean-upper-sharp|gp -q lsharp_margins.gp|@out/lsharp_margins.txt
lean-upper-sharp drift table|lean-upper-sharp|gp -q drift_lean.gp|out/drift_codes.txt
lean-upper-sharp drift module|lean-upper-sharp|gp -q drift_cells.gp|../../RegretKappa/LowerSharp/DriftCells.lean
'
while IFS='|' read -r name dir cmd outs; do
  [ -n "$name" ] || continue
  [[ -z $names || $name =~ $names ]] || continue
  echo
  t0=$(date +%s.%N)
  # shellcheck disable=SC2086
  (cd "$tmp/code/$dir" && $cmd < /dev/null > "$tmp/stdout" 2>&1)
  rc=$?
  echo "$name ($cmd in $dir/): exit $rc, $(awk -v a="$t0" -v b="$(date +%s.%N)" 'BEGIN { printf "%.1f", b - a }') s"
  [ "$rc" -eq 0 ] || fail=1
  for o in $outs; do
    case $o in
      @*) o=${o#@}; new=$tmp/stdout ;;
      *) new=$tmp/code/$dir/$o ;;
    esac
    n=$(diff <(norm "$code/$dir/$o") <(norm "$new") | grep -c '^[<>]')
    if [ "$n" -eq 0 ]; then
      echo "  $dir/$o: SAME as recorded"
    else
      echo "  $dir/$o: DIFFERS from recorded ($n lines)"
      diff <(norm "$code/$dir/$o") <(norm "$new") | head -20 | sed 's/^/    /'
      fail=1
    fi
  done
done <<< "$jobs"
echo
if [ "$fail" -eq 0 ]; then echo "overall: every script exits 0 and every output is the recorded one"; else echo "overall: FAILED"; fi
exit "$fail"
