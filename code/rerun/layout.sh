#!/bin/bash
# Reruns, in a temporary copy of code/, every run script whose paths were adapted to the layout of this repository
# (the recorded outputs were made in an earlier layout, code/README.md) and the PARI/GP programs of
# code/lean-upper-sharp/ whose comments or printed labels were renumbered to the paper, and compares each output
# file it writes with the recorded one, apart from the running times, dates and names of temporary files inside its
# lines. The committed outputs are not touched. Two passes are recorded:
#   bash code/rerun/layout.sh N > code/rerun/out/layout-passN.txt     (N = 1, 2; about 20 minutes each)
# Not compared: upper-bound-certificate/out/run.txt, which lists the sha256 of the scripts (their header comments were
# renumbered to the paper after the recorded runs), and lower-bound-3/out/run.log, which names the commit.
set -u
pass=${1:?usage: layout.sh N}
code=$(cd "$(dirname "$0")/.." && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp -r "$code" "$tmp/code"
mkdir -p "$tmp/RegretKappa/LowerSharp"    # drift_cells.gp writes ../../RegretKappa/LowerSharp/DriftCells.lean
echo "layout rerun, pass $pass, $(date -u +%Y-%m-%dT%H:%M:%SZ), commit $(git -C "$code" rev-parse HEAD 2> /dev/null)"
echo "pari: $(echo 'print(version())' | gp -q 2>&1 | head -1); $(sage --version 2>&1 | head -1)"
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
# standard output, compared with F); rerun.sh first, while every output of the copy is still the recorded one
jobs='
rerun|rerun|bash rerun.sh|
upper-bound-certificate run|upper-bound-certificate|bash run.sh|out/t0_tools.txt out/c1_gamma.txt out/c2_lemma52.txt out/c3_lemma61.txt out/c4_lemma71.txt out/c5_final.txt out/neg_fail.txt out/neg_raise.txt out/neg_fake.txt
upper-bound-certificate compare|upper-bound-certificate|bash compare.sh|out/compare.txt
upper-bound-2 run|upper-bound-2|sh run.sh|out/constants.txt out/onestep.txt out/pointwise.txt out/game.txt out/extras.txt
upper-bound lemma_check|upper-bound|gp -q -f gp/lemma_check.gp|@out/lemma_check_gp.txt
lower-bound-3 run|lower-bound-3|sh run.sh|out/drift_rational.out out/drift_arb.out out/phase1_constants.out out/phase2.out out/total_bound.out out/identities.out out/negative_controls.out
lower-bound-3 compare|lower-bound-3|sh compare.sh|out/others_extracted.txt out/compare.out
lower-bound-2 run|lower-bound-2|sh run.sh|out/drift.txt out/cex1.txt out/cex2.txt out/constants.txt out/phase2.txt out/identities.txt out/kstar.txt out/mc_phase1.txt out/author_cert_on_cex1.txt out/author_cert_on_cex2.txt out/author_rerun.txt
lean-upper-sharp margins|lean-upper-sharp|gp -q lsharp_margins.gp|@out/lsharp_margins.txt
lean-upper-sharp drift table|lean-upper-sharp|gp -q drift_lean.gp|out/drift_codes.txt
lean-upper-sharp order scan|lean-upper-sharp|gp -q drift_nscan.gp|@out/drift_nscan.txt
lean-upper-sharp drift module|lean-upper-sharp|gp -q drift_cells.gp|../../RegretKappa/LowerSharp/DriftCells.lean
'
while IFS='|' read -r name dir cmd outs; do
  [ -n "$name" ] || continue
  echo
  t0=$(date +%s)
  # shellcheck disable=SC2086
  (cd "$tmp/code/$dir" && $cmd < /dev/null > "$tmp/stdout" 2>&1)
  rc=$?
  echo "$name ($cmd in $dir/): exit $rc, $(($(date +%s) - t0)) s"
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
  if [ "$name" = rerun ]; then
    same=$(grep -c 'SAME as committed' "$tmp/stdout")
    agree=$(grep -c '^overall: both passes agree$' "$tmp/stdout")
    echo "  rerun.sh: $same of 28 runs SAME as committed; passes agree: $agree"
    if [ "$same" -ne 28 ] || [ "$agree" -ne 1 ]; then fail=1; fi
  fi
done <<< "$jobs"
echo
if [ "$fail" -eq 0 ]; then echo "overall: every script exits 0 and every output is the recorded one"; else echo "overall: FAILED"; fi
exit "$fail"
