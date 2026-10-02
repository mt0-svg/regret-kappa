#!/bin/bash
# Runs every script of this implementation after deleting its old output, then checks each
# output: exit status 0, last line "RESULT: ALL n CHECKS PASSED", exactly n PASS lines and
# no FAIL line. Three negative controls (neg_fail, neg_raise, neg_fake) must be rejected.
# Log: out/run.txt (sage version, sha256 of every script, wall time, verdict).
set -u
cd "$(dirname "$0")"
mkdir -p out
rm -f out/*.txt
log=out/run.txt
{
  echo "run of code/upper-bound-certificate, $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "SageMath $(sage --version 2>&1 | head -1)"
  sha256sum lib.sage t0_tools.sage c1_gamma.sage c2_small_steps.sage c3_large_steps.sage c4_terminal.sage c5_final.sage neg_fail.sage neg_raise.sage neg_fake.sage run.sh
} > "$log"

verify() { # $1 output file, $2 exit status; prints OK or the reason of the rejection
  f=$1
  [ "$2" -eq 0 ] || { echo "REJECTED (exit status $2)"; return 1; }
  last=$(tail -n 1 "$f")
  n=$(printf '%s\n' "$last" | sed -n 's/^RESULT: ALL \([0-9][0-9]*\) CHECKS PASSED$/\1/p')
  [ -n "$n" ] || { echo "REJECTED (no final RESULT line)"; return 1; }
  if grep -q '^FAIL' "$f"; then echo "REJECTED (FAIL line)"; return 1; fi
  p=$(grep -c '^PASS' "$f")
  [ "$p" -eq "$n" ] || { echo "REJECTED ($p PASS lines, RESULT says $n)"; return 1; }
  echo "OK ($n checks)"
}

status=0
for s in t0_tools c1_gamma c2_small_steps c3_large_steps c4_terminal c5_final neg_fail neg_raise neg_fake; do
  t0=$(date +%s.%N)
  # home-directory paths (in tracebacks) are written as ~ so that no login name is recorded
  sage "$s.sage" 2>&1 | sed "s|$HOME|~|g" > "out/$s.txt"
  code=${PIPESTATUS[0]}
  t1=$(date +%s.%N)
  v=$(verify "out/$s.txt" "$code")
  w=$(awk -v a="$t0" -v b="$t1" 'BEGIN { printf "%.1f", b - a }')
  case $s in
    neg_*)
      v0=$(verify "out/$s.txt" 0) # content test alone, as if the exit status were 0
      case "$v|$v0" in
        REJECTED*"|"REJECTED*) r="negative control rejected as it must: $v; content test alone: $v0" ;;
        *) r="ERROR: negative control accepted ($v; $v0)"; status=1 ;;
      esac ;;
    *) r=$v; case $v in OK*) ;; *) status=1 ;; esac ;;
  esac
  echo "$s: exit $code, ${w} s, $r" | tee -a "$log"
done
if [ $status -eq 0 ]; then echo "ALL RUNS VERIFIED" | tee -a "$log"; else echo "SOME RUN FAILED" | tee -a "$log"; fi
exit $status
