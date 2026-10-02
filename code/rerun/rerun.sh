#!/bin/bash
# Reruns the certificate scripts of Section 7.3 of the paper twice and compares each output with
# the committed one, line by line, with the timing tokens ("elapsed 2.4 s", "(time 6.2 s)", "time 0.8 s")
# and the ISO dates masked. The only line dropped is one that holds a running time and nothing else
# ("elapsed: 4 s", appended by code/lower-bound-referee/run.sh and absent from a direct gp run).
# Outputs go to a temporary directory; the committed outputs are not touched.
# Usage: bash rerun.sh > out/rerun-<UTC stamp>.txt   (about 8 minutes; pass outputs in out/<name>.pass<N>.txt)
set -u
here=$(cd "$(dirname "$0")" && pwd)
code=$(cd "$here/.." && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
echo "rerun of the regret-kappa certificates, $(date -u +%Y-%m-%dT%H:%M:%SZ), commit $(git -C "$here" rev-parse HEAD)"
echo "pari: $(echo 'print(version())' | gp -q 2>&1 | head -1); $(sage --version 2>&1 | head -1)"
filter() { sed -E 's/(elapsed:?|time|wall) [0-9]+(\.[0-9]+)? s/\1 <t> s/g; s/20[0-9]{2}-[0-9]{2}-[0-9]{2}T[0-9:]+Z/<date>/g; /^elapsed:? <t> s$/d' "$1"; }
fail=0
# name | directory (relative to code/) | committed output (relative to that directory) | command
jobs='
lb-drift|lower-bound|drift_check.out|gp -q drift_check.gp
lb-total|lower-bound|total_bound.out|gp -q total_bound.gp
lb-phase2|lower-bound|phase2_check.out|gp -q phase2_check.gp
lbref-drift|lower-bound-2|out/drift.txt|gp -q -s 1G gp/drift.gp
lbref-constants|lower-bound-2|out/constants.txt|gp -q -s 1G gp/constants.gp
lbref-phase2|lower-bound-2|out/phase2.txt|gp -q -s 1G gp/phase2.gp
ub-constants|upper-bound|out/constants_gp.txt|gp -q gp/constants.gp
ubref-constants|upper-bound-2|out/constants.txt|sage sage/constants.sage
ubc-t0|upper-bound-certificate|out/t0_tools.txt|sage t0_tools.sage
ubc-c1|upper-bound-certificate|out/c1_gamma.txt|sage c1_gamma.sage
ubc-c2|upper-bound-certificate|out/c2_lemma52.txt|sage c2_lemma52.sage
ubc-c3|upper-bound-certificate|out/c3_lemma61.txt|sage c3_lemma61.sage
ubc-c4|upper-bound-certificate|out/c4_lemma71.txt|sage c4_lemma71.sage
ubc-c5|upper-bound-certificate|out/c5_final.txt|sage c5_final.sage
'
for pass in 1 2; do
  echo
  echo "== pass $pass"
  printf '%s\n' "$jobs" | while IFS='|' read -r name dir committed cmd; do
    [ -n "$name" ] || continue
    t0=$(date +%s)
    # shellcheck disable=SC2086
    (cd "$code/$dir" && $cmd < /dev/null 2>&1 | sed "s|$HOME|~|g") > "$tmp/$name.$pass"
    t1=$(date +%s)
    filter "$code/$dir/$committed" > "$tmp/$name.ref"
    filter "$tmp/$name.$pass" > "$tmp/$name.new"
    nd=$(diff "$tmp/$name.ref" "$tmp/$name.new" | grep -c '^[<>]')
    if [ "$nd" -eq 0 ]; then v="SAME as committed"; else v="DIFFERS from committed ($nd lines)"; fi
    echo "$name: $((t1 - t0)) s, $(wc -l < "$tmp/$name.$pass") lines, $v"
    [ "$nd" -eq 0 ] || diff "$tmp/$name.ref" "$tmp/$name.new" | head -20 | sed 's/^/    /'
    cp "$tmp/$name.$pass" "$here/out/$name.pass$pass.txt"
  done
done
echo
for f in "$here"/out/*.pass1.txt; do
  g=${f%.pass1.txt}.pass2.txt
  n=$(basename "${f%.pass1.txt}")
  if cmp -s <(filter "$f") <(filter "$g"); then echo "$n: pass 1 = pass 2"; else echo "$n: pass 1 != pass 2"; fail=1; fi
done
echo "overall: $([ "$fail" -eq 0 ] && echo 'both passes agree' || echo 'DISAGREEMENT between passes')"
