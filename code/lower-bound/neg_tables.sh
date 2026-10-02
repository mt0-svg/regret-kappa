#!/bin/sh
# Negative controls of drift_check.gp: the certificate is run on two corrupted move tables, with s_16 = 0.1852 in
# place of 0.1602 and with s_27 = 0.0050 in place of 0.0142, and must fail on each. The corrupted copies of
# drift_check.gp live in a temporary directory. Outputs: out/neg_s16.txt and out/neg_s27.txt.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
mkdir -p out
line='tab = vector(28, j, round(5/8 * exp(-((j-1)/10 + 1/20)^2 / 2) * 10^4) / 10^4);'
grep -qF "$line" drift_check.gp
tmp=$(mktemp -d)
status=0
for c in s16 s27; do
  if [ "$c" = s16 ]; then edit='tab[17] = 1852/10000;'; else edit='tab[28] = 50/10000;'; fi
  awk -v l="$line" -v e="$edit" '{ print } $0 == l { print e }' drift_check.gp > "$tmp/$c.gp"
  grep -qF "$edit" "$tmp/$c.gp"
  {
    echo "drift_check.gp with the line: $edit"
    gp -q "$tmp/$c.gp" < /dev/null 2>&1 | sed "s#$tmp/##g" || true
  } > "out/neg_$c.txt"
  if grep -q '^PASS' "out/neg_$c.txt" || ! grep -q 'certificate failed' "out/neg_$c.txt"; then
    echo "ERROR: the corrupted table $c was accepted" | tee -a "out/neg_$c.txt"; status=1
  else
    echo "REJECTED as it must be: the certificate fails" | tee -a "out/neg_$c.txt"
  fi
done
rm -r "$tmp"
exit $status
