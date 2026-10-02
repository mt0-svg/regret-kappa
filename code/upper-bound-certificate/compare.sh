#!/bin/bash
# Compares this implementation with the recorded outputs of code/upper-bound, read through
# diff (the other implementation's code is not read): writes out/compare.txt.
set -u
cd "$(dirname "$0")"
a=../upper-bound/out/constants_gp.txt
b=../upper-bound/out/lemma_check_gp.txt
tmp=$(mktemp -d)
diff /dev/null "$a" | sed -n 's/^> //p' > "$tmp/constants_gp.txt"
diff /dev/null "$b" | sed -n 's/^> //p' > "$tmp/lemma_check_gp.txt"
rm -f out/compare.txt
{
  echo "compared: code/upper-bound/out/{constants_gp,lemma_check_gp}.txt, sha256 of the text extracted through diff:"
  (cd "$tmp" && sha256sum constants_gp.txt lemma_check_gp.txt)
  echo "this implementation (sha256):"
  sha256sum lib.sage compare.sage
} > out/compare.txt
sage compare.sage "$tmp/constants_gp.txt" "$tmp/lemma_check_gp.txt" 2>&1 | sed "s|$HOME|~|g" >> out/compare.txt
code=${PIPESTATUS[0]}
rm -rf "$tmp"
echo "compare.sage exit $code"
tail -n 3 out/compare.txt
exit "$code"
