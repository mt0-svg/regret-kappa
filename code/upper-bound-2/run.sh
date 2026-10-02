#!/bin/sh
# Second program of the upper bound and tests of Section 3 (Section 7.3 of the paper). Run from this directory.
# Each script writes its complete output to out/.
set -e
cd "$(dirname "$0")"
sage sage/constants.sage > out/constants.txt 2>&1
gp -q gp/onestep.gp < /dev/null > out/onestep.txt 2>&1
gp -q gp/pointwise.gp < /dev/null > out/pointwise.txt 2>&1
gp -q gp/game.gp < /dev/null > out/game.txt 2>&1
gp -q gp/extras.gp < /dev/null > out/extras.txt 2>&1
grep -h "ALL CHECKS OK\|ONESTEP OK\|POINTWISE DONE\|GAME OK\|EXTRAS DONE\|FAIL" out/*.txt
