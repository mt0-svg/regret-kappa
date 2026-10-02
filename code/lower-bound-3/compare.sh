#!/bin/sh
# Comparison with the two PARI/GP implementations (code/lower-bound and
# code/lower-bound-2, called author and referee below), run after this implementation's outputs were
# committed. Their recorded outputs are read through diff only, the values they print are
# extracted to out/others_extracted.txt as "source key values...", and compare.sage
# recomputes every one of them with this implementation's code (out/compare.out).
set -u
here=$(cd "$(dirname "$0")" && pwd)
cd "$here" || exit 1
A=../lower-bound
F=../lower-bound-2/out
x() { diff /dev/null "$1" | sed -n 's/^> //p'; }
num='\(-\{0,1\}[0-9][0-9.]*\( E-\{0,1\}[0-9]*\)\{0,1\}\)'
rm -f out/others_extracted.txt out/compare.out
{
  # author, drift_check.out
  x $A/drift_check.out | sed -n 's/^cell *\([0-9]*\) .* subintervals \([0-9]*\)$/author_cells \1 \2/p'
  x $A/drift_check.out | sed -n 's/^PASS: \([0-9]*\) certified subintervals, max bisection depth \([0-9]*\), smallest rational margin \([0-9.]*\)$/author_cert \1 \2 \3/p'
  x $A/drift_check.out | sed -n 's/^sanity table rule on \[0,2.8): min of drift - 1 = \([0-9.]*\) at r = \([0-9.]*\)$/author_grid1 \1 \2/p'
  x $A/drift_check.out | sed -n 's/^sanity continuous rule on \[2.8,12\]: min of drift - 1 = \([0-9.]*\) at r = \([0-9.]*\)$/author_grid2 \1 \2/p'
  x $A/drift_check.out | sed -n 's/^phi(2.8) = \([0-9.]*\) .*/author_phi28 \1/p'
  x $A/drift_check.out | sed -n 's/^max of x -> .* at x = 1 + sqrt(5): \([0-9.]*\);.*/author_phimax \1/p'
  # author, phase2_check.out
  x $A/phase2_check.out | awk -F'\t' 'NF == 8 && ($1 == "100000" || $1 == "1000000") { print "author_vT", $1, $2, $4, $5, $6 }'
  x $A/phase2_check.out | sed -n 's/^constants: A = 2, J = \([0-9.]*\), E Z^2 = \([0-9.]*\), c0 = .* = \([0-9.]*\), c1 = .* = \([0-9.]*\)$/author_p2const \1 \2 \3 \4/p'
  x $A/phase2_check.out | sed -n 's/^min over the grid .* of vT - Phi0: \([0-9.]*\) at k = \([0-9]*\), rho = \([0-9.]*\)$/author_vTgridmin \1 \2 \3/p'
  # author, total_bound.out
  x $A/total_bound.out | awk -F'\t' 'NF == 8 && $1 != "T" { t = $1; gsub(/ /, "", t); print "author_B", t, $2, $3, $4, $5 }'
  x $A/total_bound.out | sed -n 's/^at T0: j0 = \([0-9]*\), L = \([0-9.]*\), Llow = \([0-9.]*\), .*/author_T0 \1 \2 \3/p'
  x $A/total_bound.out | sed -n 's/^eps_L at L = 14.5: \([0-9.]*\) .*/author_eps145 \1/p'
  x $A/total_bound.out | sed -n 's/^C3 margin function .* at T0: \([0-9.]*\); sqrt(5\/8) exp(-14.5\/4) = \([0-9.]*\)$/author_C3 \1 \2/p'
  x $A/total_bound.out | sed -n 's/^scan T in .*; min of B(T) - Bsimple(T) = \([0-9.]*\) at T = \([0-9.]*\) e\([0-9]*\)$/author_scanmin \1 \2e\3/p'
  x $A/total_bound.out | sed -n 's/^at T0: log log T0 = \([0-9.]*\), v - 2 log(v + 2.1) = \(-[0-9.]*\) .*, 6 log log T0 = \([0-9.]*\) .*/author_v0 \1 \2 \3/p'
  x $A/total_bound.out | sed -n 's/^B(T)\/log T at T = 1e6, 1e10, 1e20, 1e50, 1e100: \(.*\)$/author_ratios \1/p'
  # referee, drift.txt and kstar.txt
  x $F/drift.txt | sed -n 's/^table s_j \* 10^4 = \[\(.*\)\]$/referee_table \1/p' | tr -d ','
  x $F/drift.txt | sed -n 's/^Lemma 3.1 (a): phi(2.8) <= \([0-9.]*\) (rational upper bound).*/referee_phi28ub \1/p'
  x $F/drift.txt | sed -n 's/^sanity: min drift on grid 1\/4000 of \[0, 2.8): \([0-9.]*\) at \([0-9.]*\)$/referee_grid1 \1 \2/p'
  x $F/drift.txt | sed -n 's/^sanity: min drift on grid 1\/4000 of \[2.8, 12\]: \([0-9.]*\) at \([0-9.]*\)$/referee_grid2 \1 \2/p'
  x $F/drift.txt | sed -n 's/^sanity (500 digits): min drift on grid 1\/100 of \[12, 40\]: \([0-9.]*\)$/referee_grid3 \1/p'
  x $F/kstar.txt | sed -n 's/^K\* = \([0-9.]*\) at rho = \([0-9.]*\) (best move s = \([0-9.]*\))$/referee_kstar \2 \1 \3/p'
  x $F/kstar.txt | sed -n 's/^  rho = \([0-9.]*\): best s = \([0-9.]*\), K(rho) = \([0-9.]*\)$/referee_krho \1 \3 \2/p'
  # referee, constants.txt
  x $F/constants.txt | sed -n "s/^  J numerical = $num, pi^2\/A^2 = $num, .*/referee_J \3/p"
  x $F/constants.txt | sed -n "s/^  E Z^2 numerical = $num, A^2 (1\/3 - 2\/pi^2) = $num, .*/referee_EZ2 \3/p"
  x $F/constants.txt | sed -n "s/^  c_1 = $num$/referee_c1 \1/p"
  x $F/constants.txt | sed -n "s/^  J E Z^2 = $num (note.*/referee_JEZ2 \1/p"
  x $F/constants.txt | sed -n "s/^  log(A^2\/(4 pi^2)) = $num = .*/referee_logA \1/p"
  x $F/constants.txt | sed -n "s/^  max of (u\/2) exp(-u^2\/4) = exp(-1\/2)\/sqrt 2 = $num; .*/referee_qmax \1/p"
  x $F/constants.txt | sed -n "s/^  1 - sqrt(5\/8) max = $num > 0$/referee_dmin \1/p"
  x $F/constants.txt | sed -n "s/^  eps_L at 14.5 = $num, log 1.1 = $num, ok: 1$/referee_eps145 \1 \3/p"
  x $F/constants.txt | sed -n "s/^  3.8^2 = .*; max over cells of (j+1)\/10 + sqrt(s_j) = $num$/referee_crudestep \1/p"
  x $F/constants.txt | sed -n "s/^  sqrt(5\/8) exp(-14.5\/4) = $num (note.*/referee_s0022 \1/p"
  x $F/constants.txt | sed -n "s/^  least integer T with L_low(T) >= 14.5: \([0-9]*\)  (L_low(T-1) = $num, L_low(T) = $num)$/referee_T0 \1 \2 \4/p"
  x $F/constants.txt | sed -n "s/^  at T_0 = 355713: j_0 = 4, L = $num, a = $num, a+ = $num, T_1 = 177856, k_0 = 177857$/referee_atT0 \1 \3 \5/p"
  x $F/constants.txt | sed -n "s/^  (C1) L >= 14.5: 1;  (C2) lhs $num <= T_1 - 1 = 177855: 1$/referee_C2lhs \1/p"
  x $F/constants.txt | sed -n "s/^  (C3) k_0 = 177857 >= pi^2 e^2 (a+ + 2)^2 = $num: 1$/referee_C3rhs \1/p"
  x $F/constants.txt | sed -n "s/^  (C3) simplified: .* at T_0 = $num$/referee_FT0 \1/p"
  x $F/constants.txt | sed -n "s/^  B_0(T_0) = $num, B(T_0) = $num$/referee_B0T0 \1 \3/p"
  x $F/constants.txt | sed -n "s/^  d\/dT of the (C3) function at T = 1000: $num (.*/referee_dF1000 \1/p"
  x $F/constants.txt | sed -n "s/^  T = \([0-9]*\): B(T) = $num  L = $num  conditions .*/referee_BT \1 \2 \4/p"
  x $F/constants.txt | sed -n "s/^  T = 10^\([0-9]*\): B(T)\/log T = $num$/referee_ratio \1 \2/p"
  x $F/constants.txt | sed -n "s/^  min of B(T) - \[3 log T - log log T - 2 log(log log T + 2.1) - 14.6\] = $num at T = \([0-9]*\)$/referee_minBs \1 \3/p"
  x $F/constants.txt | sed -n "s/^  min of \[form with 14.6\] - \[3 log T - 2 log log T - 15.2\] = $num$/referee_min2 \1/p"
  x $F/constants.txt | sed -n "s/^  min of \[3 log T - 2 log log T - 15.2\] - \[3 log T - 8 log log T\] = $num$/referee_min3 \1/p"
  x $F/constants.txt | sed -n "s/^  at T_0: v = log log T_0 = $num, v - 2 log(v + 2.1) = $num, 6 log log T_0 = $num$/referee_v0 \1 \3 \5/p"
  x $F/constants.txt | sed -n "s/^  log 3 + 1 = $num$/referee_log3 \1/p"
  x $F/constants.txt | sed -n "s/^  2 log(1 + 2\/sqrt(14.5)) = $num$/referee_c845 \1/p"
  x $F/constants.txt | sed -n "s/^  2 log(20 e) + 2 log 2 + 0.8445 + c_1 + 1e-4 + 1 = $num$/referee_const \1/p"
  x $F/constants.txt | sed -n "s/^  log(k_0)\/(2 k_0) + 1\/k_0 at k_0 = k_0(T_0): \([0-9.]*\) E-\([0-9]*\)$/referee_tailk \1e-\2/p"
  x $F/constants.txt | sed -n "s/^  dF\/du = 2u - 2\/(u+2) at u = 1: 4\/3; dF\/dk at k = 3: $num$/referee_dFdk3 \1/p"
  # referee, phase2.txt
  x $F/phase2.txt | sed -n "s/^  rho = \([0-9.]*\), k = \([0-9]*\): vT = $num, Phi_1 = $num, sum eps^2\/w = $num >= $num, (1+X)\/w_k = $num >= $num$/referee_vT \1 \2 \3 \5 \7 \9/p"
  x $F/phase2.txt | sed -n "s/^  rho = \([0-9.]*\), k = \([0-9]*\): vT = .*, (1+X)\/w_k = $num >= $num$/referee_comp \1 \2 \3 \5/p"
  x $F/phase2.txt | sed -n "s/^  rho = \([0-9.]*\), k = \([0-9]*\): Bayes bracket $num >= vT $num (ok); first sum $num >= $num; comparator $num >= $num$/referee_bayes \1 \2 \3 \5 \7 \9/p"
  x $F/phase2.txt | sed -n "s/^  rho = \([0-9.]*\), k = \([0-9]*\): Bayes bracket .*; comparator $num >= $num$/referee_bayescomp \1 \2 \3 \5/p"
  x $F/phase2.txt | sed -n "s/^  at T_0: vT(3.8470, 177857) - Phi_1 = $num$/referee_vTT0 \1/p"
} > out/others_extracted.txt
wc -l out/others_extracted.txt
sage compare.sage > out/compare.out 2>&1
rc=$?
tail -3 out/compare.out
exit $rc
