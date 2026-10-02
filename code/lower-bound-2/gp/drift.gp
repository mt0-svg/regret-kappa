\\ Second program for Lemma 4.3 of the paper (Computation 4.4), written from the statement only.
\\ Claim: for every rho >= 0, with s = s(rho) and g(rho) = 8 exp(rho^2/2),
\\   D(rho) := 8 exp((rho^2 (1-s) + s)/2) cosh(rho sqrt(s(1-s))) - g(rho) - 1 >= 0.
\\ Part (b), rho in [0, 2.8): exact rational arithmetic, a method different from the note's:
\\   midpoint value plus a Lipschitz bound, with the Lagrange form of the exponential remainder
\\   e^q <= P_N(q) / (1 - q^(N+1)/(N+1)!) (q >= 0), adaptive bisection from the cells [j/10, (j+1)/10].
\\ On [lo, hi] (0 <= lo), D(rho) >= D(m) - (hi - lo)/2 * Lip with m = (lo + hi)/2 and
\\   |D'| <= max(8 h'(hi), 8 hi e^(hi^2/2)), h' <= rho (1 - s^2) exp((rho^2 (1 - s^2) + s)/2)
\\ (from sinh x <= x cosh x and cosh x <= exp(x^2/2)); both bounds increase with rho >= 0.
\\ Usage: gp -q drift.gp (table TAB below; the perturbed-table test sets TAB before reading this file).

\\ run with gp -q -s 1G (stack size on the command line, so that cex.gp can read this file)
N = 30;
if (type(TAB) != "t_VEC", TAB = [6242, 6180, 6058, 5879, 5648, 5373, 5060, 4718, 4355, 3980, 3601, 3226, 2861, 2513, 2184, 1880, 1602, 1352, 1129, 934, 764, 620, 497, 395, 311, 242, 187, 142]);
SJ = vector(28, j, TAB[j] / 10000);

PN(q) = sum(n = 0, N, q^n / n!);
expLo(q) = if (q < 0, error("expLo: q < 0"), PN(q));
expHi(q) = my(r = q^(N+1) / (N+1)!); if (q < 0 || r >= 1, error("expHi range")); PN(q) / (1 - r);
\\ lower bound of cosh(sqrt(y)), y >= 0
coshLo(y) = if (y < 0, error("coshLo: y < 0"), sum(n = 0, N, y^n / (2*n)!));

Dlo(m, s) = 8 * expLo((m^2 * (1 - s) + s) / 2) * coshLo(m^2 * s * (1 - s)) - 8 * expHi(m^2 / 2) - 1;
Lip(hi, s) = max(8 * hi * (1 - s^2) * expHi((hi^2 * (1 - s^2) + s) / 2), 8 * hi * expHi(hi^2 / 2));

cnt = 0; maxdep = 0; minmarg = 10^9; minmargat = 0; mincentre = 10^9; mincentreat = 0; lastend = 0; bad = 0;
cellcnt = vector(28);

chk(lo, hi, s, dep, j) =
{
  my(m = (lo + hi) / 2, d = Dlo(m, s), marg = d - (hi - lo) / 2 * Lip(hi, s));
  if (d < mincentre, mincentre = d; mincentreat = m);
  if (marg >= 0,
    if (lo != lastend, bad++; print("GAP at ", lo));
    lastend = hi; cnt++; cellcnt[j]++; maxdep = max(maxdep, dep);
    if (marg < minmarg, minmarg = marg; minmargat = [lo, hi]);
    return(1));
  \\ a centre with Dlo < 0 and an upper bound of D below 0 would be a true violation; either way stop at depth 16
  if (dep >= 16, bad++; print("FAIL: no certificate on [", lo, ", ", hi, "] s = ", s, " lower bound of D at the centre = ", d * 1.); lastend = hi; return(0));
  if (bad > 0, return(0));
  chk(lo, m, s, dep + 1, j);
  chk(m, hi, s, dep + 1, j);
}

print("Lemma 3.1 (b): exact rational certificate, N = ", N);
print("table s_j * 10^4 = ", TAB);
for (j = 0, 27, chk(j / 10, (j + 1) / 10, SJ[j + 1], 0, j + 1));
print("subintervals: ", cnt, ", max bisection depth: ", maxdep, ", per cell: ", cellcnt);
print("covered up to ", lastend, " contiguously from 0: ", if (bad == 0 && lastend == 28/10, "yes", "NO"));
print("smallest certified margin: ", minmarg * 1., " on ", minmargat);
print("smallest lower bound of D at a centre (drift - 1): ", mincentre * 1., " at rho = ", mincentreat * 1.);
print("Lemma 3.1 (b): ", if (bad == 0 && lastend == 28/10, "PASS", "FAIL"));

\\ Midpoint claim of the note: s_j = (5/8) exp(-m^2/2) at m = j/10 + 1/20, rounded to 4 decimals.
\\ (Descriptive only: the adversary is defined by the table.)
\p 50
mism = 0;
for (j = 0, 27, my(v = round(10^4 * (5/8) * exp(-(j/10 + 1/20)^2 / 2))); if (v != TAB[j + 1], mism++; print("  table entry ", j, ": ", TAB[j + 1], " vs rounded formula ", v)));
print("table = rounded (5/8) exp(-m^2/2) at the cell midpoints: ", if (mism == 0, "yes", "NO"), " (", mism, " mismatches)");
print("min over the table of s_j: ", vecmin(SJ) * 1., ", max: ", vecmax(SJ) * 1., " (all in (0,1): ", if (vecmin(SJ) > 0 && vecmax(SJ) < 1, "yes", "NO"), ")");

\\ Part (a): rho >= 2.8, s = (5/8) exp(-rho^2/2). Rational bound on phi(2.8) = exp(-3.92) (3.92 + 2.8^4/4).
phiup = (392/100 + (28/10)^4 / 4) / expLo(392/100);
print("Lemma 3.1 (a): phi(2.8) <= ", phiup * 1., " (rational upper bound) < 12/25: ", if (phiup < 12/25, "PASS", "FAIL"));
print("  1 + sqrt(5) = ", (1 + sqrt(5)), " < 2.8^2 = 7.84: ", if (1 + sqrt(5) < 784/100, "yes", "NO"));
print("  1 - z > 0 check not needed (exp(-z)(1+c) >= (1-z)(1+c) since 1 + c > 0)");

\\ Sanity (floating point, 50 digits, not part of the certificate): drift on grids.
sfun(r) = my(a = abs(r)); if (a < 28/10, SJ[floor(10 * a) + 1], (5/8) * exp(-a^2 / 2));
drift(r) = my(s = sfun(r)); 8 * exp((r^2 * (1 - s) + s) / 2) * cosh(r * sqrt(s * (1 - s))) - 8 * exp(r^2 / 2);
m1 = 10^9; m1at = 0; forstep (i = 0, 11199, 1, my(r = i / 4000, d = drift(r)); if (d < m1, m1 = d; m1at = r));
m2 = 10^9; m2at = 0; forstep (i = 11200, 48000, 1, my(r = i / 4000, d = drift(r)); if (d < m2, m2 = d; m2at = r));
print("sanity: min drift on grid 1/4000 of [0, 2.8): ", m1, " at ", m1at * 1.);
print("sanity: min drift on grid 1/4000 of [2.8, 12]: ", m2, " at ", m2at * 1.);
\\ large rho: the drift is a difference of two terms of size e^(rho^2/2); 500 digits cover rho <= 40
\p 500
m3 = 10^9; forstep (r = 12, 40, 1/100, m3 = min(m3, drift(r)));
print("sanity (500 digits): min drift on grid 1/100 of [12, 40]: ", strprintf("%.12g", m3));
\\ part (a) lower bound 5/2 - (25/8) phi(rho) against the true drift on [2.8, 20] (their difference tends to 0 as rho grows, so the grid stops where 500 digits resolve it)
m4 = 10^9; forstep (i = 11200, 80000, 10, my(r = i / 4000, lb = 5/2 - (25/8) * exp(-r^2/2) * (r^2/2 + r^4/4)); m4 = min(m4, drift(r) - lb));
print("sanity (500 digits): min of (drift - part (a) lower bound) on [2.8, 20]: ", strprintf("%.6g", m4), " (must be >= 0)");
quit;
