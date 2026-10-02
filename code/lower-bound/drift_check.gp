\\ Phase 1 drift certificate: Computation B.2 of the paper, part (b) of the proof of Lemma B.1.
\\ Claim: with g(r) = 8 exp(r^2/2) and the move s(r) below, for every r in [0, 28/10],
\\   (1/2) [g(r sqrt(1-s) + sqrt(s)) + g(r sqrt(1-s) - sqrt(s))] - g(r) >= 1,
\\ where the left side equals 8 [exp((r^2 (1-s) + s)/2) cosh(r sqrt(s(1-s))) - exp(r^2/2)].
\\ Move rule on [0, 2.8): s(r) = tab[j+1] for r in [j/10, (j+1)/10), j = 0..27 (rational table).
\\ Method: exact rational arithmetic only. On an interval [lo, hi] inside one table cell the
\\ function r -> exp((r^2(1-s)+s)/2) cosh(r sqrt(s(1-s))) is increasing (r >= 0, 0 < s < 1), so
\\ it is >= its value at lo, and exp(r^2/2) <= exp(hi^2/2). Lower bounds: truncated Taylor series
\\ of exp and cosh (nonnegative arguments, all terms >= 0). Upper bound of exp(q), 0 <= q < N+2:
\\ partial sum + q^(N+1)/(N+1)! * (N+2)/(N+2-q). Intervals are bisected until the rational lower
\\ bound of the drift minus 1 is >= 0. No floating point enters a decision.

N = 40;
explo(q) = sum(n = 0, N, q^n / n!);
expup(q) = if(q >= N + 2, error("q too large"), sum(n = 0, N, q^n / n!) + q^(N+1) / (N+1)! * (N+2) / (N+2-q));
coshlo(y2) = sum(n = 0, N, y2^n / (2*n)!);

\\ table: value of 5/8 exp(-m^2/2) at the cell midpoint m = j/10 + 1/20, rounded to 1e-4
tab = vector(28, j, round(5/8 * exp(-((j-1)/10 + 1/20)^2 / 2) * 10^4) / 10^4);

\\ rational lower bound of drift - 1 on [lo, hi] with move s
cert(lo, hi, s) = 8 * (explo((lo^2 * (1-s) + s) / 2) * coshlo(lo^2 * s * (1-s)) - expup(hi^2 / 2)) - 1;

ncells = 0; minmargin = 10^9; maxdepth = 0;
check(lo, hi, s, depth) =
{
  my(c = cert(lo, hi, s));
  if(c >= 0,
    ncells++; if(c < minmargin, minmargin = c); if(depth > maxdepth, maxdepth = depth); return(1));
  if(depth > 30, error("certificate failed near ", lo * 1.));
  check(lo, (lo+hi)/2, s, depth+1) && check((lo+hi)/2, hi, s, depth+1);
}

{
  print("table s_j (j = 0..27), cell [j/10, (j+1)/10):");
  print(tab);
  for(j = 0, 27,
    my(s = tab[j+1], before = ncells);
    if(!(s > 0 && s < 1), error("bad s"));
    check(j/10, (j+1)/10, s, 0);
    printf("cell %2d [%4.2f,%4.2f)  s = %s  subintervals %d\n", j, j/10., (j+1)/10., s, ncells - before));
  printf("PASS: %d certified subintervals, max bisection depth %d, smallest rational margin %.6g\n",
         ncells, maxdepth, minmargin * 1.);
}

quit
