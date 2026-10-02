\\ pointwise.gp: floating-point stress tests (evidence) of the lemmas of Section 3 of the paper,
\\ each against an independent evaluation (quadrature of the definitions), with negative controls.
\\ Run: gp -q gp/pointwise.gp > out/pointwise.txt
default(realprecision, 60);
read("gp/gamma.gp");
gamma_selftest();
clip1(z) = max(-1, min(1, z));
setrand(20261001);
urand() = random(10^15) / 10^15 * 1.;

\\ ---------- Lemma 3.1: clip((A-B)/4) is the exact minimizer of h, value Q
Qf(A, B) = if (abs(A - B) <= 4, (A + B) / 2 + (A - B)^2 / 16, max(A, B) - 1);
{
my(worst = 0., worstgrid = 0.);
for (k = 1, 20000,
  my(A = 20 * urand() - 10, B = 20 * urand() - 10, h, es, hs, hmin);
  h = e -> max(e^2 - 2 * e + A, e^2 + 2 * e + B);
  es = clip1((A - B) / 4);
  hs = h(es);
  worst = max(worst, abs(hs - Qf(A, B)));
  hmin = vecmin(vector(4001, j, h(-2 + (j - 1) / 1000)));
  worstgrid = max(worstgrid, hs - hmin));
printf("Lemma 3.1: 20000 random (A,B) in [-10,10]^2: max |h(eta*) - Q| = %.3e, max h(eta*) - min over eta-grid of [-2,2] step 1e-3 = %.3e (must be <= 0)\n", worst, worstgrid);
}

\\ ---------- Lemma 4.1 (rate a), constructive eta = 1 - sqrt(-log(ubar)/a)
mixtest(a, xs, ws) = {
  my(ub = sum(i = 1, #xs, ws[i] * exp(-a * (xs[i] - 1)^2)), vb = sum(i = 1, #xs, ws[i] * exp(-a * (xs[i] + 1)^2)), t, eta);
  t = sqrt(max(0, -log(ub) / a)); eta = 1 - t;
  [eta, exp(-a * (eta + 1)^2) - vb, exp(-a * (eta - 1)^2) - ub]
};
{
my(minsl = oo, maxe = 0.);
for (k = 1, 20000,
  my(n = 1 + random(6), xs, ws, r, tot);
  xs = vector(n, i, my(u = random(10)); if (u == 0, 1, if (u == 1, -1, if (u == 2, 0, 2 * urand() - 1))));
  ws = vector(n, i, urand() + 1e-9); tot = vecsum(ws); ws = ws / tot;
  r = mixtest(1/2, xs, ws);
  minsl = min(minsl, r[2]); maxe = max(maxe, abs(r[1]));
  if (abs(r[1]) > 1 + 1e-30, print("eta out of [-1,1]")));
printf("Lemma 4.1 (rate 1/2): 20000 random discrete laws on [-1,1]: min of e^{-(eta+1)^2/2} - E e^{-(X+1)^2/2} = %.3e (must be >= 0), max |eta| = %.6f\n", minsl, maxe);
}
\\ negative control: rate 0.6 and pi = (delta_{-d} + delta_d)/2: no eta in [-1,1] works
{
my(a = 0.6, d = 0.1, best = -oo);
for (j = 0, 20000,
  my(e = -1 + j / 10000., g1, g2);
  g1 = exp(-a * (e - 1)^2) - (exp(-a * (d - 1)^2) + exp(-a * (-d - 1)^2)) / 2;
  g2 = exp(-a * (e + 1)^2) - (exp(-a * (d + 1)^2) + exp(-a * (-d + 1)^2)) / 2;
  best = max(best, min(g1, g2)));
printf("Lemma 4.1 control, rate 0.6, pi = (delta_-0.1 + delta_0.1)/2: max over eta of the smaller slack = %.3e (negative: fails, as it must)\n", best);
my(a = 0.5, best2 = -oo);
for (j = 0, 20000,
  my(e = -1 + j / 10000., g1, g2);
  g1 = exp(-a * (e - 1)^2) - (exp(-a * (d - 1)^2) + exp(-a * (-d - 1)^2)) / 2;
  g2 = exp(-a * (e + 1)^2) - (exp(-a * (d + 1)^2) + exp(-a * (-d + 1)^2)) / 2;
  best2 = max(best2, min(g1, g2)));
printf("   same law at rate 1/2: max over eta of the smaller slack = %.3e (>= 0)\n", best2);
}

\\ ---------- Lemma 4.2: random finite measures on [-5,5], identity e^{yx} = e^{1/2} e^{x^2/2} e^{-(x-y)^2/2}
{
my(minrel = oo, idmax = 0.);
for (k = 1, 20000,
  my(n = 1 + random(6), xs, ws, Z, pis, xb, r, eta, sl);
  xs = vector(n, i, 10 * urand() - 5);
  ws = vector(n, i, urand() * 3);
  Z = sum(i = 1, n, ws[i] * exp(xs[i]^2 / 2));
  pis = vector(n, i, ws[i] * exp(xs[i]^2 / 2) / Z);
  xb = vector(n, i, clip1(xs[i]));
  r = mixtest(1/2, xb, pis); eta = r[1];
  foreach ([-1, 1], y,
    sl = Z - exp((eta^2 - 2 * eta * y) / 2) * sum(i = 1, n, ws[i] * exp(y * xs[i]));
    minrel = min(minrel, sl / Z));
  foreach ([-1, 1], y, foreach (xs, x, idmax = max(idmax, abs(exp(y * x) / (exp(1/2) * exp(x^2 / 2) * exp(-(x - y)^2 / 2)) - 1)))));
printf("Lemma 4.2: 20000 random measures with atoms in [-5,5]: min relative slack (Z - lhs)/Z = %.3e (must be >= 0); identity max rel error %.3e\n", minrel, idmax);
}

\\ ---------- Lemma 5.1: Gamma-hat - Gamma = P - 4 s J, against quadrature of Gamma-hat
Pf(rho, s) = { my(c = sqrt(1 - s)); 2 * intnum(u = c, 1, cosh(u * rho) * exp(-u^2 / 2) * (1 / u + 2 * c^2 / u^3)) };
Jf(rho) = intsplit(u -> cosh(u * rho) * exp(-u^2 / 2) / u^3, abs(rho), 1);
{
my(worst = 0., cnt = 0);
foreach ([0, 0.3, 1, 1.7, 2.5, 4, 6], rho,
  foreach ([1e-3, 0.05, 0.2, 0.5, 2/3, 0.8, 0.95], s,
    my(lhs = GamHat(rho, s) - Gam(rho), rhs = Pf(rho, s) - 4 * s * Jf(rho));
    worst = max(worst, abs(lhs - rhs) / (abs(lhs) + 1e-30)); cnt++));
printf("Lemma 5.1: %d points, max relative |(GamHat - Gam) - (P - 4sJ)| = %.3e\n", cnt, worst);
}

\\ ---------- Lemma 5.2: GamHat - Gam <= s f(rho^2) for s <= 2/3, with f recomputed here
L0 = 3 / 2 * log(3);
Jn = vector(5); Jn[2] = E1h / 2; Jn[1] = (e12 - Jn[2]) / 2; for (n = 2, 4, Jn[n + 1] = Kv[n]);
an = vector(5); an[1] = 2 * exp(-1/6) * (1 + L0 / 2) - 4 * Jn[1]; an[2] = 2 * e12 * (1/2 + L0) - 4 * Jn[2];
for (n = 2, 4, an[n + 1] = 3 * e12 - 4 * Jn[n + 1]);
ff(x) = sum(n = 0, 4, an[n + 1] * x^n / (2 * n)!);
printf("Lemma 5.2: a_0..a_4 = %s\n", apply(z -> precision(z, 12), an));
printf("Lemma 5.2: max f on [0,10] step 1e-4 = %.10f\n", vecmax(vector(100001, j, ff((j - 1) / 10^4))));
{
my(worst = -oo, wp = 0, mx = -oo, mp = 0, cnt = 0);
forstep (rho = 0, 8, 1/10,
  foreach ([1e-4, 1e-3, 1e-2, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.65, 2/3], s,
    my(d = GamHat(rho, s) - Gam(rho), m = d - s * ff(rho^2));
    cnt++;
    if (m > worst, worst = m; wp = [rho, s]);
    if (d > mx, mx = d; mp = [rho, s])));
printf("Lemma 5.2: %d points rho in [0,8] step 0.1, 12 values of s <= 2/3: max (GamHat - Gam - s f(rho^2)) = %.4e at (rho, s) = %s (must be <= 0); max (GamHat - Gam) = %.6f at %s (bound 2.8857)\n", cnt, worst, wp, mx, mp);
}

\\ ---------- Corollary 4.3: the learner's two-point maximum Q satisfies Q/2 <= log(lam + GamHat), s < 1
{
my(worst = -oo, wp = 0, cnt = 0);
foreach ([0, 0.4, 1, 1.5, 2, 3, 4, 6], rho,
  foreach ([1e-3, 0.05, 0.2, 0.4, 0.5, 2/3, 0.8, 0.9, 0.97, 0.99], s,
    my(c = sqrt(1 - s), sg = sqrt(s), Gp = Gam(rho * c + sg), Gm = Gam(rho * c - sg), GH = GamHat(rho, s));
    foreach ([0, 0.01, 1, 100], lam,
      my(eta = clip1(log((lam + Gp) / (lam + Gm)) / 2), Q = max(eta^2 - 2 * eta + 2 * log(lam + Gp), eta^2 + 2 * eta + 2 * log(lam + Gm)), m);
      m = Q / 2 - log(lam + GH); cnt++;
      if (m > worst, worst = m; wp = [rho, s, lam]))));
printf("Corollary 4.3: %d points: max Q/2 - log(lam + GamHat) = %.4e at (rho, s, lam) = %s (must be <= 0)\n", cnt, worst, wp);
}

\\ ---------- Lemma 6.1: Gam(rho c + sig) - Gam(rho) for s in [2/3, 1], rho >= 0
{
my(best = -oo, bp = 0, cnt = 0);
forstep (rho = 0, 4, 1/200,
  my(G0 = Gam(rho));
  for (k = 0, 200,
    my(s = 2/3 + k / 600, d = Gam(rho * sqrt(1 - s) + sqrt(s)) - G0);
    cnt++;
    if (d > best, best = d; bp = [rho, s])));
printf("Lemma 6.1: %d points rho in [0,4] step 1/200, s in [2/3,1] step 1/600: max Gam(rho c + sig) - Gam(rho) = %.6f at (rho, s) = %s (bound 2.7053)\n", cnt, best, bp);
my(best2 = -oo, bp2 = 0);
forstep (rho = 1.2, 1.26, 1/10000,
  my(d = Gam(rho / sqrt(3) + sqrt(2/3)) - Gam(rho)); if (d > best2, best2 = d; bp2 = rho));
printf("Lemma 6.1: refined at s = 2/3: max %.6f at rho = %.4f\n", best2, bp2);
}

\\ ---------- Lemma 7.1: sqrt(2 pi) e^{rho^2/2} <= (rho + 1) Gam(rho) for rho >= 2
{
my(mn = oo, mp = 0);
forstep (rho = 2, 39, 1/100,
  my(v = (rho + 1) * Gam(rho) * exp(-rho^2 / 2) - sqrt(2 * Pi));
  if (v < mn, mn = v; mp = rho));
printf("Lemma 7.1: rho in [2,39] step 0.01: min (rho+1) Gam(rho) e^{-rho^2/2} - sqrt(2 pi) = %.6f at rho = %.2f (must be >= 0)\n", mn, mp);
foreach ([0, 1, 2, 3, 10, 20, 35], rho, printf("   sqrt(2 pi)/I(rho) - rho at rho = %d: %.4f\n", rho, sqrt(2 * Pi) / (Gam(rho) * exp(-rho^2 / 2)) - rho));
my(mn2 = oo, mp2 = 0);
forstep (rho = 0, 2, 1/100, my(v = (rho + 1) * Gam(rho) * exp(-rho^2 / 2) - sqrt(2 * Pi)); if (v < mn2, mn2 = v; mp2 = rho));
printf("   (for information) on [0,2]: min = %.6f at rho = %.2f (the lemma needs lambda_0 there)\n", mn2, mp2);
}
print("POINTWISE DONE");
\q
