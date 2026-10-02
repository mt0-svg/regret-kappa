\\ gamma.gp: the potential Gamma of Section 3.2 of the paper, written from its definition.
\\ Gamma(r) = sum_n Gamma_n r^(2n)/(2n)!, Gamma_n = 2 int_1^oo th^(2n) e^(-th^2/2) (1/th + 2/th^3) dth
\\ = 2 (K_n + 2 K_{n-1}) (n >= 1), Gamma_0 = 2 e^(-1/2), K_m = int_1^oo th^(2m-1) e^(-th^2/2) dth.
\\ K_m is computed by the recurrence K_{m+1} = 2 m K_m + e^(-1/2) (integration by parts),
\\ checked below against the closed form of the note and against quadrature.
\\ Usage: read("gp/gamma.gp") after setting realprecision.

e12 = exp(-1/2);
E1h = eint1(1/2);
NMAX = 2500;
Kv = vector(NMAX + 1);            \\ Kv[m+1] = K_m
Kv[1] = E1h / 2;
Kv[2] = e12;
for (m = 1, NMAX - 1, Kv[m + 2] = 2 * m * Kv[m + 1] + e12);
Gn = vector(NMAX + 1, i, my(n = i - 1); if (n == 0, 2 * e12, 2 * (Kv[n + 1] + 2 * Kv[n])));
cn = vector(NMAX + 1, i, Gn[i] / (2 * (i - 1))!);

\\ the closed form of Lemma 2.1 (c), for the self-test only
Kclosed(m) = if (m == 0, E1h / 2, 2^(m - 1) * (m - 1)! * e12 * sum(j = 0, m - 1, (1/2)^j / j!));

\\ number of series terms for X = r^2: relative tail below e^(-X/2 - 80)
nterms(X) = { my(N = ceil(exp(1) * X / 2 + 6 * sqrt(X) + 80)); if (N > NMAX, error("Gam: r too large")); N };

Gam(r) = { my(X = r^2, N = nterms(X), acc = 0); forstep (i = N + 1, 1, -1, acc = acc * X + cn[i]); acc };

\\ direct quadrature of the definition (independent of the series)
\\ split [1, oo) at the peak pk of the integrand (width w); beyond pk + 45 w the
\\ integrand is below e^(-1000) of its peak
intsplit(F, pk, w) = { my(a = max(1, pk - 15 * w), b = max(1, pk) + 15 * w, M = max(1, pk) + 45 * w);
  if (a > 1, intnum(t = 1, a, F(t)), 0) + intnum(t = a, b, F(t)) + intnum(t = b, M, F(t)) };
GamQ(r) = 2 * intsplit(t -> cosh(t * r) * exp(-t^2 / 2) * (1 / t + 2 / t^3), abs(r), 1);

\\ Gamma-hat of Corollary 4.3, by quadrature of its definition (s < 1)
GamHat(rho, s) = { my(c = sqrt(1 - s));
  2 * intsplit(t -> cosh(t * c * rho) * exp(-t^2 * c^2 / 2) * (1 / t + 2 / t^3), abs(rho) / c, 1 / c) };

gamma_selftest() = {
  my(e1 = 0., e2 = 0.);
  for (m = 0, 60, e1 = max(e1, abs(Kv[m + 1] / Kclosed(m) - 1)));
  forstep (r = 0, 8, 1/4, e2 = max(e2, abs(Gam(r) / GamQ(r) - 1)));
  printf("gamma selftest: max rel |K recurrence / K closed - 1| (m <= 60) = %.3e\n", e1);
  printf("gamma selftest: max rel |series / quadrature - 1| (r in [0,8] step 1/4) = %.3e\n", e2);
  printf("gamma selftest: Gamma(0) = %.15f, Gamma(1) = %.15f, Gamma(1) - Gamma(0) = %.15f\n", Gam(0), Gam(1), Gam(1) - Gam(0));
}
