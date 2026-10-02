\\ extras.gp: numerical remarks on Lemmas 3.10 and 3.11 of the paper that no proof uses
\\ and two controls of the split choices (evidence, floating point).
\\ Run: gp -q gp/extras.gp > out/extras.txt
default(realprecision, 60);
read("gp/gamma.gp");

\\ section 5: s -> 0 drift 3 e^{-1/2} cosh(rho) - 4 J(rho) = (1/2)(Gamma'' - rho Gamma'), coefficientwise:
\\ coefficient of rho^{2n}/(2n)! on the right is (Gamma_{n+1} - 2 n Gamma_n)/2, on the left 3 e^{-1/2} - 4 J_n, J_n = K_{n-1}
{
my(J0 = (e12 - E1h / 2) / 2, worst = 0.);
for (n = 0, 60,
  my(Jn = if (n == 0, J0, Kv[n]), lhs = 3 * e12 - 4 * Jn, rhs = (Gn[n + 2] - 2 * n * Gn[n + 1]) / 2);
  worst = max(worst, abs(lhs - rhs) / (1 + abs(lhs))));
printf("section 5: drift = (1/2)(Gamma'' - rho Gamma'), max relative coefficient mismatch n <= 60: %.3e\n", worst);
}

\\ section 6: the split s0. Lemma A analog (s <= s0) and numerical sup of psi (s >= s0)
lemmaA(s0) = {
  my(L = -log(1 - s0) / s0, J0 = (e12 - E1h / 2) / 2, J1 = E1h / 2, a = vector(5), P, x0);
  a[1] = 2 * exp(-(1 - s0) / 2) * (1 + L / 2) - 4 * J0;
  a[2] = 2 * e12 * (1/2 + L) - 4 * J1;
  for (n = 2, 4, a[n + 1] = 3 * e12 - 4 * Kv[n]);
  P = sum(n = 0, 4, a[n + 1] * 'X^n / (2 * n)!);
  x0 = solve(t = 0, 20, subst(deriv(P, 'X), 'X, t));
  s0 * subst(P, 'X, x0)
};
psisup(s0) = {
  my(c0 = sqrt(1 - s0), sg0 = sqrt(s0), rs = sqrt(1 / s0 - 1), best = -oo, bp = 0);
  forstep (rho = 0, 3, 1/2000,
    my(m = if (rho <= rs, sqrt(1 + rho^2), c0 * rho + sg0), d = Gam(m) - Gam(rho));
    if (d > best, best = d; bp = rho));
  [best, bp]
};
{
foreach ([1/2, 3/5, 2/3, 3/4], s0,
  my(p = psisup(s0));
  printf("split s0 = %s: Lemma A analog bound %.6f; numerical sup of psi %.6f at rho = %.4f\n", s0, lemmaA(s0), p[1], p[2]));
}

\\ Lemma 7.1: the analytic constant on the region rho >= r0 (x = r0 - 1), r0/(r0-1) phi(x)/N(x) + phi(x)/N(x)^2
{
foreach ([3/2, 7/4, 2, 3], r0,
  my(x = r0 - 1, ph = exp(-x^2 / 2) / sqrt(2 * Pi), Nx = 1 - erfc(x / sqrt(2)) / 2);
  printf("Lemma 7.1 region rho >= %s: constant %.6f (must be <= 1 for the argument)\n", r0, r0 / (r0 - 1) * ph / Nx + ph / Nx^2));
}
print("EXTRAS DONE");
\q
