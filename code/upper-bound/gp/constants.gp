\\ Constants of Section 3 of the paper (potential theta1 = 1, b = 2), computed in PARI/GP, 60 digits.
\\ Every printed number is used in Section 3; the checks at the end must print OK.
default(realprecision, 60);
e12 = exp(-1/2);
E1h = eint1(1/2);                 \\ E_1(1/2)
J1 = E1h/2;                        \\ int_1^oo e^{-u^2/2} u^{-1} du
J0 = (e12 - J1)/2;                 \\ int_1^oo e^{-u^2/2} u^{-3} du, from J1 + 2 J0 = e^{-1/2}
\\ K(m) = int_1^oo t^{2m-1} e^{-t^2/2} dt
K(m) = if(m == -1, J0, if(m == 0, J1, 2^(m-1)*(m-1)!*e12*sum(j = 0, m-1, (1/2)^j/j!)));
J(n) = K(n-1);                     \\ J_n = int_1^oo u^{2n-3} e^{-u^2/2} du
Gn(n) = 2*(K(n) + 2*K(n-1));       \\ Gamma(r) = sum_n Gn(n) r^{2n}/(2n)!
Gam(r) = { my(s = 0., n = 0, t); while(1, t = Gn(n)*r^(2*n)/(2*n)!; s += t; if(n > 5 && t < 1e-40*s, break); n++); s };
dGx(x) = { my(s = 0., n = 1, t); while(1, t = n*Gn(n)*x^(n-1)/(2*n)!; s += t; if(n > 5 && t < 1e-40*s, break); n++); s };  \\ d/dx Gamma(sqrt x)
\\ direct quadrature for cross-checks
Gq(r) = 2*intnum(t = 1, max(r, 1) + 40, cosh(t*r)*exp(-t^2/2)*(1/t + 2/t^3));
printf("e^{-1/2} = %.15f\nE_1(1/2) = %.15f\nJ_0 = %.15f\nJ_1 = %.15f\nJ_2 = %.15f\nJ_3 = %.15f\nJ_4 = %.15f\n", e12, E1h, J0, J1, J(2), J(3), J(4));
printf("Gamma_n, n = 0..6: %s\n", vector(7, n, Gn(n-1)*1.));
printf("Gamma(0) = %.15f (2 e^{-1/2} = %.15f)\n", Gam(0), 2*e12);
foreach([0.5, 1, 1.7, 2.5], r, printf("Gamma(%s): series %.15f  quadrature %.15f\n", r, Gam(r), Gq(r)));
printf("Gamma(1) - Gamma(0) = %.15f\n", Gam(1) - Gam(0));

\\ ---- Lemma A: for s in [0, s0], hat Gamma - Gamma <= s f(rho^2), f(x) = sum_{n<=4} a_n x^n/(2n)!
lemA(s0) =
{
  my(L0 = -log(1 - s0)/s0, a = vector(5), f, df, r, xm, fm);
  a[1] = 2*exp(-(1 - s0)/2)*(1 + L0/2) - 4*J0;
  a[2] = 2*e12*(1/2 + L0) - 4*J1;
  for(n = 2, 4, a[n+1] = 3*e12 - 4*J(n));
  f = sum(n = 0, 4, a[n+1]*'x^n/(2*n)!);
  df = deriv(f, 'x);
  r = [real(z) | z <- polroots(df), abs(imag(z)) < 1e-30 && real(z) > 0];
  xm = if(#r, r[1], 0); fm = max(subst(f, 'x, xm), subst(f, 'x, 0));
  [L0, a, xm, fm, s0*fm];
}
{
  foreach([1/2, 0.6, 2/3], s0,
    my(v = lemA(s0));
    printf("Lemma A s0=%.4f: L0=%.10f a=%s argmax x=%.6f max f=%.10f bound s0*max f=%.10f\n",
      s0, v[1], v[2]*1., v[3], v[4], v[5]));
}
\\ positive root x0 of f for s0 = 2/3: f <= 0 on [x0, oo) (f concave, f(0) > 0), so hat Gamma <= Gamma for rho^2 >= x0, s <= 2/3
{
  my(v = lemA(2/3), f = sum(n = 0, 4, v[2][n+1]*'x^n/(2*n)!), r = [real(z) | z <- polroots(f), abs(imag(z)) < 1e-30 && real(z) > 0]);
  printf("Lemma A s0=2/3: positive roots of f: %s, sqrt = %s\n", r, apply(sqrt, r));
}

\\ ---- Lemma B: for s in [s0, 1], Gamma(|rho| c + sigma) - Gamma(rho) <= psi(rho) := Gamma(m(rho)) - Gamma(rho),
\\ m(rho) = sqrt(1 + rho^2) if rho^2 <= 1/s0 - 1, else rho sqrt(1-s0) + sqrt(s0); psi <= 0 for rho >= (1 + c0)/sigma0.
mB(rho, s0) = if(rho^2 <= 1/s0 - 1, sqrt(1 + rho^2), rho*sqrt(1 - s0) + sqrt(s0));
lemBnum(s0) = { my(best = -1e9, arg = 0, v); for(i = 0, 30000, my(rho = i/10000.); v = Gam(mB(rho, s0)) - Gam(rho); if(v > best, best = v; arg = rho)); [best, arg] };
\\ Rigorous piecewise bound: on [ra, rb] (m increasing), psi <= q_max * dGx(m(rb)^2), q = m^2 - rho^2,
\\ with q_max over [ra, rb] of the explicit q (concave quadratic beyond rho*, 1 below).
qB(rho, s0) = mB(rho, s0)^2 - rho^2;
qmax(ra, rb, s0) = { my(c0 = sqrt(1-s0), g0 = sqrt(s0), rs = sqrt(1/s0 - 1), rv = c0/g0, cand = [ra, rb]);
  if(rv > ra && rv < rb, cand = concat(cand, rv)); if(rs > ra && rs < rb, cand = concat(cand, rs));
  vecmax(apply(r -> qB(r, s0), cand)) };
lemBpieces(s0, cuts) = { my(out = []); for(i = 1, #cuts - 1, my(ra = cuts[i], rb = cuts[i+1]);
    out = concat(out, [[ra, rb, qmax(ra, rb, s0), dGx(mB(rb, s0)^2), qmax(ra, rb, s0)*dGx(mB(rb, s0)^2)]])); out };
{
  foreach([1/2, 0.6, 2/3], s0,
    my(v = lemBnum(s0), rz = (1 + sqrt(1 - s0))/sqrt(s0));
    printf("Lemma B s0=%.4f: numerical sup psi = %.10f at rho = %.4f; psi <= 0 beyond rho_z = %.10f\n", s0, v[1], v[2], rz));
}
s0B = 2/3; rzB = (1 + sqrt(1 - s0B))/sqrt(s0B);
cutsB = vector(21, i, rzB*(i-1)/20);
P = lemBpieces(s0B, cutsB);
{
  printf("Lemma B pieces, s0 = 2/3, 20 uniform pieces of [0, rho_z] (ra, rb, q_max, g'(m(rb)^2), bound):\n");
  for(i = 1, #P, printf("  [%.4f, %.4f] q_max=%.6f g'=%.6f bound=%.6f\n", P[i][1], P[i][2], P[i][3], P[i][4], P[i][5]));
  printf("Lemma B max piece bound = %.10f\n", vecmax(apply(v -> v[5], P)));
}

\\ ---- Lemma C (terminal condition): for rho >= 2, sqrt(2 pi) e^{rho^2/2} / Gamma(rho) <= rho + 1
\\ Proof bound: sqrt(2 pi)/I(rho) <= rho/Phi(rho-1) + e^{-(rho-1)^2/2}/(sqrt(2 pi) Phi(rho-1)^2), Phi the normal cdf.
Phi(x) = 1 - erfc(x/sqrt(2))/2;
bC(rho) = rho/Phi(rho - 1) + exp(-(rho-1)^2/2)/(sqrt(2*Pi)*Phi(rho-1)^2) - rho;
{
  printf("Lemma C: max over rho in [2, 60] of [CS bound - rho] = %.10f (must be <= 1)\n", vecmax(vector(5801, i, bC(2 + (i-1)/100.))));
  printf("Lemma C analytic: 2 phi(1)/Phi(1) = %.10f, phi(1)/Phi(1)^2 = %.10f, sum = %.10f (must be <= 1)\n", 2*exp(-1/2)/sqrt(2*Pi)/Phi(1), exp(-1/2)/sqrt(2*Pi)/Phi(1)^2, 2*exp(-1/2)/sqrt(2*Pi)/Phi(1) + exp(-1/2)/sqrt(2*Pi)/Phi(1)^2);
  printf("Lemma C: exact sqrt(2pi)/I(rho) - rho at rho = 0, 1, 3, 10: %s\n",
    vector(4, i, my(r = [0, 1, 3, 10][i]); sqrt(2*Pi)*exp(r^2/2)/Gam(r) - r));
}

\\ ---- Tail bound used for the series: n Gamma_n x^{n-1}/(2n)! <= 2 x^{n-1}/n!, and Gamma_n <= 2^{n+1} (n-1)! (n >= 1).
{
  my(ok = 1);
  for(n = 1, 200, if(Gn(n) > 2^(n+1)*(n-1)!, ok = 0); if(n*Gn(n)/(2*n)! > 2/n!, ok = 0));
  printf("series tail bounds Gamma_n <= 2^{n+1}(n-1)! and n Gamma_n/(2n)! <= 2/n! for n <= 200: %s\n", if(ok, "OK", "FAIL"));
}

\\ ---- Lemma B with an explicit truncation: g'(x) <= sum_{n=1}^{N} n Gamma_n x^{n-1}/(2n)! + 2 x^N/((N+1)! (1 - x/(N+2))),
\\ the tail from n Gamma_n/(2n)! <= 2/n! (checked above, proved in the note, Lemma 2.1 (d)); N = 30, x <= m(rho_z)^2.
dGxU(x, N) = sum(n = 1, N, n*Gn(n)*x^(n-1)/(2*n)!) + 2*x^N/((N+1)!*(1 - x/(N+2)));
PU = vector(#cutsB - 1, i, qmax(cutsB[i], cutsB[i+1], s0B)*dGxU(mB(cutsB[i+1], s0B)^2, 30));
{
  printf("Lemma B with truncation N = 30 and explicit tail: max piece bound = %.10f (x max = %.6f)\n", vecmax(PU), mB(rzB, s0B)^2);
}

\\ ---- Final constants of the theorem: s0 = 2/3, beta = 3.
{
  my(bA = lemA(2/3)[5], bB = vecmax(PU), beta = 3, ok = 1);
  printf("FINAL s0 = 2/3: Lemma A bound %.10f, Lemma B bound %.10f, beta = %d\n", bA, bB, beta);
  if(!(bA < beta && bB < beta), ok = 0);
  \\ Lemma A: concavity of f on [0, oo) (all of a_2, a_3, a_4 negative) and f'(0) = a_1/2 > 0
  my(a = lemA(2/3)[2]); if(!(a[3] < 0 && a[4] < 0 && a[5] < 0 && a[2] > 0), ok = 0);
  printf("regret bound: 3 log T + 2 log(3/sqrt(2 pi)) + eps_T, 2 log(3/sqrt(2 pi)) = %.10f\n", 2*log(3/sqrt(2*Pi)));
  printf("e^2 = %.10f, 2 sqrt(2 pi) e^2/3 = %.10f, 2 Gamma(0)/3 = %.10f\n", exp(2), 2*sqrt(2*Pi)*exp(2)/3, 4*e12/3);
  foreach([10, 100, 1000, 10^4, 10^5, 10^6, 10^9], T,
    printf("T = %d: bound 2 log(e^2 + (sqrt T + 1)(3T + 2e^{-1/2})/sqrt(2 pi)) = %.6f, minus 3 log T = %.6f, eps_T bound = %.6f\n",
      T, 2*log(exp(2) + (sqrt(T) + 1)*(3*T + 2*e12)/sqrt(2*Pi)), 2*log(exp(2) + (sqrt(T) + 1)*(3*T + 2*e12)/sqrt(2*Pi)) - 3*log(T), 2/sqrt(T) + 4*e12/(3*T) + 2*sqrt(2*Pi)*exp(2)/(3*T^(3/2))));
  printf("FINAL CHECKS: %s\n", if(ok, "OK", "FAIL"));
}
