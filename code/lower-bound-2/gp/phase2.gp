\\ Second program for the tests of Lemma 4.11 of the paper (phase 2), written from the statement only.
\\ Units: Z = sqrt(V) (theta* - theta_tau) has density f_A on [-A, A], A = 2; theta* x_{tau+i} = (rho + Z) eps_i;
\\ eps_i^2 = (1/2)(i/k)/r^2, nu_i^2 = (1/2) i/k, r = |rho| + A.
\\ Part 1: vT(rho, k) by its recursion against Phi_1(rho, k) where k >= pi^2 e^2 r^2, and the two
\\         intermediate bounds of step (iv).
\\ Part 2: the Fisher information of one +-1 outcome with mean theta x, by numerical differentiation.
\\ Part 3: the Bayes value of the phase-2 bracket for small k (exact enumeration of the outcomes, Gauss-Legendre
\\         quadrature in Z) must be >= vT(rho, k): van Trees bounds every learner, the Bayes one included;
\\         also the comparator term in closed form against (1 + X)/w_k.
\\ Usage: gp -q -s 1G phase2.gp
\p 40
A = 2; J = Pi^2 / A^2; EZ2 = A^2 * (1/3 - 2 / Pi^2);
c1 = 1 + EZ2 + log(Pi^2) - 1/2 + (J - 2) / (Pi^2 * exp(2));

\\ returns [vT, sum eps^2/w, comparator lower bound (1+X)/w_k, w_k, X]
vT(rho, k) =
{
  my(r = abs(rho) + A, w = J, s1 = 0., X = 0.);
  for (i = 1, k, my(e2 = (i / k) / (2 * r^2), n2 = (i / k) / 2.);
    s1 += e2 / w; w += e2 / (1 - n2); X += e2);
  [s1 - EZ2 + (1 + X) / w, s1, (1 + X) / w, w, X];
}
Phi1(rho, k) = my(r = abs(rho) + A); log(k / r^2) - c1 - log(k) / (2 * k) - 1 / k;
Lam(rho, k) = my(r = abs(rho) + A); log(k * A^2 / (4 * Pi^2 * r^2));

print("== Part 1: vT >= Phi_1 for k >= pi^2 e^2 r^2");
ok = 1; minmarg = 10^9; minat = 0;
{
foreach ([0, 1, 2, 3.8, 3.85, 3.9, 4.5, 5, 6, 8, 10, 15, 20], rho,
  my(r = abs(rho) + A, kmin = ceil(Pi^2 * exp(2) * r^2));
  foreach ([kmin, kmin + 1, 2 * kmin, 5 * kmin, 10^4, 177857, 10^6], k,
    if (k >= kmin && k <= 10^6,
      my(v = vT(rho, k), p = Phi1(rho, k), b1 = Lam(rho, k) - 1 - log(k) / (2 * k) - 1 / k, b2 = 1/2 - (J - 2) / (Pi^2 * exp(2)));
      if (v[1] < p || v[2] < b1 || v[3] < b2, ok = 0; print("  FAIL rho = ", rho, " k = ", k));
      if (v[1] - p < minmarg, minmarg = v[1] - p; minat = [rho, k]);
      if (k == kmin || k == 177857 || k == 10^6,
        print("  rho = ", rho, ", k = ", k, ": vT = ", strprintf("%.6f", v[1]), ", Phi_1 = ", strprintf("%.6f", p),
              ", sum eps^2/w = ", strprintf("%.6f", v[2]), " >= ", strprintf("%.6f", b1),
              ", (1+X)/w_k = ", strprintf("%.6f", v[3]), " >= ", strprintf("%.6f", b2))))));
}
print("  vT >= Phi_1 and both intermediate bounds at every point: ", if (ok, "PASS", "FAIL"), "; smallest vT - Phi_1 = ", minmarg, " at ", minat);
\\ the range used by the theorem at T_0: rho in [a, a+] = [3.8470, 3.8666], k in [k_0, T - 1]
print("  at T_0: vT(3.8470, 177857) - Phi_1 = ", vT(3.8470, 177857)[1] - Phi1(3.8470, 177857));

print("== Part 2: Fisher information of y in {-1, 1} with P(y = 1) = (1 + theta x)/2");
fis(th, x) = my(h = 10^-12, s = 0.); foreach ([1, -1], y, my(p = (1 + y * th * x) / 2, dp = ((1 + y * (th + h) * x) / 2 - (1 + y * (th - h) * x) / 2) / (2 * h)); s += dp^2 / p); s;
foreach ([[0.3, 0.5], [1.7, 0.4], [-2, 0.3]], c, print("  theta = ", c[1], ", x = ", c[2], ": numerical ", fis(c[1], c[2]), ", x^2/(1 - theta^2 x^2) = ", c[2]^2 / (1 - c[1]^2 * c[2]^2)));

print("== Part 3: Bayes value of the phase-2 bracket for small k against vT");
\\ Gauss-Legendre nodes on [-A, A]
NG = 80;
{
  my(P = pollegendre(NG), R = polrootsreal(P), dP = deriv(P));
  gl = vector(NG, i, my(x = R[i]); [A * x, A * 2 / ((1 - x^2) * subst(dP, 'x, x)^2)]);
}
Zn = vector(NG, i, gl[i][1]); Wn = vector(NG, i, gl[i][2] * cos(Pi * gl[i][1] / (2 * A))^2 / A);
print("  quadrature: total mass ", vecsum(Wn), ", E Z^2 ", sum(i = 1, NG, Wn[i] * Zn[i]^2), " (exact ", EZ2, ")");
\\ Bayes risk of the first sum: sum_i eps_i^2 E[Var(Z | D_{i-1})], by depth-first enumeration of D
\\ lik[n] = quadrature weight of node n times the likelihood of the outcomes of rounds < i; globals Bk, Brho, Be, Bacc
rec(lik, i) =
{
  my(m0 = sum(n = 1, NG, lik[n]), m1 = sum(n = 1, NG, lik[n] * Zn[n]), m2 = sum(n = 1, NG, lik[n] * Zn[n]^2));
  Bacc[i] += m2 - m1^2 / m0;
  if (i < Bk, foreach ([1, -1], y, rec(vector(NG, n, lik[n] * (1 + y * (Brho + Zn[n]) * Be[i]) / 2), i + 1)));
}
bayes(rho, k) =
{
  my(r = abs(rho) + A, e = vector(k, i, sqrt((i / k) / (2 * r^2))));
  Bk = k; Brho = rho; Be = e; Bacc = vector(k);
  rec(Wn, 1);
  my(acc = Bacc);
  my(first = sum(i = 1, k, e[i]^2 * acc[i]), X = sum(i = 1, k, e[i]^2), X4 = sum(i = 1, k, e[i]^4));
  \\ comparator term E[V_T (theta* - hat theta_T)^2] = E[Z^2 + X - (rho + Z)^2 sum eps^4]/(1 + X)
  my(comp = (EZ2 + X - (rho^2 + EZ2) * X4) / (1 + X));
  [first - EZ2 + comp, first, comp];
}
{
foreach ([[0, 6], [0, 10], [3.9, 8], [3.9, 12], [8, 12], [3.9, 14]], c,
  my(rho = c[1], k = c[2], b = bayes(rho, k), v = vT(rho, k));
  print("  rho = ", rho, ", k = ", k, ": Bayes bracket ", strprintf("%.6f", b[1]), " >= vT ", strprintf("%.6f", v[1]),
        " (", if (b[1] >= v[1], "ok", "VIOLATION"), "); first sum ", strprintf("%.6f", b[2]), " >= ", strprintf("%.6f", v[2]),
        "; comparator ", strprintf("%.6f", b[3]), " >= ", strprintf("%.6f", v[3])));
}
quit;
