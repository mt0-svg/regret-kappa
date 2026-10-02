\\ Pointwise stress test of Lemmas 3.10 and 3.11 of the paper (evidence; the proofs are on paper).
\\ Lemma 5.2: E(rho, s) := hat Gamma - Gamma = P(rho, s) - 4 s J(rho) (Lemma 5.1) <= s f(rho^2) for s <= 2/3.
\\ Lemma 6.1: Gamma(rho c + sigma) - Gamma(rho) <= 2.7053 for s >= 2/3.
default(realprecision, 38);
e12 = exp(-1/2); E1h = eint1(1/2); J1 = E1h/2; J0 = (e12 - J1)/2;
K(m) = if(m == -1, J0, if(m == 0, J1, 2^(m-1)*(m-1)!*e12*sum(j = 0, m-1, (1/2)^j/j!)));
Jn(n) = K(n-1);
Gn(n) = 2*(K(n) + 2*K(n-1));
Gam(r) = { my(s = 0., n = 0, t); while(1, t = Gn(n)*r^(2*n)/(2*n)!; s += t; if(n > 5 && abs(t) < 1e-30*s, break); n++); s };
L0 = 3/2*log(3);
a = vector(5); a[1] = 2*exp(-1/6)*(1 + L0/2) - 4*J0; a[2] = 2*e12*(1/2 + L0) - 4*J1; for(n = 2, 4, a[n+1] = 3*e12 - 4*Jn(n));
f(x) = sum(n = 0, 4, a[n+1]*x^n/(2*n)!);
Pf(rho, s) = { my(c = sqrt(1 - s)); 2*intnum(u = c, 1, cosh(u*rho)*exp(-u^2/2)*(1/u + 2*c^2/u^3)) };
Jf(rho) = { my(m = max(rho, 1)); intnum(u = 1, m, cosh(u*rho)*exp(-u^2/2)/u^3) + intnum(u = m, m + 30, cosh(u*rho)*exp(-u^2/2)/u^3) };
{
  my(ss = [1e-4, 1e-3, 0.01, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.65, 2/3], worst = -1e99, arg = 0, maxE = -1e99, argE = 0, cnt = 0);
  for(i = 0, 60, my(rho = i/10., jr = Jf(rho));
    foreach(ss, s, my(E = Pf(rho, s) - 4*s*jr, d = E - s*f(rho^2)); cnt++;
      if(d > worst, worst = d; arg = [rho, s]); if(E > maxE, maxE = E; argE = [rho, s])));
  printf("Lemma 5.2 pointwise: %d points (rho in [0, 6] step 0.1, s in %s)\n", cnt, ss*1.);
  printf("  max of E - s f(rho^2) = %.6e at (rho, s) = %s (must be <= 0)\n", worst, arg*1.);
  printf("  max of E = %.10f at (rho, s) = %s (Lemma 5.2 bound 2.8856915928)\n", maxE, argE*1.);
}
{
  my(worst = -1e99, arg = 0, cnt = 0);
  for(j = 0, 100, my(s = 2/3 + j/300.);
    for(i = 0, 300, my(rho = i/50., v = Gam(rho*sqrt(1 - s) + sqrt(s)) - Gam(rho)); cnt++;
      if(v > worst, worst = v; arg = [rho, s])));
  printf("Lemma 6.1 pointwise: %d points (s in [2/3, 1] step 1/300, rho in [0, 6] step 0.02)\n", cnt);
  printf("  max of Gamma(rho c + sigma) - Gamma(rho) = %.10f at (rho, s) = %s (Lemma 6.1 bound 2.7053)\n", worst, arg*1.);
}
printf("DONE\n");
