\\ onestep.gp: numerical check (evidence, floating point) of the one-step inequality (P)
\\ (3.3) of the paper for the learner of Theorem 3.1, on a grid of (rho, s, y, lambda):
\\   inc := max_y [ exp((eta^2 - 2 eta y)/2) (lam + Gam(rho c + y sig)) ] - lam - Gam(rho)  <= beta = 3,
\\   eta = clip((1/2) log((lam + Gam(rho c + sig)) / (lam + Gam(rho c - sig)))), c = sqrt(1-s), sig = sqrt(s).
\\ Also three negative controls (a learner or an increment that must fail).
\\ Run: gp -q gp/onestep.gp > out/onestep.txt
default(realprecision, 120);
read("gp/gamma.gp");
gamma_selftest();

clip1(z) = max(-1, min(1, z));
lams = [0, 1/1000, 1/10, 1, 3, 10, 100, 10^4, 10^8];
ys = [-1, 1, -99/100, 99/100, -9/10, 9/10, -3/4, -1/2, -1/4, 0, 1/4, 1/2, 3/4];
rhos = concat([vector(301, i, (i - 1) / 50), vector(56, i, 6 + i / 4), [-1/2, -13/10, -5/2, -7]]);
ss = concat([vector(101, k, (k - 1) / 100), vector(9, j, 10^(-j - 1)), vector(8, j, 1 - 10^(-j - 2)), [2/3 - 10^-6, 2/3 + 10^-6]]);
nl = #lams; ny = #ys;

\\ per lambda: [max inc, rho, s, eta clipped?], max log excess over rho >= 3, max relative gain of interior y, violations of beta = 3
best = vector(nl, i, [-oo, 0, 0, 0]);
logex = vector(nl, i, -oo);
intgain = vector(nl, i, -oo);
viol3 = vector(nl);
\\ controls
viol145 = vector(nl); maxinc0 = vector(nl, i, -oo); maxflip = vector(nl, i, -oo);
symm = 0.;
incstore = Map();

{
for (ir = 1, #rhos,
  my(rho = rhos[ir], G0 = Gam(rho));
  for (is = 1, #ss,
    my(s = ss[is], c = sqrt(1 - s), sg = sqrt(s), Gy = vector(ny, j, Gam(rho * c + ys[j] * sg)));
    for (il = 1, nl,
      my(lam = lams[il], ratio = (lam + Gy[2]) / (lam + Gy[1]), e0 = log(ratio) / 2, eta = clip1(e0),
         vals, vend, vall, inc, f0, ff);
      vals = vector(ny, j, exp((eta^2 - 2 * eta * ys[j]) / 2) * (lam + Gy[j]));
      vend = max(vals[1], vals[2]);
      vall = vecmax(vals);
      inc = vall - lam - G0;
      if (inc > best[il][1], best[il] = [inc, rho, s, abs(e0) > 1]);
      if (abs(rho) >= 3, logex[il] = max(logex[il], log(vall) - log(lam + 3 + G0)));
      intgain[il] = max(intgain[il], (vall - vend) / (lam + G0));
      if (inc > 3, viol3[il]++);
      if (inc > 1.4, viol145[il]++);
      \\ control learner eta = 0
      f0 = max(lam + Gy[1], lam + Gy[2]) - lam - G0;
      maxinc0[il] = max(maxinc0[il], f0);
      \\ control learner with the sign of eta flipped
      ff = max(exp((eta^2 - 2 * eta) / 2) * (lam + Gy[1]), exp((eta^2 + 2 * eta) / 2) * (lam + Gy[2])) - lam - G0;
      maxflip[il] = max(maxflip[il], ff);
      if (il == 4 && (rho == 1/2 || rho == -1/2 || rho == 13/10 || rho == -13/10 || rho == 5/2 || rho == -5/2 || rho == 7 || rho == -7),
        my(key = [abs(rho), s], old);
        if (mapisdefined(incstore, key, &old), symm = max(symm, abs(old - inc) / (1 + abs(inc))), mapput(incstore, key, inc)));
    )
  )
);
}

{
printf("grid: %d values of rho, %d of s, %d of y, %d of lambda\n", #rhos, #ss, ny, nl);
for (il = 1, nl,
  printf("lambda = %s: max inc = %.10f at rho = %.4f, s = %.8f (unclipped branch: %d); violations of beta=3: %d; max over |rho|>=3 of Q/2 - log(lam+3+Gam(rho)) = %.4e; max relative gain of interior y over y=+-1 = %.3e\n",
    lams[il], best[il][1], best[il][2], best[il][3], !best[il][4], viol3[il], logex[il], intgain[il]));
printf("symmetry rho -> -rho (lambda = 1): max relative difference of inc = %.3e\n", symm);
printf("Gamma(1) - Gamma(0) = %.10f\n", Gam(1) - Gam(0));
print("controls (each must fail):");
for (il = 1, nl, printf("  lambda = %s: points with inc > 1.4: %d; learner eta = 0: max inc = %.4e; learner -eta: max inc = %.4e\n", lams[il], viol145[il], maxinc0[il], maxflip[il]));
total = sum(il = 1, nl, viol3[il]);
printf("TOTAL violations of (P) with beta = 3: %d\n", total);
print(if (total == 0, "ONESTEP OK", "ONESTEP FAIL"));
}
\q
