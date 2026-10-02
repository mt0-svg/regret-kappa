\\ Sanity check of Lemmas 4.5 to 4.7 of the paper (Monte Carlo, numerical evidence only):
\\ the phase-1 chain rho -> rho sqrt(1 - s) +- sqrt(s) from rho = 1, hitting time eta of rho^2 >= L,
\\ against the Lyapunov bounds E[eta] <= G and P(eta > ceil(e G)) <= 1/e, G = 8.8 exp(L/2);
\\ and the largest |rho| at the hitting time against a+ = sqrt(L) + sqrt(5/8) exp(-L/4).
\\ Usage: gp -q -s 1G mc_phase1.gp
\p 19
setrand(20260930);
TAB = [6242, 6180, 6058, 5879, 5648, 5373, 5060, 4718, 4355, 3980, 3601, 3226, 2861, 2513, 2184, 1880, 1602, 1352, 1129, 934, 764, 620, 497, 395, 311, 242, 187, 142];
SJ = vector(28, j, TAB[j] / 10000.);
sfun(r) = my(a = abs(r)); if (a < 2.8, SJ[floor(10 * a) + 1], 0.625 * exp(-a^2 / 2));
run(L) = my(r = 1., n = 0); while (r^2 < L, my(s = sfun(r)); r = r * sqrt(1 - s) + if (random(2), 1, -1) * sqrt(s); n++); [n, abs(r)];
{
foreach ([[10, 4000], [14.799705740494663880, 2000]], c,
  my(L = c[1], R = c[2], G = 8.8 * exp(L / 2), n = ceil(exp(1) * G), tot = 0., over = 0, mx = 0, maxr = 0., ap = sqrt(L) + sqrt(5/8) * exp(-L / 4));
  for (i = 1, R, my(v = run(L)); tot += v[1]; mx = max(mx, v[1]); maxr = max(maxr, v[2]); if (v[1] > n, over++));
  print("L = ", L, ", runs ", R, ": mean eta = ", tot / R, " (G = ", G, ", mean/G = ", tot / R / G, ", mean/exp(L/2) = ", tot / R / exp(L / 2), ")");
  print("   P(eta > ceil(e G) = ", n, ") estimated ", over / R * 1., " (bound 1/e = ", exp(-1), "); max eta ", mx);
  print("   max |rho_eta| = ", maxr, " <= a+ = ", ap, ": ", maxr <= ap));
}
quit;
