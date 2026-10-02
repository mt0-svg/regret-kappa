\\ game.gp: the learner of Theorem 3.1 of the paper played in the original variables
\\ (x_t, yhat_t, y_t) against several adaptive adversaries (evidence). For each play it checks
\\ that the potential Psi_t = sum_{i<=t} (yhat_i^2 - 2 yhat_i y_i) + Phi_{T-t}(rho_t) never increases,
\\ and that the regret, computed from its definition with the best theta in hindsight, is at most
\\ the bound of Theorem U. Features include 0 and negative values, outcomes interior values.
\\ Run: gp -q gp/game.gp > out/game.txt
default(realprecision, 60);
read("gp/gamma.gp");
clip1(z) = max(-1, min(1, z));
sgn1(x) = if (x < 0, -1, 1);
setrand(4242);
urand() = random(10^15) / 10^15 * 1.;

\\ the learner: state (S, V) before round t, feature x, horizon T; returns yhat
learner(S, V, x, t, T, lam0) = {
  my(rho = if (V == 0, 0, S / sqrt(V)), Vt = V + x^2, s = if (Vt == 0, 0, x^2 / Vt), c = sqrt(1 - s), sg = sqrt(s),
     lam = lam0 + 3 * (T - t), eta);
  eta = clip1(log((lam + Gam(rho * c + sg)) / (lam + Gam(rho * c - sg))) / 2);
  sgn1(x) * eta
};
Phi(k, rho, Cc, lam0) = 2 * log(Cc * (lam0 + 3 * k + Gam(rho)));
bound(T) = 2 * log(exp(2) + (sqrt(T) + 1) * (3 * T + 2 * exp(-1/2)) / sqrt(2 * Pi));

\\ adversary kinds: 1 random, 2 growth with y = -sign(yhat), 3 greedy on the potential, 4 myopic regret
sgrid = concat([[0, 1e-6, 1e-4, 1e-3, 1e-2], vector(19, j, j / 20), [0.99, 0.999, 0.9999, 1 - 1e-6]]);
ygrid = [-1, -1/2, 0, 1/2, 1];

play(kind, T) = {
  my(Cc = (sqrt(T) + 1) / sqrt(2 * Pi), lam0 = exp(2) / Cc, S = 0, V = 0, cum = 0, Psi, maxinc = -oo, xs = vector(T), ys = vector(T), yh = vector(T), loss = 0, rho, regret, th, comp);
  Psi = Phi(T, 0, Cc, lam0);
  for (t = 1, T,
    my(k = T - t + 1, x, y, p, rho0 = if (V == 0, 0, S / sqrt(V)), Snew, Vnew, rho1, Psinew);
    if (kind == 1,
      x = if (random(7) == 0, 0, (2 * random(2) - 1) * 10^(6 * urand() - 3) * urand());
      p = learner(S, V, x, t, T, lam0);
      y = if (random(2), 2 * urand() - 1, 2 * random(2) - 1));
    if (kind == 2,
      x = if (t % 5 == 0, 0, (2 * random(2) - 1) * 2.^t);
      p = learner(S, V, x, t, T, lam0);
      y = if (p == 0, 1, -sgn1(p)));
    if (kind == 3 || kind == 4,
      my(bestv = -oo, bx = 0, by = 0, cand = if (V == 0, [0, 1], sgrid));
      foreach (cand, s,
        my(xx = if (V == 0, s, if (s == 0, 0, sqrt(s * V / (1 - s)))) * (2 * random(2) - 1), pp = learner(S, V, xx, t, T, lam0));
        foreach (ygrid, yy,
          my(r1 = if (V + xx^2 == 0, 0, (S + xx * yy) / sqrt(V + xx^2)), v);
          v = pp^2 - 2 * pp * yy + if (kind == 3, Phi(k - 1, r1, Cc, lam0) - Phi(k, rho0, Cc, lam0), r1^2 - rho0^2);
          if (v > bestv, bestv = v; bx = xx; by = yy)));
      x = bx; y = by; p = learner(S, V, x, t, T, lam0));
    xs[t] = x; ys[t] = y; yh[t] = p;
    cum += p^2 - 2 * p * y;
    S += x * y; V += x^2;
    rho1 = if (V == 0, 0, S / sqrt(V));
    Psinew = cum + Phi(T - t, rho1, Cc, lam0);
    maxinc = max(maxinc, Psinew - Psi);
    Psi = Psinew);
  \\ regret from the definition
  loss = sum(t = 1, T, (yh[t] - ys[t])^2);
  th = if (V == 0, 0, S / V);
  comp = sum(t = 1, T, (th * xs[t] - ys[t])^2);
  regret = loss - comp;
  [regret, bound(T), maxinc, if (V == 0, 0, S / sqrt(V)), #select(z -> z == 0, xs), #select(z -> z < 0, xs), #select(z -> abs(z) < 1 && z != 0 && abs(z) != 1/2, ys)]
};

{
my(allok = 1);
foreach ([[1, 200], [1, 1000], [2, 200], [3, 50], [3, 300], [4, 50], [4, 300]], kt,
  for (rep = 1, if (kt[1] == 1, 5, if (kt[2] > 100, 1, 3)),
    my(r = play(kt[1], kt[2]));
    printf("adversary %d, T = %d, rep %d: regret = %.6f, bound = %.6f, max Psi increment = %.3e, final rho = %.4f, zero x: %d, negative x: %d, interior y (not 0, +-1/2): %d\n", kt[1], kt[2], rep, r[1], r[2], r[3], r[4], r[5], r[6], r[7]);
    if (r[1] > r[2] || r[3] > 1e-30, allok = 0)));
print(if (allok, "GAME OK", "GAME FAIL"));
}
\q
