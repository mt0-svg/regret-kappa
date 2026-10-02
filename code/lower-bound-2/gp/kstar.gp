\\ A descriptive number of the drift of Lemma 4.3 of the paper, not a proof step:
\\ "the smallest admissible constant K in g = K exp(rho^2/2), with the best move at each rho, is 7.16, near rho = 1.65".
\\ K(rho) = 1 / max over s in (0,1) of [exp((rho^2 (1-s) + s)/2) cosh(rho sqrt(s(1-s))) - exp(rho^2/2)]; K* = sup over rho.
\\ Floating point (38 digits), grid in s of step 1/2000 refined by golden section; numerical evidence only.
\\ Usage: gp -q -s 1G kstar.gp
\p 38
gain(r, s) = exp((r^2 * (1 - s) + s) / 2) * cosh(r * sqrt(s * (1 - s))) - exp(r^2 / 2);
best(r) =
{
  my(bs = 0, bv = -10^9);
  for (i = 1, 1999, my(s = i / 2000., v = gain(r, s)); if (v > bv, bv = v; bs = s));
  my(a = max(bs - 1/2000, 10^-9), b = min(bs + 1/2000, 1 - 10^-9), gr = (sqrt(5) - 1) / 2);
  for (it = 1, 80, my(c = b - gr * (b - a), d = a + gr * (b - a)); if (gain(r, c) > gain(r, d), b = d, a = c));
  [(a + b) / 2, gain(r, (a + b) / 2)];
}
{
  my(Km = 0, Kat = 0, Ks = 0);
  forstep (r = 0, 6, 1/200, my(v = best(r)); if (1 / v[2] > Km, Km = 1 / v[2]; Kat = r; Ks = v[1]));
  print("K* = ", Km, " at rho = ", Kat * 1., " (best move s = ", Ks, ")");
  foreach ([1.6, 1.65, 1.7], r, my(v = best(r)); print("  rho = ", r, ": best s = ", v[1], ", K(rho) = ", 1 / v[2]));
}
\\ Open statement O1 (not a proof step): g = K exp(rho^2/2)/sqrt(rho^2 + b) with the best move at each rho needs
\\ K = 69, 59, 53, 46, 43 for b = 1, 2, 3, 5, 8 (note, floating point scan of rho in [0, 9]).
g1(r, b) = exp(r^2 / 2) / sqrt(r^2 + b);
gainb(r, s, b) = (g1(r * sqrt(1 - s) + sqrt(s), b) + g1(r * sqrt(1 - s) - sqrt(s), b)) / 2 - g1(r, b);
bestb(r, b) =
{
  my(bs = 0, bv = -10^9);
  for (i = 1, 999, my(s = i / 1000., v = gainb(r, s, b)); if (v > bv, bv = v; bs = s));
  my(a = max(bs - 1/1000, 10^-9), c = min(bs + 1/1000, 1 - 10^-9), gr = (sqrt(5) - 1) / 2);
  for (it = 1, 60, my(u = c - gr * (c - a), w = a + gr * (c - a)); if (gainb(r, u, b) > gainb(r, w, b), c = w, a = u));
  gainb(r, (a + c) / 2, b);
}
{
  foreach ([1, 2, 3, 5, 8], b,
    my(Km = 0, Kat = 0);
    forstep (r = 0, 9, 1/100, my(v = bestb(r, b)); if (v <= 0, Km = oo; Kat = r; break); if (1 / v > Km, Km = 1 / v; Kat = r));
    print("O1: b = ", b, ": K needed = ", strprintf("%.2f", Km), " at rho = ", Kat * 1.));
}
quit;
