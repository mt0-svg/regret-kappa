\\ Check of Lemmas 2.2, 4.8 and 4.2 of the paper in exact rational arithmetic on random data.
\\ Lemma 1.1: Regret_T = sum (yhat^2 - 2 yhat y) + S_T^2/V_T (min over theta computed independently, at theta = S_T/V_T,
\\            and compared with a brute minimisation of the quadratic by its vertex formula a theta^2 + b theta + c).
\\ Lemma 1.2: split at n with any theta*.
\\ Lemma 2.1: rho_{t+1} = rho_t sqrt(1 - s) + y sqrt(s) when x_{t+1}^2 = V_t s/(1 - s) (checked on squares, exact).
\\ Usage: gp -q -s 1G identities.gp
setrand(7);
rr() = (random(2001) - 1000) / random([1, 97]);
bad = 0;
{
for (trial = 1, 300,
  my(T = 2 + random(12), x = vector(T, i, rr()), y = vector(T, i, (random(201) - 100) / 100), yh = vector(T, i, rr()));
  if (x[1] == 0, x[1] = 1);
  my(V = sum(t = 1, T, x[t]^2), S = sum(t = 1, T, x[t] * y[t]), Y2 = sum(t = 1, T, y[t]^2));
  \\ comparator: quadratic V th^2 - 2 S th + Y2, vertex value Y2 - S^2/V
  my(minq = subst(V * 'th^2 - 2 * S * 'th + Y2, 'th, S / V));
  my(reg = sum(t = 1, T, (yh[t] - y[t])^2) - minq);
  if (reg != sum(t = 1, T, yh[t]^2 - 2 * yh[t] * y[t]) + S^2 / V, bad++; print("Lemma 1.1 fails"));
  \\ Lemma 1.2
  my(n = 1 + random(T - 1), Vn = sum(t = 1, n, x[t]^2), Sn = sum(t = 1, n, x[t] * y[t]), thn = Sn / Vn, ths = rr(), thT = S / V);
  my(rhs = sum(t = 1, n, yh[t]^2 - 2 * yh[t] * y[t]) + Sn^2 / Vn + sum(t = n + 1, T, (yh[t] - y[t])^2 - (ths * x[t] - y[t])^2) - Vn * (ths - thn)^2 + V * (ths - thT)^2);
  if (reg != rhs, bad++; print("Lemma 1.2 fails at T = ", T, " n = ", n)));
}
print("Lemmas 1.1 and 1.2 on 300 random exact instances: ", if (bad == 0, "PASS", "FAIL"));
\\ Lemma 2.1: with x = sqrt(V s/(1-s)), (rho_{t+1})^2 = (S + x y)^2/(V + x^2) must equal (rho sqrt(1-s) + y sqrt(s))^2
\\ = rho^2 (1-s) + s + 2 rho y sqrt(s(1-s)); compare after isolating the irrational part: both equal A + B sqrt(s(1-s)) x-free.
bad2 = 0;
{
for (trial = 1, 300,
  my(V = random([1, 10^6]) / random([1, 999]), S = (random(2001) - 1000) / random([1, 99]), s = random([1, 9999]) / 10000, y = 2 * random(2) - 1);
  \\ x^2 = V s/(1-s); (S + x y)^2 = S^2 + 2 S x y + x^2; V + x^2 = V/(1-s)
  \\ rational part: (S^2 + x^2)(1-s)/V; irrational part: 2 S y x (1-s)/V with x = sqrt(V s/(1-s))
  \\ target: rational part S^2 (1-s)/V + s; irrational part 2 (S/sqrt V) y sqrt(s(1-s)), i.e. same after squaring the coefficients
  my(x2 = V * s / (1 - s), ratL = (S^2 + x2) * (1 - s) / V, ratR = S^2 * (1 - s) / V + s);
  my(irL2 = (2 * S * y * (1 - s) / V)^2 * x2, irR2 = (2 * y)^2 * (S^2 / V) * s * (1 - s));
  if (ratL != ratR || irL2 != irR2, bad2++));
}
print("Lemma 2.1 (rho update, exact on 300 random instances, rational and irrational parts): ", if (bad2 == 0, "PASS", "FAIL"));
quit;
