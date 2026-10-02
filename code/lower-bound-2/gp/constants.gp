\\ Second program for the constants of Theorem 4.1 of the paper (Lemmas 4.5, 4.10, 4.12 and the proof of
\\ Theorem 4.1), written from the statements only. 80-digit floating point (PARI), every inequality checked below has a
\\ margin far above the rounding error of 80 digits; the tightest is the minimality of T_0.
\\ Usage: gp -q -s 1G constants.gp
\p 80
A = 2;
print("== Lemma 4.2: the prior f_A(z) = (1/A) cos^2(pi z/(2A)) on [-A, A], A = 2");
fA(z) = cos(Pi * z / (2 * A))^2 / A;
dfA(z) = -(Pi / (2 * A^2)) * sin(Pi * z / A);
print("  integral of f_A: ", intnum(z = -A, A, fA(z)));
print("  f_A' formula vs numerical derivative at z = 0.7: ", dfA(0.7), " ", derivnum(z = 0.7, fA(z)));
print("  f_A(+-A) = ", fA(A), ", f_A'(+-A) = ", dfA(A), " ", dfA(-A));
Jnum = intnum(z = -A, A, dfA(z)^2 / fA(z));
J = Pi^2 / A^2;
print("  J numerical = ", Jnum, ", pi^2/A^2 = ", J, ", difference ", Jnum - J);
EZ2num = intnum(z = -A, A, z^2 * fA(z));
EZ2 = A^2 * (1/3 - 2 / Pi^2);
print("  E Z^2 numerical = ", EZ2num, ", A^2 (1/3 - 2/pi^2) = ", EZ2, ", 4/3 - 8/pi^2 = ", 4/3 - 8/Pi^2);
\\ scaling: the law of c + Z/sqrt(v) has Fisher information v J
v = 7; cc = 1/3; Jv = intnum(t = cc - A/sqrt(v), cc + A/sqrt(v), my(z = sqrt(v) * (t - cc)); (v * dfA(z))^2 / (sqrt(v) * fA(z)));
print("  scaled prior (c = 1/3, v = 7): information ", Jv, " vs v J = ", v * J);

print("== c_1 = 1 + E Z^2 + log(pi^2) - 1/2 + (J - 2)/(pi^2 e^2)");
c1 = 1 + EZ2 + log(Pi^2) - 1/2 + (J - 2) / (Pi^2 * exp(2));
print("  c_1 = ", c1);
print("  rounded to 6 decimals: ", round(c1 * 10^6) / 10^6 * 1., " (note: 3.318633)");
print("  J E Z^2 = ", J * EZ2, " (note: pi^2/3 - 2 = ", Pi^2/3 - 2, ")");
print("  log(A^2/(4 pi^2)) = ", log(A^2 / (4 * Pi^2)), " = -log(pi^2) = ", -log(Pi^2));

print("== Lemma 3.3");
mx = exp(-1/2) / sqrt(2);
print("  max of (u/2) exp(-u^2/4) = exp(-1/2)/sqrt 2 = ", mx, "; numerical max ", vecmax(vector(40000, i, my(u = i / 10000.); u / 2 * exp(-u^2 / 4))));
print("  1 - sqrt(5/8) max = ", 1 - sqrt(5/8) * mx, " > 0");
epsL(L) = sqrt(5 * L / 8) * exp(-L / 4) + (5/16) * exp(-L / 2);
print("  eps_L at 14.5 = ", epsL(14.5), ", log 1.1 = ", log(1.1), ", ok: ", epsL(14.5) <= log(1.1));
print("  eps_L decreasing on [2, 40] on a grid: ", my(ok = 1, p = epsL(2)); forstep (L = 2.01, 40, 0.01, my(q = epsL(L)); if (q > p, ok = 0); p = q); ok);
print("  (a+)^2/2 - L/2 - eps_L at L = 14.5 (identity, must be 0): ", (sqrt(14.5) + sqrt(5/8) * exp(-14.5/4))^2 / 2 - 14.5/2 - epsL(14.5));
print("  3.8^2 = ", 3.8^2, " (a >= 3.8 iff L >= 14.44); max over cells of (j+1)/10 + sqrt(s_j) = ", \
  my(S = [6242, 6180, 6058, 5879, 5648, 5373, 5060, 4718, 4355, 3980, 3601, 3226, 2861, 2513, 2184, 1880, 1602, 1352, 1129, 934, 764, 620, 497, 395, 311, 242, 187, 142]); vecmax(vector(28, j, j / 10 + sqrt(S[j] / 10000.))));
print("  sqrt(5/8) exp(-14.5/4) = ", sqrt(5/8) * exp(-14.5 / 4), " (note: <= 0.022)");

print("== Theorem LB: constants as functions of T");
j0(T) = ceil(log(3 * log(T)));
LL(T) = 2 * log(T / (20 * exp(1) * j0(T)));
Llow(T) = 2 * log(T) - 2 * log(20 * exp(1)) - 2 * log(log(3 * log(T)) + 1);
aa(T) = sqrt(LL(T));
ap(T) = aa(T) + sqrt(5/8) * exp(-LL(T) / 4);
T1(T) = floor(T / 2);
k0(T) = T - T1(T);
B0(T) = my(L = LL(T), a = sqrt(L), k = k0(T)); L + log(k / (a + 2)^2) - c1 - log(k) / (2 * k) - 1 / k;
BB(T) = (1 - exp(-j0(T))) * B0(T);
C1(T) = LL(T) >= 14.5;
C2(T) = j0(T) * (8.8 * exp(1) * exp(LL(T) / 2) + 1) <= T1(T) - 1;
C3(T) = k0(T) >= Pi^2 * exp(2) * (ap(T) + 2)^2;
S1(T) = my(l = log(T), ll = log(l)); 3 * l - ll - 2 * log(ll + 2.1) - 14.6;
S1b(T) = my(l = log(T), ll = log(l)); 3 * l - ll - 2 * log(ll + 2.1) - 14.55;
S2(T) = my(l = log(T), ll = log(l)); 3 * l - 2 * ll - 15.2;
S3(T) = my(l = log(T), ll = log(l)); 3 * l - 8 * ll;

\\ T_0: least integer with Llow(T) >= 14.5 (Llow is increasing in T)
lo = 1000; hi = 10^7; while (hi - lo > 1, my(mid = (lo + hi) \ 2); if (Llow(mid) >= 14.5, hi = mid, lo = mid));
print("  least integer T with L_low(T) >= 14.5: ", hi, "  (L_low(T-1) = ", Llow(hi - 1), ", L_low(T) = ", Llow(hi), ")");
T0 = 355713;
print("  at T_0 = ", T0, ": j_0 = ", j0(T0), ", L = ", LL(T0), ", a = ", aa(T0), ", a+ = ", ap(T0), ", T_1 = ", T1(T0), ", k_0 = ", k0(T0));
print("  (C1) L >= 14.5: ", C1(T0), ";  (C2) lhs ", j0(T0) * (8.8 * exp(1) * exp(LL(T0) / 2) + 1), " <= T_1 - 1 = ", T1(T0) - 1, ": ", C2(T0));
print("  (C3) k_0 = ", k0(T0), " >= pi^2 e^2 (a+ + 2)^2 = ", Pi^2 * exp(2) * (ap(T0) + 2)^2, ": ", C3(T0));
print("  (C3) simplified: T/2 - pi^2 e^2 (sqrt(2 log T) + 2.03)^2 at T_0 = ", T0 / 2 - Pi^2 * exp(2) * (sqrt(2 * log(T0)) + 2.03)^2);
print("  B_0(T_0) = ", B0(T0), ", B(T_0) = ", BB(T0));
print("  0.06 T_0 = ", 0.06 * T0, " >= j_0 + 3/2 = ", j0(T0) + 3/2);
\\ derivative of T/2 - pi^2 e^2 (sqrt(2 log T) + 2.03)^2 at T = 1000 (it decreases in T): 1/2 - pi^2 e^2 (sqrt(2 log T) + 2.03) * 2/(T sqrt(2 log T))
print("  d/dT of the (C3) function at T = 1000: ", 1/2 - Pi^2 * exp(2) * (sqrt(2 * log(1000)) + 2.03) * 2 / (1000 * sqrt(2 * log(1000))), " (the subtracted term decreases in T, so positive for T >= 1000)");

print("== values");
foreach ([10^5, T0, 10^6, 10^7, 10^10], T, print("  T = ", T, ": B(T) = ", BB(T), "  L = ", LL(T), "  conditions ", [C1(T), C2(T), C3(T)]));
foreach ([6, 10, 20, 50, 100], e, my(T = 10^e); print("  T = 10^", e, ": B(T)/log T = ", BB(T) / log(T)));

print("== grid T_0 .. 10^100 (100 points per decade) and both sides of every jump of j_0");
minC = 1; minB_S1 = 10^9; minB_S1at = 0; minS1b = 10^9; minS12 = 10^9; minS23 = 10^9; minB0 = 10^9; cntT = 0;
chkT(T) = {
  cntT++;
  if (!(C1(T) && C2(T) && C3(T)), minC = 0; print("  CONDITION FAILS at T = ", T));
  my(b = BB(T)); minB0 = min(minB0, B0(T));
  if (b - S1(T) < minB_S1, minB_S1 = b - S1(T); minB_S1at = T);
  minS1b = min(minS1b, b - S1b(T));
  minS12 = min(minS12, S1(T) - S2(T));
  minS23 = min(minS23, S2(T) - S3(T));
}
for (i = 0, 9500, my(T = floor(10^(log(T0) / log(10) + i / 100))); if (T >= T0, chkT(T)));
\\ jumps of j_0: log(3 log T) = j, i.e. T = exp(e^j / 3)
for (j = 4, 6, my(Tj = exp(exp(j) / 3)); if (Tj > T0, foreach ([floor(Tj) - 1, floor(Tj), floor(Tj) + 1, floor(Tj) + 2], T, if (T >= T0, chkT(T)))));
chkT(T0); chkT(T0 + 1);
print("  points checked: ", cntT, "; conditions (C1)-(C3) hold at all: ", minC);
print("  min B_0 = ", minB0, " (> 0 needed)");
print("  min of B(T) - [3 log T - log log T - 2 log(log log T + 2.1) - 14.6] = ", minB_S1, " at T = ", minB_S1at);
print("  min of B(T) - [same with 14.55] = ", minS1b);
print("  min of [form with 14.6] - [3 log T - 2 log log T - 15.2] = ", minS12);
print("  min of [3 log T - 2 log log T - 15.2] - [3 log T - 8 log log T] = ", minS23);
print("  at T_0: v = log log T_0 = ", log(log(T0)), ", v - 2 log(v + 2.1) = ", log(log(T0)) - 2 * log(log(log(T0)) + 2.1), ", 6 log log T_0 = ", 6 * log(log(T0)));

print("== simplified-form constants (section 5)");
print("  log 3 + 1 = ", log(3) + 1);
print("  2 log(1 + 2/sqrt(14.5)) = ", 2 * log(1 + 2 / sqrt(14.5)));
print("  2 log(20 e) + 2 log 2 + 0.8445 + c_1 + 1e-4 + 1 = ", 2 * log(20 * exp(1)) + 2 * log(2) + 0.8445 + c1 + 10^-4 + 1);
print("  log(k_0)/(2 k_0) + 1/k_0 at k_0 = k_0(T_0): ", log(k0(T0)) / (2 * k0(T0)) + 1 / k0(T0));
print("== monotonicity of F(u, k) = u^2 + log(k/(u+2)^2) - log(k)/(2k) - 1/k (section 5)");
print("  dF/du = 2u - 2/(u+2) at u = 1: ", 2 - 2/3, "; dF/dk at k = 3: ", 1/3. + (log(3) - 1) / 18 + 1/9);
quit;
