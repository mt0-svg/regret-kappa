\\ Lemma 3.10 of the paper with rational bounds of the constants, for the Lean proof.
\\ Run: gp -q quartic.gp > out/quartic.txt
default(realprecision, 50);
Em = 6065306597/10^10; Ep = 6065306598/10^10;      \\ e^{-1/2}
Km = 2798867/10^7; Kp = 2798869/10^7;              \\ K_0 = E_1(1/2)/2
E6p = 8464817249/10^10;                            \\ e^{-1/6} <= E6p
Lp = 3/2*10986123/10^7;                            \\ (3/2) log 3 <= Lp
print("check: e^{-1/2} in [Em, Ep]: ", Em <= exp(-1/2) && exp(-1/2) <= Ep);
print("check: K_0 in [Km, Kp]: ", Km <= eint1(1/2)/2 && eint1(1/2)/2 <= Kp);
print("check: e^{-1/6} <= E6p: ", exp(-1/6) <= E6p, "  log 3 <= 1.0986123: ", log(3) <= 10986123/10^7);
a0 = 2*E6p*(1 + Lp/2) - 2*(Em - Kp);
a1 = 2*Ep*(1/2 + Lp) - 4*Km;
a2 = -Em; a3 = -9*Em; a4 = -49*Em;
b = [a0, a1/2, a2/24, a3/720, a4/40320];
fp(x) = b[1] + b[2]*x + b[3]*x^2 + b[4]*x^3 + b[5]*x^4;
dfp(x) = b[2] + 2*b[3]*x + 3*b[4]*x^2 + 4*b[5]*x^3;
print("a0+ = ", a0*1., "  a1+ = ", a1*1.);
print("b = ", b);
r = 3968325/10^6;
print("f+(r) = ", fp(r)*1., "  f+'(r) = ", dfp(r)*1.);
C = 43286/10^4 - fp(r) - dfp(r)^2/(4*abs(b[3]));
print("C = 4.3286 - f+(r) - f+'(r)^2/(4|b2|) = ", C*1., "  (positive: ", C > 0, ")");
rp = r + dfp(r)/(2*abs(b[3]));
print("r' = ", rp, " = ", rp*1.);
\\ identity: 4.3286 - f+(x) = C + |b2| (x - r')^2 + (x - r)^2 (|b3| (x + 2r) + |b4| (x^2 + 2 r x + 3 r^2))
id = 43286/10^4 - fp('x) - (C + abs(b[3])*('x - rp)^2 + ('x - r)^2*(abs(b[4])*('x + 2*r) + abs(b[5])*('x^2 + 2*r*'x + 3*r^2)));
print("identity residual (must be 0): ", simplify(id));
print("(2/3) * 4.3286 = ", 2/3*43286/10^4*1.);
\\ true maximum with the exact constants
E = exp(-1/2); K = eint1(1/2)/2; L = 3/2*log(3);
c = [2*exp(-1/6)*(1+L/2) - 2*(E - K), (2*E*(1/2+L) - 4*K)/2, -E/24, -9*E/720, -49*E/40320];
f(x) = c[1] + c[2]*x + c[3]*x^2 + c[4]*x^3 + c[5]*x^4;
xs = solve(x = 3, 5, c[2] + 2*c[3]*x + 3*c[4]*x^2 + 4*c[5]*x^3);
print("exact: x* = ", xs, "  max f = ", f(xs));
