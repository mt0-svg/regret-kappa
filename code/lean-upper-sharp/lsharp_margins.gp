\\ Margins of the numerical steps of Section 4 and Appendix B of the paper (Lemmas 4.3, B.1 and B.3, the proof of
\\ Theorem 4.1), in 60 digits. They size the steps; the Lean
\\ proof certifies the inequalities it uses with its own rational bounds.
default(realprecision, 60);
T0 = 355713;
j0(T) = ceil(log(3 * log(T)));
L(T) = 2 * log(T / (20 * exp(1) * j0(T)));
Llow(T) = 2 * log(T) - 2 * log(20 * exp(1)) - 2 * log(log(3 * log(T)) + 1);
ap(T) = sqrt(L(T)) + sqrt(5/8) * exp(-L(T) / 4);
J = Pi^2 / 4;
c1 = 1/2 + 4/3 - 8/Pi^2 + log(Pi^2) + (J - 2) / (Pi^2 * exp(2));
eps(x) = sqrt(5 * x / 8) * exp(-x / 4) + 5/16 * exp(-x / 2);
chi(r) = exp(-r^2 / 2) * (r^2 / 2 + r^4 / 4);
pr(s, v) = printf("%-58s %.15g\n", s, v);
pr("(C1) Llow(T0) - 14.5", Llow(T0) - 14.5);
pr("(C1) Llow(T0 - 1) - 14.5", Llow(T0 - 1) - 14.5);
pr("j0(T0)", j0(T0));
pr("(C1) L(T0) with the actual j0", L(T0));
pr("least T with j0(T) >= 4: e^(e^3 / 3)", exp(exp(3) / 3));
for(JJ = 5, 8, pr(Str("(C1) lower bound of L where j0 = ", JJ, ": 2e^(j0-1)/3 - 2log(20e j0)"), 2 * exp(JJ - 1) / 3 - 2 * log(20 * exp(1) * JJ)));
pr("(C2) 0.06 T0 - j0(T0) - 3/2", 0.06 * T0 - j0(T0) - 3/2);
pr("(C3) k0 - pi^2 e^2 (a_+ + 2)^2 at T0", (T0 - T0 \ 2) - Pi^2 * exp(2) * (ap(T0) + 2)^2);
pr("pi^2 e^2", Pi^2 * exp(2));
pr("Lemma B.3: eps(14.5)", eps(14.5));
pr("Lemma B.3: log 1.1", log(1.1));
pr("Lemma B.3: crude eps(14.5) with e^(-3.625) <= 1/37", sqrt(5 * 14.5 / 8) / 37 + 5/16 / 37^2);
pr("e^3.625", exp(3.625));
pr("Lemma B.3: 2.8 + sqrt(0.6242) and sqrt(14.5)", 2.8 + sqrt(0.6242));
pr("  sqrt(14.5)", sqrt(14.5));
pr("Lemma B.3: 1 - sqrt(5/8) e^(-1/2) / sqrt 2", 1 - sqrt(5/8) * exp(-1/2) / sqrt(2));
pr("Lemma B.1 (a): chi(2.8) and 12/25", chi(2.8));
pr("  12/25", 12/25);
pr("  e^3.92 and the needed (3.92 + 15.3664) 25/12", exp(3.92));
pr("  needed", (3.92 + 15.3664) * 25 / 12);
pr("c1", c1);
pr("J - 2 = pi^2/4 - 2", J - 2);
pr("E Z^2 = 4/3 - 8/pi^2", 4/3 - 8/Pi^2);
pr("simplified: 2 log(1 + 2/sqrt(14.5))", 2 * log(1 + 2 / sqrt(14.5)));
pr("simplified: 2 log(20e) + 2 log 2 + 0.85 + 3.33 + 10^-4 (at most 13.59)", 2 * log(20 * exp(1)) + 2 * log(2) + 0.85 + 3.33 + 10^-4);
pr("simplified: log 3 + 1", log(3) + 1);
pr("simplified: z - 2 log(z + 2.1) at z = log log T0", log(log(T0)) - 2 * log(log(log(T0)) + 2.1));
pr("  log log T0", log(log(T0)));
quit
