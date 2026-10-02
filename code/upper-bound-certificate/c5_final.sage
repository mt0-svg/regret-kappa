# c5_final.sage: the final inequality of Theorem 3.1 of the paper, item (5) of Computation A.9:
#   2 log(e^2 + (sqrt T + 1)(3T + 2e^{-1/2})/sqrt(2 pi))
#     <= 3 log T + 2 log(3/sqrt(2 pi)) + 2/sqrt T + 0.81/T + 12.35/T^{3/2}   for every integer T >= 1.
# Proof (analytic, all real T > 0): write the argument as X(1 + a)(1 + b) + e^2 with
# X = 3 T^{3/2}/sqrt(2 pi), a = T^{-1/2}, b = Gamma_0/(3T), Gamma_0 = 2e^{-1/2}. Then
# log A = log X + log(1+a) + log(1+b) + log(1 + e^2/(X(1+a)(1+b))) <= log X + a + b + e^2/X
# (log(1+t) <= t, t >= 0), and 2 log X = 3 log T + 2 log(3/sqrt(2 pi)), 2b = (4e^{-1/2}/3)/T,
# 2e^2/X = (2 sqrt(2 pi) e^2/3)/T^{3/2}. It remains to certify 4e^{-1/2}/3 <= 0.81 and
# 2 sqrt(2 pi) e^2/3 <= 12.35.
load("lib.sage")

say("c5_final: final inequality of Theorem 3.1, %d-bit balls" % PREC)

E2 = RB(2).exp()
k1 = 4 * EM / 3
k2 = 2 * SQRT2PI * E2 / 3
K0 = 2 * (3 / SQRT2PI).log()
say("4 e^{-1/2}/3          =", iv(k1, 25))
say("2 sqrt(2 pi) e^2 / 3  =", iv(k2, 25))
say("2 log(3/sqrt(2 pi))   =", iv(K0, 25))
check("4 e^{-1/2}/3 < 0.81", k1 < QQ(81) / 100, "margin %s" % lo(QQ(81) / 100 - k1, 6))
check("2 sqrt(2 pi) e^2/3 < 12.35", k2 < QQ(1235) / 100, "margin %s" % lo(QQ(1235) / 100 - k2, 6))
check("2 log(3/sqrt(2 pi)) = 0.35935 to 5 decimals", small(K0 - QQ(35935) / 100000, QQ(5) / 10 ^ 6))
check("NEG 4 e^{-1/2}/3 < 0.80 is refuted", k1 > QQ(80) / 100)

say("log(1 + t) <= t for t >= 0: analytic (concavity of log)")

finish()
