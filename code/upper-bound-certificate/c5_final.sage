# c5_final.sage: the final inequality of Theorem 3.1 of the paper (Theorem U in the outputs), item (5) of Computation 3.13:
#   2 log(e^2 + (sqrt T + 1)(3T + 2e^{-1/2})/sqrt(2 pi))
#     <= 3 log T + 2 log(3/sqrt(2 pi)) + 2/sqrt T + 0.81/T + 12.35/T^{3/2}   for every integer T >= 1.
# Proof (analytic, all real T > 0): write the argument as X(1 + a)(1 + b) + e^2 with
# X = 3 T^{3/2}/sqrt(2 pi), a = T^{-1/2}, b = Gamma_0/(3T), Gamma_0 = 2e^{-1/2}. Then
# log A = log X + log(1+a) + log(1+b) + log(1 + e^2/(X(1+a)(1+b))) <= log X + a + b + e^2/X
# (log(1+t) <= t, t >= 0), and 2 log X = 3 log T + 2 log(3/sqrt(2 pi)), 2b = (4e^{-1/2}/3)/T,
# 2e^2/X = (2 sqrt(2 pi) e^2/3)/T^{3/2}. It remains to certify 4e^{-1/2}/3 <= 0.81 and
# 2 sqrt(2 pi) e^2/3 <= 12.35. A direct certified check for T = 1..10^5 is a cross-check.
load("lib.sage")

say("c5_final: final inequality of Theorem U, %d-bit balls" % PREC)

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
check("the displayed 12.348 is the 3-decimal rounding of 2 sqrt(2 pi) e^2/3", small(k2 - QQ(12348) / 1000, QQ(5) / 10 ^ 4))
check("the displayed 0.8088 is an upper bound of 4 e^{-1/2}/3, whose 4-decimal rounding is 0.8087",
      k1 < QQ(8088) / 10000 and small(k1 - QQ(8087) / 10000, QQ(5) / 10 ^ 5))
check("NEG 4 e^{-1/2}/3 < 0.80 is refuted", k1 > QQ(80) / 100)

# Symbolic identities of the proof.
T, g0 = var("T g0")
assume(T > 0)
Xs = 3 * T ^ (QQ(3) / 2) / sqrt(2 * pi)
id1 = Xs * (1 + T ^ (-QQ(1) / 2)) * (1 + g0 / (3 * T)) - (sqrt(T) + 1) * (3 * T + g0) / sqrt(2 * pi)
check("X (1 + T^{-1/2}) (1 + Gamma_0/(3T)) = (sqrt T + 1)(3T + Gamma_0)/sqrt(2 pi) (Sage symbolic)", bool(id1.simplify_full() == 0))
id2 = 2 * log(Xs) - (3 * log(T) + 2 * log(3 / sqrt(2 * pi)))
check("2 log X = 3 log T + 2 log(3/sqrt(2 pi)) (Sage symbolic)", bool(id2.simplify_log().simplify_full() == 0) or bool(id2.expand_log().simplify_full() == 0))
id3 = 2 * (Xs.subs(T=T) ^ -1) * exp(2) - (2 * sqrt(2 * pi) * exp(2) / 3) * T ^ (-QQ(3) / 2)
check("2 e^2/X = (2 sqrt(2 pi) e^2/3) T^{-3/2} (Sage symbolic)", bool(id3.simplify_full() == 0))
forget()
say("log(1 + t) <= t for t >= 0: analytic (concavity of log)")


def lhs(t):
    t = RB(t)
    return 2 * (E2 + (t.sqrt() + 1) * (3 * t + 2 * EM) / SQRT2PI).log()


def rhs(t, c_half=2, c1=QQ(81) / 100, c32=QQ(1235) / 100):
    t = RB(t)
    return 3 * t.log() + K0 + c_half / t.sqrt() + c1 / t + c32 / t ^ (QQ(3) / 2)


say("")
t0 = time.time()
TMAX = 10 ^ 5
ok = True
worst = None
for t in range(1, TMAX + 1):
    d = rhs(t) - lhs(t)
    if not (d > 0):
        ok = False
        say("not certified at T =", t, iv(d))
    w = d * t
    if worst is None or w.lower() < worst[0].lower():
        worst = (w, t)
check("direct check: RHS - LHS > 0 for every integer T = 1..%d (certified, cross-check of the analytic proof)" % TMAX, ok,
      "min over T of T (RHS - LHS) = %s at T = %d" % (lo(worst[0], 8), worst[1]))
say("  (time %.1f s)" % (time.time() - t0))
for e in [6, 7, 8, 9, 10, 12, 15, 20, 30]:
    t = 10 ^ e
    d = rhs(t) - lhs(t)
    check("direct check at T = 10^%d" % e, d > 0, "T (RHS - LHS) = %s" % iv(d * t, 8))
say("")
say("Values of the bound 2 log(e^2 + (sqrt T + 1)(3T + 2e^{-1/2})/sqrt(2 pi)):")
for e in [2, 4, 6]:
    t = 10 ^ e
    say("  T = 10^%d: %s, minus 3 log T: %s, second form (RHS): %s" % (e, iv(lhs(t), 12), iv(lhs(t) - 3 * RB(t).log(), 10), iv(rhs(t), 12)))

# Negative control: with 1.99/sqrt T in place of 2/sqrt T the inequality fails for large T,
# so the direct check is sensitive at the scale of the claim.
first = None
for t in range(1, TMAX + 1):
    if rhs(t, c_half=QQ(199) / 100) - lhs(t) < 0:
        first = t
        break
check("NEG with 1.99/sqrt T the inequality is refuted at some T <= 10^5", first is not None, "first refuted T = %s" % first)

finish()
