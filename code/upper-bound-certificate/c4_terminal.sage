# c4_terminal.sage: Lemma 3.4 of the paper, item (4) of Computation A.9:
#   the constant 2 phi(1)/N(1) + phi(1)/N(1)^2 < 1.
load("lib.sage")

say("c4_terminal: Lemma 3.4, %d-bit balls" % PREC)


def phi(x):
    x = RB(x)
    return (-x ^ 2 / 2).exp() / SQRT2PI


def Ncdf(x):
    return (1 + (RB(x) / RB(2).sqrt()).erf()) / 2


phi1 = phi(1)
N1 = Ncdf(1)
N1q = QQ(1) / 2 + quad(lambda z, an: (-z * z / 2).exp(), 0, 1) / SQRT2PI
say("phi(1) = e^{-1/2}/sqrt(2 pi) =", iv(phi1, 30))
say("N(1) (Arb erf)                =", iv(N1, 30))
say("N(1) (1/2 + quadrature)       =", iv(N1q, 30))
check("N(1): erf form = quadrature form", N1.overlaps(N1q) and N1q.rad() < 10 ^ -50)
t1 = 2 * phi1 / N1
t2 = phi1 / N1 ^ 2
tot = t1 + t2
say("2 phi(1)/N(1)   =", iv(t1, 30))
say("phi(1)/N(1)^2   =", iv(t2, 30))
say("sum             =", iv(tot, 30))
check("2 phi(1)/N(1) + phi(1)/N(1)^2 < 1 (Lemma 3.4)", tot < 1, "margin 1 - sum >= %s" % lo(1 - tot, 10))
check("the sum is 0.91703362 to 8 decimals", small(tot - QQ(91703362) / 10 ^ 8, QQ(1) / 10 ^ 8))
check("NEG the sum < 0.91 is refuted", tot > QQ(91) / 100)

finish()
