# c4_lemma71.sage: Lemma 3.12 of the paper and the terminal condition, item (4) of Computation 3.13 (Lemma 7.1 or Lemma C in the outputs).
#   The constant 2 phi(1)/N(1) + phi(1)/N(1)^2 < 1; the steps of the proof at sample points;
#   the conclusion sqrt(2 pi) e^{rho^2/2} <= (rho + 1) Gamma(rho) certified on [2, 6] as a
#   cross-check; values of sqrt(2 pi)/I(rho) - rho.
load("lib.sage")

say("c4_lemma71: Lemma 7.1, %d-bit balls" % PREC)


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
check("2 phi(1)/N(1) + phi(1)/N(1)^2 < 1 (Lemma 7.1)", tot < 1, "margin 1 - sum >= %s" % lo(1 - tot, 10))
check("the displayed values 0.5752, 0.3418, 0.9170 are the 4-digit roundings",
      small(t1 - QQ(5752) / 10000, QQ(5) / 100000) and small(t2 - QQ(3418) / 10000, QQ(5) / 100000)
      and small(tot - QQ(9170) / 10000, QQ(5) / 100000))
check("NEG the sum < 0.91 is refuted", tot > QQ(91) / 100)

say("")
say("Analytic steps (method: analytic), with certified spot checks:")
say("  Mills: Nbar(x) = int_x^oo phi(t) dt <= int_x^oo (t/x) phi(t) dt = phi(x)/x for x > 0")
okM = all((1 - Ncdf(xx)) < phi(xx) / xx for xx in [QQ(1) / 2, 1, 2, 3, 5, 10])
check("  Mills spot checks Nbar(x) < phi(x)/x at x = 1/2, 1, 2, 3, 5, 10", okM)
say("  rho/(rho - 1) <= 2 for rho >= 2; phi decreasing and N increasing on [1, oo): analytic")
check("  phi(x)/N(x) and phi(x)/N(x)^2 decrease at x = 1, 3/2, 2, 3, 5 (spot checks)",
      all(phi(a) / Ncdf(a) > phi(b) / Ncdf(b) and phi(a) / Ncdf(a) ^ 2 > phi(b) / Ncdf(b) ^ 2
          for a, b in [(1, QQ(3) / 2), (QQ(3) / 2, 2), (2, 3), (3, 5)]))

# The chain I(rho) >= int gamma/theta >= Z^2/(rho Z + e^{-(rho-1)^2/2}) at sample points.
for rho in [2, QQ(5) / 2, 3, 5, 8]:
    rc = CB(rho)
    Gq = Gamma_quad(rho)
    I = (-RB(rho) ^ 2 / 2).exp() * Gq
    gth = int_1_inf(lambda z, an: (-(z - rc) ^ 2 / 2).exp() / z, 1, 0, rho, 1)
    Z = int_1_inf(lambda z, an: (-(z - rc) ^ 2 / 2).exp(), 1, 0, rho, 1)
    Zt = int_1_inf(lambda z, an: z * (-(z - rc) ^ 2 / 2).exp(), 1, 1, rho, 1)
    x = RB(rho) - 1
    okZ = Z.overlaps(SQRT2PI * Ncdf(x)) and Zt.overlaps(rho * Z + (-x ^ 2 / 2).exp())
    lowb = Z ^ 2 / (rho * Z + (-x ^ 2 / 2).exp())
    chain = I > gth and gth > lowb
    bound = SQRT2PI / I
    rhsb = rho / Ncdf(x) + phi(x) / Ncdf(x) ^ 2
    check("  rho = %s: Z = sqrt(2pi) N(rho-1), int theta gamma = rho Z + e^{-(rho-1)^2/2}; I >= int gamma/theta >= Z^2/(...)" % rho,
          okZ and chain, "I = %s" % iv(I, 12))
    check("  rho = %s: sqrt(2pi)/I <= rho/N(x) + phi(x)/N(x)^2 <= rho + 2 phi(1)/N(1) + phi(1)/N(1)^2 < rho + 1" % rho,
          bound <= rhsb and rhsb <= rho + tot and rho + tot < rho + 1,
          "sqrt(2pi)/I - rho = %s, bound - rho = %s" % (iv(bound - rho, 10), iv(rhsb - rho, 10)))

say("")
say("Values of sqrt(2 pi)/I(rho) - rho, I(rho) = e^{-rho^2/2} Gamma(rho) (Gamma by quadrature):")
for rho in [0, 1, 2, 3, 10]:
    I = (-RB(rho) ^ 2 / 2).exp() * Gamma_quad(rho)
    say("  rho = %2s: %s" % (rho, iv(SQRT2PI / I - rho, 15)))
I3s = (-RB(3) ^ 2 / 2).exp() * Gamma_series(3)
check("Gamma(3): series = quadrature (cross-check of the values above)", I3s.overlaps((-RB(3) ^ 2 / 2).exp() * Gamma_quad(3)))
check("NEG at rho = 0 the inequality sqrt(2pi) e^{rho^2/2} <= (rho+1) Gamma(rho) is false (refuted)",
      SQRT2PI > Gamma_quad(0))

# Where the inequality starts to hold (evidence on the region rho < 2 that the lemma does not use).
NG = 200
GC = [Gamma_n(n) / factorial(2 * n) for n in range(NG + 1)]


def Gam(r):
    x = RB(r) ^ 2
    acc = RB(0)
    for cn in reversed(GC):
        acc = acc * x + cn
    return acc + RB(0).add_error(series_tail(x, NG, 0))


Fc = lambda r: (r + 1) * Gam(r) - SQRT2PI * (r ^ 2 / 2).exp()
rl, rh = bisect_root(Fc, 0, 2, QQ(2) ^ -60)
say("")
say("(rho+1) Gamma(rho) - sqrt(2pi) e^{rho^2/2} changes sign on [0, 2] at rho in", iv(RB(rl).union(RB(rh)), 15), "(evidence)")

# Certified check of the conclusion on [2, 6]: on [a, b] (0 < a), (rho+1) Gamma(rho) >= (a+1) Gamma(a)
# and sqrt(2pi) e^{rho^2/2} <= sqrt(2pi) e^{b^2/2}.
h = QQ(1) / 1000
okC = True
worst = None
for j in range(4000):
    a_, b_ = 2 + j * h, 2 + (j + 1) * h
    lhs = (a_ + 1) * Gam(a_)
    rhs = SQRT2PI * (RB(b_) ^ 2 / 2).exp()
    rat = lhs / rhs
    if not (lhs > rhs):
        okC = False
    if worst is None or rat.lower() < worst[0].lower():
        worst = (rat, a_)
check("sqrt(2pi) e^{rho^2/2} < (rho+1) Gamma(rho) on [2, 6] (4000 pieces, certified; a cross-check of Lemma 7.1)", okC,
      "smallest piece ratio %s at rho = %s" % (lo(worst[0], 8), worst[1]))
say("Consequence for |rho| <= 2: C lambda_0 = e^2 >= e^{rho^2/2} since rho^2/2 <= 2 (analytic, no computation);")
say("for 2 <= |rho| <= sqrt T: C >= (|rho| + 1)/sqrt(2 pi) (analytic).")

finish()
