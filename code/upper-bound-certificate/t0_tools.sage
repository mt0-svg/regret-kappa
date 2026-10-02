# t0_tools.sage: known-answer tests and negative controls for every tool of lib.sage.
load("lib.sage")


def dec(s):
    """Exact rational of a decimal string 'a.b', and the half unit of its last digit."""
    a, b = s.split(".")
    q = ZZ(a + b) / 10 ^ len(b)
    return q, QQ(1) / (2 * 10 ^ len(b))


def known(s):
    """Ball of a decimal value known to len(digits) places (radius one unit of the last place)."""
    q, h = dec(s)
    return RB(q).add_error(RB(2 * h))


say("t0_tools: known-answer tests (KAT) and negative controls (NEG) of lib.sage, %d bits" % PREC)

# 1. Ball comparisons.
check("KAT ball: 1 < 2 is certified", RB(1) < RB(2))
check("KAT ball: pi lies in its 50-digit decimal",
      RB.pi().overlaps(known("3.14159265358979323846264338327950288419716939937510")))
check("NEG ball: pi < 314159/100000 is not certified", not (RB.pi() < QQ(314159) / 100000))
check("NEG ball: pi > 314159/100000 is certified (refutes the false claim)", RB.pi() > QQ(314159) / 100000)
wide = RB(1).add_error(QQ(1) / 10)
check("NEG ball: overlapping balls compare neither way",
      (not (wide < QQ(105) / 100)) and (not (wide > QQ(105) / 100)))
check("NEG ball: a nan ball (sqrt of a negative ball) passes no comparison",
      (not (RB(-1).sqrt() > 0)) and (not (RB(-1).sqrt() < 0)))

# 2. Exponential series (exact rationals plus tail) against Arb's exp and known decimals.
e_known = known("2.71828182845904523536028747135266249775724709369995")
check("KAT exp_series(1) overlaps the 50-digit decimal of e", exp_series(1).overlaps(e_known), iv(exp_series(1)))
check("KAT exp_series(-1/2) overlaps Arb exp(-1/2)", exp_series(-1 / 2).overlaps(EM), iv(exp_series(-1 / 2), 30))
check("KAT e^{-1/2} overlaps 0.60653065971263342360379953499118045344",
      EM.overlaps(known("0.60653065971263342360379953499118045344")))
check("KAT exp_series(-1/2) radius < 1e-70", exp_series(-1 / 2).rad() < 10 ^ -70)
check("NEG e^{-1/2} is disjoint from the decimal altered in the 40th place",
      disjoint(EM, known("0.6065306597126334236037995349911804534429")))

# 3. E_1 by its series against Arb's exp_integral_e, a known decimal, and quadrature.
E1one = E1_series(1)
check("KAT E1_series(1) overlaps 0.2193839343955202736771637754601216490310",
      E1one.overlaps(known("0.2193839343955202736771637754601216490310")), iv(E1one, 30))
arb_E1one = CB(1).exp_integral_e(1).real()
arb_E1half = CB(1 / 2).exp_integral_e(1).real()
check("KAT E1_series(1) overlaps Arb exp_integral_e(1, 1)", E1one.overlaps(arb_E1one))
check("KAT E1_series(1/2) overlaps Arb exp_integral_e(1, 1/2)", E1H.overlaps(arb_E1half), iv(E1H, 30))
E1_by_quad = 2 * int_1_inf(lambda z, an: (-z * z / 2).exp() / z, 1, 0, 0, 1)
check("KAT E1(1/2) = 2 int_1^oo e^{-u^2/2}/u du (quadrature)", E1H.overlaps(E1_by_quad), iv(E1_by_quad, 30))
check("KAT E1(1/2) enclosure radius < 1e-70", E1H.rad() < 10 ^ -70 and E1_by_quad.rad() < 10 ^ -60)
no_gamma = E1H + RB.euler_constant()
check("NEG series without the Euler constant is disjoint from Arb's E1(1/2)", disjoint(no_gamma, arb_E1half))

# 4. Quadrature.
I01 = quad(lambda z, an: z.exp(), 0, 1)
check("KAT quad: int_0^1 e^x = e - 1", I01.overlaps(RB(1).exp() - 1) and I01.rad() < 10 ^ -60, iv(I01))
I1 = int_1_inf(lambda z, an: z * (-z * z / 2).exp(), 1, 1, 0, 1)
check("KAT int_1_inf: int_1^oo t e^{-t^2/2} = e^{-1/2}", I1.overlaps(EM) and I1.rad() < 10 ^ -60, iv(I1))
I3 = int_1_inf(lambda z, an: z ^ 3 * (-z * z / 2).exp(), 1, 3, 0, 1)
check("KAT int_1_inf: int_1^oo t^3 e^{-t^2/2} = 3 e^{-1/2}", I3.overlaps(3 * EM), iv(I3))
check("NEG int_1^oo t^3 e^{-t^2/2} is certified different from 2 e^{-1/2}", disjoint(I3, 2 * EM))
G0 = quad(lambda z, an: (-z * z / 2).exp(), 0, 1) + int_1_inf(lambda z, an: (-z * z / 2).exp(), 1, 0, 0, 1)
check("KAT int_0^oo e^{-t^2/2} = sqrt(pi/2)", G0.overlaps((RB.pi() / 2).sqrt()), iv(G0))
N1q = QQ(1) / 2 + quad(lambda z, an: (-z * z / 2).exp(), 0, 1) / SQRT2PI
check("KAT N(1) = 1/2 + int_0^1 phi = 0.8413447460685429485852325456320379",
      N1q.overlaps(known("0.8413447460685429485852325456320379")), iv(N1q))

# 5. Tail bound of lib.sage against exact tails, and its guards.
for R in [2, 3, 5]:
    exact = (-RB(R) ^ 2 / 2).exp()
    tb = tail_bound(1, 1, 0, 1, R)
    check("KAT tail_bound >= exact tail int_%d^oo t e^{-t^2/2} = e^{-R^2/2}" % R, tb >= exact,
          "bound %s exact %s" % (up(tb, 6), lo(exact, 6)))
for R in [8, 10]:
    F = lambda z, an: z ^ 3 * (z - z * z / 2).exp()
    Rf = R + 40
    tail = quad(F, R, Rf) + RB(0).add_error(tail_bound(1, 3, 1, 1, Rf))
    tb = tail_bound(1, 3, 1, 1, R)
    check("KAT tail_bound(k=3, r=1, a=1, R=%d) >= int_R^oo t^3 e^{t - t^2/2} (quadrature)" % R, tb >= tail,
          "bound %s tail %s" % (up(tb, 6), up(tail, 6)))
try:
    tail_bound(1, 0, 1, 1, 4)
    check("NEG tail_bound refuses R < 8 r / a", False)
except ValueError:
    check("NEG tail_bound refuses R < 8 r / a", True)
try:
    tail_bound(1, 40, 0, 1, 3)
    check("NEG tail_bound refuses R^2 < 4 k / a", False)
except ValueError:
    check("NEG tail_bound refuses R^2 < 4 k / a", True)
# The formula used outside its hypotheses is wrong, so the guard matters.
raw = 2 * RB(3) ^ 39 * (-RB(27) / 8).exp()
true40 = quad(lambda z, an: z ^ 40 * (-z * z / 2).exp(), 3, 60) + RB(0).add_error(tail_bound(1, 40, 0, 1, 60))
check("NEG formula outside its hypotheses (k=40, R=3) undercuts the true tail", raw < true40,
      "formula %s true %s" % (up(raw, 6), lo(true40, 6)))

# 6. Closed forms K_m and the series of Gamma against quadrature.
check("KAT K_m / e^{-1/2} = 1, 3, 13, 79 for m = 1..4", [K_coef(m) for m in range(1, 5)] == [1, 3, 13, 79])
for m in range(1, 5):
    Kq = int_1_inf(lambda z, an: z ^ (2 * m - 1) * (-z * z / 2).exp(), 1, 2 * m - 1, 0, 1)
    check("KAT K_%d closed form = quadrature" % m, Kq.overlaps(K_closed(m)) and Kq.rad() < 10 ^ -50, iv(Kq))
inc = [(RB(2) ^ (m - 1) * RB(m).gamma_inc(RB(1) / 2)) for m in range(1, 5)]
check("KAT K_m = 2^{m-1} Gamma(m, 1/2) (Arb gamma_inc), m = 1..4",
      all(inc[m - 1].overlaps(K_closed(m)) for m in range(1, 5)))
for r in [QQ(1) / 2, 1, QQ(17) / 10, QQ(5) / 2, 4]:
    gs, gq = Gamma_series(r), Gamma_quad(r)
    check("KAT Gamma(%s): series = quadrature" % r, gs.overlaps(gq) and gs.rad() < 10 ^ -50 and gq.rad() < 10 ^ -50,
          "series %s quad %s" % (iv(gs, 25), iv(gq, 25)))
xb = RB(1)
bad = sum((9 * EM if n == 2 else Gamma_n(n)) * xb ^ n / factorial(2 * n) for n in range(40)) + RB(0).add_error(series_tail(xb, 39, 0))
check("NEG series with Gamma_2 = 9 e^{-1/2} is disjoint from the quadrature of Gamma(1)", disjoint(bad, Gamma_quad(1)))

# 7. g'(x) series against quadrature of Gamma'(sqrt x)/(2 sqrt x).
for x in [QQ(1) / 2, 1, 2, QQ(37) / 10]:
    r = RB(x).sqrt()
    gq = dGamma_quad(r) / (2 * r)
    gs = gprime_series(x)
    g30 = gprime_upper(x, 30)
    check("KAT g'(%s): series = quadrature" % x, gs.overlaps(gq) and gs.rad() < 10 ^ -50, iv(gs, 25))
    check("KAT g'(%s) <= truncated series N=30 plus tail bound" % x, gq.upper() <= g30.upper(),
          "N=30 bound %s" % up(g30, 20))
x = RB(2)
badg = sum(Gamma_n(n) * x ^ (n - 1) / factorial(2 * n) for n in range(1, 60))
check("NEG g' series without the factor n is disjoint from the quadrature", disjoint(badg, dGamma_quad(x.sqrt()) / (2 * x.sqrt())))

# 8. Root enclosure.
a, b = bisect_root(lambda t: t ^ 3 - 2, 1, 2, QQ(2) ^ -200)
check("KAT bisect_root(t^3 - 2) encloses 2^(1/3)", a ^ 3 < 2 and b ^ 3 > 2 and RB(a) <= RB(2) ^ (QQ(1) / 3) <= RB(b),
      "width 2^-200")
try:
    bisect_root(lambda t: t ^ 2 + 1, 0, 1, QQ(1) / 1000)
    check("NEG bisect_root refuses an interval without sign change", False)
except ValueError:
    check("NEG bisect_root refuses an interval without sign change", True)

# 9. Symbolic identity checks (Sage simplify_full), used in c2, c3, c5.
Ts = var("Ts")
assume(Ts > 0)
check("KAT symbolic: (sqrt T + 1)^2 - (T + 2 sqrt T + 1) simplifies to 0",
      bool(((sqrt(Ts) + 1) ^ 2 - (Ts + 2 * sqrt(Ts) + 1)).simplify_full() == 0))
check("NEG symbolic: (sqrt T + 1)^2 - (T + 1) does not simplify to 0",
      not bool(((sqrt(Ts) + 1) ^ 2 - (Ts + 1)).simplify_full() == 0))
forget()

finish()
