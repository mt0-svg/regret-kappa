# c2_lemma52.sage: Lemma 3.10 of the paper, item (2) of Computation 3.13 (Lemma 5.2 or Lemma A in the outputs).
#   J_0..J_4 (closed forms and quadrature), a_0..a_4, concavity of f on [0, oo), the
#   positive root of the cubic f', max f, (2/3) max f < 3; the positive root of f
#   (Remark 8.1); the elementary inequalities of the proof; spot checks of the lemma.
load("lib.sage")

say("c2_lemma52: Lemma 5.2, %d-bit balls" % PREC)

L0 = 3 * RB(3).log() / 2
say("L_0 = (3/2) log 3 =", iv(L0, 30))


def J_closed(n):
    """J_n = int_1^oo u^{2n-3} e^{-u^2/2} du: J_0 = (e^{-1/2} - J_1)/2, J_n = K_{n-1} (n >= 1)."""
    if n == 0:
        return (EM - E1H / 2) / 2
    return K_closed(n - 1)


def J_quad(n):
    k = 2 * n - 3
    return int_1_inf(lambda z, an: z ^ k * (-z * z / 2).exp(), 1, max(k, 0), 0, 1)


say("")
say("J_n = int_1^oo u^{2n-3} e^{-u^2/2} du")
J = {}
for n in range(5):
    J[n] = J_closed(n)
    Jq = J_quad(n)
    say("  J_%d closed %s" % (n, iv(J[n], 30)))
    say("      quad   %s" % iv(Jq, 30))
    check("J_%d closed form = quadrature" % n, J[n].overlaps(Jq) and Jq.rad() < 10 ^ -50)
check("J_1 = E_1(1/2)/2, J_2 = e^{-1/2}, J_3 = 3 e^{-1/2}, J_4 = 13 e^{-1/2}",
      J[1].overlaps(E1H / 2) and J[2].overlaps(EM) and J[3].overlaps(3 * EM) and J[4].overlaps(13 * EM))

a = {}
a[0] = 2 * (-RB(1) / 6).exp() * (1 + L0 / 2) - 4 * J[0]
a[1] = 2 * EM * (QQ(1) / 2 + L0) - 4 * J[1]
for n in (2, 3, 4):
    a[n] = 3 * EM - 4 * J[n]
say("")
for n in range(5):
    say("a_%d = %s" % (n, iv(a[n], 30)))
check("a_2 = -e^{-1/2}, a_3 = -9 e^{-1/2}, a_4 = -49 e^{-1/2}",
      a[2].overlaps(-EM) and a[3].overlaps(-9 * EM) and a[4].overlaps(-49 * EM))
check("a_0 > 0", a[0] > 0)
check("a_1 > 0, so f'(0) = a_1/2 > 0", a[1] > 0)
check("a_2, a_3, a_4 < 0, so every coefficient of f'' is negative and f'' < 0 on [0, oo)",
      a[2] < 0 and a[3] < 0 and a[4] < 0)


def f(x):
    return sum(a[n] * x ^ n / factorial(2 * n) for n in range(5))


def fp(x):
    return sum(n * a[n] * x ^ (n - 1) / factorial(2 * n) for n in range(1, 5))


def fpp(x):
    return sum(n * (n - 1) * a[n] * x ^ (n - 2) / factorial(2 * n) for n in range(2, 5))


say("f''(0) = 2 a_2/4! =", iv(fpp(RB(0)), 20), "; coefficients of f'' (x^0, x^1, x^2):",
    ", ".join(iv(n * (n - 1) * a[n] / factorial(2 * n), 12) for n in range(2, 5)))
check("f''(0) < 0", fpp(RB(0)) < 0)

# Positive root of the cubic f'. f' is strictly decreasing on [0, oo) (f'' < 0), f'(0) > 0,
# so a certified sign change on [0, 8] gives the unique positive root.
check("f'(8) < 0", fp(RB(8)) < 0, iv(fp(RB(8)), 10))
xl, xh = bisect_root(fp, 0, 8, QQ(2) ^ -220)
xs = RB(xl).union(RB(xh))
say("")
say("positive root x* of f' in", iv(xs, 40))
fmax = f(xs)
say("max_{x>=0} f = f(x*) in", iv(fmax, 40))
check("f(x*) enclosure radius < 1e-60", fmax.rad() < 10 ^ -60)
check("f(x*) >= f(lo), f(hi) (consistency of the maximum)", fmax.upper() >= f(RB(xl)).lower() and fmax.upper() >= f(RB(xh)).lower())
B = 2 * fmax / 3
say("(2/3) max f in", iv(B, 40))
check("max f > 0 (so s f(rho^2) <= (2/3) max f for s <= 2/3)", fmax > 0)
check("max f <= 4.3286 (section 9, item 1)", fmax <= QQ(43286) / 10000, up(fmax, 15))
check("(2/3) max f <= 2.8857 (Lemma 5.2 as stated)", B <= QQ(28857) / 10000, up(B, 15))
check("(2/3) max f < 3 (Lemma 5.2 against beta = 3)", B < 3, "margin 3 - (2/3) max f >= %s" % lo(3 - B, 10))
check("NEG (2/3) max f < 2.8856 is refuted", B > QQ(28856) / 10000)
check("x* in [3.968, 3.969]", RB(xl) > QQ(3968) / 1000 and RB(xh) < QQ(3969) / 1000)

# Remark 8.1: the positive root of f.
check("f(20) < 0", f(RB(20)) < 0)
yl, yh = bisect_root(f, xh, 20, QQ(2) ^ -220)
x0 = RB(yl).union(RB(yh))
say("")
say("positive root x_0 of f (Remark 8.1) in", iv(x0, 30))
say("sqrt(x_0) in", iv(x0.sqrt(), 30))
check("f has exactly one root on (x*, oo) and none on [0, x*] (f increasing from a_0 > 0 then strictly decreasing)",
      a[0] > 0 and fmax > 0)
check("sqrt(x_0) <= 2.8190 (Remark 8.1)", x0.sqrt() <= QQ(28190) / 10000, up(x0.sqrt(), 12))

# ---------------------------------------------------------------------------
say("")
say("Elementary inequalities of the proof")
s, x, c, u, L, rr = var("s x c u L rr")

# (E1) chord bound -log(1-s) <= L_0 s on [0, 2/3].
h = L0 * RB(2) / 3 + (RB(1) / 3).log()
say("(E1) -log(1-s) <= L_0 s on [0, 2/3]: method = analytic (h(s) = L_0 s + log(1-s) is concave,")
say("     h(0) = 0, h(2/3) = log 3 - log 3 = 0, so h >= 0 between); checks below")
check("(E1) h(2/3) = 0 (ball contains 0, |h(2/3)| < 1e-70)", h.contains_exact(0) and small(h, QQ(10) ^ -70))
hs = diff(rr * s + log(1 - s), s, 2)
check("(E1) h''(s) = -1/(1-s)^2 (Sage symbolic)", bool((hs + 1 / (1 - s) ^ 2).simplify_full() == 0), str(hs))
check("(E1) h(j/1500) > 0 at the 999 points j = 1..999 of (0, 2/3) (certified point values)",
      all(L0 * QQ(j) / 1500 + (1 - RB(QQ(j) / 1500)).log() > 0 for j in range(1, 1000)))
check("(E1) chord slope: (log 3)/(2/3) = L_0", (RB(3).log() / (RB(2) / 3)).overlaps(L0))

# (E2) Bernoulli 1 - (1-s)^m <= m s on [0, 1], m >= 1.
say("(E2) 1 - (1-s)^m <= m s: method = analytic (Bernoulli: d/ds[(1-s)^m - 1 + m s] = m(1 - (1-s)^{m-1}) >= 0,")
say("     value 0 at s = 0); exact rational check below")
check("(E2) exact check at s = k/100, k = 0..100, m = 1..60",
      all(1 - (1 - QQ(k) / 100) ^ m <= m * QQ(k) / 100 for k in range(101) for m in range(1, 61)))
mm = var("mm")
dB = diff((1 - s) ^ mm - 1 + mm * s, s)
check("(E2) derivative = m(1 - (1-s)^{m-1}) (Sage symbolic)", bool((dB - mm * (1 - (1 - s) ^ (mm - 1))).simplify_full() == 0), str(dB))

# (E3) the integrals behind the bounds on P_0, P_1, P_n (symbolic, 0 < c < 1).
assume(c > 0)
assume(c < 1)
I_a = integrate(1 / u, u, c, 1)
I_b = integrate(2 * c ^ 2 / u ^ 3, u, c, 1)
I_c = integrate(u, u, c, 1)
I_d = integrate(2 * c ^ 2 / u, u, c, 1)
check("(E3) int_c^1 du/u = log(1/c)", bool((I_a - log(1 / c)).simplify_full() == 0), str(I_a))
check("(E3) int_c^1 2c^2/u^3 du = 1 - c^2", bool((I_b - (1 - c ^ 2)).simplify_full() == 0), str(I_b))
check("(E3) int_c^1 u du = (1 - c^2)/2", bool((I_c - (1 - c ^ 2) / 2).simplify_full() == 0), str(I_c))
check("(E3) int_c^1 2c^2/u du = 2 c^2 log(1/c)", bool((I_d - 2 * c ^ 2 * log(1 / c)).simplify_full() == 0), str(I_d))
ok = True
for n in range(2, 9):
    i1 = integrate(u ^ (2 * n - 1), u, c, 1)
    i2 = integrate(2 * c ^ 2 * u ^ (2 * n - 3), u, c, 1)
    ok = ok and bool((i1 - (1 - c ^ (2 * n)) / (2 * n)).simplify_full() == 0)
    ok = ok and bool((i2 - 2 * c ^ 2 * (1 - c ^ (2 * n - 2)) / (2 * n - 2)).simplify_full() == 0)
check("(E3) int_c^1 u^{2n-1} = (1-c^{2n})/(2n), int_c^1 2c^2 u^{2n-3} = 2c^2 (1-c^{2n-2})/(2n-2), n = 2..8", ok)
forget()
say("(E3) e^{-u^2/2} <= e^{-c^2/2} on [c, 1] and e^{-c^2/2} <= e^{-1/6} for c^2 >= 1/3: monotonicity of exp (analytic)")

# (E4) monotonicity in x on [0, 1] (n = 1 and n >= 2 bounds).
d1 = diff(exp(-x / 2) * (QQ(1) / 2 + L * x), x)
check("(E4) d/dx e^{-x/2}(1/2 + L x) = e^{-x/2}(L - 1/4 - L x/2) (Sage symbolic)",
      bool((d1 - exp(-x / 2) * (L - QQ(1) / 4 - L * x / 2)).simplify_full() == 0))
check("(E4) L_0 - 1/4 - L_0 x/2 > 0 at x = 0 and x = 1 (linear, so > 0 on [0, 1])",
      L0 - QQ(1) / 4 > 0 and L0 - QQ(1) / 4 - L0 / 2 > 0, "value at x = 1: %s" % iv(L0 / 2 - QQ(1) / 4, 12))
d2 = diff(exp(-x / 2) * (QQ(1) / 2 + x), x)
check("(E4) d/dx e^{-x/2}(1/2 + x) = e^{-x/2}(3/4 - x/2) (Sage symbolic)",
      bool((d2 - exp(-x / 2) * (QQ(3) / 4 - x / 2)).simplify_full() == 0))
check("(E4) 3/4 - x/2 > 0 at x = 0 and x = 1 (exact)", QQ(3) / 4 > 0 and QQ(3) / 4 - QQ(1) / 2 > 0)
check("(E4) values at x = 1: 2 e^{-1/2}(1/2 + L_0) and 2 e^{-1/2}(3/2) = 3 e^{-1/2}",
      (2 * EM * (QQ(1) / 2 + L0) - 4 * J[1]).overlaps(a[1]) and (2 * EM * QQ(3) / 2).overlaps(3 * EM))

# (E5) the terms n >= 5: 3 e^{-1/2} - 4 J_n <= 0.
say("(E5) 3 e^{-1/2} - 4 J_n <= 0 for n >= 5: method = analytic (J_n increasing in n as u >= 1, J_2 = e^{-1/2});")
check("(E5) 3 e^{-1/2} - 4 J_n < 0 for n = 2..60 (closed forms)", all(3 * EM - 4 * J_closed(n) < 0 for n in range(2, 61)))
check("(E5) J_n < J_{n+1} for n = 0..59 (closed forms)", all(J_closed(n) < J_closed(n + 1) for n in range(60)))

# (E6) spot checks of the bounds on P_n(s) by certified quadrature, s = 1 - c^2 for rational c.
say("")
say("(E6) spot checks: P_n(s) = 2 int_c^1 u^{2n} e^{-u^2/2}(1/u + 2c^2/u^3) du <= s B_n,")
say("     B_0 = 2e^{-1/6}(1 + L_0/2), B_1 = 2e^{-1/2}(1/2 + L_0), B_n = 3e^{-1/2} (n >= 2)")
Bn = lambda n: 2 * (-RB(1) / 6).exp() * (1 + L0 / 2) if n == 0 else (2 * EM * (QQ(1) / 2 + L0) if n == 1 else 3 * EM)
cs = [QQ(999) / 1000, QQ(99) / 100, QQ(9) / 10, QQ(4) / 5, QQ(7) / 10, QQ(3) / 5, QQ(29) / 50]
check("(E6) every c has c^2 >= 1/3 (so s = 1 - c^2 <= 2/3)", all(cc ^ 2 >= QQ(1) / 3 for cc in cs))
worst = None
okP = True
for cc in cs:
    ss = 1 - cc ^ 2
    c2 = CB(cc ^ 2)
    for n in range(7):
        Pn = 2 * quad(lambda z, an: z ^ (2 * n) * (-z * z / 2).exp() * (1 / z + 2 * c2 / z ^ 3), cc, 1)
        rat = Pn / (ss * Bn(n))
        okP = okP and (Pn < ss * Bn(n))
        if worst is None or rat.upper() > worst[0].upper():
            worst = (rat, n, cc)
    say("  c = %s, s = %s: P_n(s)/(s B_n) for n = 0..6: %s" % (cc, ss, ", ".join(
        up(2 * quad(lambda z, an: z ^ (2 * n) * (-z * z / 2).exp() * (1 / z + 2 * c2 / z ^ 3), cc, 1) / (ss * Bn(n)), 6)
        for n in range(7))))
check("(E6) P_n(s) < s B_n at the 49 points (n = 0..6, 7 values of c)", okP,
      "largest ratio %s at n = %d, c = %s" % (up(worst[0], 8), worst[1], worst[2]))

# (E7) spot checks of the lemma itself: hat Gamma(rho, s) - Gamma(rho) <= s f(rho^2) (direct quadratures).
say("")
say("(E7) spot checks: hat Gamma(rho, s) - Gamma(rho) <= s f(rho^2), both Gammas by direct quadrature")
okL = True
worst = None
rhos = [0, QQ(1) / 2, 1, QQ(3) / 2, 2, QQ(5) / 2, QQ(14) / 5, 3, QQ(7) / 2]
for rho in rhos:
    G = Gamma_quad(rho)
    row = []
    for cc in cs:
        ss = 1 - cc ^ 2
        Gh = Ghat_quad(rho, ss)
        lhs = Gh - G
        rhs = ss * f(RB(rho) ^ 2)
        okL = okL and (lhs < rhs)
        row.append("%s/%s" % (up(lhs, 5), up(rhs, 5)))
        gap = rhs - lhs
        if worst is None or gap.lower() < worst[0].lower():
            worst = (gap, rho, ss)
    say("  rho = %s: (lhs/rhs) over c = %s: %s" % (rho, ",".join(str(cc) for cc in cs), " ".join(row)))
check("(E7) hat Gamma - Gamma < s f(rho^2) at the 63 points", okL,
      "smallest gap %s at rho = %s, s = %s" % (lo(worst[0], 8), worst[1], worst[2]))

# Remark of section 6 (evidence): the same proof with s_0 = 0.6 in place of 2/3.
say("")
say("Remark (section 6, evidence): Lemma 5.2's bound with the split s_0 = 3/5 instead of 2/3,")
say("  L = -log(1 - s_0)/s_0, a_0 = 2 e^{-(1-s_0)/2}(1 + L/2) - 4 J_0, a_1 = 2 e^{-1/2}(1/2 + L) - 4 J_1, a_n as above")
s0 = QQ(3) / 5
Ls = -(1 - RB(s0)).log() / s0
a6 = dict(a)
a6[0] = 2 * (-(1 - RB(s0)) / 2).exp() * (1 + Ls / 2) - 4 * J[0]
a6[1] = 2 * EM * (QQ(1) / 2 + Ls) - 4 * J[1]
check("(remark) L - 1/4 - L/2 > 0 (monotonicity step still valid)", Ls / 2 - QQ(1) / 4 > 0)
fp6 = lambda t: sum(n * a6[n] * t ^ (n - 1) / factorial(2 * n) for n in range(1, 5))
f6 = lambda t: sum(a6[n] * t ^ n / factorial(2 * n) for n in range(5))
zl, zh = bisect_root(fp6, 0, 8, QQ(2) ^ -200)
m6 = f6(RB(zl).union(RB(zh)))
say("  s_0 = 3/5: argmax", iv(RB(zl).union(RB(zh)), 12), " max f =", iv(m6, 15), " s_0 max f =", iv(s0 * m6, 15))

finish()
