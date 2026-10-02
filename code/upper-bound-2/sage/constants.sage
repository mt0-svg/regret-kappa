# Rigorous enclosures (Arb balls, Sage RealBallField) of every load-bearing
# constant of Section 3 of the paper (Computation 3.13), written from the statements only.
# A line "CHECK <name>: OK" means the inequality holds for the whole ball
# (Arb comparisons are true only when certain).
# Run: sage sage/constants.sage > out/constants.txt

R = RealBallField(300)
C = ComplexBallField(300)
FAILS = []


def show(name, b):
    print("%s = %s" % (name, b))


def check(name, cond):
    print("CHECK %s: %s" % (name, "OK" if cond else "FAIL"))
    if not cond:
        FAILS.append(name)


def tail_gauss(M, k):
    # rigorous bound on int_M^oo th^k e^{-th^2/2} dth for M > 0, M^2 > max(k,0):
    # d/dth log(th^k e^{-th^2/2}) = k/th - th <= -(M - max(k,0)/M) =: -a on [M, oo)
    a = M - max(k, 0) / M
    assert a > 0
    return R(M) ** k * (-R(M) ** 2 / 2).exp() / a


def integral_1_oo(f, ks, M=40):
    # int_1^oo f(th) dth with f(th) = sum_j coef_j th^{k_j} e^{-th^2/2} (coef_j >= 0),
    # computed as a rigorous quadrature on [1, M] plus the bound of tail_gauss
    val = C.integral(lambda t, _: f(t), 1, M).real()
    tail = sum(cf * tail_gauss(M, k) for (cf, k) in ks)
    return val + R(0).add_error(tail.upper())


print("== 1. e^{-1/2} and E_1(1/2), three ways")
e12 = R(-1 / 2).exp()
show("e^{-1/2}", e12)
E1_inc = R(0).gamma_inc(R(1 / 2))
E1_ei = -R(-1 / 2).Ei()
x = R(1 / 2)
N = 80
ser = sum((-x) ** k / (k * factorial(k)) for k in range(1, N + 1))
tail = x ** (N + 1) / ((N + 1) * factorial(N + 1))
E1_ser = -R.euler_constant() - x.log() - ser
E1_ser = E1_ser + R(0).add_error(tail.upper())
show("E_1(1/2) gamma_inc", E1_inc)
show("E_1(1/2) -Ei(-1/2)", E1_ei)
show("E_1(1/2) series", E1_ser)
check("E1 three ways overlap", E1_inc.overlaps(E1_ei) and E1_inc.overlaps(E1_ser))
E1 = E1_inc

print("== 2. K_m, Gamma_n closed forms (Lemma 2.1 (c)) against quadrature and gamma_inc")


def K_closed(m):
    if m == 0:
        return E1 / 2
    return R(2) ** (m - 1) * factorial(m - 1) * e12 * sum(R(1 / 2) ** j / factorial(j) for j in range(m))


def Gam_closed(n):
    if n == 0:
        return 2 * e12
    return 2 * (K_closed(n) + 2 * K_closed(n - 1))


for m in range(0, 7):
    kc = K_closed(m)
    kq = integral_1_oo(lambda t, m=m: t ** (2 * m - 1) * (-t * t / 2).exp(), [(1, 2 * m - 1)])
    ki = R(2) ** (m - 1) * R(m).gamma_inc(R(1 / 2)) if m >= 1 else E1_ei / 2
    show("K_%d closed" % m, kc)
    check("K_%d closed = quadrature = 2^(m-1) Gamma(m,1/2)" % m, kc.overlaps(kq) and kc.overlaps(ki))

for n in range(0, 7):
    gc = Gam_closed(n)
    gq = 2 * integral_1_oo(
        lambda t, n=n: (t ** (2 * n - 1) + 2 * t ** (2 * n - 3)) * (-t * t / 2).exp(),
        [(1, 2 * n - 1), (2, 2 * n - 3)],
    )
    show("Gamma_%d" % n, gc)
    print("   Gamma_%d / e^{-1/2} = %s" % (n, gc / e12))
    check("Gamma_%d closed = quadrature" % n, gc.overlaps(gq))
check("Gamma_2 = 10 e^-1/2", (Gam_closed(2) - 10 * e12).contains_zero())
check("Gamma_3 = 38 e^-1/2", (Gam_closed(3) - 38 * e12).contains_zero())
check("Gamma_4 = 210 e^-1/2", (Gam_closed(4) - 210 * e12).contains_zero())
check("Gamma_1 = 2e^-1/2 + 2E1", (Gam_closed(1) - 2 * e12 - 2 * E1).contains_zero())

print("== 2b. Lemma 2.1 (d): Gamma_n <= 2^{n+1}(n-1)! and n Gamma_n/(2n)! <= 2/n!, n = 1..200")
ok = True
for n in range(1, 201):
    g = Gam_closed(n)
    ok = ok and (g <= R(2) ** (n + 1) * factorial(n - 1)) and (n * g / factorial(2 * n) <= R(2) / factorial(n))
check("Lemma 2.1 (d) for n <= 200", ok)

GAM = [Gam_closed(n) for n in range(0, 400)]


def Gamma_series(r, Nt=120):
    # Gamma(r) = sum_n Gamma_n r^{2n}/(2n)!, rigorous tail: Gamma_n/(2n)! <= 2/(n n!) <= 2/n!,
    # sum_{n>Nt} 2 X^n/n! <= 2 X^{Nt+1}/(Nt+1)! / (1 - X/(Nt+2)) with X = r^2 < Nt+2
    X = R(r) ** 2
    s = sum(GAM[n] * X ** n / factorial(2 * n) for n in range(0, Nt + 1))
    assert X.upper() < Nt + 2
    t = 2 * X ** (Nt + 1) / factorial(Nt + 1) / (1 - X / (Nt + 2))
    return s + R(0).add_error(t.upper())


def Gamma_quad(r, M=60):
    r = R(r)
    val = C.integral(
        lambda t, _: ((t * r + (-t * t / 2)).exp() + (-t * r - t * t / 2).exp()) * (1 / t + 2 / t ** 3),
        1,
        M,
    ).real()
    # tail: for th >= M >= 2|r|+2, both exponentials <= e^{th|r| - th^2/2} <= e^{-th^2/4} ... use
    # e^{th|r|-th^2/2} <= e^{r^2/2} e^{-(th-|r|)^2/2}, and 1/th + 2/th^3 <= 1
    ra = abs(r)
    u = R(M) - ra
    tail = 2 * (ra ** 2 / 2).exp() * (-(u ** 2) / 2).exp() / u
    return val + R(0).add_error(tail.upper())


print("== 3. Gamma(0), Gamma(1), and the series against quadrature")
G0 = Gamma_series(0)
G1 = Gamma_series(1)
show("Gamma(0)", G0)
show("Gamma(1)", G1)
show("Gamma(1) - Gamma(0)", G1 - G0)
for r in [R(1 / 2), R(1), R(17 / 10), R(5 / 2), R(4), R(6)]:
    gs = Gamma_series(r)
    gq = Gamma_quad(r)
    print("   r = %s: series %s, quadrature %s" % (r.mid().n(20), gs, gq))
    check("Gamma(%s) series = quadrature" % r.mid().n(10), gs.overlaps(gq))

print("== 4. Lemma 5.2: J_n, a_n, f, max f")
L0 = R(3) / 2 * R(3).log()
J = {}
J[1] = E1 / 2
J[0] = (e12 - J[1]) / 2
for n in range(2, 7):
    J[n] = K_closed(n - 1)
for n in range(0, 7):
    jq = integral_1_oo(lambda t, n=n: t ** (2 * n - 3) * (-t * t / 2).exp(), [(1, 2 * n - 3)])
    show("J_%d" % n, J[n])
    check("J_%d closed = quadrature" % n, J[n].overlaps(jq))
check("J_n increasing n=2..6 and J_2 = e^-1/2", all(J[n] < J[n + 1] for n in range(2, 6)) and (J[2] - e12).contains_zero())
a = {}
a[0] = 2 * R(-1 / 6).exp() * (1 + L0 / 2) - 4 * J[0]
a[1] = 2 * e12 * (R(1) / 2 + L0) - 4 * J[1]
for n in range(2, 5):
    a[n] = 3 * e12 - 4 * J[n]
for n in range(0, 5):
    show("a_%d" % n, a[n])
for n, k in [(2, -1), (3, -9), (4, -49)]:
    check("a_%d = %d e^-1/2" % (n, k), (a[n] - k * e12).contains_zero())
check("a_2, a_3, a_4 < 0 (f concave on x >= 0)", a[2] < 0 and a[3] < 0 and a[4] < 0)
check("a_1 > 0 (f'(0) > 0)", a[1] > 0)
check("n=1 monotonicity: L0 - 1/4 - L0/2 > 0", L0 - R(1) / 4 - L0 / 2 > 0)
check("n=5..: 3e^-1/2 - 4 J_5 <= 0", 3 * e12 - 4 * J[5] <= 0)


def f(xb):
    return sum(a[n] * xb ** n / factorial(2 * n) for n in range(0, 5))


def fp(xb):
    return sum(a[n] * n * xb ** (n - 1) / factorial(2 * n) for n in range(1, 5))


lo, hi = RR(3), RR(5)
check("f'(3) > 0 > f'(5)", fp(R(lo)) > 0 and fp(R(hi)) < 0)
for _ in range(60):
    mid = (lo + hi) / 2
    if fp(R(mid)).mid() > 0:
        lo = mid
    else:
        hi = mid
lo = RR(lo) - RR(1e-12)
hi = RR(hi) + RR(1e-12)
check("root of f' certified in [lo, hi]", fp(R(lo)) > 0 and fp(R(hi)) < 0)
xs = R(lo).union(R(hi))
fmax = f(xs)
show("argmax f in", xs)
show("max f (enclosure)", fmax)
show("(2/3) max f", 2 * fmax / 3)
print("   upper bound of (2/3) max f: %s" % (2 * fmax / 3).upper())
check("max f <= 4.3286 (note, section 9)", fmax < R(43286) / 10000)
check("(2/3) max f <= 2.8857 (Lemma 5.2)", 2 * fmax / 3 < R(28857) / 10000)
check("(2/3) max f < 3", 2 * fmax / 3 < 3)
# positive root of f (Remark 8.1, not load-bearing)
lo2, hi2 = RR(7), RR(9)
check("f(7) > 0 > f(9)", f(R(lo2)) > 0 and f(R(hi2)) < 0)
for _ in range(60):
    mid = (lo2 + hi2) / 2
    if f(R(mid)).mid() > 0:
        lo2 = mid
    else:
        hi2 = mid
print("   positive root of f: x0 = %.9f, sqrt(x0) = %.9f" % (lo2, sqrt(lo2)))

print("== 5. Lemma 6.1: twenty pieces")


def gprime_trunc(xb, Nt=30):
    s = sum(n * GAM[n] * xb ** (n - 1) / factorial(2 * n) for n in range(1, Nt + 1))
    assert xb.upper() < Nt + 2
    t = 2 * xb ** Nt / factorial(Nt + 1) / (1 - xb / (Nt + 2))
    return s + t  # the note's bound (tail added as an upper bound, not an error ball)


def gprime_ball(xb, Nt=150):
    s = sum(n * GAM[n] * xb ** (n - 1) / factorial(2 * n) for n in range(1, Nt + 1))
    t = 2 * xb ** Nt / factorial(Nt + 1) / (1 - xb / (Nt + 2))
    return s + R(0).add_error(t.upper())


def pieces(s0, npieces, gp_fun):
    s0 = R(s0)
    c0 = (1 - s0).sqrt()
    sg0 = s0.sqrt()
    rs = (1 / s0 - 1).sqrt()
    rz = (1 + c0) / sg0

    def m(r):
        if r < rs or r == 0:
            return (1 + r * r).sqrt()
        if r > rs:
            return c0 * r + sg0
        raise ValueError("undecided branch")

    def q(r):
        return m(r) ** 2 - r ** 2

    out = []
    for i in range(1, npieces + 1):
        r0 = rz * (i - 1) / npieces
        r1 = rz * i / npieces
        b = q(r0) * gp_fun(m(r1) ** 2)
        out.append((r0, r1, q(r0), b))
    return rz, rs, out


rz, rs, P = pieces(R(2) / 3, 20, gprime_trunc)
show("rho_*", rs)
show("rho_z", rz)
check("rho_z = (1+sqrt3)/sqrt2", (rz - (1 + R(3).sqrt()) / R(2).sqrt()).contains_zero())
check("rho_z^2 = 2 + sqrt3 < 32", (rz ** 2 - 2 - R(3).sqrt()).contains_zero() and rz ** 2 < 32)
best = None
for (r0, r1, q0, b) in P:
    print("   piece [%.5f, %.5f]  q(left) = %.7f  bound = %.7f (upper %.10f)" % (r0.mid(), r1.mid(), q0.mid(), b.mid(), b.upper()))
    if best is None or b.upper() > best[3].upper():
        best = (r0, r1, q0, b)
print("   largest piece bound: %.10f on [%.5f, %.5f]" % (best[3].upper(), best[0].mid(), best[1].mid()))
check("all q(left) >= 0", all(q0 >= 0 for (_, _, q0, _) in P))
check("Lemma 6.1 bound <= 2.7053", all(b < R(27053) / 10000 for (_, _, _, b) in P))
check("Lemma 6.1 bound < 3", all(b < 3 for (_, _, _, b) in P))
# same pieces with g' summed to N = 150 (tail as error ball)
_, _, P150 = pieces(R(2) / 3, 20, gprime_ball)
print("   max piece with N = 150: %.10f" % max(b.upper() for (_, _, _, b) in P150))
# controls: the certificate is sensitive to the split s0
for s0, npc in [(R(1) / 2, 20), (R(1) / 2, 400), (R(6) / 10, 20), (R(6) / 10, 400), (R(2) / 3, 400)]:
    _, _, Pc = pieces(s0, npc, gprime_ball)
    print("   control s0 = %s, %d pieces: max piece bound %.6f" % (s0.mid().n(10), npc, max(b.upper() for (_, _, _, b) in Pc)))

print("== 6. Lemma 7.1")
phi1 = e12 / (2 * R.pi()).sqrt()
N1 = (1 + (1 / R(2).sqrt()).erf()) / 2
lc = 2 * phi1 / N1 + phi1 / N1 ** 2
show("phi(1)", phi1)
show("N(1)", N1)
show("2 phi(1)/N(1)", 2 * phi1 / N1)
show("phi(1)/N(1)^2", phi1 / N1 ** 2)
show("sum", lc)
check("Lemma 7.1 constant <= 0.9170 + 1e-4 and < 1", lc < R(9171) / 10000 and lc < 1)
check("e^2 = e^{rho^2/2} at |rho| = 2 (equality, so e^2 >= e^{rho^2/2} on |rho| <= 2)", (R(2).exp() - (R(2) ** 2 / 2).exp()).contains_zero())

print("== 7. Theorem U")
c3 = 2 * (3 / (2 * R.pi()).sqrt()).log()
show("2 log(3/sqrt(2 pi))", c3)
show("4 e^{-1/2}/3", 4 * e12 / 3)
show("2 sqrt(2 pi) e^2/3", 2 * (2 * R.pi()).sqrt() * R(2).exp() / 3)
check("4e^-1/2/3 <= 0.81 and 2 sqrt(2pi) e^2/3 <= 12.35", 4 * e12 / 3 <= R(81) / 100 and 2 * (2 * R.pi()).sqrt() * R(2).exp() / 3 <= R(1235) / 100)


def bound1(T):
    T = R(T)
    return 2 * (R(2).exp() + (T.sqrt() + 1) * (3 * T + 2 * e12) / (2 * R.pi()).sqrt()).log()


def bound2(T):
    T = R(T)
    return 3 * T.log() + c3 + 2 / T.sqrt() + R(81) / 100 / T + R(1235) / 100 / T ** (R(3) / 2)


for T in [1, 2, 3, 10, 100, 10 ** 4, 10 ** 6]:
    b1 = bound1(T)
    print("   T = %d: bound = %.6f, 3 log T + %.6f; second form %.6f" % (T, b1.mid(), (b1 - 3 * R(T).log()).mid(), bound2(T).mid()))
ok = all(bound1(T) <= bound2(T) for T in list(range(1, 2001)) + [10 ** k for k in range(4, 13)])
check("bound1 <= bound2 for T = 1..2000 and 10^4..10^12", ok)
print("== 8. Phi_0(rho) >= rho^2 (Lemma 7.1 consequence), checked on a grid for several T")
ok = True
for T in [1, 2, 3, 4, 5, 9, 16, 50, 100]:
    Cc = (R(T).sqrt() + 1) / (2 * R.pi()).sqrt()
    lam0 = R(2).exp() / Cc
    for j in range(0, 201):
        r = R(T).sqrt() * j / 200
        ok = ok and (Cc * (lam0 + Gamma_series(r, 300)) >= (r * r / 2).exp())
check("C(lambda0 + Gamma(rho)) >= e^{rho^2/2} on 201 points of [0, sqrt T], T <= 100", ok)

print("FAILS:", FAILS)
print("ALL CHECKS OK" if not FAILS else "SOME CHECKS FAILED")
