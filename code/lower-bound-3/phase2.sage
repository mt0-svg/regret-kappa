# Section 4.4 of the paper: the prior (Lemma 4.10, 4.2 in the outputs) by exact integration, c_1, the
# Fisher information of one observation, and Lemma 4.3: vT(rho, k) >= Phi_1(rho, k) at points
# of its validity range k >= pi^2 e^2 r^2 with every step of the closed form (iv) checked, and
# (sanity) the Bayes learner's exact expected bracket >= vT for small k.
# Run from this directory: sage phase2.sage

load("common.sage")
load("lb_lib.sage")
import time

C = Checker("phase2")
t_start = time.time()
var('z A u th x')
assume(A > 0)

print("== Lemma 4.2 by exact integration (Maxima), A symbolic and A = 2")
fA = cos(pi * z / (2 * A)) ** 2 / A
dfA = diff(fA, z)
C.check("integral of f_A over [-A, A] = 1", bool(integrate(fA, z, -A, A).simplify_full() == 1))
C.check("f_A(A) = f_A(-A) = 0", bool(fA.subs(z=A).simplify_full() == 0 and fA.subs(z=-A).simplify_full() == 0))
C.check("f_A'(A) = f_A'(-A) = 0 (C^1 at the ends)",
        bool(dfA.subs(z=A).simplify_full() == 0 and dfA.subs(z=-A).simplify_full() == 0))
C.check("f_A' = -(pi/(2 A^2)) sin(pi z/A)", bool((dfA + pi / (2 * A ** 2) * sin(pi * z / A)).trig_reduce().simplify_full() == 0))
C.check("f_A'^2 = (pi^2/A^3) sin^2(pi z/(2A)) f_A (so f_A'^2/f_A = (pi^2/A^3) sin^2)",
        bool((dfA ** 2 - pi ** 2 / A ** 3 * sin(pi * z / (2 * A)) ** 2 * fA).simplify_full() == 0))
Jsym = integrate(pi ** 2 / A ** 3 * sin(pi * z / (2 * A)) ** 2, z, -A, A).simplify_full()
C.check("J(f_A) = pi^2/A^2", bool((Jsym - pi ** 2 / A ** 2).simplify_full() == 0), str(Jsym))
EZ2sym = integrate(z ** 2 * fA, z, -A, A).simplify_full()
C.check("integral of z^2 f_A = A^2 (1/3 - 2/pi^2)", bool((EZ2sym - A ** 2 * (QQ(1) / 3 - 2 / pi ** 2)).simplify_full() == 0),
        str(EZ2sym))
C.check("integral over [-1, 1] of u^2 cos(pi u) = -4/pi^2",
        bool((integrate(u ** 2 * cos(pi * u), u, -1, 1) + 4 / pi ** 2).simplify_full() == 0))
J2 = Jsym.subs(A=2)
EZ22 = EZ2sym.subs(A=2)
C.check("A = 2: J = pi^2/4 and E Z^2 = 4/3 - 8/pi^2",
        bool((J2 - pi ** 2 / 4).simplify_full() == 0 and (EZ22 - QQ(4) / 3 + 8 / pi ** 2).simplify_full() == 0))
# change of variables theta = c + z/sqrt(v): Fisher information v J
var('c v')
assume(v > 0)
ft = sqrt(v) * fA.subs(z=sqrt(v) * (th - c))
Jt = integrate((diff(ft, th) ** 2 / ft).simplify_full(), th, c - A / sqrt(v), c + A / sqrt(v)).simplify_full()
C.check("the law of c + Z/sqrt(v) has Fisher information v J(f_A)",
        bool((Jt - v * pi ** 2 / A ** 2).simplify_full() == 0), str(Jt))
forget(v > 0)

print("== Lemma 4.2 cross-checked by Arb rigorous integration (A = 2)")
CB = ComplexBallField(PREC)
f2 = lambda t, _: (CB.pi() * t / 4).cos() ** 2 / 2
I0 = CB.integral(f2, 0, 2) * 2
I2 = CB.integral(lambda t, _: t ** 2 * f2(t, _), 0, 2) * 2
C.check("Arb: integral of f_2 = 1", I0.real().overlaps(R(1)) and I0.real().rad() < 1e-40)
C.check("Arb: E Z^2 = 4/3 - 8/pi^2", I2.real().overlaps(EZ2_prior()) and I2.real().rad() < 1e-40,
        "%s" % I2.real().mid().n(digits=12))
dlt = QQ(1) / 10 ** 6
fd = lambda t, _: (CB.pi() / 8 * (CB.pi() * t / 2).sin()) ** 2 / ((CB.pi() * t / 4).cos() ** 2 / 2)
IJ = CB.integral(fd, 0, 2 - dlt) * 2   # f'^2/f <= pi^2/8 on the remaining [2 - dlt, 2]
Jlo = R(IJ.real().lower())
Jhi = R(IJ.real().upper()) + 2 * dlt * PI ** 2 / 8
C.check("Arb: integral of f'^2/f lies in [I, I + 2.5e-6] and contains pi^2/4",
        Jlo <= J_prior() and J_prior() <= Jhi, "[%.9f, %.9f]" % (Jlo.mid(), Jhi.mid()))

print("== the prior moments used by the Bayes sanity check")
M = prior_moments(16)
ok = True
for m in range(0, 9):
    sym = integrate(z ** m * cos(pi * z / 4) ** 2 / 2, z, -2, 2)
    ok = ok and M[m].overlaps(R(sym.n(prec=400)))
C.check("moment recursion M_0..M_8 agrees with exact integration", ok)
C.check("M_0 = 1, M_odd = 0, M_2 = E Z^2", M[0].overlaps(R(1)) and all(M[m].overlaps(R(0)) for m in range(1, 17, 2))
        and M[2].overlaps(EZ2_prior()))

print("== c_1")
J = J_prior()
EZ2 = EZ2_prior()
c1 = c1_of(J, EZ2)
print("J = %s\nE Z^2 = %s\nc_1 = %s" % (J.mid().n(digits=15), EZ2.mid().n(digits=15), c1.mid().n(digits=15)))
C.check("c_1 rounds to 3.318633 (note: 3.318633)", abs(c1 - R(C1_STATED)) < R(QQ(5) / 10 ** 7), "%.9f" % c1.mid())
C.check("c_1 <= 3.318633 (the 6-decimal value is an upper rounding)", c1 <= R(C1_STATED))
const_iv = (R(A_PRIOR) ** 2 / (4 * PI ** 2)).log() - 1 - EZ2 + R(1) / 2 - (J - 2) / (PI ** 2 * E1 ** 2)
C.check("constant of step (iv) at A = 2 equals -c_1", const_iv.overlaps(-c1))
C.check("J E Z^2 = pi^2/3 - 2 >= 1 (zero-data van Trees: Var Z >= 1/J)",
        (J * EZ2).overlaps(PI ** 2 / 3 - 2) and J * EZ2 >= 1, "%.6f" % (J * EZ2).mid())
C.check("J >= 2 (used in (1 + X)/(J + 2X) = 1/2 - (J/2 - 1)/(J + 2X))", J >= 2)

print("== Fisher information of one observation y = +-1, P(y = +-1) = (1 +- th x)/2")
p1 = (1 + th * x) / 2
p2 = (1 - th * x) / 2
Ione = (diff(p1, th) ** 2 / p1 + diff(p2, th) ** 2 / p2).simplify_full()
C.check("I(theta) = x^2/(1 - theta^2 x^2)", bool((Ione - x ** 2 / (1 - th ** 2 * x ** 2)).simplify_full() == 0), str(Ione))

print("== vT, known-answer test at k = 2 (closed form by hand)")
rho0 = QQ(4)
r = R(rho0) + 2
e1, e2 = R(1) / (4 * r ** 2), R(1) / (2 * r ** 2)
n1, n2 = R(1) / 4, R(1) / 2
w1 = J + e1 / (1 - n1)
w2 = w1 + e2 / (1 - n2)
vT2 = e1 / J + e2 / w1 - EZ2 + (1 + e1 + e2) / w2
C.check("vT(4, 2) agrees with the closed form", vT_detail(rho0, 2)["vT"].overlaps(vT2), "%.12f" % vT2.mid())

print("== Bayes learner, known-answer test at k = 2 (posterior by Arb integration)")
rho1 = QQ(3)
BV, Q = bayes_value(rho1, 2, M)
r1 = R(rho1) + 2
eps1 = (R(1) / 4).sqrt() / r1
q_direct = R(0)
for y in (1, -1):
    lik = lambda t, _, y=y: (1 + y * (CB(rho1) + t) * CB(eps1)) / 2 * f2(t, _)
    n0 = CB.integral(lik, -2, 2).real()
    n1_ = CB.integral(lambda t, _: t * lik(t, _), -2, 2).real()
    q_direct += n1_ ** 2 / n0
C.check("posterior sum Q_1 at rho = 3, k = 2: moments = direct integration", Q[1].overlaps(q_direct),
        "%.12f" % q_direct.mid())
C.check("Q_1 = (E Z^2 eps_1)^2/(1 - rho^2 eps_1^2) (closed form for one observation)",
        Q[1].overlaps((EZ2 * eps1) ** 2 / (1 - R(rho1) ** 2 * eps1 ** 2)))

print("== Lemma 4.3, first claim (sanity): Bayes learner's expected bracket >= vT, k = 2..12")
t0 = time.time()
gaps = []
for rho in [QQ(0), QQ(1), QQ(5) / 2, QQ(385) / 100, QQ(6)]:
    row = []
    for k in range(2, 13):
        bv, _ = bayes_value(rho, k, M)
        vt = vT_detail(rho, k, steps=False)["vT"]
        gaps.append((bv - vt, rho, k))
        row.append("%.4f" % (bv - vt).mid())
    print("  rho = %-6s Bayes - vT for k = 2..12: %s" % (rho, " ".join(row)))
gmin = min(gaps, key=lambda g: g[0].lower())
print("least Bayes - vT = %.6f at rho = %s, k = %d (time %.1f s)" % (gmin[0].mid(), gmin[1], gmin[2], time.time() - t0))
C.check("Bayes value >= vT at all 55 points", all(g[0] > 0 for g in gaps), "%.6f" % gmin[0].lower())

print("== Lemma 4.3, closed form: vT >= Phi_1 for k >= pi^2 e^2 r^2, with the steps of (iv)")
print("   S = sum eps_i^2/w_{i-1}, (s1) S >= l_k/2 + (1/(2k)) sum_{i<k} l_i, (s2) l_i >= log(1 + beta i^2),")
print("   (s3) S >= Lambda - 1 - log(k)/(2k) - 1/k, (s4) (1+X)/w_k >= 1/2 - (J-2)/(pi^2 e^2),")
print("   (s5) X = (k+1)/(4 r^2), (s6) w_k <= J + 2X, (s7) Lambda <= log k")
comp_lb = R(1) / 2 - (J - 2) / (PI ** 2 * E1 ** 2)


def check_point(rho, k):
    d = vT_detail(rho, k)
    r = d["r"]
    lk, S, X, wk, Lam = d["lk"], d["S"], d["X"], d["wk"], d["Lam"]
    s1 = S >= lk / 2 + d["sum_l"] / (2 * k)
    s2 = d["min_gap"] >= 0
    s3 = S >= Lam - 1 - R(k).log() / (2 * k) - R(1) / k
    s4 = (1 + X) / wk >= comp_lb
    s5 = X.overlaps(R(k + 1) / (4 * r ** 2))
    s6 = wk <= J + 2 * X
    s7 = Lam <= R(k).log()
    ph = Phi1(rho, k, c1)
    fin = d["vT"] >= ph
    marg = d["vT"] - ph
    ok = s1 and s2 and s3 and s4 and s5 and s6 and s7 and fin
    print("  rho = %-6s k = %8d  vT = %10.6f  Phi_1 = %10.6f  vT - Phi_1 = %.6f  steps %s" %
          (rho, k, d["vT"].mid(), ph.mid(), marg.mid(),
           "".join("1" if t else "0" for t in (s1, s2, s3, s4, s5, s6, s7))))
    sys.stdout.flush()
    return ok, marg


t0 = time.time()
results = []
for rho in [QQ(0), QQ(2), QQ(381) / 100, QQ(39) / 10, QQ(9) / 2, QQ(6), QQ(10)]:
    km = k_min(rho)
    for k in sorted(set([km, km + 1, 2 * km, 10 * km, 177857, 10 ** 6])):
        if k >= km:
            results.append(check_point(rho, k) + (rho, k))
results.append(check_point(QQ(385) / 100, 5 * 10 ** 6) + (QQ(385) / 100, 5 * 10 ** 6))
print("time %.1f s" % (time.time() - t0))
print("   boundary scan: rho = 3.81 + i/10, i = 0..40, at k = k_min(rho)")
t0 = time.time()
for i in range(41):
    rho = QQ(381) / 100 + QQ(i) / 10
    results.append(check_point(rho, k_min(rho)) + (rho, k_min(rho)))
print("time %.1f s" % (time.time() - t0))
worst = min(results, key=lambda t: t[1].lower())
print("least vT - Phi_1 = %.6f at rho = %s, k = %d, over %d points" % (worst[1].mid(), worst[2], worst[3], len(results)))
C.check("vT >= Phi_1 and steps (s1) to (s7) at all %d points" % len(results), all(t[0] for t in results),
        "%.6f" % worst[1].lower())
C.check("k_min(3.81) = 2462 = ceil(pi^2 e^2 5.81^2)", k_min(QQ(381) / 100) == 2462, str(k_min(QQ(381) / 100)))
print("time %.1f s" % (time.time() - t_start))
C.finish(27)
