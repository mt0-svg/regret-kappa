# Lemma 3.1 (drift), independent check with Arb balls.
# (b) [0, 2.8): D > 0 on each cell from the definition of the drift, by bisection of ball
#     enclosures; the infimum of D on each closed cell enclosed by branch and bound.
# (a) [2.8, oo): the constants and the algebra of the analytic argument; plus a rigorous
#     ball cover of [2.8, 12] (redundant with (a), a cross-check).
# Run from this directory: sage drift_arb.sage

load("common.sage")
load("drift_lib.sage")
import time

C = Checker("drift_arb")
t_start = time.time()
K8 = R(K_G)

print("== known-answer tests of the ball arithmetic and of the drift evaluator")
C.check("Arb exp(1) within 1e-49 of 2.71828182845904523536028747135266249775724709369995",
        abs(R(1).exp() - R("2.71828182845904523536028747135266249775724709369995")) < R(10) ** -49)
C.check("Arb cosh(1) within 1e-36 of 1.5430806348152437784779056207570616826",
        abs(R(1).cosh() - R("1.5430806348152437784779056207570616826")) < R(10) ** -36)
# negative control of the known-answer test itself: a wrong digit must be detected
C.check("a wrong 30th digit of e is detected",
        not (abs(R(1).exp() - R("2.71828182845904523536028747136266249775724709369995")) < R(10) ** -49))
# rho = 0: D(0) = K (exp(s/2) - 1) - 1 exactly.
s0 = MOVES[0]
C.check("drift at rho = 0 equals K(exp(s/2) - 1) - 1",
        drift_direct(R(0), R(s0), K8).overlaps(K8 * ((R(s0) / 2).exp() - 1) - 1))
# The identity of Lemma 3.1 (average of g = K h_s(rho)) at random rational points.
set_random_seed(20261001)
ok = True
for i in range(200):
    rho = QQ(randint(0, 120000)) / 10000
    s = QQ(randint(1, 9999)) / 10000
    lhs = drift_direct(R(rho), R(s), K8)
    h = ((R(rho) ** 2 * (1 - R(s)) + R(s)) / 2).exp() * (R(rho) * (R(s) * (1 - R(s))).sqrt()).cosh()
    ok = ok and lhs.overlaps(K8 * h - K8 * (R(rho) ** 2 / 2).exp() - 1)
C.check("identity average = K h_s(rho) at 200 random points", ok)
ok = True
for i in range(200):
    rho = QQ(28) / 10 + QQ(randint(0, 92000)) / 10000
    sr = R(QQ(5) / 8) * (-(R(rho) ** 2) / 2).exp()
    ok = ok and drift_factored(R(rho), K8).overlaps(drift_direct(R(rho), sr, K8))
C.check("factored form = definition at 200 random points of [2.8, 12]", ok)
# Negative control of the evaluator: a tiny move cannot give drift 1 at rho = 1.7.
C.check("evaluator rejects s = 1/1000 at rho = 17/10 (D certainly < 0)",
        drift_direct(R(QQ(17) / 10), R(QQ(1) / 1000), K8) < 0)

print("== the move table: s_j = (5/8) exp(-m^2/2) at m = j/10 + 1/20, rounded to 4 decimals")
ok_round = True
for j, (d, r, v) in enumerate(table_rounding(S_DIGITS)):
    if r != d:
        ok_round = False
        print("  cell %d: table %d, rounding gives %d" % (j, d, r))
    print("  s_%-2d = %s = %d/10000, (5/8) exp(-m^2/2) = %s" % (j, MOVES[j], d, v.mid().n(digits=8)))
C.check("table equals the 4-decimal rounding of (5/8) exp(-m^2/2)", ok_round)
C.check("every s_j lies in (0, 1)", all(0 < s < 1 for s in MOVES))

print("== known-answer tests of the derivative D' used by the mean value form")
var('x')
sx = QQ(1352) / 10000
Dsym = 4 * (exp((x * sqrt(1 - sx) + sqrt(sx)) ** 2 / 2) + exp((x * sqrt(1 - sx) - sqrt(sx)) ** 2 / 2)) - 8 * exp(x ** 2 / 2) - 1
dDsym = diff(Dsym, x)
ok = True
for xv in [QQ(0), QQ(3) / 10, QQ(17) / 10, QQ(27) / 10]:
    ok = ok and drift_deriv(R(xv), R(sx), K8).overlaps(R(dDsym.subs(x=xv)))
C.check("D' equals the symbolic derivative at 4 points (s = 0.1352)", ok)
hh = QQ(1) / 10 ** 30
ok = True
for xv in [QQ(1) / 7, QQ(13) / 10, QQ(26) / 10]:
    fd = (drift_direct(R(xv + hh), R(sx), K8) - drift_direct(R(xv - hh), R(sx), K8)) / (2 * hh)
    ok = ok and abs(fd - drift_deriv(R(xv), R(sx), K8)) < R(10) ** -20
C.check("D' equals the central difference (h = 1e-30) at 3 points", ok)
C.check("negative control: D' without the factor sqrt(1-s) differs from the symbolic derivative",
        not drift_deriv(R(QQ(17) / 10), R(sx), K8).overlaps(
            R(dDsym.subs(x=QQ(17) / 10)) / R(1 - sx).sqrt()))

print("== (b) certification of D > 0 on [0, 2.8): mean value form, trisection")
t0 = time.time()
ok_m, per_m = certify_table_mvf(MOVES, K_G)
nl_m = sum(p[1] for p in per_m)
print("total subintervals %d, max trisection depth %d, least lower bound %.6g, time %.1f s" %
      (nl_m, max(p[2] for p in per_m), min(p[3] for p in per_m), time.time() - t0))
C.check("D > 0 on all 28 closed cells (mean value form, trisection)", ok_m, "%d subintervals" % nl_m)

print("== (b') the same with direct ball evaluation and bisection")
print("   (the ball of a monotone expression on [a, b] is its endpoint bracket, so this run")
print("   reproduces the bracket and the bisection tree of the rational certificate)")
t0 = time.time()
ok_b, per = certify_table(MOVES, K_G)
nleaves = sum(p[1] for p in per)
print("total subintervals %d, max depth %d, time %.1f s" % (nleaves, max(p[2] for p in per),
                                                            time.time() - t0))
C.check("D > 0 on all 28 cells of [0, 2.8) (ball bisection)", ok_b, "%d subintervals" % nleaves)

print("== infimum of D on each closed cell [j/10, (j+1)/10] (branch and bound, tol 1e-7)")
t0 = time.time()
encl = []
for j in range(NCELLS):
    s = R(MOVES[j])
    f = lambda rho, s=s: drift_direct(rho, s, K8)
    L, U, xU = min_enclosure(QQ(j) / 10, QQ(j + 1) / 10, f, 1e-7)
    encl.append((L, U, xU, j))
    print("  cell %2d: inf D in [%.8f, %.8f], attained near rho = %.6f" % (j, L, U, float(xU)))
Lmin = min(e[0] for e in encl)
jmin = min(encl)[3]
emin = min(encl)
print("smallest margin on [0, 2.8): inf D in [%.8f, %.8f] in cell %d, near rho = %.7f "
      "(time %.1f s)" % (emin[0], emin[1], emin[3], float(emin[2]), time.time() - t0))
C.check("inf of D on [0, 2.8] is positive (rigorous lower bound)", Lmin > 0, "%.8f" % Lmin)
C.check("smallest margin lies in [0.088, 0.090] (note: drift >= 1.089)",
        emin[0] > 0.088 and emin[1] < 0.090)

print("== (a) rho >= 2.8, s = (5/8) exp(-rho^2/2): the analytic argument")
var('rho s v')
# (rho sqrt(1-s) +- sqrt(s))^2 = rho^2 (1-s) + s +- 2 rho sqrt(s(1-s))
for sg in (1, -1):
    e = (rho * sqrt(1 - s) + sg * sqrt(s)) ** 2 - (rho ** 2 * (1 - s) + s + sg * 2 * rho * sqrt(s) * sqrt(1 - s))
    C.check("expansion of (rho sqrt(1-s) %s sqrt(s))^2" % ("+" if sg == 1 else "-"),
            bool(e.expand().simplify_full() == 0))
z = s * (rho ** 2 - 1) / 2
c = rho ** 2 * s * (1 - s) / 2
C.check("exponent (rho^2(1-s)+s)/2 = rho^2/2 - z",
        bool(((rho ** 2 * (1 - s) + s) / 2 - (rho ** 2 / 2 - z)).expand() == 0))
C.check("(1-z)(1+c) - 1 = c - z - zc", bool(((1 - z) * (1 + c) - 1 - (c - z - z * c)).expand() == 0))
C.check("c - z = s/2 - rho^2 s^2/2", bool((c - z - (s / 2 - rho ** 2 * s ** 2 / 2)).expand() == 0))
C.check("zc = s^2 rho^2 (rho^2 - 1)(1 - s)/4",
        bool((z * c - s ** 2 * rho ** 2 * (rho ** 2 - 1) * (1 - s) / 4).expand() == 0))
# zc <= s^2 rho^4/4 because rho^4 - rho^2 (rho^2 - 1)(1 - s) = rho^2 (1 + s rho^2 - s) > 0.
C.check("s^2 rho^4/4 - zc = s^2 rho^2 (1 - s + s rho^2)/4 (nonnegative for 0<s<1)",
        bool((s ** 2 * rho ** 4 / 4 - z * c - s ** 2 * rho ** 2 * (1 - s + s * rho ** 2) / 4).expand() == 0))
phi_expr = exp(-rho ** 2 / 2) * (rho ** 2 / 2 + rho ** 4 / 4)
lower = 8 * exp(rho ** 2 / 2) * s * (QQ(1) / 2 - s * (rho ** 2 / 2 + rho ** 4 / 4))
C.check("8 e^{rho^2/2} s (1/2 - s(rho^2/2 + rho^4/4)) = 5/2 - (25/8) phi at s = (5/8)e^{-rho^2/2}",
        bool((lower.subs(s=QQ(5) / 8 * exp(-rho ** 2 / 2)) - (QQ(5) / 2 - QQ(25) / 8 * phi_expr)).simplify_full() == 0))
dphi = diff(exp(-v / 2) * (v / 2 + v ** 2 / 4), v)
C.check("d/dv e^{-v/2}(v/2 + v^2/4) = e^{-v/2}(1/2 + v/4 - v^2/8)",
        bool((dphi - exp(-v / 2) * (QQ(1) / 2 + v / 4 - v ** 2 / 8)).expand() == 0))
# 1/2 + v/4 - v^2/8 < 0 iff v^2 - 2v - 4 > 0 iff v > 1 + sqrt(5); 2.8^2 = 7.84.
C.check("2.8^2 = 196/25 > 1 + sqrt(5)", R(QQ(196) / 25) > 1 + R(5).sqrt())
C.check("v^2 - 2v - 4 = (v - 1 - sqrt(5))(v - 1 + sqrt(5))",
        bool(((v - 1 - sqrt(5)) * (v - 1 + sqrt(5)) - (v ** 2 - 2 * v - 4)).expand() == 0))
phi28 = phi_ball(RHO_SPLIT)
print("phi(2.8) = %s" % phi28)
C.check("phi(2.8) < 12/25", phi28 < R(QQ(12) / 25), "phi(2.8) = %.6f" % phi28.mid())
C.check("part (a) conditions at split 2.8, constant 12/25 (phi decreasing, phi(2.8) < 12/25, "
        "5/2 - (25/8)(12/25) >= 1)", all(part_a_conditions(RHO_SPLIT, QQ(12) / 25)))
C.check("phi(2.8) rounds to 0.3827", abs(phi28 - R(QQ(3827) / 10000)) < R(QQ(5) / 10 ** 5))
analytic_margin = R(QQ(5) / 2) - R(QQ(25) / 8) * phi28 - 1
print("analytic lower bound of D on [2.8, oo): 5/2 - (25/8) phi(2.8) - 1 = %s" % analytic_margin)
C.check("analytic lower bound of D on [2.8, oo) is positive", analytic_margin > 0)

print("== redundant rigorous cover of [2.8, 12] by the factored form")
t0 = time.time()
fa = lambda r: drift_factored(r, K8)
ok_a = True
nl_a = 0
for k in range(28, 120):
    ok, leaves, info = certify_interval(QQ(k) / 10, QQ(k + 1) / 10, fa, maxdepth=30)
    nl_a += len(leaves)
    if not ok:
        ok_a = False
        print("  piece [%s, %s] not certified" % info)
print("[2.8, 12]: %d subintervals, time %.1f s" % (nl_a, time.time() - t0))
C.check("D > 0 on [2.8, 12] (ball bisection, factored form)", ok_a, "%d subintervals" % nl_a)
La, Ua, xa = min_enclosure(QQ(28) / 10, QQ(12), fa, 1e-6)
print("inf D on [2.8, 12] in [%.7f, %.7f], near rho = %.5f" % (La, Ua, float(xa)))
C.check("inf D on [2.8, 12] > 0.959", La > 0.959, "%.6f" % La)
if La < 0.96:
    print("NOTE: the note states drift - 1 >= 0.96 on [2.8, 12]; the infimum is %.5f, at rho = 2.8 "
          "(a rounding up in the note, not load-bearing: part (a) needs only D >= 0)" % La)

print("== grid scan as in the note (step 1/4000, ball point values)")
gmin1 = min((drift_direct(R(QQ(i) / 4000), R(MOVES[min(i // 400, 27)]), K8).lower(), i) for i in range(0, 11200))
gmin2 = min((drift_factored(R(QQ(i) / 4000), K8).lower(), i) for i in range(11200, 48001))
print("grid [0, 2.8): min drift = %.6f at rho = %s;  grid [2.8, 12]: min drift = %.6f at rho = %s" %
      (gmin1[0] + 1, QQ(gmin1[1]) / 4000, gmin2[0] + 1, QQ(gmin2[1]) / 4000))
C.check("grid min of the drift on [0, 2.8) >= 1.089", gmin1[0] + 1 >= 1.089)
C.check("grid min of the drift on [2.8, 12] > 1.959", gmin2[0] + 1 > 1.959)

print("== remark (exploration, floating point): smallest K with the best move at each rho")
import math
def gain(r, sv):
    u = r * math.sqrt(1 - sv)
    w = math.sqrt(sv)
    return 0.5 * (math.exp((u + w) ** 2 / 2) + math.exp((u - w) ** 2 / 2)) - math.exp(r ** 2 / 2)
worst = (0, 0)
for i in range(0, 281):
    r = float(i) / 100
    best = max(gain(r, float(k) / 4000) for k in range(1, 4000))
    worst = max(worst, (1 / best, r))
print("max over rho in [0, 2.8] of 1/max_s gain = %.4f at rho = %.2f (note: 7.16 near 1.65)" % worst)

print("time %.1f s" % (time.time() - t_start))
C.finish(35)
