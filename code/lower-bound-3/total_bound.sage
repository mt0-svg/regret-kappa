# Section 4.5 of the paper: T_0, the side conditions (C1) to (C3) of Lemma 4.12, the bound B(T) and
# its simplified and cleaner forms. Two kinds of checks, kept apart in the output:
#  [analytic]  the constants and monotonicity facts of the note's argument valid for every
#              T >= T_0 (symbolic derivatives by Sage, numbers by Arb balls);
#  [finite]    the exact conditions and inequalities evaluated with balls at finitely many T
#              (T_0 and its neighbours, 50 points per decade up to 10^30, the jumps of j_0
#              up to 10^59), a cross-check of the analytic part at those T only.
# Run from this directory: sage total_bound.sage

load("common.sage")
load("lb_lib.sage")
import time

C = Checker("total_bound")
t_start = time.time()
c1 = c1_of(J_prior(), EZ2_prior())
var('T v w k')
assume(T > 3)


def ok_all(Ts, pred):
    bad = [t for t in Ts if not pred(t)]
    return len(bad) == 0, bad


print("== T_0: least integer with L_low(T) >= 14.5, L_low(T) = 2 log T - 2 log(20 e) - 2 log(log(3 log T) + 1)")
Llow_sym = 2 * log(T) - 2 * log(20 * e) - 2 * log(log(3 * log(T)) + 1)
dL = diff(Llow_sym, T)
C.check("[analytic] L_low'(T) = (2/T)(1 - 1/((log(3 log T) + 1) log T))",
        bool((dL - (2 / T) * (1 - 1 / ((log(3 * log(T)) + 1) * log(T)))).simplify_full() == 0))
# (log(3 log T) + 1) log T is increasing and exceeds 1 at T = 3, so L_low increases on [3, oo).
C.check("[analytic] (log(3 log 3) + 1) log 3 > 1", ((3 * R(3).log()).log() + 1) * R(3).log() > 1)
T0c = T0_least()
print("least T with L_low(T) >= 14.5: %d; L_low(T0 - 1) = %s, L_low(T0) = %s" %
      (T0c, L_low(T0c - 1).mid().n(digits=10), L_low(T0c).mid().n(digits=10)))
C.check("T_0 = 355713 (note: 355713)", T0c == T0 and L_low(T0) >= R(QQ(145) / 10) and L_low(T0 - 1) < R(QQ(145) / 10),
        str(T0c))
j0T0 = j0_of(T0)
LT0 = L_of(T0)
print("at T_0: j_0 = %d, L = %s, a = %s, a+ = %s, T_1 = %d, k_0 = %d" %
      (j0T0, LT0.mid().n(digits=10), LT0.sqrt().mid().n(digits=10), aplus_of(LT0).mid().n(digits=10),
       T0 // 2, k0_of(T0)))
C.check("[finite] L(T_0) >= L_low(T_0) and j_0(T_0) = 4", LT0 >= L_low(T0) and j0T0 == 4)

print("== (C1) L >= 14.5: L >= L_low (j_0 <= log(3 log T) + 1), L_low increasing, L_low(T_0) >= 14.5")

print("== (C2) j_0 (8.8 e exp(L/2) + 1) <= T_1 - 1")
C.check("[analytic] 8.8 e exp(L/2) j_0 = 0.44 T (exp(L/2) = T/(20 e j_0)), checked at T_0 and 10^9",
        all((R(QQ(88) / 10) * E1 * (L_of(t) / 2).exp() * j0_of(t)).overlaps(R(QQ(44) / 100) * t) for t in [T0, 10 ** 9]))
C.check("[analytic] d/dT (0.06 T - log log T) = 0.06 - 1/(T log T) > 0 for T >= 17",
        bool((diff(QQ(6) / 100 * T - log(log(T)), T) - (QQ(6) / 100 - 1 / (T * log(T)))).simplify_full() == 0)
        and R(QQ(6) / 100) - 1 / (17 * R(17).log()) > 0)
g2 = R(QQ(6) / 100) * T0 - (R(QQ(5) / 2) + R(3).log() + R(T0).log().log())
C.check("[analytic] 0.06 T_0 >= 2.5 + log 3 + log log T_0 (so 0.06 T >= j_0 + 3/2 for T >= T_0)", g2 > 0,
        "slack %.2f" % g2.mid())

print("== (C3) k_0 >= pi^2 e^2 (a+ + 2)^2")
F_sym = T / 2 - pi ** 2 * e ** 2 * (sqrt(2 * log(T)) + QQ(203) / 100) ** 2
dF = diff(F_sym, T)
C.check("[analytic] F'(T) = 1/2 - 2 pi^2 e^2 (1 + 2.03/sqrt(2 log T))/T",
        bool((dF - (QQ(1) / 2 - 2 * pi ** 2 * e ** 2 * (1 + QQ(203) / 100 / sqrt(2 * log(T))) / T)).simplify_full() == 0))
F1000 = R(1) / 2 - 2 * PI ** 2 * E1 ** 2 * (1 + R(QQ(203) / 100) / (2 * R(1000).log()).sqrt()) / 1000
C.check("[analytic] F'(10^3) > 0, and the subtracted term decreases in T, so F increases on [10^3, oo)",
        F1000 > 0, "F'(1000) = %.4f" % F1000.mid())
FT0 = R(T0) / 2 - PI ** 2 * E1 ** 2 * ((2 * R(T0).log()).sqrt() + R(QQ(203) / 100)) ** 2
print("F(T_0) = %s" % FT0.mid().n(digits=10))
C.check("[analytic] F(T_0) > 0", FT0 > 0, "%.3f" % FT0.mid())
C.check("[analytic] L <= 2 log T (20 e j_0 >= 1) and sqrt(5/8) e^{-L/4} <= 0.022 <= 0.03 under (C1)",
        R(QQ(5) / 8).sqrt() * R(-QQ(145) / 40).exp() <= R(QQ(22) / 1000))

print("== exact (C1), (C2), (C3) at finitely many T")
Tgrid = sorted(set([T0 + i for i in range(0, 101)] +
                   [unique_floor(R(10) ** (R(i) / 50)) for i in range(279, 1501)]))
jumps = []
for m in range(4, 7):
    Tm = unique_floor((R(m).exp() / 3).exp())
    jumps.append((m, Tm))
    print("jump of j_0 at m = %d: T = %d (j_0(T) = %d, j_0(T + 1) = %d)" % (m, Tm, j0_of(Tm), j0_of(Tm + 1)))
Tjump = []
for m, Tm in jumps:
    Tjump += [Tm - 1, Tm, Tm + 1, Tm + 2]
C.check("[finite] j_0 jumps where predicted (m = 4, 5, 6)", all(j0_of(Tm) == m and j0_of(Tm + 1) == m + 1 for m, Tm in jumps))
Tall = sorted(set(Tgrid + Tjump))
print("%d values of T: T_0..T_0 + 100, 50 per decade from 10^5.58 to 10^30, the jumps up to 10^59" % len(Tall))
for name, pred in [("(C1)", C1_holds), ("(C2)", C2_holds), ("(C3)", C3_holds)]:
    ok, bad = ok_all(Tall, pred)
    C.check("[finite] %s holds at all %d values" % (name, len(Tall)), ok, "" if ok else str(bad[:5]))

print("== proof of the theorem: monotonicity of u^2 + log(k/(u + 2)^2) - log(k)/(2k) - 1/k")
var('uu kk')
Hf = uu ** 2 + log(kk / (uu + 2) ** 2) - log(kk) / (2 * kk) - 1 / kk
C.check("[analytic] d/du = 2u - 2/(u + 2) (> 0 for u >= 1)", bool((diff(Hf, uu) - (2 * uu - 2 / (uu + 2))).simplify_full() == 0))
C.check("[analytic] d/dk = 1/k + (log k - 1)/(2k^2) + 1/k^2 (> 0 for k >= 3)",
        bool((diff(Hf, kk) - (1 / kk + (log(kk) - 1) / (2 * kk ** 2) + 1 / kk ** 2)).simplify_full() == 0))

print("== B(T) = (1 - e^{-j_0}) B_0 >= B_0 - 1 (e^{-j_0} <= 1/(3 log T), 0 < B_0 <= 3 log T)")
ok, bad = ok_all(Tall, lambda t: B0_of(t, c1) > 0 and B0_of(t, c1) <= 3 * R(t).log())
C.check("[finite] 0 < B_0 <= 3 log T at all values", ok)

print("== simplified form: B(T) >= 3 log T - log log T - 2 log(log log T + 2.1) - 14.55 (constants)")
C.check("[analytic] j_0 <= log log T + log 3 + 1 <= log log T + 2.0987", R(3).log() + 1 <= R(QQ(20987) / 10000),
        "log 3 + 1 = %.6f" % (R(3).log() + 1).mid())
c845 = 2 * (1 + 2 / R(QQ(145) / 10).sqrt()).log()
C.check("[analytic] 2 log(1 + 2/sqrt(14.5)) <= 0.8445", c845 <= R(QQ(8445) / 10000), "%.6f" % c845.mid())
k00 = k0_of(T0)
tailk = R(k00).log() / (2 * k00) + R(1) / k00
C.check("[analytic] log(k)/(2k) + 1/k <= 1e-4 at k = k_0(T_0) = 177857 (decreasing in k >= 1)",
        tailk <= R(QQ(1) / 10 ** 4) and
        bool((diff(log(kk) / (2 * kk) + 1 / kk, kk) - ((1 - log(kk)) / (2 * kk ** 2) - 1 / kk ** 2)).simplify_full() == 0),
        "%.3e" % tailk.mid())
const = 2 * (20 * E1).log() + 2 * R(2).log() + R(QQ(8445) / 10000) + R(C1_STATED) + R(QQ(1) / 10 ** 4) + 1
print("2 log(20 e) + 2 log 2 + 0.8445 + c_1 + 1e-4 + 1 = %s" % const.mid().n(digits=10))
C.check("[analytic] the collected constant is <= 14.55 (note: 14.55)", const <= R(QQ(1455) / 100), "%.6f" % const.mid())

print("== cleaner forms")
C.check("[analytic] d/dv (v - 2 log(v + 2.1)) = 1 - 2/(v + 2.1) (> 0 for v > -0.1)",
        bool((diff(v - 2 * log(v + QQ(21) / 10), v) - (1 - 2 / (v + QQ(21) / 10))).simplify_full() == 0))
v0 = R(T0).log().log()
hv0 = v0 - 2 * (v0 + R(QQ(21) / 10)).log()
print("log log T_0 = %s, v - 2 log(v + 2.1) there = %s" % (v0.mid().n(digits=10), hv0.mid().n(digits=10)))
C.check("[analytic] log log T_0 rounds to 2.5480 and the value there is >= -0.5249 (note: -0.5249)",
        abs(v0 - R(QQ(2548) / 1000)) < R(QQ(5) / 10 ** 5) and hv0 >= R(-QQ(5249) / 10000), "%.6f" % hv0.mid())
C.check("[analytic] 14.6 + 0.5249 <= 15.2", QQ(146) / 10 + QQ(5249) / 10000 <= QQ(152) / 10)
C.check("[analytic] 6 log log T_0 >= 15.2 (note: 15.29), and 6 log log T increases",
        6 * v0 >= R(QQ(152) / 10), "%.4f" % (6 * v0).mid())

print("== [finite] B(T) against the three forms at all values of T")
rows = []
for t in Tall:
    b = B_of(t, c1)
    rows.append((t, b, b - form_simplified(t), form_simplified(t) - form_clean(t), form_clean(t) - form_clean8(t)))
d1 = min(rows, key=lambda r: r[2].lower())
d2 = min(rows, key=lambda r: r[3].lower())
d3 = min(rows, key=lambda r: r[4].lower())
print("min of B - simplified form: %.6f at T = %d" % (d1[2].mid(), d1[0]))
print("min of simplified - (3 log T - 2 log log T - 15.2): %.6f at T = %d" % (d2[3].mid(), d2[0]))
print("min of (3 log T - 2 log log T - 15.2) - (3 log T - 8 log log T): %.6f at T = %d" % (d3[4].mid(), d3[0]))
C.check("[finite] B(T) >= 3 log T - log log T - 2 log(log log T + 2.1) - 14.6 at all values", d1[2] > 0)
C.check("[finite] that form >= 3 log T - 2 log log T - 15.2 at all values", d2[3] > 0)
C.check("[finite] 3 log T - 2 log log T - 15.2 >= 3 log T - 8 log log T at all values", d3[4] >= 0)
C.check("[finite] B(T) >= 3 log T - 2 log log T - 15.2 at all values",
        all(r[1] - form_clean(r[0]) > 0 for r in rows), "min %.4f" % min((r[1] - form_clean(r[0])).mid() for r in rows))
for t in [T0, T0 + 1] + Tjump:
    print("  T = %-62d j_0 = %d  B = %12.6f  B - simplified = %.6f" % (t, j0_of(t), B_of(t, c1).mid(),
                                                                       (B_of(t, c1) - form_simplified(t)).mid()))

print("== values quoted in the note")
vals = {10 ** 6: QQ(2263) / 100, 10 ** 7: QQ(2925) / 100, 10 ** 10: QQ(4939) / 100}
ok = True
for t, q in vals.items():
    b = B_of(t, c1)
    print("  B(10^%d) = %.6f (note: %s)" % (ZZ(t).exact_log(10), b.mid(), q.n(digits=4)))
    ok = ok and abs(b - R(q)) < R(QQ(5) / 1000)
C.check("B(10^6), B(10^7), B(10^10) = 22.63, 29.25, 49.39 to 2 decimals", ok)
ratios = {6: QQ(164) / 100, 10: QQ(214) / 100, 20: QQ(255) / 100, 50: QQ(281) / 100, 100: QQ(290) / 100}
ok = True
for ex, q in sorted(ratios.items()):
    t = 10 ** ex
    rr = B_of(t, c1) / R(t).log()
    print("  B/log T at 10^%d = %.6f (note: %s)" % (ex, rr.mid(), q.n(digits=3)))
    ok = ok and abs(rr - R(q)) < R(QQ(5) / 1000)
C.check("B(T)/log T = 1.64, 2.14, 2.55, 2.81, 2.90 at 10^6, 10^10, 10^20, 10^50, 10^100", ok)
print("time %.1f s" % (time.time() - t_start))
C.finish(32)
