# Recomputes, with this implementation's code, every value of out/others_extracted.txt (the
# values printed by the author's and the referee's PARI/GP implementations, extracted by
# compare.sh through diff), and compares at the printed precision: MATCH when
# |ours - theirs| <= one unit of their last printed digit (plus our ball radius).
# Run by compare.sh.

load("common.sage")
load("drift_lib.sage")
load("rational_lib.sage")
load("lb_lib.sage")
import time

t_start = time.time()
RF = RealField(500)
c1 = c1_of(J_prior(), EZ2_prior())
J = J_prior()
EZ2 = EZ2_prior()
n_match = 0
mismatches = []


def ulp(t):
    """One unit of the last printed digit of the decimal string t (with an optional e-exponent)."""
    t = t.lower().replace(" ", "")
    m, ex = (t.split("e") + ["0"])[:2]
    d = len(m.split(".")[1]) if "." in m else 0
    return QQ(10) ** (-d + int(ex))


def val(t):
    return R(RF(t.replace(" ", "").lower()))


def cmp(label, theirs, ours, tol=None):
    """theirs: printed string; ours: a ball, an integer or a rational."""
    global n_match
    if isinstance(ours, (int, Integer)) and "." not in theirs and "e" not in theirs.lower():
        ok = ZZ(theirs) == ours
        detail = "%s" % ours
    else:
        ob = R(ours)
        u = R(ulp(theirs)) if tol is None else R(tol)
        diff = abs(ob - val(theirs))
        ok = bool(diff.lower() <= u.upper())
        detail = "%s (|diff| %.2e, unit %.0e)" % (ob.mid().n(digits=max(8, min(60, len(theirs) + 2))),
                                                  diff.mid(), u.mid())
    if ok:
        n_match += 1
    else:
        mismatches.append(label)
    print("%-8s %-58s theirs %s  ours %s" % ("MATCH" if ok else "MISMATCH", label, theirs, detail))
    sys.stdout.flush()


lines = [l.split() for l in open("out/others_extracted.txt").read().splitlines() if l.strip()]
by = {}
for l in lines:
    by.setdefault(l[0], []).append(l[1:])
print("values extracted from the other implementations: %d lines, %d kinds" % (len(lines), len(by)))

print("== author, drift_check.out")
leaves_all = {}
for j in range(NCELLS):
    ok, leaves, info = certify_cell(j, MOVES)
    leaves_all[j] = leaves
for j, cnt in by["author_cells"]:
    cmp("author cell %s subintervals" % j, cnt, len(leaves_all[int(j)]))
tot, dep, marg = by["author_cert"][0]
allleaves = [l for j in leaves_all for l in leaves_all[j]]
cmp("author total subintervals", tot, len(allleaves))
cmp("author max bisection depth", dep, max(l[2] for l in allleaves))
cmp("author smallest rational margin", marg, min(l[3] for l in allleaves))
grid1 = min(((drift_direct(R(QQ(i) / 4000), R(MOVES[i // 400]), R(K_G)).mid(), i) for i in range(11200)))
g1v = drift_direct(R(QQ(grid1[1]) / 4000), R(MOVES[grid1[1] // 400]), R(K_G))
cmp("author grid min of drift - 1 on [0, 2.8)", by["author_grid1"][0][0], g1v)
cmp("author grid argmin on [0, 2.8)", by["author_grid1"][0][1], QQ(grid1[1]) / 4000)
grid2 = min(((drift_factored(R(QQ(i) / 4000), R(K_G)).mid(), i) for i in range(11200, 48001)))
g2v = drift_factored(R(QQ(grid2[1]) / 4000), R(K_G))
cmp("author grid min of drift - 1 on [2.8, 12]", by["author_grid2"][0][0], g2v)
cmp("author grid argmin on [2.8, 12]", by["author_grid2"][0][1], QQ(grid2[1]) / 4000)
cmp("author phi(2.8)", by["author_phi28"][0][0], phi_ball(RHO_SPLIT))
x5 = 1 + R(5).sqrt()
cmp("author max of e^{-x/2}(x/2 + x^2/4) at x = 1 + sqrt 5", by["author_phimax"][0][0], (-x5 / 2).exp() * (x5 / 2 + x5 ** 2 / 4))

print("== author, phase2_check.out")
Jt, EZt, c0t, c1t = by["author_p2const"][0]
cmp("author J", Jt, J)
cmp("author E Z^2", EZt, EZ2)
cmp("author c0 = -log(A^2/(4 pi^2)) + 1 + E Z^2", c0t, -(R(4) / (4 * PI ** 2)).log() + 1 + EZ2)
cmp("author c1", c1t, c1)
t0 = time.time()
for k, rho, vt, ph, valid in by["author_vT"]:
    k = int(k)
    rq = QQ(RF(rho).exact_rational())
    d = vT_detail(rq, k, steps=False)
    cmp("author vT(%s, %d)" % (rho, k), vt, d["vT"])
    cmp("author Phi0(%s, %d)" % (rho, k), ph, Phi1(rq, k, c1))
    cmp("author validity k >= pi^2 e^2 r^2 at (%s, %d)" % (rho, k), valid, int(R(k) >= PI ** 2 * E1 ** 2 * (rq + 2) ** 2))
print("(time %.1f s)" % (time.time() - t0))
t0 = time.time()
best = None
for k in [10 ** 3, 10 ** 4, 10 ** 5]:
    for i in range(0, 161):
        rq = QQ(i) / 4
        if R(k) >= PI ** 2 * E1 ** 2 * (rq + 2) ** 2:
            m = vT_detail(rq, k, steps=False)["vT"] - Phi1(rq, k, c1)
            if best is None or m.mid() < best[0].mid():
                best = (m, k, rq)
gm, gk, grho = by["author_vTgridmin"][0]
cmp("author grid min of vT - Phi0 (k in 1e3, 1e4, 1e5; rho step 1/4)", gm, best[0])
cmp("author grid argmin k", gk, best[1])
cmp("author grid argmin rho", grho, best[2])
print("(time %.1f s)" % (time.time() - t0))

print("== author, total_bound.out")
for t, j0s, Ls, Bs, Bss in by["author_B"]:
    T = ZZ(10) ** int(t.split("e")[1]) if "e" in t else ZZ(t)
    cmp("author j_0(%s)" % t, j0s, j0_of(T))
    cmp("author L(%s)" % t, Ls, L_of(T))
    cmp("author B(%s)" % t, Bs, B_of(T, c1))
    cmp("author Bsimple(%s)" % t, Bss, form_simplified(T))
j0s, Ls, Lls = by["author_T0"][0]
cmp("author j_0(T_0)", j0s, j0_of(T0))
cmp("author L(T_0)", Ls, L_of(T0))
cmp("author L_low(T_0)", Lls, L_low(T0))
cmp("author eps_14.5", by["author_eps145"][0][0], eps_L(QQ(145) / 10))
FT0 = R(T0) / 2 - PI ** 2 * E1 ** 2 * ((2 * R(T0).log()).sqrt() + R(QQ(203) / 100)) ** 2
cmp("author F(T_0)", by["author_C3"][0][0], FT0)
cmp("author sqrt(5/8) exp(-14.5/4)", by["author_C3"][0][1], R(QQ(5) / 8).sqrt() * R(-QQ(145) / 40).exp())
# the author's scan grid is read as T = floor(T_0 10^(i/50)), i = 0..1222 (up to 10^30)
scan = []
for i in range(0, 1223):
    T = unique_floor(R(T0) * R(10) ** (R(i) / 50))
    if T <= 10 ** 30:
        scan.append(((B_of(T, c1) - form_simplified(T)), T))
sm = min(scan, key=lambda r: r[0].mid())
cmp("author scan min of B - Bsimple (grid T_0 10^(i/50) assumed)", by["author_scanmin"][0][0], sm[0])
cmp("author scan argmin T (4 significant digits)", by["author_scanmin"][0][1], R(sm[1]), tol=QQ(1) / 1000 * sm[1])
v0 = R(T0).log().log()
cmp("author log log T_0", by["author_v0"][0][0], v0)
cmp("author v - 2 log(v + 2.1) at log log T_0", by["author_v0"][0][1], v0 - 2 * (v0 + R(QQ(21) / 10)).log())
cmp("author 6 log log T_0", by["author_v0"][0][2], 6 * v0)
for t, e in zip(by["author_ratios"][0], [6, 10, 20, 50, 100]):
    cmp("author B/log T at 10^%d" % e, t, B_of(10 ** e, c1) / R(10 ** e).log())

print("== referee, drift.txt and kstar.txt")
cmp("referee move table", " ".join(by["referee_table"][0]) == " ".join(str(d) for d in S_DIGITS) and "1" or "0", 1)
ub = val(by["referee_phi28ub"][0][0])
ph = phi_ball(RHO_SPLIT)
cmp("referee rational upper bound of phi(2.8) (within 1e-15 above)", by["referee_phi28ub"][0][0], ph, tol=QQ(1) / 10 ** 15)
print("         (their upper bound minus phi(2.8) = %.3e, positive: %s)" % ((ub - ph).mid(), ub > ph))
cmp("referee grid min of the drift on [0, 2.8)", by["referee_grid1"][0][0], g1v + 1)
cmp("referee grid argmin on [0, 2.8)", by["referee_grid1"][0][1], QQ(grid1[1]) / 4000)
cmp("referee grid min of the drift on [2.8, 12]", by["referee_grid2"][0][0], g2v + 1)
cmp("referee grid argmin on [2.8, 12]", by["referee_grid2"][0][1], QQ(grid2[1]) / 4000)
g3 = min((drift_factored(R(QQ(i) / 100), R(K_G)) for i in range(1200, 4001)), key=lambda b: b.mid())
cmp("referee grid min of the drift on [12, 40], step 1/100", by["referee_grid3"][0][0], g3 + 1)

RFk = RealField(400)


def gain(rho, s):
    u = rho * (1 - s).sqrt()
    w = s.sqrt()
    return ((u + w) ** 2 / 2).exp() / 2 + ((u - w) ** 2 / 2).exp() / 2 - (rho ** 2 / 2).exp()


def best_move(rho):
    """max over s in (0, 1) of the one-step gain of exp(rho^2/2), golden section in 400 bits."""
    rho = RFk(rho)
    a, b = RFk(1) / 1000, RFk(999) / 1000
    g = (RFk(5).sqrt() - 1) / 2
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = gain(rho, c), gain(rho, d)
    for _ in range(400):
        if fc > fd:
            b, d, fd = d, c, fc
            c = b - g * (b - a)
            fc = gain(rho, c)
        else:
            a, c, fc = c, d, fd
            d = a + g * (b - a)
            fd = gain(rho, d)
    s = (a + b) / 2
    return s, 1 / gain(rho, s)


def best_move_newton(rho):
    """The same maximum by Newton's method on d gain/ds = 0 (symbolic derivatives, 600 bits)."""
    RN = RealField(600)
    sv = var('sv')
    u = rho * sqrt(1 - sv)
    w = sqrt(sv)
    G = exp((u + w) ** 2 / 2) / 2 + exp((u - w) ** 2 / 2) / 2 - exp(rho ** 2 / 2)
    g = fast_callable(G, vars=[sv], domain=RN)
    g1 = fast_callable(diff(G, sv), vars=[sv], domain=RN)
    g2 = fast_callable(diff(G, sv, 2), vars=[sv], domain=RN)
    x = RN(QQ(15) / 100)
    for _ in range(60):
        x = x - g1(x) / g2(x)
    return x, 1 / g(x)


for rho, K, s in by["referee_krho"] + [by["referee_kstar"][0]]:
    rq_ = QQ(RF(rho).exact_rational())
    sb, Kb = best_move(rq_)
    sn, Kn = best_move_newton(rq_)
    print("         rho = %s: golden section K = %s, Newton K = %s, |difference| %.1e" %
          (rho[:6], Kb.n(digits=45), Kn.n(digits=45), abs(RealField(400)(Kn) - Kb)))
    cmp("referee K(rho) = 1/max_s gain at rho = %s" % rho[:6], K, R(Kb))
    cmp("referee best move s at rho = %s (to 1e-12)" % rho[:6], s, R(sb), tol=QQ(1) / 10 ** 12)
# (the remark of the note, 7.16 near 1.65, is the max over rho of K(rho))

print("== referee, constants.txt")
cmp("referee J", by["referee_J"][0][0], J)
cmp("referee E Z^2", by["referee_EZ2"][0][0], EZ2)
cmp("referee c_1", by["referee_c1"][0][0], c1)
cmp("referee J E Z^2", by["referee_JEZ2"][0][0], J * EZ2)
cmp("referee log(A^2/(4 pi^2))", by["referee_logA"][0][0], (R(4) / (4 * PI ** 2)).log())
qmax = R(-QQ(1) / 2).exp() / R(2).sqrt()
cmp("referee max of (u/2) e^{-u^2/4}", by["referee_qmax"][0][0], qmax)
cmp("referee 1 - sqrt(5/8) max", by["referee_dmin"][0][0], 1 - R(QQ(5) / 8).sqrt() * qmax)
cmp("referee eps_14.5", by["referee_eps145"][0][0], eps_L(QQ(145) / 10))
cmp("referee log 1.1", by["referee_eps145"][0][1], R(QQ(11) / 10).log())
cmp("referee max over cells of (j+1)/10 + sqrt(s_j)", by["referee_crudestep"][0][0],
    max((R(QQ(j + 1) / 10) + R(MOVES[j]).sqrt() for j in range(NCELLS)), key=lambda b: b.mid()))
cmp("referee sqrt(5/8) e^{-14.5/4}", by["referee_s0022"][0][0], R(QQ(5) / 8).sqrt() * R(-QQ(145) / 40).exp())
T0s, l1, l2 = by["referee_T0"][0]
cmp("referee T_0", T0s, T0_least())
cmp("referee L_low(T_0 - 1)", l1, L_low(T0 - 1))
cmp("referee L_low(T_0)", l2, L_low(T0))
Ls, as_, aps = by["referee_atT0"][0]
cmp("referee L(T_0)", Ls, L_of(T0))
cmp("referee a(T_0)", as_, L_of(T0).sqrt())
cmp("referee a+(T_0)", aps, aplus_of(L_of(T0)))
cmp("referee (C2) left side at T_0", by["referee_C2lhs"][0][0], j0_of(T0) * (R(QQ(88) / 10) * E1 * (L_of(T0) / 2).exp() + 1))
cmp("referee (C3) right side at T_0", by["referee_C3rhs"][0][0], PI ** 2 * E1 ** 2 * (aplus_of(L_of(T0)) + 2) ** 2)
cmp("referee F(T_0)", by["referee_FT0"][0][0], FT0)
cmp("referee B_0(T_0)", by["referee_B0T0"][0][0], B0_of(T0, c1))
cmp("referee B(T_0)", by["referee_B0T0"][0][1], B_of(T0, c1))
cmp("referee F'(1000)", by["referee_dF1000"][0][0],
    R(1) / 2 - 2 * PI ** 2 * E1 ** 2 * (1 + R(QQ(203) / 100) / (2 * R(1000).log()).sqrt()) / 1000)
for t, b, l in by["referee_BT"]:
    cmp("referee B(%s)" % t, b, B_of(ZZ(t), c1))
    cmp("referee L(%s)" % t, l, L_of(ZZ(t)))
for e, r in by["referee_ratio"]:
    cmp("referee B/log T at 10^%s" % e, r, B_of(10 ** int(e), c1) / R(10 ** int(e)).log())
mv, mT = by["referee_minBs"][0]
cmp("referee B - simplified at its argmin T (the j_0 jump near 2.5e58)", mv, B_of(ZZ(mT), c1) - form_simplified(ZZ(mT)))
cmp("referee min of [14.6 form] - [15.2 form] (at T_0)", by["referee_min2"][0][0], form_simplified(T0) - form_clean(T0))
cmp("referee min of [15.2 form] - [8 log log T form] (at T_0)", by["referee_min3"][0][0], form_clean(T0) - form_clean8(T0))
vv, hv, v6 = by["referee_v0"][0]
cmp("referee log log T_0", vv, v0)
cmp("referee v - 2 log(v + 2.1) at log log T_0", hv, v0 - 2 * (v0 + R(QQ(21) / 10)).log())
cmp("referee 6 log log T_0", v6, 6 * v0)
cmp("referee log 3 + 1", by["referee_log3"][0][0], R(3).log() + 1)
cmp("referee 2 log(1 + 2/sqrt(14.5))", by["referee_c845"][0][0], 2 * (1 + 2 / R(QQ(145) / 10).sqrt()).log())
cmp("referee collected constant", by["referee_const"][0][0],
    2 * (20 * E1).log() + 2 * R(2).log() + R(QQ(8445) / 10000) + c1 + R(QQ(1) / 10 ** 4) + 1)
k00 = k0_of(T0)
cmp("referee log(k_0)/(2 k_0) + 1/k_0 at T_0", by["referee_tailk"][0][0], R(k00).log() / (2 * k00) + R(1) / k00)
cmp("referee dF/dk at k = 3", by["referee_dFdk3"][0][0], R(1) / 3 + (R(3).log() - 1) / 18 + R(1) / 9)

print("== referee, phase2.txt")
t0 = time.time()
comp_lb = R(1) / 2 - (J - 2) / (PI ** 2 * E1 ** 2)
comps = {(r[0], r[1]): r[2:] for r in by["referee_comp"]}
for rho, k, vt, ph, S, Sb in by["referee_vT"]:
    k = int(k)
    rq = QQ(RF(rho).exact_rational())
    d = vT_detail(rq, k, steps=False)
    tag = "(%s, %d)" % (rho[:4], k)
    cmp("referee vT%s" % tag, vt, d["vT"])
    cmp("referee Phi_1%s" % tag, ph, Phi1(rq, k, c1))
    cmp("referee sum eps^2/w%s" % tag, S, d["S"])
    cmp("referee its lower bound Lambda - 1 - ...%s" % tag, Sb, d["Lam"] - 1 - R(k).log() / (2 * k) - R(1) / k)
    cv, cb = comps[(rho, str(k))]
    cmp("referee (1+X)/w_k%s" % tag, cv, (1 + d["X"]) / d["wk"])
    cmp("referee 1/2 - (J-2)/(pi^2 e^2)%s" % tag, cb, comp_lb)
print("(time %.1f s)" % (time.time() - t0))
M = prior_moments(20)
bcomps = {(r[0], r[1]): r[2:] for r in by["referee_bayescomp"]}
for rho, k, br, vt, fs, fsb in by["referee_bayes"]:
    k = int(k)
    rq = QQ(RF(rho).exact_rational())
    bv, Q = bayes_value(rq, k, M)
    r = R(rq) + 2
    X = sum(R(NU_M2) * i / (r ** 2 * k) for i in range(1, k + 1))
    X4 = sum((R(NU_M2) * i / (r ** 2 * k)) ** 2 for i in range(1, k + 1))
    compB = (EZ2 + X - (R(rq) ** 2 + EZ2) * X4) / (1 + X)
    d = vT_detail(rq, k, steps=False)
    tag = "(%s, %d)" % (rho[:4], k)
    cmp("referee Bayes bracket%s" % tag, br, bv)
    cmp("referee vT%s (Bayes table)" % tag, vt, d["vT"])
    cmp("referee Bayes first sum%s" % tag, fs, bv + EZ2 - compB)
    cmp("referee vT first sum%s" % tag, fsb, d["S"])
    cb, cbb = bcomps[(rho, str(k))]
    cmp("referee Bayes comparator%s" % tag, cb, compB)
    cmp("referee vT comparator (1+X)/w_k%s" % tag, cbb, (1 + d["X"]) / d["wk"])
r4 = QQ(38470) / 10000
d4 = vT_detail(r4, 177857, steps=False)
cmp("referee vT(3.8470, 177857) - Phi_1 (rho = 3.8470 as labelled)", by["referee_vTT0"][0][0], d4["vT"] - Phi1(r4, 177857, c1))
aT0 = L_of(T0).sqrt()
dT0 = vT_detail(aT0, 177857, steps=False)
print("         (at rho = a(T_0) = %s itself: vT - Phi_1 = %s)" % (aT0.mid().n(digits=12),
                                                                (dT0["vT"] - Phi1(aT0, 177857, c1)).mid().n(digits=12)))

print("SUMMARY compare: %d values compared, %d MATCH, %d MISMATCH (time %.1f s)" %
      (n_match + len(mismatches), n_match, len(mismatches), time.time() - t_start))
if mismatches:
    print("MISMATCHES: " + "; ".join(mismatches))
print("RESULT compare %s" % ("ALL MATCH" if not mismatches else "MISMATCHES FOUND"))
