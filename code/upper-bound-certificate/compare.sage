# compare.sage: comparison with the recorded outputs of the first implementation
# (code/upper-bound/out/constants_gp.txt and lemma_check_gp.txt), given as the two arguments
# (compare.sh extracts them through diff). Written after this implementation's outputs were
# committed. Every value of the other implementation is set against the enclosure computed here
# with the functions of lib.sage and the formulas of c1..c5; the grids of section B are taken
# from lemma_check_gp.txt and computed here only for this comparison.
#
# Verdict per value, u = one unit of the last printed digit of the other output:
#   MATCH     the printed decimal is within u/2 of the enclosure (a correct rounding);
#   NEAR      within u (last digit off by one);
#   MISMATCH  farther; the distance is given in units u.
import re

load("lib.sage")

A = open(sys.argv[1]).read().splitlines()
B = open(sys.argv[2]).read().splitlines()
say("compare: this implementation (Arb balls, %d bits) against code/upper-bound/out/{constants_gp,lemma_check_gp}.txt" % PREC)

NUM = r"-?\d+\.\d+(?:\s?e-?\d+)?"
counts = {"MATCH": 0, "NEAR": 0, "MISMATCH": 0}


def line(lines, pat):
    hits = [l for l in lines if re.search(pat, l)]
    if len(hits) != 1:
        raise ValueError("expected one line matching %r, found %d" % (pat, len(hits)))
    return hits[0]


def parse(s):
    """Exact rational of a printed decimal, and the unit u of its last digit."""
    s = s.replace(" ", "")
    m = re.fullmatch(r"(-?)(\d+)\.(\d+)(?:e(-?\d+))?", s)
    if not m:
        raise ValueError("not a decimal: %r" % s)
    sign, ip, fp, ex = m.groups()
    q = ZZ(ip + fp) / 10 ^ len(fp)
    u = QQ(1) / 10 ^ len(fp)
    if ex is not None:
        q, u = q * QQ(10) ^ ZZ(ex), u * QQ(10) ^ ZZ(ex)
    return (-q if sign else q), u


def cmp(name, printed, ball):
    q, u = parse(printed)
    ball = RB(ball)
    d = (ball - q).abs()  # ball of |mine - theirs|
    if d.lower() <= u / 2:
        verdict = "MATCH"
    elif d.lower() <= u:
        verdict = "NEAR"
    else:
        verdict = "MISMATCH"
    counts[verdict] += 1
    extra = ""
    if verdict == "MISMATCH":
        extra = "; |theirs - here| in [%s, %s], agreement to %d decimals" % (
            d.lower().str(digits=3), d.upper().str(digits=3), int(floor(-(d.upper().log10()))))
    say("%-8s %s: theirs %s, here %s, distance %s units of the last digit%s" % (verdict, name, printed, iv(ball, 25), (d.upper() / u).str(digits=3) if d.upper() > 0 else "0", extra))


nums = lambda s: re.findall(NUM, s)

# ---------------------------------------------------------------------------
say("")
say("A. constants_gp.txt")
cmp("e^{-1/2}", nums(line(A, r"^e\^\{-1/2\} ="))[-1], EM)
cmp("E_1(1/2)", nums(line(A, r"^E_1\(1/2\) ="))[-1], E1H)


def J_closed(n):
    return (EM - E1H / 2) / 2 if n == 0 else K_closed(n - 1)


for n in range(5):
    cmp("J_%d" % n, nums(line(A, r"^J_%d =" % n))[-1], J_closed(n))
gl = nums(line(A, r"^Gamma_n, n = 0\.\.6"))
for n in range(7):
    cmp("Gamma_%d" % n, gl[n], Gamma_n(n))
l0 = nums(line(A, r"^Gamma\(0\) ="))
cmp("Gamma(0)", l0[0], Gamma_quad(0))
cmp("2 e^{-1/2}", l0[1], 2 * EM)
for r, pat in [(QQ(1) / 2, r"^Gamma\(0\.5"), (1, r"^Gamma\(1\): series"), (QQ(17) / 10, r"^Gamma\(1\.7"), (QQ(5) / 2, r"^Gamma\(2\.5")]:
    v = nums(line(A, pat))
    cmp("Gamma(%s) series" % r, v[-2], Gamma_series(r))
    cmp("Gamma(%s) quadrature" % r, v[-1], Gamma_quad(r))
cmp("Gamma(1) - Gamma(0)", nums(line(A, r"^Gamma\(1\) - Gamma\(0\)"))[-1], Gamma_series(1) - 2 * EM)


def lemmaA(s0):
    """Lemma 5.2 with the split s_0: L = -log(1-s_0)/s_0, a_0 = 2e^{-(1-s_0)/2}(1 + L/2) - 4J_0,
    a_1 = 2e^{-1/2}(1/2 + L) - 4J_1, a_n = 3e^{-1/2} - 4J_n (n = 2, 3, 4)."""
    s0 = QQ(s0)
    L = -(1 - RB(s0)).log() / s0
    a = [2 * (-(1 - RB(s0)) / 2).exp() * (1 + L / 2) - 4 * J_closed(0), 2 * EM * (QQ(1) / 2 + L) - 4 * J_closed(1)]
    a += [3 * EM - 4 * J_closed(n) for n in (2, 3, 4)]
    f = lambda t: sum(a[n] * t ^ n / factorial(2 * n) for n in range(5))
    fp = lambda t: sum(n * a[n] * t ^ (n - 1) / factorial(2 * n) for n in range(1, 5))
    xl, xh = bisect_root(fp, 0, 8, QQ(2) ^ -200)
    xs = RB(xl).union(RB(xh))
    return L, a, xs, f(xs), s0 * f(xs), f, xh


for s0, tag in [(QQ(1) / 2, "0.5000"), (QQ(3) / 5, "0.6000"), (QQ(2) / 3, "0.6667")]:
    L, a, xs, fm, bd, f, xh = lemmaA(s0)
    l = line(A, r"^Lemma A s0=%s:" % re.escape(tag))
    v = nums(l)
    # v: s0, L0, a_0..a_4, argmax, max f, bound
    cmp("Lemma A s0=%s L0" % tag, v[1], L)
    for n in range(5):
        cmp("Lemma A s0=%s a_%d" % (tag, n), v[2 + n], a[n])
    cmp("Lemma A s0=%s argmax x" % tag, v[7], xs)
    cmp("Lemma A s0=%s max f" % tag, v[8], fm)
    cmp("Lemma A s0=%s s0 max f" % tag, v[9], bd)
    if s0 == QQ(2) / 3:
        yl, yh = bisect_root(f, xh, 20, QQ(2) ^ -220)
        x0 = RB(yl).union(RB(yh))
        v = nums(line(A, r"positive roots of f"))
        cmp("positive root x_0 of f", v[-2], x0)
        cmp("sqrt(x_0)", v[-1], x0.sqrt())


# Lemma B: m, q for the split s_0 (as in c3_lemma61.sage).
class Split:
    def __init__(self, s0):
        self.s0 = QQ(s0)
        self.c0 = (1 - RB(self.s0)).sqrt()
        self.sig0 = RB(self.s0).sqrt()
        self.rstar = (1 / RB(self.s0) - 1).sqrt()
        self.rz = (1 + self.c0) / self.sig0

    def m(self, rho):
        rho = RB(rho)
        if rho <= self.rstar:
            return (1 + rho ^ 2).sqrt()
        if rho >= self.rstar:
            return self.c0 * rho + self.sig0
        raise ValueError("straddle")

    def q(self, rho):
        rho = RB(rho)
        if rho <= self.rstar:
            return RB(1)
        if rho >= self.rstar:
            return -self.s0 * rho ^ 2 + 2 * self.c0 * self.sig0 * rho + self.s0
        raise ValueError("straddle")


NG = 200
GC = [Gamma_n(n) / factorial(2 * n) for n in range(NG + 1)]


def Gam(r):
    x = RB(r) ^ 2
    acc = RB(0)
    for cn in reversed(GC):
        acc = acc * x + cn
    return acc + RB(0).add_error(series_tail(x, NG, 0))


def psi_max(Sp):
    """Golden-section maximizer of psi near the grid maximum (step 1/2000) and the certified
    value there: a certified lower bound of sup psi."""
    h = QQ(1) / 2000
    J = ZZ(ceil((Sp.rz / h).upper()))
    jb = max(range(J + 1), key=lambda j: (Gam(Sp.m(j * h)) - Gam(j * h)).mid())
    a_, b_ = QQ(max(jb - 1, 0)) * h, QQ(min(jb + 1, J)) * h
    for _ in range(80):
        m1, m2 = a_ + (b_ - a_) * QQ(382) / 1000, a_ + (b_ - a_) * QQ(618) / 1000
        if (Gam(Sp.m(m1)) - Gam(m1)).mid() < (Gam(Sp.m(m2)) - Gam(m2)).mid():
            a_ = m1
        else:
            b_ = m2
    rb = (a_ + b_) / 2
    return rb, Gam(Sp.m(rb)) - Gam(rb)


say("  (sup psi: the value here is psi at the maximizer, a certified lower bound of the supremum; the")
say("   certified upper bounds are in out/c3_lemma61.txt, at most 1e-6 above)")
for s0, tag in [(QQ(1) / 2, "0.5000"), (QQ(3) / 5, "0.6000"), (QQ(2) / 3, "0.6667")]:
    Sp = Split(s0)
    rb, val = psi_max(Sp)
    v = nums(line(A, r"^Lemma B s0=%s:" % re.escape(tag)))
    cmp("Lemma B s0=%s sup psi" % tag, v[1], val)
    cmp("Lemma B s0=%s argmax rho" % tag, v[2], RB(rb))
    cmp("Lemma B s0=%s rho_z" % tag, v[3], Sp.rz)

S = Split(QQ(2) / 3)
i0 = [k for k, l in enumerate(A) if l.startswith("Lemma B pieces")]
rows = A[i0[0] + 1:i0[0] + 21]
best = None
for i, l in enumerate(rows, start=1):
    v = nums(l)
    ra, rb = (i - 1) * S.rz / 20, i * S.rz / 20
    qa = S.q(ra)
    g = gprime_series(S.m(rb) ^ 2)
    cmp("piece %2d rho_{i-1}" % i, v[0], ra)
    cmp("piece %2d rho_i" % i, v[1], rb)
    cmp("piece %2d q(rho_{i-1})" % i, v[2], qa)
    cmp("piece %2d g'(m(rho_i)^2)" % i, v[3], g)
    cmp("piece %2d bound" % i, v[4], qa * g)
    b30 = qa * gprime_upper(S.m(rb) ^ 2, 30)
    if best is None or b30.upper() > best.upper():
        best = b30
cmp("Lemma B max piece bound", nums(line(A, r"^Lemma B max piece bound"))[-1], best)
v = nums(line(A, r"^Lemma B with truncation N = 30"))
cmp("Lemma B max piece bound, N = 30 plus tail", v[-2], best)
cmp("Lemma B x max = m(rho_z)^2", v[-1], S.rz ^ 2)


def phi(x):
    x = RB(x)
    return (-x ^ 2 / 2).exp() / SQRT2PI


def Ncdf(x):
    return (1 + (RB(x) / RB(2).sqrt()).erf()) / 2


x = RB(1)
cmp("Lemma C CS bound - rho at rho = 2 (theirs: max over [2, 60])", nums(line(A, r"^Lemma C: max over rho"))[-1],
    2 / Ncdf(x) - 2 + phi(x) / Ncdf(x) ^ 2)
v = nums(line(A, r"^Lemma C analytic"))
cmp("2 phi(1)/N(1)", v[-3], 2 * phi(1) / Ncdf(1))
cmp("phi(1)/N(1)^2", v[-2], phi(1) / Ncdf(1) ^ 2)
cmp("2 phi(1)/N(1) + phi(1)/N(1)^2", v[-1], 2 * phi(1) / Ncdf(1) + phi(1) / Ncdf(1) ^ 2)
v = nums(line(A, r"^Lemma C: exact sqrt"))
for k, rho in enumerate([0, 1, 3, 10]):
    I = (-RB(rho) ^ 2 / 2).exp() * Gamma_quad(rho)
    Is = (-RB(rho) ^ 2 / 2).exp() * Gamma_series(rho)
    check("rho = %d: sqrt(2 pi)/I - rho by quadrature and by the series agree, both radii < 1e-65" % rho,
          (SQRT2PI / I).overlaps(SQRT2PI / Is) and (SQRT2PI / I).rad() < 10 ^ -65 and (SQRT2PI / Is).rad() < 10 ^ -65,
          iv(SQRT2PI / I - rho, 66))
    cmp("sqrt(2 pi)/I(rho) - rho at rho = %d" % rho, v[-4 + k], SQRT2PI / I - rho)
cmp("2 log(3/sqrt(2 pi))", nums(line(A, r"^regret bound"))[-1], 2 * (3 / SQRT2PI).log())
v = nums(line(A, r"^e\^2 ="))
cmp("e^2", v[0], RB(2).exp())
cmp("2 sqrt(2 pi) e^2/3", v[1], 2 * SQRT2PI * RB(2).exp() / 3)
cmp("2 Gamma(0)/3 = 4 e^{-1/2}/3", v[2], 4 * EM / 3)
for l in [l for l in A if l.startswith("T = ")]:
    v = nums(l)
    T = ZZ(re.match(r"T = (\d+)", l).group(1))
    t = RB(T)
    bound = 2 * (RB(2).exp() + (t.sqrt() + 1) * (3 * t + 2 * EM) / SQRT2PI).log()
    eps = 2 / t.sqrt() + (4 * EM / 3) / t + (2 * SQRT2PI * RB(2).exp() / 3) / t ^ (QQ(3) / 2)
    cmp("T = %s bound" % T, v[-3], bound)
    cmp("T = %s bound - 3 log T" % T, v[-2], bound - 3 * t.log())
    cmp("T = %s eps_T = 2/sqrt T + (4e^{-1/2}/3)/T + (2 sqrt(2pi) e^2/3)/T^{3/2}" % T, v[-1], eps)
check("constants_gp.txt ends with FINAL CHECKS: OK", A[-1].strip() == "FINAL CHECKS: OK")

# ---------------------------------------------------------------------------
say("")
say("B. lemma_check_gp.txt (grids read from that file, computed here with certified point values)")
L0 = 3 * RB(3).log() / 2
a = [2 * (-RB(1) / 6).exp() * (1 + L0 / 2) - 4 * J_closed(0), 2 * EM * (QQ(1) / 2 + L0) - 4 * J_closed(1)]
a += [3 * EM - 4 * J_closed(n) for n in (2, 3, 4)]
f = lambda t: sum(a[n] * t ^ n / factorial(2 * n) for n in range(5))
svals = [QQ(1) / 10000, QQ(1) / 1000, QQ(1) / 100, QQ(1) / 20, QQ(1) / 10, QQ(1) / 5, QQ(3) / 10, QQ(2) / 5, QQ(1) / 2, QQ(3) / 5, QQ(13) / 20, QQ(2) / 3]
rhos = [QQ(k) / 10 for k in range(61)]
t0 = time.time()
G = {rho: Gam(rho) for rho in rhos}
best1, best2 = None, None
npts = 0
for rho in rhos:
    for s in svals:
        E = Ghat_quad(rho, s) - G[rho]
        D = E - s * f(RB(rho) ^ 2)
        npts += 1
        if best1 is None or D.mid() > best1[0].mid():
            best1 = (D, rho, s)
        if best2 is None or E.mid() > best2[0].mid():
            best2 = (E, rho, s)
say("Lemma 5.2 grid: %d points, %.1f s" % (npts, time.time() - t0))
check("Lemma 5.2 grid: E - s f(rho^2) < 0 at every grid point (max certified negative)", best1[0] < 0, iv(best1[0], 12))
l = line(B, r"max of E - s f")
cmp("Lemma 5.2 grid max of E - s f(rho^2)", re.findall(NUM, l)[0], best1[0])
say("   argmax here (rho, s) = (%s, %s); theirs: %s" % (best1[1], best1[2], l.split(" at ")[-1]))
l = line(B, r"max of E = ")
cmp("Lemma 5.2 grid max of E", re.findall(NUM, l)[0], best2[0])
say("   argmax here (rho, s) = (%s, %s); theirs: %s" % (best2[1], best2[2], l.split(" at ")[-1]))
t0 = time.time()
srange = [QQ(2) / 3 + QQ(k) / 300 for k in range(101)]
rhos2 = [QQ(k) / 50 for k in range(301)]
G2 = {rho: Gam(rho) for rho in rhos2}
best3 = None
for s in srange:
    c, sg = (1 - RB(s)).sqrt(), RB(s).sqrt()
    for rho in rhos2:
        D = Gam(rho * c + sg) - G2[rho]
        if best3 is None or D.mid() > best3[0].mid():
            best3 = (D, rho, s)
say("Lemma 6.1 grid: %d points, %.1f s" % (len(srange) * len(rhos2), time.time() - t0))
check("Lemma 6.1 grid: max of Gamma(rho c + sigma) - Gamma(rho) < 2.7053", best3[0] < QQ(27053) / 10000, iv(best3[0], 12))
l = line(B, r"max of Gamma\(rho c")
cmp("Lemma 6.1 grid max of Gamma(rho c + sigma) - Gamma(rho)", re.findall(NUM, l)[0], best3[0])
say("   argmax here (rho, s) = (%s, %s); theirs: %s" % (best3[1], best3[2], l.split(" at ")[-1]))
check("lemma_check_gp.txt ends with DONE", B[-1].strip() == "DONE")

say("")
say("COMPARISON: %d MATCH, %d NEAR, %d MISMATCH" % (counts["MATCH"], counts["NEAR"], counts["MISMATCH"]))
finish()
