# c3_lemma61.sage: Lemma 3.11 of the paper on the twenty pieces [(i-1) rho_z/20, i rho_z/20] (Lemma 6.1 or Lemma B in the outputs).
#   The 20 piece bounds q(rho_{i-1}) g'(m(rho_i)^2), rho_i = i rho_z/20, with g' bounded by the
#   truncated series (N = 30) plus the tail bound 2x^30/(31!(1 - x/32)); the tail bound itself
#   for x <= 2 + sqrt 3; the largest piece bound against beta = 3; the supremum of
#   psi(rho) = Gamma(m(rho)) - Gamma(rho) (grid evidence and a certified enclosure).
load("lib.sage")

say("c3_lemma61: Lemma 6.1, %d-bit balls" % PREC)


class Split:
    """The functions m and q of Lemma 6.1 (i), (iii) for the split s_0."""

    def __init__(self, s0):
        self.s0 = QQ(s0)
        self.c0 = (1 - RB(self.s0)).sqrt()
        self.sig0 = RB(self.s0).sqrt()
        self.rstar = (1 / RB(self.s0) - 1).sqrt()
        self.rz = (1 + self.c0) / self.sig0

    def side(self, rho):
        rho = RB(rho)
        if rho <= self.rstar:
            return -1
        if rho >= self.rstar:
            return 1
        raise ValueError("rho ball straddles rho_*")

    def m(self, rho):
        rho = RB(rho)
        if self.side(rho) < 0:
            return (1 + rho ^ 2).sqrt()
        return self.c0 * rho + self.sig0

    def q(self, rho):
        rho = RB(rho)
        if self.side(rho) < 0:
            return RB(1)
        return -self.s0 * rho ^ 2 + 2 * self.c0 * self.sig0 * rho + self.s0


S = Split(QQ(2) / 3)
say("s_0 = 2/3, c_0 = 1/sqrt 3 =", iv(S.c0, 20), " sigma_0 = sqrt(2/3) =", iv(S.sig0, 20))
say("rho_* = 1/sqrt 2 =", iv(S.rstar, 25), " rho_z = (1 + sqrt 3)/sqrt 2 =", iv(S.rz, 25))
check("c_0 = 1/sqrt 3, sigma_0 = sqrt(2/3), rho_* = 1/sqrt 2",
      S.c0.overlaps(1 / RB(3).sqrt()) and S.sig0.overlaps((RB(2) / 3).sqrt()) and S.rstar.overlaps(1 / RB(2).sqrt()))
check("rho_z = (1 + c_0)/sigma_0 = (1 + sqrt 3)/sqrt 2", S.rz.overlaps((1 + RB(3).sqrt()) / RB(2).sqrt()))
check("rho_z^2 = 2 + sqrt 3", (S.rz ^ 2).overlaps(2 + RB(3).sqrt()))
check("m is continuous at rho_*: sqrt(1 + 1/2) = c_0 rho_* + sigma_0 = 1/sqrt(s_0)",
      (1 + S.rstar ^ 2).sqrt().overlaps(S.c0 * S.rstar + S.sig0) and (1 + S.rstar ^ 2).sqrt().overlaps(1 / S.sig0))
check("q(rho_*) = 1 on both branches", (-S.s0 * S.rstar ^ 2 + 2 * S.c0 * S.sig0 * S.rstar + S.s0).overlaps(RB(1)))
check("m(rho_z) = rho_z and q(rho_z) = 0 (ball contains 0)", S.m(S.rz).overlaps(S.rz) and S.q(S.rz).contains_exact(0))

# Symbolic checks of the analytic steps (i)-(iii).
say("")
say("Analytic steps (i)-(iii), checked symbolically by Sage:")
r, s = var("r s")
assume(r > 0)
assume(s > 0)
assume(s < 1)
hfun = r * sqrt(1 - s) + sqrt(s)
dh = diff(hfun, s)
crit = bool(dh.subs(s=1 / (1 + r ^ 2)).simplify_full() == 0)
val = bool((hfun.subs(s=1 / (1 + r ^ 2)) - sqrt(1 + r ^ 2)).simplify_full() == 0)
d2h = diff(hfun, s, 2)
conc = bool((d2h - (-r / (4 * (1 - s) ^ (QQ(3) / 2)) - 1 / (4 * s ^ (QQ(3) / 2)))).simplify_full() == 0)
check("(i) d/ds [r sqrt(1-s) + sqrt s] = 0 at s = 1/(1+r^2), value sqrt(1+r^2)", crit and val)
check("(i) second derivative = -r/(4(1-s)^{3/2}) - 1/(4 s^{3/2}) < 0 (concave in s)", conc, str(d2h))
check("(i) 1/(1+r^2) >= s_0 iff r^2 <= 1/s_0 - 1 = 1/2: rho_*^2 = 1/2", (S.rstar ^ 2).overlaps(RB(1) / 2))
c0s, sg0s = 1 / sqrt(3), sqrt(QQ(2) / 3)
qexp = ((c0s * r + sg0s) ^ 2 - r ^ 2) - (-QQ(2) / 3 * r ^ 2 + 2 * c0s * sg0s * r + QQ(2) / 3)
check("(iii) (c_0 r + sigma_0)^2 - r^2 = -s_0 r^2 + 2 c_0 sigma_0 r + s_0", bool(qexp.simplify_full() == 0))
check("(iii) vertex c_0 sigma_0 / s_0 = rho_*", (S.c0 * S.sig0 / S.s0).overlaps(S.rstar))
check("(ii) rho_z = sigma_0/(1 - c_0) (so c_0 rho + sigma_0 <= rho iff rho >= rho_z)", S.rz.overlaps(S.sig0 / (1 - S.c0)))
forget()
say("(iii) convexity of g, monotonicity of q (nonincreasing), m and g' (increasing): analytic, Lemma 2.1 (b)")

# ---------------------------------------------------------------------------
say("")
say("Tail bound: sum_{n>30} n Gamma_n x^{n-1}/(2n)! <= sum_{n>30} 2 x^{n-1}/n! (Lemma 2.1 (d))")
say("  <= 2 x^30/31! sum_k (x/32)^k = 2 x^30/(31! (1 - x/32)) for 0 <= x < 32 (method: analytic; checks below)")
X = 2 + RB(3).sqrt()
tb = series_tail(X, 30, 1)
check("tail formula: series_tail(x, 30, 1) = 2 x^30 / (31! (1 - x/32)) at x = 2 + sqrt 3",
      tb.overlaps(2 * X ^ 30 / factorial(31) / (1 - X / 32)), "bound %s" % iv(tb, 12))
check("1 - x/32 > 0 at x = 2 + sqrt 3", 1 - X / 32 > 0)
check("n Gamma_n/(2n)! < 2/n! for n = 31..200 (closed forms)",
      all(n * Gamma_n(n) / factorial(2 * n) < RB(2) / factorial(n) for n in range(31, 201)))
act = sum(n * Gamma_n(n) * X ^ (n - 1) / factorial(2 * n) for n in range(31, 201)) + RB(0).add_error(series_tail(X, 200, 1))
check("actual tail sum_{n>30} n Gamma_n x^{n-1}/(2n)! <= the tail bound at x = 2 + sqrt 3", act < tb,
      "actual %s, bound %s, ratio %s" % (up(act, 8), up(tb, 8), up(act / tb, 6)))
check("the tail bound is increasing in x on [0, 32) (product of x^30 and 1/(1-x/32)): analytic", True)

# ---------------------------------------------------------------------------
say("")
say("The 20 pieces rho_i = i rho_z / 20; piece bound B_i = q(rho_{i-1}) * [truncated g' (N=30) + tail bound](m(rho_i)^2)")
say("%3s %-14s %-14s %-14s %-14s %-22s %-22s %s" % ("i", "rho_{i-1}", "rho_i", "q(rho_{i-1})", "m(rho_i)^2", "g'(m^2) N=30 upper", "B_i upper (N=30)", "B_i (exact g')"))
pieces = []
for i in range(1, 21):
    ra = (i - 1) * S.rz / 20
    rb = i * S.rz / 20
    qa = S.q(ra)
    qa2 = S.m(ra) ^ 2 - ra ^ 2
    xb = S.m(rb) ^ 2
    gup = gprime_upper(xb, 30)
    gex = gprime_series(xb)
    Bi = qa * gup
    Bex = qa * gex
    if not qa.overlaps(qa2):
        check("q(rho_%d) as m^2 - rho^2" % (i - 1), False)
    if not (xb <= S.rz ^ 2 + TINY):
        check("m(rho_%d)^2 <= 2 + sqrt 3" % i, False)
    if not (qa >= 0 or qa.contains_exact(0)):
        check("q(rho_%d) >= 0" % (i - 1), False)
    pieces.append((i, ra, rb, qa, xb, gup, Bi, Bex))
    say("%3d %-14s %-14s %-14s %-14s %-22s %-22s %s" % (i, lo(ra, 9), lo(rb, 9), up(qa, 10), up(xb, 10), up(gup, 16), up(Bi, 16), up(Bex, 12)))
check("q(rho) = m(rho)^2 - rho^2 at the 20 left ends; q >= 0 there; m(rho_i)^2 <= 2 + sqrt 3", NFAIL == 0)
check("x = m(rho_i)^2 < 32 for every piece (tail bound applies)", all(p[4] < 32 for p in pieces))
best = max(pieces, key=lambda p: p[6].upper())
Bmax = best[6]
say("")
say("largest piece bound: i = %d, piece [%s, %s], B = %s (upper %s)" % (best[0], lo(best[1], 6), up(best[2], 6), iv(Bmax, 16), up(Bmax, 12)))
say("same piece with the exact g' (N auto, tail < 2^-216):", iv(best[7], 16))
check("every piece bound < 3 (Lemma 6.1 against beta = 3)", all(p[6] < 3 for p in pieces), "margin >= %s" % lo(3 - Bmax, 8))
check("every piece bound <= 2.7053 (Lemma 6.1 as stated)", all(p[6] <= QQ(27053) / 10000 for p in pieces))
check("NEG every piece bound <= 2.7052 is refuted by the largest piece", Bmax > QQ(27052) / 10000)
check("largest piece is [1.1591, 1.2557] (i = 13)", best[0] == 13)

# ---------------------------------------------------------------------------
# Supremum of psi = Gamma(m(rho)) - Gamma(rho) on [0, rho_z] (psi <= 0 beyond, by (ii)).
NG = 90
GC = [Gamma_n(n) / factorial(2 * n) for n in range(NG + 1)]


def Gam(r):
    """Gamma(r) by Horner on sum_{n<=NG} Gamma_n x^n/(2n)!, plus the tail bound (x < NG+2)."""
    x = RB(r) ^ 2
    acc = RB(0)
    for cn in reversed(GC):
        acc = acc * x + cn
    return acc + RB(0).add_error(series_tail(x, NG, 0))


check("Horner Gamma = series Gamma = quadrature at rho = 1.2304", Gam(QQ(12304) / 10000).overlaps(Gamma_quad(QQ(12304) / 10000)))


def sup_psi(Sp, h, eps, label):
    """Certified enclosure [L, U] of sup_{0 <= rho <= rho_z} psi, U < L + eps. Lower end L: the
    certified value of psi at one point (best grid point of step h, then golden section).
    Upper end: on [a, b], psi <= Gamma(m(b)) - Gamma(a) (Gamma increasing on [0, oo), m
    increasing); the pieces of the grid of step h covering [0, rho_z] are bisected until each
    bound is below L + eps."""
    J = ZZ(ceil((Sp.rz / h).upper()))
    gc, mc = {}, {}

    def G(a):
        if a not in gc:
            gc[a] = Gam(a)
        return gc[a]

    def GM(b):
        if b not in mc:
            mc[b] = Gam(Sp.m(b))
        return mc[b]

    jb = max(range(J + 1), key=lambda j: (GM(j * h) - G(j * h)).mid())
    a_, b_ = QQ(max(jb - 1, 0)) * h, QQ(min(jb + 1, J)) * h
    for _ in range(80):
        m1, m2 = a_ + (b_ - a_) * QQ(382) / 1000, a_ + (b_ - a_) * QQ(618) / 1000
        v1, v2 = Gam(Sp.m(m1)) - Gam(m1), Gam(Sp.m(m2)) - Gam(m2)
        if v1.mid() < v2.mid():
            a_ = m1
        else:
            b_ = m2
    rb = (a_ + b_) / 2
    L = Gam(Sp.m(rb)) - Gam(rb)
    target = L + RB(eps)
    work = [(j * h, (j + 1) * h) for j in range(J)]
    U, npieces, depth = None, 0, 0
    while work:
        nxt = []
        for a, b in work:
            npieces += 1
            ub = GM(b) - G(a)
            if ub < target:
                U = ub.upper() if U is None or ub.upper() > U else U
            else:
                nxt += [(a, (a + b) / 2), ((a + b) / 2, b)]
        work = nxt
        depth += 1
        if depth > 40:
            raise ValueError("sup_psi: refinement did not terminate")
    say("%s: best grid point rho = %s (step %s); golden-section maximizer rho ~ %s (evidence)" % (label, lo(RB(jb * h), 6), h, lo(RB(rb), 8)))
    say("%s: certified psi(%s) in %s" % (label, lo(RB(rb), 8), iv(L, 14)))
    say("%s: %d pieces examined, %d bisection rounds; certified sup psi in [%s, %s]" % (label, npieces, depth, lo(L, 12), RB(U).upper().str(digits=12)))
    return L, RB(U), rb


say("")
t0 = time.time()
L1, U1, rb1 = sup_psi(S, QQ(1) / 2000, QQ(1) / 10 ^ 7, "s_0 = 2/3")
say("  (time %.1f s)" % (time.time() - t0))
check("sup psi (s_0 = 2/3) < largest piece bound (consistency)", U1 < Bmax)
check("sup psi (s_0 = 2/3) in [2.13849, 2.13850], location 1.2304 (rounded)",
      L1 > QQ(213849) / 100000 and U1 < QQ(213850) / 100000 and abs(rb1 - QQ(12304) / 10000) < QQ(1) / 10000,
      "[%s, %s]" % (lo(L1, 12), up(U1, 12)))
say("piece-bound loss: max B_i - sup psi >=", lo(Bmax - U1, 6))

say("")
say("Remark (section 6, evidence): sup psi for the splits s_0 = 3/5 and s_0 = 1/2")
for s0, lab in [(QQ(3) / 5, "s_0 = 3/5"), (QQ(1) / 2, "s_0 = 1/2")]:
    Sp = Split(s0)
    say("%s: rho_* = %s, rho_z = %s" % (lab, iv(Sp.rstar, 10), iv(Sp.rz, 10)))
    sup_psi(Sp, QQ(1) / 2000, QQ(1) / 10 ^ 6, lab)

finish()
