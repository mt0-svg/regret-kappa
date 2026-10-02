# c3_large_steps.sage: Lemma A.8 of the paper on the twenty pieces [(i-1) rho_z/20, i rho_z/20].
#   The 20 piece bounds q(rho_{i-1}) g'(m(rho_i)^2), rho_i = i rho_z/20, with g' bounded by the
#   truncated series (N = 30) plus the tail bound 2x^30/(31!(1 - x/32)), and the largest piece bound.
load("lib.sage")

say("c3_large_steps: Lemma A.8, %d-bit balls" % PREC)


class Split:
    """The functions m and q of the proof of Lemma A.8 for the split s_0."""

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


# ---------------------------------------------------------------------------
say("")
say("Tail bound: sum_{n>30} n Gamma_n x^{n-1}/(2n)! <= sum_{n>30} 2 x^{n-1}/n! (Lemma A.1 (c))")
say("  <= 2 x^30/31! sum_k (x/32)^k = 2 x^30/(31! (1 - x/32)) for 0 <= x < 32 (method: analytic)")
X = 2 + RB(3).sqrt()
tb = series_tail(X, 30, 1)
check("tail formula: series_tail(x, 30, 1) = 2 x^30 / (31! (1 - x/32)) at x = 2 + sqrt 3",
      tb.overlaps(2 * X ^ 30 / factorial(31) / (1 - X / 32)), "bound %s" % iv(tb, 12))
check("1 - x/32 > 0 at x = 2 + sqrt 3", 1 - X / 32 > 0)

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
check("every piece bound < 3 (Lemma A.8, below the increment 3)", all(p[6] < 3 for p in pieces), "margin >= %s" % lo(3 - Bmax, 8))
check("every piece bound <= 2.7053 (Lemma A.8 as stated)", all(p[6] <= QQ(27053) / 10000 for p in pieces))
check("NEG every piece bound <= 2.7052 is refuted by the largest piece", Bmax > QQ(27052) / 10000)
check("largest piece is [1.1591, 1.2557] (i = 13)", best[0] == 13)

finish()
