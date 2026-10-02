# Lemmas 4.5 to 4.7 of the paper (3.2 to 3.4 in the outputs): the numbers they rest on.
# Lemma 3.3: a step from |rho| < a lands in |rho'| <= a+ = a + sqrt(5/8) exp(-L/4) when
# L >= 14.5, and G = 8 exp((a+)^2/2) <= 8.8 exp(L/2). Lemma 3.2 and 3.4: n = ceil(e G) gives
# G/n <= 1/e and n <= e G + 1. Symbolic identities by Sage, numbers by Arb balls.
# Run from this directory: sage phase1_constants.sage

load("common.sage")
load("lb_lib.sage")

C = Checker("phase1_constants")
var('u L')

print("== Lemma 3.3, a step from |rho| < 2.8 (move table)")
# For fixed s, |rho| sqrt(1-s) + sqrt(s) increases with |rho|; on cell j its sup is at (j+1)/10.
steps = [(QQ(j + 1) / 10) * R(1 - MOVES[j]).sqrt() + R(MOVES[j]).sqrt() for j in range(NCELLS)]
jm = max(range(NCELLS), key=lambda j: steps[j].mid())
print("max over cells of ((j+1)/10) sqrt(1 - s_j) + sqrt(s_j) = %s (cell %d)" % (steps[jm].mid().n(digits=8), jm))
C.check("one step from |rho| < 2.8 stays below 3.8", all(x < R(QQ(38) / 10) for x in steps),
        "%.6f" % steps[jm].mid())
C.check("crude bound 2.8 + sqrt(max s_j) <= 3.8", R(QQ(28) / 10) + R(max(MOVES)).sqrt() <= R(QQ(38) / 10),
        "%.6f" % (R(QQ(28) / 10) + R(max(MOVES)).sqrt()).mid())
C.check("3.8^2 = 14.44 <= 14.5, so a >= 3.8 when L >= 14.5", QQ(38) ** 2 / 100 == QQ(1444) / 100 and QQ(1444) / 100 <= QQ(145) / 10)

print("== Lemma 3.3, a step from 2.8 <= |rho| < a: u -> u + sqrt(5/8) exp(-u^2/4) is increasing")
q = (u / 2) * exp(-u ** 2 / 4)
dq = diff(q, u)
C.check("d/du (u/2) e^{-u^2/4} = (1/2) e^{-u^2/4} (1 - u^2/2)",
        bool((dq - exp(-u ** 2 / 4) * (1 - u ** 2 / 2) / 2).simplify_full() == 0))
qmax = (R(2).sqrt() / 2) * R(-QQ(1) / 2).exp()
C.check("max over u >= 0 of (u/2) e^{-u^2/4} is e^{-1/2}/sqrt(2) (at u = sqrt 2)",
        qmax.overlaps(R(-QQ(1) / 2).exp() / R(2).sqrt()))
dmin = 1 - R(QQ(5) / 8).sqrt() * qmax
print("1 - sqrt(5/8) e^{-1/2}/sqrt(2) = %s" % dmin.mid().n(digits=8))
C.check("derivative of u + sqrt(5/8) e^{-u^2/4} is >= 1 - sqrt(5/8) e^{-1/2}/sqrt 2 > 0", dmin > 0)
C.check("sqrt(s(rho)) = sqrt(5/8) e^{-rho^2/4} for s = (5/8) e^{-rho^2/2}",
        bool((sqrt(QQ(5) / 8 * exp(-u ** 2 / 2)) - sqrt(QQ(5) / 8) * exp(-u ** 2 / 4)).simplify_full() == 0))

print("== Lemma 3.3, the constant G")
a_sym = sqrt(L)
ap = a_sym + sqrt(QQ(5) / 8) * exp(-L / 4)
epsL_sym = sqrt(5 * L / 8) * exp(-L / 4) + QQ(5) / 16 * exp(-L / 2)
C.check("(a+)^2/2 = L/2 + sqrt(5L/8) e^{-L/4} + (5/16) e^{-L/2}",
        bool((ap ** 2 / 2 - L / 2 - epsL_sym).simplify_full() == 0))
depsL = diff(epsL_sym, L)
target = sqrt(QQ(5) / 8) * exp(-L / 4) * (1 / (2 * sqrt(L)) - sqrt(L) / 4) - QQ(5) / 32 * exp(-L / 2)
C.check("d eps_L/dL = sqrt(5/8) e^{-L/4} (1/(2 sqrt L) - sqrt(L)/4) - (5/32) e^{-L/2}",
        bool((depsL - target).simplify_full() == 0))
# 1/(2 sqrt L) - sqrt(L)/4 = (2 - L)/(4 sqrt L) <= 0 for L >= 2, so eps_L decreases on [2, oo).
C.check("1/(2 sqrt L) - sqrt(L)/4 = (2 - L)/(4 sqrt L)",
        bool((1 / (2 * sqrt(L)) - sqrt(L) / 4 - (2 - L) / (4 * sqrt(L))).simplify_full() == 0))
e145 = eps_L(QQ(145) / 10)
print("eps_14.5 = %s, log(1.1) = %s" % (e145.mid().n(digits=8), R(QQ(11) / 10).log().mid().n(digits=8)))
C.check("eps_14.5 rounds to 0.0804 (note: 0.0804)", abs(e145 - R(QQ(804) / 10000)) < R(QQ(5) / 10 ** 5),
        "%.6f" % e145.mid())
C.check("eps_14.5 <= log(1.1), so G = 8 exp((a+)^2/2) <= 8.8 exp(L/2) for L >= 14.5",
        e145 <= R(QQ(11) / 10).log())
# the same at a grid of L (redundant with the monotonicity)
C.check("8 exp((a+)^2/2) <= 8.8 exp(L/2) at L = 14.5, 14.6, ..., 60 (ball check)",
        all(8 * (aplus_of(QQ(l) / 10) ** 2 / 2).exp() <= R(QQ(88) / 10) * (R(QQ(l) / 20)).exp()
            for l in range(145, 601)))
C.check("sqrt(5/8) e^{-14.5/4} <= 0.022 (used in (C3))",
        R(QQ(5) / 8).sqrt() * R(-QQ(145) / 40).exp() <= R(QQ(22) / 1000),
        "%.6f" % (R(QQ(5) / 8).sqrt() * R(-QQ(145) / 40).exp()).mid())

print("== Lemmas 3.2 and 3.4: n = ceil(e G)")
ok = True
for l in [145, 150, 200, 300, 500]:
    G = R(QQ(88) / 10) * R(QQ(l) / 20).exp()
    n = unique_ceil(E1 * G)
    ok = ok and (G / n <= (-R(1)).exp()) and (R(n) <= E1 * G + 1)
C.check("G/n <= 1/e and n <= e G + 1 at L = 14.5, 15, 20, 30, 50", ok)
C.check("(G/n)^j0 <= e^{-j0} for j0 = 1..10 at L = 14.5",
        all((R(QQ(88) / 10) * R(QQ(145) / 20).exp() / unique_ceil(E1 * R(QQ(88) / 10) * R(QQ(145) / 20).exp())) ** j
            <= (-R(j)).exp() for j in range(1, 11)))
C.finish(16)
