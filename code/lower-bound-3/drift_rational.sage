# Lemma 3.1 (b), the certificate of the note redone in exact rational arithmetic (Sage QQ).
# On [lo, hi] inside cell j (move s = s_j), 8 h_s - g - 1 >= the rational number
#   8 P_N((lo^2 (1-s) + s)/2) C_N(lo^2 s (1-s)) - 8 E_N(hi^2/2) - 1,
# P_N(q) = sum_{n<=N} q^n/n!, C_N(y) = sum_{n<=N} y^n/(2n)!,
# E_N(q) = P_N(q) + q^(N+1) (N+2) / ((N+1)! (N+2-q)), valid for 0 <= q < N+2.
# Each cell is bisected until the number is >= 0. No floating point enters a decision.
# Run from this directory: sage drift_rational.sage

load("common.sage")
load("rational_lib.sage")
import time

C = Checker("drift_rational")

print("== known-answer tests of the series bounds (against Arb at 2000 bits)")
R2 = RealBallField(2000)
ok = True
for q in [QQ(0), QQ(1) / 7, QQ(1), QQ(3), QQ(392) / 100, QQ(5), QQ(20)]:
    ok = ok and R2(P(q)) <= R2(q).exp() and R2(q).exp() <= R2(E(q))
C.check("P_40(q) <= e^q <= E_40(q) at 7 points of [0, 20]", ok)
ok = True
for q in [QQ(1) / 3, QQ(2), QQ(392) / 100]:
    ok = ok and R2(P(q, 5)) < R2(q).exp() and R2(q).exp() <= R2(E(q, 5))
C.check("P_5(q) < e^q <= E_5(q) (low order, tail term active)", ok)
ok = True
for y in [QQ(0), QQ(1) / 5, QQ(2), QQ(9)]:
    ok = ok and R2(Cc(y)) <= R2(y).sqrt().cosh()
C.check("C_40(y) <= cosh(sqrt(y)) at 4 points", ok)
C.check("C_3(4) = 1 + 4/2 + 16/24 + 64/720", Cc(QQ(4), 3) == 1 + QQ(4) / 2 + QQ(16) / 24 + QQ(64) / 720)
C.check("E_5(1) = P_5(1) + 7/(720*6)", E(QQ(1), 5) == P(QQ(1), 5) + QQ(7) / (720 * 6))
C.check("negative control: the tail bound without geometric factor fails at q = 3.92, N = 5",
        R(E_wrong(QQ(392) / 100, 5)) < R(QQ(392) / 100).exp())
# The bound never exceeds the true drift lower end: compare with Arb on random subintervals.
load("drift_lib.sage")
set_random_seed(1)
ok = True
for i in range(100):
    j = randint(0, 27)
    a = QQ(j) / 10 + QQ(randint(0, 900)) / 10000
    b = a + QQ(randint(1, 100)) / 10000
    ok = ok and R(bound(a, b, MOVES[j])) < drift_direct(R(a), R(MOVES[j]), R(K_G))
C.check("rational bound <= drift at the left end, 100 random pieces", ok)

print("== certificate on [0, 2.8), N = %d, g = %d exp(rho^2/2)" % (N, K_G))
t0 = time.time()
tot, dmax, allok = 0, 0, True
worst = None
for j in range(NCELLS):
    ok, leaves, info = certify_cell(j, MOVES)
    allok = allok and ok
    tot += len(leaves)
    d = max(l[2] for l in leaves)
    dmax = max(dmax, d)
    w = min(leaves, key=lambda l: l[3])
    if worst is None or w[3] < worst[3]:
        worst = w
    print("cell %2d: s = %s, %s, %3d subintervals, depth <= %d, least margin %.6e on [%s, %s]" %
          (j, MOVES[j], "certified" if ok else "NOT certified", len(leaves), d, float(w[3]), w[0], w[1]))
    sys.stdout.flush()
print("total %d subintervals, at most %d bisections, smallest margin %.6e = %s... on [%s, %s], "
      "time %.1f s" % (tot, dmax, float(worst[3]), str(float(worst[3]))[:10], worst[0], worst[1],
                       time.time() - t0))
C.check("every cell certified with exact rationals", allok)
C.check("1128 subintervals (note: 1128)", tot == 1128, str(tot))
C.check("at most 7 bisections (note: 7)", dmax == 7, str(dmax))
C.check("smallest margin rounds to 7.2e-4 (note: 7.2e-4)",
        QQ(715) / 10 ** 6 <= worst[3] < QQ(725) / 10 ** 6, "%.6e" % float(worst[3]))
C.finish(11)
