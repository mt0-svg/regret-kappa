# c1_gamma.sage: Lemma 3.4 (b) and (c) of the paper, item (1) of Computation 3.13 (Lemma 2.1 in the outputs).
#   (c) closed forms of Gamma_n through K_m, against certified quadrature, n = 0..6;
#       Gamma(0) = 2 e^{-1/2}; Gamma(1) by quadrature and by the series (b);
#   (d) Gamma_n <= 2^{n+1} (n-1)! and n Gamma_n/(2n)! <= 2/n!, n = 1..60, and the
#       ingredient K_m <= 2^{m-1} (m-1)!, m = 1..60.
load("lib.sage")

say("c1_gamma: Lemma 2.1, %d-bit balls" % PREC)
say("e^{-1/2}  =", iv(EM, 30))
say("E_1(1/2)  =", iv(E1H, 30))

say("")
say("(c) Gamma_n: closed form 2(K_n + 2K_{n-1}) (K_0 = E_1(1/2)/2) against quadrature of")
say("    2 int_1^oo t^{2n} e^{-t^2/2} (1/t + 2/t^3) dt")
for n in range(7):
    gc = Gamma_n(n)
    gq = Gamma_n_quad(n)
    if n == 0:
        form = "2 e^{-1/2}"
        gc2 = 2 * (K_closed(0) + 2 * ((EM - E1H / 2) / 2))  # 2(J_1 + 2 J_0), J_0 = (e^{-1/2} - J_1)/2
    elif n == 1:
        form = "2 e^{-1/2} + 2 E_1(1/2)"
        gc2 = 2 * (K_closed(1) + 2 * K_closed(0))
    else:
        form = "%s e^{-1/2}" % Gamma_n_coef(n)
        gc2 = 2 * (K_closed(n) + 2 * K_closed(n - 1))
    say("  Gamma_%d = %s" % (n, form))
    say("     closed %s" % iv(gc, 30))
    say("     quad   %s" % iv(gq, 30))
    check("Gamma_%d closed form = quadrature" % n, gc.overlaps(gq) and gc2.overlaps(gq) and gq.rad() < 10 ^ -50)
check("Gamma_2, Gamma_3, Gamma_4 = 10, 38, 210 times e^{-1/2}",
      [Gamma_n_coef(n) for n in (2, 3, 4)] == [10, 38, 210])
check("NEG Gamma_3 = 37 e^{-1/2} is refuted by quadrature", disjoint(37 * EM, Gamma_n_quad(3)))

say("")
G0q = Gamma_quad(0)
check("Gamma(0) = 2 e^{-1/2} (quadrature of Gamma at r = 0)", G0q.overlaps(2 * EM), iv(G0q, 30))
G1q = Gamma_quad(1)
G1s = Gamma_series(1)
say("Gamma(1) quadrature", iv(G1q, 30))
say("Gamma(1) series    ", iv(G1s, 30))
check("Gamma(1): series (b) with closed forms = quadrature", G1q.overlaps(G1s) and G1q.rad() < 10 ^ -50)
D = G1s - 2 * EM
say("Gamma(1) - Gamma(0) =", iv(D, 30))
for r in [QQ(1) / 2, 1, QQ(17) / 10, QQ(5) / 2]:
    a, b = Gamma_series(r), Gamma_quad(r)
    check("Gamma(%s): series = quadrature, |difference| < 1e-60" % r, small(a - b, QQ(10) ^ -60), iv(a, 25))

say("")
say("(d) bounds, n = 1..60, from the closed forms (every comparison certified, strict)")
worst = None
for n in range(1, 61):
    g = Gamma_n(n)
    ok1 = g < 2 ^ (n + 1) * factorial(n - 1)
    ok2 = n * g / factorial(2 * n) < RB(2) / factorial(n)
    ratio = g / (2 ^ (n + 1) * factorial(n - 1))
    if worst is None or ratio.upper() > worst[1].upper():
        worst = (n, ratio)
    if not (ok1 and ok2):
        check("Gamma_%d bounds" % n, False, iv(g))
check("Gamma_n < 2^{n+1} (n-1)! and n Gamma_n/(2n)! < 2/n! for n = 1..60",
      all(Gamma_n(n) < 2 ^ (n + 1) * factorial(n - 1) and n * Gamma_n(n) / factorial(2 * n) < RB(2) / factorial(n)
          for n in range(1, 61)),
      "largest Gamma_n / (2^{n+1}(n-1)!) = %s at n = %d" % (up(worst[1]), worst[0]))
for n in [1, 2, 3, 10, 30, 60]:
    say("  n = %2d: Gamma_n / (2^{n+1} (n-1)!) in %s" % (n, iv(Gamma_n(n) / (2 ^ (n + 1) * factorial(n - 1)), 15)))
# The margin of K_m < 2^{m-1}(m-1)! is e^{-1/2} sum_{j>=m} 2^-j/j!, about 1e-100 relative at m = 60,
# below 256 bits: this check runs in 2048-bit balls.
RB2 = RealBallField(2048)
EM2 = RB2(-1 / 2).exp()
check("K_m < 2^{m-1} (m-1)! for m = 1..60 (the step of (d): sum_{j<m} 2^-j/j! < e^{1/2}), 2048-bit balls",
      all(K_coef(m) * EM2 < 2 ^ (m - 1) * factorial(m - 1) for m in range(1, 61)))
check("(2n)! >= 2^n (n!)^2 for n = 1..60 (exact integers)",
      all(factorial(2 * n) >= 2 ^ n * factorial(n) ^ 2 for n in range(1, 61)))
check("Gamma_n > 0 for n = 0..60", all(Gamma_n(n) > 0 for n in range(61)))
check("NEG the sharper Gamma_n < 2^n (n-1)! fails (refuted at n = 1)", Gamma_n(1) > 2 ^ 1 * factorial(0), iv(Gamma_n(1)))

finish()
