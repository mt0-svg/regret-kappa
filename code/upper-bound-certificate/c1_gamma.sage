# c1_gamma.sage: Lemma A.1 (a) and (b) of the paper and item (1) of Computation A.9.
#   The enclosures of K_0 and e^{-1/2} of item (1); the closed forms of Gamma_n through K_m
#   against certified quadrature, n = 0..6; Gamma(0) = 2 e^{-1/2}.
load("lib.sage")

say("c1_gamma: Lemma A.1, %d-bit balls" % PREC)
say("e^{-1/2}  =", iv(EM, 30))
say("E_1(1/2)  =", iv(E1H, 30))
say("K_0 = E_1(1/2)/2 =", iv(E1H / 2, 30))
check("item (1): 0.2798867 <= K_0 <= 0.2798869", QQ(2798867) / 10 ^ 7 <= E1H / 2 and E1H / 2 <= QQ(2798869) / 10 ^ 7)
check("item (1): 0.6065306597 <= e^{-1/2} <= 0.6065306598", QQ(6065306597) / 10 ^ 10 <= EM and EM <= QQ(6065306598) / 10 ^ 10)

say("")
say("(b) Gamma_n: closed form 2(K_n + 2K_{n-1}) (K_0 = E_1(1/2)/2) against quadrature of")
say("    2 int_1^oo t^{2n} e^{-t^2/2} (1/t + 2/t^3) dt")
for n in range(7):
    gc = Gamma_n(n)
    gq = Gamma_n_quad(n)
    if n == 0:
        form = "2 e^{-1/2}"
        gc2 = 2 * (K_closed(0) + 2 * ((EM - E1H / 2) / 2))  # 2(H_1 + 2 H_0), H_0 = (e^{-1/2} - H_1)/2
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


finish()
