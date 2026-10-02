# c2_small_steps.sage: Lemma A.7 of the paper, item (2) of Computation A.9.
#   H_0..H_4 (closed forms and quadrature), the coefficients f_0..f_4 of the quartic f, its
#   concavity on [0, oo), the positive root of the cubic f', max f and (2/3) max f.
load("lib.sage")

say("c2_small_steps: Lemma A.7, %d-bit balls" % PREC)

tau = 3 * RB(3).log() / 2
say("tau = (3/2) log 3 =", iv(tau, 30))


def H_closed(n):
    """H_n = int_1^oo u^{2n-3} e^{-u^2/2} du: H_0 = (e^{-1/2} - H_1)/2, H_n = K_{n-1} (n >= 1)."""
    if n == 0:
        return (EM - E1H / 2) / 2
    return K_closed(n - 1)


def H_quad(n):
    k = 2 * n - 3
    return int_1_inf(lambda z, an: z ^ k * (-z * z / 2).exp(), 1, max(k, 0), 0, 1)


say("")
say("H_n = int_1^oo u^{2n-3} e^{-u^2/2} du")
H = {}
for n in range(5):
    H[n] = H_closed(n)
    Hq = H_quad(n)
    say("  H_%d closed %s" % (n, iv(H[n], 30)))
    say("      quad   %s" % iv(Hq, 30))
    check("H_%d closed form = quadrature" % n, H[n].overlaps(Hq) and Hq.rad() < 10 ^ -50)
check("H_1 = E_1(1/2)/2, H_2 = e^{-1/2}, H_3 = 3 e^{-1/2}, H_4 = 13 e^{-1/2}",
      H[1].overlaps(E1H / 2) and H[2].overlaps(EM) and H[3].overlaps(3 * EM) and H[4].overlaps(13 * EM))

fc = {}
fc[0] = 2 * (-RB(1) / 6).exp() * (1 + tau / 2) - 4 * H[0]
fc[1] = 2 * EM * (QQ(1) / 2 + tau) - 4 * H[1]
for n in (2, 3, 4):
    fc[n] = 3 * EM - 4 * H[n]
say("")
for n in range(5):
    say("f_%d = %s" % (n, iv(fc[n], 30)))
check("f_2 = -e^{-1/2}, f_3 = -9 e^{-1/2}, f_4 = -49 e^{-1/2}",
      fc[2].overlaps(-EM) and fc[3].overlaps(-9 * EM) and fc[4].overlaps(-49 * EM))
check("f_0 > 0", fc[0] > 0)
check("f_1 > 0, so f'(0) = f_1/2 > 0", fc[1] > 0)
check("f_2, f_3, f_4 < 0, so every coefficient of f'' is negative and f'' < 0 on [0, oo)",
      fc[2] < 0 and fc[3] < 0 and fc[4] < 0)


def f(v):
    return sum(fc[n] * v ^ n / factorial(2 * n) for n in range(5))


def fp(v):
    return sum(n * fc[n] * v ^ (n - 1) / factorial(2 * n) for n in range(1, 5))


def fpp(v):
    return sum(n * (n - 1) * fc[n] * v ^ (n - 2) / factorial(2 * n) for n in range(2, 5))


say("f''(0) = 2 f_2/4! =", iv(fpp(RB(0)), 20), "; coefficients of f'' (v^0, v^1, v^2):",
    ", ".join(iv(n * (n - 1) * fc[n] / factorial(2 * n), 12) for n in range(2, 5)))
check("f''(0) < 0", fpp(RB(0)) < 0)

# Positive root of the cubic f'. f' is strictly decreasing on [0, oo) (f'' < 0), f'(0) > 0,
# so a certified sign change on [0, 8] gives the unique positive root.
check("f'(8) < 0", fp(RB(8)) < 0, iv(fp(RB(8)), 10))
xl, xh = bisect_root(fp, 0, 8, QQ(2) ^ -220)
vs = RB(xl).union(RB(xh))
say("")
say("positive root v* of f' in", iv(vs, 40))
fmax = f(vs)
say("max_{v>=0} f = f(v*) in", iv(fmax, 40))
check("f(v*) enclosure radius < 1e-60", fmax.rad() < 10 ^ -60)
check("f(v*) >= f(lo), f(hi) (consistency of the maximum)", fmax.upper() >= f(RB(xl)).lower() and fmax.upper() >= f(RB(xh)).lower())
B = 2 * fmax / 3
say("(2/3) max f in", iv(B, 40))
check("max f > 0 (so s f(rho^2) <= (2/3) max f for s <= 2/3)", fmax > 0)
check("max f <= 4.32855 (Computation A.9, item (2))", fmax <= QQ(432855) / 100000, up(fmax, 15))
check("(2/3) max f <= 2.8857 (Lemma A.7 as stated)", B <= QQ(28857) / 10000, up(B, 15))
check("(2/3) max f < 3 (Lemma A.7, below the increment 3)", B < 3, "margin 3 - (2/3) max f >= %s" % lo(3 - B, 10))
check("NEG (2/3) max f < 2.8856 is refuted", B > QQ(28856) / 10000)
check("v* in [3.968, 3.969]", RB(xl) > QQ(3968) / 1000 and RB(xh) < QQ(3969) / 1000)


finish()
