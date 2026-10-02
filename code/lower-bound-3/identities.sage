# Exact identities of Sections 2 and 4 of the paper on random instances (names of code/README.md):
# Lemma 1.1 (regret identity), Lemma 1.2 (split at n), the clipping step of Lemma 1.3,
# Lemma 2.1 (V and rho updates, in the real algebraic field AA), the one-step identity (i) of
# Lemma 4.3, and the closed form of V_T (theta* - hat theta_T)^2 used by the Bayes check of
# phase2.sage. Exact arithmetic throughout (QQ, AA). Each identity has a corrupted twin that
# must fail on the same instances.
# Run from this directory: sage identities.sage

load("common.sage")

C = Checker("identities")
set_random_seed(20261001)


def rq(den=50, span=3):
    return QQ(randint(-span * den, span * den)) / den


def best_fit(xs, ys):
    """inf over theta of sum (theta x - y)^2, by exact minimisation (V = 0: the constant)."""
    V = sum(x * x for x in xs)
    S = sum(x * y for x, y in zip(xs, ys))
    if V == 0:
        return sum(y * y for y in ys)
    th = S / V
    return sum((th * x - y) ** 2 for x, y in zip(xs, ys))


ok = okw = True
for trial in range(300):
    T = randint(1, 12)
    xs = [rq() if randint(0, 4) else QQ(0) for _ in range(T)]
    if trial % 25 == 0:
        xs = [QQ(0)] * T
    ys = [rq(10, 1) for _ in range(T)]
    yh = [rq() for _ in range(T)]
    reg = sum((a - b) ** 2 for a, b in zip(yh, ys)) - best_fit(xs, ys)
    V = sum(x * x for x in xs)
    S = sum(x * y for x, y in zip(xs, ys))
    rhs = sum(a * a - 2 * a * b for a, b in zip(yh, ys)) + (S ** 2 / V if V else 0)
    ok = ok and reg == rhs
    okw = okw and (V == 0 or reg == rhs - S ** 2 / V)
C.check("Lemma 1.1 on 300 exact instances (12 with V_T = 0)", ok)
C.check("negative control: Lemma 1.1 without S_T^2/V_T fails", not okw)

ok = okw = True
for trial in range(300):
    T = randint(2, 12)
    n = randint(1, T - 1)
    xs = [rq() for _ in range(T)]
    xs[0] = QQ(randint(1, 100)) / 37
    ys = [rq(10, 1) for _ in range(T)]
    yh = [rq() for _ in range(T)]
    ts = rq()
    reg = sum((a - b) ** 2 for a, b in zip(yh, ys)) - best_fit(xs, ys)
    Vn = sum(x * x for x in xs[:n]); Sn = sum(x * y for x, y in zip(xs[:n], ys[:n]))
    VT = sum(x * x for x in xs); ST = sum(x * y for x, y in zip(xs, ys))
    rhs = (sum(yh[t] ** 2 - 2 * yh[t] * ys[t] for t in range(n)) + Sn ** 2 / Vn
           + sum((yh[t] - ys[t]) ** 2 - (ts * xs[t] - ys[t]) ** 2 for t in range(n, T))
           - Vn * (ts - Sn / Vn) ** 2 + VT * (ts - ST / VT) ** 2)
    ok = ok and reg == rhs
    okw = okw and reg == rhs + Vn * (ts - Sn / Vn) ** 2
C.check("Lemma 1.2 on 300 exact instances (random n and theta*)", ok)
C.check("negative control: Lemma 1.2 without -V_n (theta* - theta_n)^2 fails", not okw)

ok = True
for trial in range(1000):
    y = rq(100, 1)
    yh = rq(10, 5)
    c = max(-1, min(1, yh))
    ok = ok and abs(c - y) <= abs(yh - y)
C.check("Lemma 1.3: |clip(yhat) - y| <= |yhat - y| for |y| <= 1, 1000 instances", ok)

ok = okw = True
for trial in range(60):
    V = QQ(randint(1, 400)) / 7
    Sv = rq(7, 4)
    s = QQ(randint(1, 999)) / 1000
    y = 1 if randint(0, 1) else -1
    x1 = AA(V * s / (1 - s)).sqrt()
    V1 = V + x1 ** 2
    S1 = AA(Sv) + x1 * y
    rho = AA(Sv) / AA(V).sqrt()
    rho1 = S1 / V1.sqrt()
    ok = ok and V1 == AA(V / (1 - s)) and rho1 == rho * AA(1 - s).sqrt() + y * AA(s).sqrt()
    okw = okw and rho1 == rho * AA(1 - s).sqrt() + y * AA(s)
C.check("Lemma 2.1 (V_{t+1} = V_t/(1 - s), rho update) on 60 instances in AA", ok)
C.check("negative control: the rho update with s in place of sqrt(s) fails", not okw)

ok = okw = True
for trial in range(300):
    m = rq(100, 1) * QQ(9) / 10      # theta* x, |.| < 1
    yh = rq(10, 2)
    p = (1 + m) / 2                   # P(y = 1)
    lhs = p * ((yh - 1) ** 2 - (m - 1) ** 2) + (1 - p) * ((yh + 1) ** 2 - (m + 1) ** 2)
    ok = ok and lhs == (yh - m) ** 2
    okw = okw and lhs == (yh - m) ** 2 + m ** 2
C.check("Lemma 4.3 (i): E[(yhat - y)^2 - (theta* x - y)^2] = (yhat - theta* x)^2, 300 instances", ok)
C.check("negative control: with an extra (theta* x)^2 it fails", not okw)

ok = True
for trial in range(200):
    k = randint(1, 8)
    V = QQ(randint(1, 50)) / 3
    rho = rq(10, 5)
    Z = rq(10, 2)
    eps = [rq(20, 1) for _ in range(k)]
    ys = [1 if randint(0, 1) else -1 for _ in range(k)]
    sV = AA(V).sqrt()
    X = sum(e * e for e in eps)
    th_tau = AA(rho) / sV
    th_star = th_tau + AA(Z) / sV
    ST = AA(rho) * sV + sum(sV * e * y for e, y in zip(eps, ys))
    VT = V * (1 + X)
    lhs = VT * (th_star - ST / VT) ** 2
    rhs = (rho * X + Z * (1 + X) - sum(e * y for e, y in zip(eps, ys))) ** 2 / (1 + X)
    ok = ok and lhs == AA(rhs)
C.check("V_T (theta* - hat theta_T)^2 = (rho X + Z(1 + X) - sum eps_i y_i)^2/(1 + X), 200 instances", ok)
C.finish(10)
