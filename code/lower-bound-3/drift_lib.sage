# Drift of the phase-1 chain with Arb balls (Sage RealBallField), loaded after common.sage.
#
# D(rho) = (1/2) [g(rho sqrt(1-s) + sqrt(s)) + g(rho sqrt(1-s) - sqrt(s))] - g(rho) - 1,
# g(rho) = K exp(rho^2/2). Lemma 3.1 claims D >= 0 for every rho with s = s(rho), K = 8.
# On [0, 2.8) D is evaluated from this definition (no identity, no monotonicity): a ball
# enclosure of D over a subinterval; bisection until the enclosure is positive.

import heapq

NEG_INF = RealField(PREC)("-inf")


def lower_or_neg_inf(v):
    """Lower end of a ball, -inf when the ball carries no information (NaN midpoint)."""
    l = v.lower()
    return NEG_INF if l.is_NaN() else l


def drift_direct(rho, s, K):
    """Ball enclosure of D over the ball rho, move s (ball), constant K, from the definition."""
    u = rho * (1 - s).sqrt()
    v = s.sqrt()
    g_plus = ((u + v) ** 2 / 2).exp()
    g_minus = ((u - v) ** 2 / 2).exp()
    return (K / 2) * (g_plus + g_minus) - K * (rho ** 2 / 2).exp() - 1


def drift_factored(rho, K):
    """D for rho >= 2.8 (s = (5/8) exp(-rho^2/2)) through the identity of Lemma 3.1:
    average = K exp(rho^2/2) exp(-z) cosh(x), z = s (rho^2 - 1)/2, x = rho sqrt(s (1 - s)).
    The bracket exp(-z) cosh(x) - 1 is formed as expm1(-z) + exp(-z) 2 sinh(x/2)^2."""
    s = R(QQ(5) / 8) * (-(rho ** 2) / 2).exp()
    z = s * (rho ** 2 - 1) / 2
    x = rho * (s * (1 - s)).sqrt()
    bracket = (-z).expm1() + (-z).exp() * 2 * (x / 2).sinh() ** 2
    return K * (rho ** 2 / 2).exp() * bracket - 1


def drift_deriv(rho, s, K):
    """Ball enclosure of dD/drho over the ball rho for a fixed move s (ball):
    D' = (K/2) w [p e^{p^2/2} + m e^{m^2/2}] - K rho e^{rho^2/2}, w = sqrt(1-s),
    p = rho w + sqrt(s), m = rho w - sqrt(s)."""
    w = (1 - s).sqrt()
    v = s.sqrt()
    p = rho * w + v
    m = rho * w - v
    return (K / 2) * w * (p * (p ** 2 / 2).exp() + m * (m ** 2 / 2).exp()) - K * rho * (rho ** 2 / 2).exp()


def drift_mean_value(a, b, s, K):
    """Mean value form on [a, b]: D([a, b]) is contained in D(c) + D'([a, b]) [a - c, b - c],
    c = (a + b)/2. Its overestimate is |D'| (b - a)/2 instead of (|g'| + |K h_s'|)(b - a) for
    the direct ball evaluation, so it needs a much coarser subdivision."""
    c = (a + b) / 2
    return drift_direct(R(c), s, K) + drift_deriv(ball(a, b), s, K) * ball(a - c, b - c)


def certify_trisect(lo, hi, f, maxdepth=16):
    """Trisect [lo, hi] until f(a, b) > 0 on every piece [a, b] (f returns a ball enclosure of
    the function over [a, b]). Same return convention as certify_interval."""
    stack = [(lo, hi, 0)]
    leaves = []
    while stack:
        a, b, d = stack.pop()
        v = f(a, b)
        if v > 0:
            leaves.append((a, b, d, v.lower()))
        elif d >= maxdepth:
            return False, leaves, (a, b)
        else:
            h = (b - a) / 3
            stack.extend([(a + 2 * h, b, d + 1), (a + h, a + 2 * h, d + 1), (a, a + h, d + 1)])
    return True, leaves, None


def certify_table_mvf(moves, K, verbose=True):
    """Certify D > 0 on every closed cell [j/10, (j+1)/10] with move moves[j], by the mean value
    form and trisection. Returns (ok, per_cell) as certify_table."""
    Kb = R(K)
    allok = True
    per = []
    for j in range(NCELLS):
        s = R(moves[j])
        f = lambda a, b, s=s: drift_mean_value(a, b, s, Kb)
        lo, hi = QQ(j) / 10, QQ(j + 1) / 10
        ok, leaves, info = certify_trisect(lo, hi, f)
        nl = len(leaves)
        md = max(l[2] for l in leaves) if leaves else -1
        ml = min(l[3] for l in leaves) if leaves else None
        per.append((ok, nl, md, ml, info))
        if verbose:
            if ok:
                print("cell %2d [%s, %s] s = %s: certified, %d subintervals, trisection depth <= %d, "
                      "least lower bound %.6g" % (j, lo, hi, moves[j], nl, md, ml))
            else:
                print("cell %2d [%s, %s] s = %s: NOT certified, piece [%s, %s] not positive "
                      "at depth 16" % (j, lo, hi, moves[j], info[0], info[1]))
            sys.stdout.flush()
        allok = allok and ok
    return allok, per


def table_rounding(digits):
    """For each cell j: (digits[j], nearest integer to 10^4 (5/8) exp(-m^2/2), m = j/10 + 1/20,
    the ball value). The nearest integer is certified (the ball must not straddle a half)."""
    rows = []
    for j in range(NCELLS):
        m = QQ(j) / 10 + QQ(1) / 20
        v = 10000 * R(QQ(5) / 8) * (-(R(m) ** 2) / 2).exp()
        rows.append((digits[j], unique_floor(v + R(QQ(1) / 2)), v / 10000))
    return rows


def phi_ball(rho):
    """phi(rho) = exp(-rho^2/2) (rho^2/2 + rho^4/4)."""
    rho = R(rho)
    return (-(rho ** 2) / 2).exp() * (rho ** 2 / 2 + rho ** 4 / 4)


def part_a_conditions(split, const):
    """The three numerical conditions of Lemma 3.1 (a) from rho = split on, with the constant
    const in place of 12/25: split^2 > 1 + sqrt 5 (phi decreasing), phi(split) < const, and
    5/2 - (25/8) const >= 1 (exact rationals)."""
    return (R(split) ** 2 > 1 + R(5).sqrt(), phi_ball(split) < R(const),
            QQ(5) / 2 - QQ(25) / 8 * QQ(const) >= 1)


def move_of_cell(j, moves):
    return R(moves[j])


def certify_interval(lo, hi, f, maxdepth=24):
    """Bisect [lo, hi] until f(ball) > 0 on every piece.
    Returns (ok, leaves, info): leaves = list of (lo, hi, depth, lower bound);
    on failure info = (lo, hi) of a piece still not positive at maxdepth."""
    stack = [(lo, hi, 0)]
    leaves = []
    while stack:
        a, b, d = stack.pop()
        v = f(ball(a, b))
        if v > 0:
            leaves.append((a, b, d, v.lower()))
        elif d >= maxdepth:
            return False, leaves, (a, b)
        else:
            m = (a + b) / 2
            stack.append((m, b, d + 1))
            stack.append((a, m, d + 1))
    return True, leaves, None


def find_counterexample(lo, hi, f, npts=2000):
    """A rational point of [lo, hi] where f is certainly negative, or None."""
    best = None
    for i in range(npts + 1):
        x = lo + (hi - lo) * QQ(i) / npts
        v = f(R(x))
        if v < 0 and (best is None or v.upper() < best[1]):
            best = (x, v.upper())
    return best


def min_enclosure(lo, hi, f, tol):
    """Branch and bound: returns (L, U, xU) with L <= min over [lo, hi] of f <= U = upper bound
    of f at the rational point xU, and U - L <= tol."""
    U, xU = None, None
    for x in (lo, hi, (lo + hi) / 2):
        u = f(R(x)).upper()
        if U is None or u < U:
            U, xU = u, x
    heap = [(lower_or_neg_inf(f(ball(lo, hi))), lo, hi)]
    while True:
        lb, a, b = heap[0]
        if lb >= U - tol:
            break
        heapq.heappop(heap)
        m = (a + b) / 2
        for c, d in ((a, m), (m, b)):
            heapq.heappush(heap, (lower_or_neg_inf(f(ball(c, d))), c, d))
            xm = (c + d) / 2
            u = f(R(xm)).upper()
            if u < U:
                U, xU = u, xm
    L = min(h[0] for h in heap)
    return L, U, xU


def certify_table(moves, K, verbose=True):
    """Certify D > 0 on every cell [j/10, (j+1)/10] with move moves[j]. Returns
    (ok, per_cell) with per_cell[j] = (ok_j, nleaves, maxdepth, min leaf lower bound, fail info)."""
    Kb = R(K)
    allok = True
    per = []
    for j in range(NCELLS):
        s = R(moves[j])
        f = lambda rho, s=s: drift_direct(rho, s, Kb)
        lo, hi = QQ(j) / 10, QQ(j + 1) / 10
        ok, leaves, info = certify_interval(lo, hi, f)
        nl = len(leaves)
        md = max(l[2] for l in leaves) if leaves else -1
        ml = min(l[3] for l in leaves) if leaves else None
        per.append((ok, nl, md, ml, info))
        if verbose:
            if ok:
                print("cell %2d [%s, %s) s = %s: certified, %d subintervals, depth <= %d, "
                      "least lower bound %.6g" % (j, lo, hi, moves[j], nl, md, ml))
            else:
                print("cell %2d [%s, %s) s = %s: NOT certified, piece [%s, %s] not positive "
                      "at depth 24" % (j, lo, hi, moves[j], info[0], info[1]))
            sys.stdout.flush()
        allok = allok and ok
    return allok, per
