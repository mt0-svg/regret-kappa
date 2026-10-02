# lib.sage: certified tools shared by the scripts of this implementation.
#
# Every real number is an Arb ball (Sage RealBallField, 256 bits): a midpoint and a
# radius that encloses the exact value, with rounding handled by Arb. A comparison of
# two balls is True only when it holds for every pair of points of the two balls, so
# every check below that passes is a proof of the stated inequality, given the
# correctness of Arb and of the analytic tail bounds written next to each tool.
# Floats never enter: RB refuses to coerce them, constants are exact rationals.

import sys
import time

PREC = 256
RB = RealBallField(PREC)
CB = ComplexBallField(PREC)

NCHECK = 0
NFAIL = 0
T_START = time.time()


def say(*args):
    print(*args)
    sys.stdout.flush()


def check(name, ok, detail=""):
    """Record one check. ok must be the Python value True to pass."""
    global NCHECK, NFAIL
    NCHECK += 1
    if ok is True:
        say("PASS", name, detail) if detail else say("PASS", name)
    else:
        NFAIL += 1
        say("FAIL", name, detail) if detail else say("FAIL", name)


def finish():
    say("elapsed %.2f s" % (time.time() - T_START))
    if NFAIL == 0 and NCHECK > 0:
        say("RESULT: ALL %d CHECKS PASSED" % NCHECK)
        sys.exit(int(0))  # a Sage Integer would print and exit 1
    say("RESULT: %d OF %d CHECKS FAILED" % (NFAIL, NCHECK))
    sys.exit(int(1))


def iv(b, d=22):
    """Rigorous decimal interval [lo, hi] containing the ball b (lo rounded down, hi up)."""
    b = RB(b)
    return "[%s, %s]" % (b.lower().str(digits=d), b.upper().str(digits=d))


def up(b, d=12):
    """Decimal upper bound of the ball b, rounded up."""
    return RB(b).upper().str(digits=d)


def lo(b, d=12):
    """Decimal lower bound of the ball b, rounded down."""
    return RB(b).lower().str(digits=d)


def disjoint(a, b):
    return (RB(a) < RB(b)) or (RB(a) > RB(b))


def small(b, eps):
    """True when |b| <= eps for every point of the ball."""
    return RB(b).abs() < RB(eps)


TINY = RB(2) ^ (-(PREC - 40))

# ---------------------------------------------------------------------------
# Elementary constants by exact rational series with explicit tails.
# ---------------------------------------------------------------------------


def exp_series(x):
    """e^x for rational x: sum_{k<=K} x^k/k! (exact) plus the tail bound
    |x|^{K+1}/(K+1)! / (1 - |x|/(K+2)), valid for |x| < K+2."""
    x = QQ(x)
    K = 10
    while True:
        if abs(x) < K + 2:
            tail = abs(x) ^ (K + 1) / factorial(K + 1) / (1 - abs(x) / (K + 2))
            if tail < QQ(2) ^ (-(PREC + 20)):
                break
        K += 10
    S = sum(x ^ k / factorial(k) for k in range(K + 1))
    return RB(S).add_error(RB(tail))


def E1_series(x):
    """E_1(x) = -gamma - log x - sum_{k>=1} (-x)^k/(k k!) for rational x > 0.
    The tail sum_{k>K} x^k/(k k!) <= x^{K+1}/(K+1)! / (1 - x/(K+2)), for x < K+2."""
    x = QQ(x)
    if not x > 0:
        raise ValueError("E1_series needs x > 0")
    K = 10
    while True:
        if x < K + 2:
            tail = x ^ (K + 1) / factorial(K + 1) / (1 - x / (K + 2))
            if tail < QQ(2) ^ (-(PREC + 20)):
                break
        K += 10
    S = sum((-x) ^ k / (k * factorial(k)) for k in range(1, K + 1))
    return -RB.euler_constant() - RB(x).log() - RB(S).add_error(RB(tail))


EM = RB(-1 / 2).exp()  # e^{-1/2}
E1H = E1_series(1 / 2)  # E_1(1/2)
SQRT2PI = (2 * RB.pi()).sqrt()

# ---------------------------------------------------------------------------
# Certified quadrature on [1, infinity): Arb's acb_calc_integrate on [lo, R]
# plus an analytic tail bound on [R, infinity).
# ---------------------------------------------------------------------------


def quad(F, a, b):
    """Rigorous enclosure of int_a^b F for F holomorphic (or meromorphic with poles
    away from the segment) given as F(z, analytic) on complex balls; a, b exact."""
    I = CB.integral(F, a, b)
    if not I.imag().contains_exact(0):
        raise ValueError("imaginary part of a real integral excludes 0")
    return I.real()


def tail_bound(coef, k, r, a, R):
    """Upper bound of coef * int_R^oo t^k e^{t r - a t^2/2} dt.

    Proof: for t >= R >= 8 r / a, t r <= a t^2 / 8; for t >= R with R^2 >= 4 k / a
    (or k <= 0), t^k e^{-a t^2/8} is nonincreasing, so t^k <= R^k e^{-a R^2/8} e^{a t^2/8}.
    Hence the integrand is <= R^k e^{-a R^2/8} e^{-a t^2/4}, and
    int_R^oo e^{-a t^2/4} <= int_R^oo (t/R) e^{-a t^2/4} = (2/(a R)) e^{-a R^2/4}.
    Total: coef (2/a) R^{k-1} e^{-3 a R^2/8}."""
    coef, r, a, Rb = RB(coef), RB(r), RB(a), RB(R)
    if not (Rb >= 1 and a > 0 and r >= 0 and coef >= 0):
        raise ValueError("tail_bound: need R >= 1, a > 0, r >= 0, coef >= 0")
    if not (Rb >= 8 * r / a):
        raise ValueError("tail_bound: need R >= 8 r / a")
    if k > 0 and not (Rb ^ 2 >= 4 * k / a):
        raise ValueError("tail_bound: need R^2 >= 4 k / a")
    return coef * (2 / a) * Rb ^ (k - 1) * (-3 * a * Rb ^ 2 / 8).exp()


def choose_R(k, r, a):
    """Smallest integer R (from a coarse search) meeting the conditions of tail_bound
    with a tail below 2^-(PREC+10)."""
    r, a = RB(r), RB(a)
    R = max(2, ZZ(ceil((8 * r / a).upper())) + 1)
    if k > 0:
        R = max(R, ZZ(ceil((4 * k / a).sqrt().upper())) + 1)
    while not (tail_bound(1, k, r, a, R) < RB(2) ^ (-(PREC + 10))):
        R += 2
    return R


def int_1_inf(F, coef, k, r, a):
    """int_1^oo F where 0 <= F(t) <= coef t^k e^{t r - a t^2/2} for t >= 1."""
    R = choose_R(k, r, a)
    return quad(F, 1, R) + RB(0).add_error(tail_bound(coef, k, r, a, R))


def Gamma_quad(r):
    """Gamma(r) = 2 int_1^oo cosh(t r) e^{-t^2/2} (1/t + 2/t^3) dt; integrand
    <= 6 e^{t |r|} e^{-t^2/2} for t >= 1."""
    rc = CB(r)
    F = lambda z, an: 2 * (rc * z).cosh() * (-z * z / 2).exp() * (1 / z + 2 / z ^ 3)
    return int_1_inf(F, 6, 0, RB(r).abs(), 1)


def Gamma_n_quad(n):
    """Gamma_n = 2 int_1^oo t^{2n} e^{-t^2/2} (1/t + 2/t^3) dt; integrand <= 6 t^{max(2n-1,0)} e^{-t^2/2}."""
    F = lambda z, an: 2 * z ^ (2 * n) * (-z * z / 2).exp() * (1 / z + 2 / z ^ 3)
    return int_1_inf(F, 6, max(2 * n - 1, 0), 0, 1)


def dGamma_quad(r):
    """Gamma'(r) = 2 int_1^oo sinh(t r) e^{-t^2/2} (1 + 2/t^2) dt, r >= 0; integrand <= 6 e^{t r} e^{-t^2/2}."""
    rc = CB(r)
    F = lambda z, an: 2 * (rc * z).sinh() * (-z * z / 2).exp() * (1 + 2 / z ^ 2)
    return int_1_inf(F, 6, 0, RB(r).abs(), 1)


def Ghat_quad(rho, s):
    """hat Gamma(rho, s) = 2 int_1^oo e^{t^2 s/2} cosh(t c rho) e^{-t^2/2} (1/t + 2/t^3) dt,
    c = sqrt(1 - s), s in [0, 1); integrand <= 6 e^{t c |rho|} e^{-(1-s) t^2/2}."""
    s = RB(s)
    c = (1 - s).sqrt()
    sc, cr = CB(s), CB(c * rho)
    F = lambda z, an: 2 * (z * z * (sc - 1) / 2).exp() * (cr * z).cosh() * (1 / z + 2 / z ^ 3)
    return int_1_inf(F, 6, 0, (c * rho).abs(), 1 - s)


# ---------------------------------------------------------------------------
# Closed forms from the recursion of Lemma A.1 (b) and the power series of Gamma and g'.
# ---------------------------------------------------------------------------


def K_coef(m):
    """K_m / e^{-1/2} for m >= 1: 2^{m-1} (m-1)! sum_{j<m} 2^{-j}/j!, an exact rational."""
    if m < 1:
        raise ValueError("K_coef needs m >= 1")
    return 2 ^ (m - 1) * factorial(m - 1) * sum(QQ(1) / (2 ^ j * factorial(j)) for j in range(m))


def K_closed(m):
    if m == 0:
        return E1H / 2
    return K_coef(m) * EM


def Gamma_n_coef(n):
    """Gamma_n / e^{-1/2} for n >= 2: 2 (K_n + 2 K_{n-1}) / e^{-1/2}, an exact rational."""
    if n < 2:
        raise ValueError("Gamma_n_coef needs n >= 2")
    return 2 * (K_coef(n) + 2 * K_coef(n - 1))


_GN = {}


def Gamma_n(n):
    """Closed form from the recursion of Lemma A.1 (b)."""
    if n not in _GN:
        if n == 0:
            _GN[n] = 2 * EM
        elif n == 1:
            _GN[n] = 2 * EM + 2 * E1H
        else:
            _GN[n] = Gamma_n_coef(n) * EM
    return _GN[n]


def series_tail(x, N, shift):
    """Bound of sum_{n>N} 2 x^{n-shift}/n! for 0 <= x < N+2:
    2 x^{N+1-shift}/(N+1)! / (1 - x/(N+2))."""
    x = RB(x)
    if not (x >= 0 and x < N + 2):
        raise ValueError("series_tail: need 0 <= x < N+2")
    return 2 * x ^ (N + 1 - shift) / factorial(N + 1) / (1 - x / (N + 2))


def Gamma_series(r, N=None):
    """Gamma(r) = sum_n Gamma_n x^n/(2n)!, x = r^2 (expanding cosh in the definition of Gamma), truncated at N.
    Tail: Gamma_n x^n/(2n)! <= 2 x^n/n! for n >= 1 (Lemma A.1 (c), with
    (2n)! >= 2^n (n!)^2 and 1/n <= 1), so the tail is <= series_tail(x, N, 0)."""
    x = RB(r) ^ 2
    if N is None:
        N = 20
        while not (x < N + 2 and series_tail(x, N, 0) < TINY):
            N += 10
    S = sum(Gamma_n(n) * x ^ n / factorial(2 * n) for n in range(N + 1))
    t = series_tail(x, N, 0)
    return S + RB(0).add_error(t)


def gprime_series(x, N=None):
    """g'(x) = sum_{n>=1} n Gamma_n x^{n-1}/(2n)!, truncated at N, plus the tail bound
    2 x^N / ((N+1)! (1 - x/(N+2))) from n Gamma_n/(2n)! <= 2/n! (Lemma A.1 (c))."""
    x = RB(x)
    if N is None:
        N = 20
        while not (x < N + 2 and series_tail(x, N, 1) < TINY):
            N += 10
    S = sum(n * Gamma_n(n) * x ^ (n - 1) / factorial(2 * n) for n in range(1, N + 1))
    t = series_tail(x, N, 1)
    return S + RB(0).add_error(t)


def gprime_upper(x, N):
    """Upper bound of g'(x): truncated series plus the tail bound, as one number (a ball
    whose upper end bounds g'(x))."""
    x = RB(x)
    S = sum(n * Gamma_n(n) * x ^ (n - 1) / factorial(2 * n) for n in range(1, N + 1))
    return S + series_tail(x, N, 1)


# ---------------------------------------------------------------------------
# Root enclosure by bisection with certified signs.
# ---------------------------------------------------------------------------


def bisect_root(F, a, b, width):
    """[a, b] exact rationals with F(a), F(b) of certified opposite signs; returns exact
    rationals lo < hi, hi - lo <= width, with F(lo), F(hi) of certified opposite signs,
    so a root of the continuous F lies in (lo, hi)."""
    a, b = QQ(a), QQ(b)
    fa, fb = F(RB(a)), F(RB(b))
    if fa > 0 and fb < 0:
        sg = 1
    elif fa < 0 and fb > 0:
        sg = -1
    else:
        raise ValueError("bisect_root: no certified sign change on [%s, %s]" % (a, b))
    while b - a > width:
        m = (a + b) / 2
        fm = F(RB(m)) * sg
        if fm > 0:
            a = m
        elif fm < 0:
            b = m
        else:
            raise ValueError("bisect_root: sign undecided at %s" % m)
    return a, b
