# Inputs of Theorem 4.1 of the paper (Theorem LB in the outputs), and the check bookkeeping.
# Every script loads this file; a negative control overrides one input after loading it.

import sys

# Move table s_0, ..., s_27 of section 2, as printed in the note (4 decimals), as exact rationals.
S_DIGITS = [6242, 6180, 6058, 5879, 5648, 5373, 5060, 4718, 4355, 3980, 3601, 3226, 2861, 2513,
            2184, 1880, 1602, 1352, 1129, 934, 764, 620, 497, 395, 311, 242, 187, 142]
MOVES = [QQ(d) / 10000 for d in S_DIGITS]
NCELLS = 28           # cells [j/10, (j+1)/10), j = 0..27, cover [0, 2.8)
RHO_SPLIT = QQ(28) / 10
K_G = 8               # g(rho) = K_G exp(rho^2/2)
A_PRIOR = 2           # support [-A, A] of the cos^2 prior
NU_M2 = QQ(1) / 2     # nu_m^2
T0 = 355713
C1_STATED = QQ(3318633) / 10**6   # c_1 to 6 decimals

PREC = 256
R = RealBallField(PREC)


def ball(lo, hi):
    """A ball containing the real segment [lo, hi] (lo, hi exact rationals)."""
    return R(lo).union(R(hi))


def unique_floor(x):
    """floor of a real known as a ball; raises if the ball straddles an integer."""
    lo = x.lower().floor()
    hi = x.upper().floor()
    if lo != hi:
        raise ValueError("ball %s straddles an integer" % x)
    return ZZ(lo)


def unique_ceil(x):
    lo = x.lower().ceil()
    hi = x.upper().ceil()
    if lo != hi:
        raise ValueError("ball %s straddles an integer" % x)
    return ZZ(lo)


class Checker:
    """Counts checks; finish() exits nonzero on a failure or a wrong number of checks."""

    def __init__(self, name):
        self.name = name
        self.n = 0
        self.fails = []

    def check(self, label, ok, detail=""):
        self.n += 1
        ok = bool(ok)
        print(("CHECK %-58s %s  %s" % (label, "PASS" if ok else "FAIL", detail)).rstrip())
        sys.stdout.flush()
        if not ok:
            self.fails.append(label)
        return ok

    def finish(self, expected):
        print("SUMMARY %s: %d checks, %d failed, expected %d checks" %
              (self.name, self.n, len(self.fails), expected))
        if self.fails:
            print("FAILED: " + "; ".join(self.fails))
        if self.fails or self.n != expected:
            print("RESULT %s FAIL" % self.name)
            sys.stdout.flush()
            sys.exit(1)
        print("RESULT %s PASS" % self.name)
        sys.stdout.flush()
