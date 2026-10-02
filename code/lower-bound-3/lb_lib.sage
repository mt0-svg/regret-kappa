# Constants and functions of Section 4 of the paper with Arb balls
# (RealBallField R of common.sage). Loaded after common.sage by the scripts that use them.

PI = R.pi()
E1 = R(1).exp()


# ---- Lemma 4.2: the cos^2 prior on [-A, A], A = 2, in closed form

def J_prior(A=A_PRIOR):
    """Fisher information of f_A: pi^2/A^2."""
    return PI ** 2 / R(A) ** 2


def EZ2_prior(A=A_PRIOR):
    """Second moment of f_A: A^2 (1/3 - 2/pi^2)."""
    return R(A) ** 2 * (R(1) / 3 - 2 / PI ** 2)


def c1_of(J, EZ2):
    """c_1 = 1 + E Z^2 + log(pi^2) - 1/2 + (J - 2)/(pi^2 e^2) (A = 2)."""
    return 1 + EZ2 + (PI ** 2).log() - R(1) / 2 + (J - 2) / (PI ** 2 * E1 ** 2)


def prior_moments(mmax):
    """M_m = integral over [-2, 2] of z^m f_2(z) dz, f_2(z) = (1/2) cos^2(pi z/4)
    = (1/4)(1 + cos(pi z/2)), for m = 0..mmax, by the integration by parts recursion
    C_m = int z^m cos(b z), S_m = int z^m sin(b z) on [-2, 2], b = pi/2 (sin(2b) = 0, cos(2b) = -1):
    C_m = -(m/b) S_{m-1}, S_m = (2^m - (-2)^m)/b + (m/b) C_{m-1}, C_0 = S_0 = 0."""
    b = PI / 2
    C = [R(0)]
    S = [R(0)]
    for m in range(1, mmax + 1):
        C.append(-(m / b) * S[m - 1])
        S.append(R(2 ** m - (-2) ** m) / b + (m / b) * C[m - 1])
    return [(R(2 ** (m + 1) - (-2) ** (m + 1)) / (m + 1) + C[m]) / 4 for m in range(mmax + 1)]


# ---- Lemma 4.3: the van Trees value vT(rho, k) and the closed form Phi_1

def vT_detail(rho, k, J=None, EZ2=None, nu_m2=NU_M2, steps=True):
    """vT(rho, k) = sum_{i<=k} eps_i^2/w_{i-1} - E Z^2 + (1 + X)/w_k, with
    eps_i^2 = (nu_m^2/r^2)(i/k), nu_i^2 = nu_m^2 i/k, w_0 = J, w_i = w_{i-1} + eps_i^2/(1 - nu_i^2),
    X = sum eps_i^2, r = |rho| + A. With steps=True also the quantities of step (iv):
    l_i = log(w_i/J), sum_{i<k} l_i, min_i (l_i - log(1 + beta i^2))."""
    J = J_prior() if J is None else J
    EZ2 = EZ2_prior() if EZ2 is None else EZ2
    r = abs(R(rho)) + A_PRIOR
    r2 = r * r
    nm = R(nu_m2)
    beta = R(A_PRIOR) ** 2 / (4 * PI ** 2 * r2 * k)
    w = J
    S = R(0)
    X = R(0)
    sum_l = R(0)          # sum over i = 0..k-1 of l_i (l_0 = 0)
    min_gap = None        # min over i = 1..k of l_i - log(1 + beta i^2)
    for i in range(1, k + 1):
        e2 = nm * i / (r2 * k)
        n2 = nm * i / k
        S += e2 / w
        X += e2
        if steps and i > 1:
            sum_l += (w / J).log()       # l_{i-1}
        w = w + e2 / (1 - n2)
        if steps:
            gap = (w / J).log() - (1 + beta * i * i).log()
            if min_gap is None or gap.lower() < min_gap.lower():
                min_gap = gap
    v = S - EZ2 + (1 + X) / w
    return dict(vT=v, S=S, X=X, wk=w, lk=(w / J).log(), sum_l=sum_l, min_gap=min_gap, r=r,
                Lam=(R(k) * R(A_PRIOR) ** 2 / (4 * PI ** 2 * r2)).log(), J=J, EZ2=EZ2)


def Phi1(rho, k, c1):
    r = abs(R(rho)) + A_PRIOR
    return (R(k) / r ** 2).log() - c1 - R(k).log() / (2 * k) - R(1) / k


def k_min(rho):
    """Least integer k with k >= pi^2 e^2 r^2, r = |rho| + 2 (validity range of Phi_1)."""
    r = abs(R(rho)) + A_PRIOR
    return unique_ceil(PI ** 2 * E1 ** 2 * r ** 2)


# ---- Lemma 4.3, first claim, against the Bayes learner (sanity, small k)

def bayes_value(rho, k, M):
    """Expected bracket of Lemma 4.3 for the Bayes learner (yhat_t = x_t E[theta* | past]):
    sum_i eps_i^2 E Var(Z | D_{i-1}) - E Z^2 + [E Z^2 + X - (rho^2 + E Z^2) sum eps_i^4]/(1 + X).
    The posterior sums Q_d = sum over D in {-1,1}^d of (int z p(D|z) f)^2 / int p(D|z) f come from
    a depth-first enumeration with p(D|z) = prod_l (1 + y_l (rho + z) eps_l)/2 a polynomial in z
    and the exact prior moments M."""
    r = abs(R(rho)) + A_PRIOR
    eps = [None] + [(R(NU_M2) * l / k).sqrt() / r for l in range(1, k + 1)]
    Q = [R(0)] * k
    rb = R(rho)

    def dfs(poly, d):
        n0 = sum(c * M[m] for m, c in enumerate(poly))
        n1 = sum(c * M[m + 1] for m, c in enumerate(poly))
        Q[d] += n1 ** 2 / n0
        if d == k - 1:
            return
        e = eps[d + 1]
        for y in (1, -1):
            a0 = (1 + y * rb * e) / 2
            a1 = y * e / 2
            new = [R(0)] * (len(poly) + 1)
            for m, c in enumerate(poly):
                new[m] += c * a0
                new[m + 1] += c * a1
            dfs(new, d + 1)

    dfs([R(1)], 0)
    EZ2 = M[2]
    X = sum(eps[i] ** 2 for i in range(1, k + 1))
    X4 = sum(eps[i] ** 4 for i in range(1, k + 1))
    pred = sum(eps[i] ** 2 * (EZ2 - Q[i - 1]) for i in range(1, k + 1))
    return pred - EZ2 + (EZ2 + X - (rb ** 2 + EZ2) * X4) / (1 + X), Q


# ---- Sections 3 and 5: the functions of T

def j0_of(T):
    return unique_ceil((3 * R(T).log()).log())


def L_of(T):
    return 2 * (R(T) / (20 * E1 * j0_of(T))).log()


def L_low(T):
    """2 log T - 2 log(20 e) - 2 log(log(3 log T) + 1) <= L(T)."""
    return 2 * R(T).log() - 2 * (20 * E1).log() - 2 * ((3 * R(T).log()).log() + 1).log()


def eps_L(L):
    """(a+)^2/2 - L/2 = sqrt(5L/8) exp(-L/4) + (5/16) exp(-L/2) (Lemma 3.3)."""
    L = R(L)
    return (R(5) * L / 8).sqrt() * (-L / 4).exp() + R(5) / 16 * (-L / 2).exp()


def aplus_of(L):
    L = R(L)
    return L.sqrt() + R(QQ(5) / 8).sqrt() * (-L / 4).exp()


def k0_of(T):
    return T - T // 2


def B0_of(T, c1):
    L = L_of(T)
    a = L.sqrt()
    k0 = k0_of(T)
    return L + (R(k0) / (a + 2) ** 2).log() - c1 - R(k0).log() / (2 * k0) - R(1) / k0


def B_of(T, c1):
    return (1 - (-R(j0_of(T))).exp()) * B0_of(T, c1)


def form_simplified(T, c=QQ(146) / 10):
    """3 log T - log log T - 2 log(log log T + 2.1) - 14.6."""
    lT = R(T).log()
    return 3 * lT - lT.log() - 2 * (lT.log() + R(21) / 10).log() - R(c)


def form_clean(T, c=QQ(152) / 10):
    """3 log T - 2 log log T - 15.2."""
    lT = R(T).log()
    return 3 * lT - 2 * lT.log() - R(c)


def form_clean8(T):
    """3 log T - 8 log log T."""
    lT = R(T).log()
    return 3 * lT - 8 * lT.log()


def C1_holds(T):
    return L_of(T) >= R(QQ(145) / 10)


def C2_holds(T, Gfac=QQ(88) / 10):
    """j_0 (G e + 1) <= T_1 - 1 with G = Gfac exp(L/2)."""
    return j0_of(T) * (R(Gfac) * E1 * (L_of(T) / 2).exp() + 1) <= R(T // 2 - 1)


def C3_holds(T):
    return R(k0_of(T)) >= PI ** 2 * E1 ** 2 * (aplus_of(L_of(T)) + 2) ** 2


def T0_least(target=QQ(145) / 10, lo=10 ** 3, hi=10 ** 7):
    """Least integer T in (lo, hi] with L_low(T) >= target (L_low is increasing, bisection)."""
    tg = R(target)
    if L_low(lo) >= tg or not (L_low(hi) >= tg):
        raise ValueError("bracket")
    while hi - lo > 1:
        m = (lo + hi) // 2
        v = L_low(m)
        if v >= tg:
            hi = m
        elif v < tg:
            lo = m
        else:
            raise ValueError("ball straddles the target at T = %d" % m)
    return hi
