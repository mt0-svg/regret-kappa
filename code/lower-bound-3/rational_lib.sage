# Exact rational bounds of the certificate of Lemma 3.1 (b) (see drift_rational.sage).
# Loaded after common.sage.

N = 40


def P(q, N=N):
    t, acc = QQ(1), QQ(1)
    for n in range(1, N + 1):
        t = t * q / n
        acc += t
    return acc


def Cc(y, N=N):
    t, acc = QQ(1), QQ(1)
    for n in range(1, N + 1):
        t = t * y / ((2 * n - 1) * (2 * n))
        acc += t
    return acc


def E(q, N=N):
    if not (0 <= q < N + 2):
        raise ValueError("E_N needs 0 <= q < N + 2")
    return P(q, N) + q ** (N + 1) * (N + 2) / (factorial(N + 1) * (N + 2 - q))


def E_wrong(q, N=N):
    """Tail bound without the geometric factor: not an upper bound of e^q (negative control)."""
    return P(q, N) + q ** (N + 1) / factorial(N + 1)


def bound(lo, hi, s, K=K_G):
    q_lo = (lo ** 2 * (1 - s) + s) / 2
    y_lo = lo ** 2 * s * (1 - s)
    return K * P(q_lo) * Cc(y_lo) - K * E(hi ** 2 / 2) - 1


def certify_cell(j, moves, K=K_G, maxdepth=20):
    s = moves[j]
    stack = [(QQ(j) / 10, QQ(j + 1) / 10, 0)]
    leaves = []
    while stack:
        a, b, d = stack.pop()
        v = bound(a, b, s, K)
        if v >= 0:
            leaves.append((a, b, d, v))
        elif d >= maxdepth:
            return False, leaves, (a, b)
        else:
            m = (a + b) / 2
            stack.append((m, b, d + 1))
            stack.append((a, m, d + 1))
    return True, leaves, None
