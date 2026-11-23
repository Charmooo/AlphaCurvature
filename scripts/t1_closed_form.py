"""Cross-check of the closed form (test T1 of the development plan; numerical, uncertified).
The closed form of the scalar curvature of the classical alpha-geometry vs. a direct computation
from the metric.

Metric on the open simplex, coordinates x_1..x_{n-1}, rho_n = 1 - sum x:
    g_ab = x_a^s delta_ab + rho_n^s,   s = 2/p - 2,
whose first and second partial derivatives are explicit. The direct value uses the coordinate
formula
    R_abcd = 1/2 (g_ad,bc + g_bc,ad - g_ac,bd - g_bd,ac) + g_ef (Gam^e_bc Gam^f_ad - Gam^e_bd Gam^f_ac),
    Scal   = g^ac g^bd R_abcd,
(convention: the round sphere has positive Scal; p = 2 is the calibration, Scal = (n-1)(n-2)/4).
Everything in mpmath at 40 digits.
"""
import itertools, random
import mpmath as mp

mp.mp.dps = 40

def scal_direct(n, p, x):
    m, s = n - 1, mp.mpf(2) / p - 2
    rn = 1 - sum(x)
    d = lambda a, b: 1 if a == b else 0
    g = mp.matrix(m, m)
    for a, b in itertools.product(range(m), repeat=2):
        g[a, b] = d(a, b) * x[a] ** s + rn ** s
    gi = g ** -1
    def dg(a, b, c):  # d_c g_ab
        return s * (d(a, b) * d(a, c) * x[a] ** (s - 1) - rn ** (s - 1))
    def ddg(a, b, c, e):  # d_c d_e g_ab
        return s * (s - 1) * (d(a, b) * d(a, c) * d(a, e) * x[a] ** (s - 2) + rn ** (s - 2))
    Gam1 = {(e, b, c): (dg(e, b, c) + dg(e, c, b) - dg(b, c, e)) / 2   # Gamma_{e,bc} (lowered)
            for e, b, c in itertools.product(range(m), repeat=3)}
    Gam = {(e, b, c): sum(gi[e, f] * Gam1[(f, b, c)] for f in range(m))
           for e, b, c in itertools.product(range(m), repeat=3)}
    def R(a, b, c, e):  # R_abce, with d playing "d" index renamed e
        t = (ddg(a, e, b, c) + ddg(b, c, a, e) - ddg(a, c, b, e) - ddg(b, e, a, c)) / 2
        t += sum(g[f, h] * (Gam[(f, b, c)] * Gam[(h, a, e)] - Gam[(f, b, e)] * Gam[(h, a, c)])
                 for f in range(m) for h in range(m))
        return t
    return sum(gi[a, c] * gi[b, e] * R(a, b, c, e)
               for a, b, c, e in itertools.product(range(m), repeat=4))

def scal_closed(n, p, rho):
    r = 1 - mp.mpf(2) / p
    W = sum(t ** (1 + r) for t in rho)
    N = sum(sum(rho[i] for i in T) * mp.fprod(rho[i] ** r for i in T)
            for T in itertools.combinations(range(n), 3))
    return (1 + r) ** 2 / 2 * N / W ** 2

random.seed(1)
worst = mp.mpf(0)
for n in (3, 4, 5, 6):
    for p in (mp.mpf(3) / 2, mp.mpf(2), mp.mpf(3), mp.mpf(4), mp.mpf(10)):
        for _ in range(4):
            w = [mp.mpf(random.random()) + mp.mpf("0.01") for _ in range(n)]
            rho = [t / sum(w) for t in w]
            a, b = scal_direct(n, p, rho[:-1]), scal_closed(n, p, rho)
            worst = max(worst, abs(a - b) / max(1, abs(b)))
        print(f"n={n} p={mp.nstr(p,3):>4}  last: direct={mp.nstr(a,15):>20}  closed={mp.nstr(b,15):>20}", flush=True)
print("max relative |direct - closed| =", mp.nstr(worst, 5))
