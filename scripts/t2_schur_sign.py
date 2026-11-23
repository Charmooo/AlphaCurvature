"""Numerical test of the conjecture (test T2 of the development plan; numerical, uncertified).
Searches for violations of the Schur-Ostrowski sign of Scal_p = ((1+r)^2/2) N/W^2 (closed form, T1).

Conjecture: SO_ij := (rho_i - rho_j)(d_i Scal - d_j Scal) <= 0 for p > 2 (r > 0, Schur-concave),
>= 0 for p in (1,2) (r < 0, Schur-convex). Reported quantity: the "wrong-signed" part
  v = sign_conj * SO_ij / (|rho_i - rho_j| * (|d_i Scal| + |d_j Scal|)),  sign_conj = +1 (r>0), -1 (r<0)
so v > 0 is a violation; v is scale-free.
"""
import itertools, sys
import numpy as np
from scipy.optimize import minimize

def grad_scal(rho, r):
    n = len(rho)
    u = rho ** r
    W = np.sum(rho ** (1 + r))
    dW = (1 + r) * u
    N = 0.0
    dN = np.zeros(n)
    for T in itertools.combinations(range(n), 3):
        T = list(T)
        s, pi = rho[T].sum(), np.prod(u[T])
        N += s * pi
        for i in T:
            dN[i] += pi + s * r * pi / rho[i]
    c = (1 + r) ** 2 / 2
    return c * N / W ** 2, c * (dN / W ** 2 - 2 * N * dW / W ** 3)

def worst_v(rho, r):
    S, g = grad_scal(rho, r)
    sgn = 1.0 if r > 0 else -1.0
    best = -np.inf
    for i, j in itertools.combinations(range(len(rho)), 2):
        den = abs(rho[i] - rho[j]) * (abs(g[i]) + abs(g[j]))
        if den < 1e-300 or abs(rho[i] - rho[j]) < 1e-12:
            continue
        best = max(best, sgn * (rho[i] - rho[j]) * (g[i] - g[j]) / den)
    return best

rng = np.random.default_rng(0)
ps = [1.02, 1.1, 1.3, 1.5, 1.7, 1.9, 1.98, 2.02, 2.2, 2.5, 3, 4, 6, 10, 30, 1e6]
summary = []
for n in range(4, 9):
    for p in ps:
        r = 1 - 2 / p
        worst = -np.inf
        # random: Dirichlet with several concentrations (small alpha -> near the boundary)
        for alpha in (0.05, 0.2, 1.0, 5.0):
            X = rng.dirichlet([alpha] * n, size=400)
            X = np.clip(X, 1e-9, None); X /= X.sum(1, keepdims=True)
            for rho in X:
                worst = max(worst, worst_v(rho, r))
        # adversarial: maximize v over the simplex (softmax parametrization)
        def obj(z):
            rho = np.exp(z - z.max()); rho /= rho.sum()
            rho = np.clip(rho, 1e-12, None); rho /= rho.sum()
            v = worst_v(rho, r)
            return -v if np.isfinite(v) else 0.0
        for _ in range(12):
            z0 = rng.normal(scale=rng.choice([0.5, 2, 6]), size=n)
            res = minimize(obj, z0, method="Nelder-Mead", options={"maxiter": 3000, "xatol": 1e-10, "fatol": 1e-14})
            if -res.fun > worst:
                worst = -res.fun
        summary.append((n, p, worst))
        print(f"n={n} p={p:<8} worst v = {worst:+.3e}  {'VIOLATION?' if worst > 1e-8 else ''}", flush=True)
print("overall max v:", max(w for _, _, w in summary))
