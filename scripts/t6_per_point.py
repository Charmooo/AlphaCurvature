"""How the per-point form was found (test T6 of the development plan; numerical, uncertified).

Z(q) = sum_i q_i H_i(q); Psi(y; q) = sum_i m_i(y) H_i(q); Z = sum_k Psi(y_k; q).
H = H0 (Euler) + J, J_i = sum_j A_ij(q) q_j, A antisymmetric with affine entries.
LP: maximize eps s.t. Psi_s / |row_s| <= -eps on samples.
"""
import itertools, sys
import numpy as np, sympy as sp
from scipy.optimize import linprog

q = sp.symbols('q0:5')

def alphaNum(al, a, b):
    A, B = a**al, b**al
    def BD(Pa, P2a, W, P12, x, X):
        return ((2*Pa*(al*X/x) - 2*al*X**2/x)*W + (Pa**2 - P2a)*((1+al)*X)
                - 2*(al*X/x)*P12 - 2*Pa*((1+2*al)*X**2) + 2*((1+3*al)*X**3))
    Pa, P2a, W = A+B+q[0], A**2+B**2+q[1], a*A+b*B+q[2]
    P12, P13 = a*A**2+b*B**2+q[3], a*A**3+b*B**3+q[4]
    Bv = (Pa**2 - P2a)*W - 2*Pa*P12 + 2*P13
    return sp.expand(W*(BD(Pa, P2a, W, P12, a, A) - BD(Pa, P2a, W, P12, b, B))
                     - 2*Bv*((1+al)*A - (1+al)*B))

def mono(al, y):
    v = y**al
    return np.array([v, v**2, y*v, y*v**2, y*v**3])

def setup(al, t):
    Z = alphaNum(sp.Float(al, 30), sp.Float(t, 30), sp.Integer(1))
    P = sp.Poly(Z, *q)
    assert abs(P.coeff_monomial(1)) < 1e-12 * max(abs(c) for c in P.coeffs())
    Zd = {d: sum(c*sp.prod([x**e for x, e in zip(q, m)]) for m, c in P.terms() if sum(m) == d)
          for d in (1, 2, 3)}
    H0 = [sum(sp.diff(Zd[d], q[i])/d for d in (1, 2, 3)) for i in range(5)]
    H0f = sp.lambdify(q, H0, 'numpy')
    Zf = sp.lambdify(q, Z, 'numpy')
    return H0f, Zf

pairs = list(itertools.combinations(range(5), 2))
def row(al, H0f, y, others):
    m = mono(al, y)
    Q = m + sum((mono(al, z) for z in others), np.zeros(5))
    psi0 = float(np.dot(m, np.array(H0f(*Q), dtype=float)))
    coefs = []
    for i, j in pairs:
        base = m[i]*Q[j] - m[j]*Q[i]
        coefs.append(base)
        coefs.extend(Q[l]*base for l in range(5))
    return psi0, np.array(coefs), Q

def sample(rng, n):
    out = []
    for _ in range(n):
        y = 10**rng.uniform(-3, 3)
        r = rng.integers(0, 6)
        out.append((y, list(10**rng.uniform(-3, 3, r))))
    return out

def run(al, t, rng, ntrain=6000, ntest=20000, verbose=False):
    H0f, Zf = setup(al, t)
    # check the identity Z = sum_k Psi0 on a random configuration
    ys = list(10**rng.uniform(-1, 1, 4))
    Q = sum(mono(al, y) for y in ys)
    tot = sum(np.dot(mono(al, y), np.array(H0f(*Q), dtype=float)) for y in ys)
    assert abs(tot - Zf(*Q)) <= 1e-8*abs(Zf(*Q)), (tot, Zf(*Q))
    R, c0 = [], []
    for y, oth in sample(rng, ntrain):
        p0, cf, _ = row(al, H0f, y, oth)
        nrm = np.sqrt(p0**2 + cf @ cf)
        R.append(cf/nrm); c0.append(p0/nrm)
    R, c0 = np.array(R), np.array(c0)
    nv = R.shape[1]
    # variables: A (nv), eps. constraint: R A + eps <= -c0. maximize eps
    A_ub = np.hstack([R, np.ones((len(R), 1))])
    res = linprog(np.r_[np.zeros(nv), -1.0], A_ub=A_ub, b_ub=-c0,
                  bounds=[(-1e8, 1e8)]*nv + [(None, 1.0)], method='highs')
    if res.status != 0:
        return None, None, None
    Aopt, eps = res.x[:nv], res.x[-1]
    # holdout
    worst = -np.inf; worst0 = -np.inf
    for y, oth in sample(rng, ntest):
        p0, cf, _ = row(al, H0f, y, oth)
        nrm = np.sqrt(p0**2 + cf @ cf)
        worst = max(worst, (p0 + cf @ Aopt)/nrm)
        worst0 = max(worst0, p0/nrm)
    return eps, worst, worst0

if __name__ == '__main__':
    rng = np.random.default_rng(6)
    als = [float(x) for x in sys.argv[1:]] or [0.95, 0.99]
    for al in als:
        for t in (1.1, 2.0, 10.0, 100.0):
            eps, worst, worst0 = run(al, t, rng)
            print(f'alpha={al} t={t}: LP margin {eps}, holdout worst Psi/|row| {worst}, '
                  f'(Euler H0 alone: {worst0})', flush=True)
