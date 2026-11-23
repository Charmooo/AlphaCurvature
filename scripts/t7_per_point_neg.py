"""The per-point form for alpha < 0 (test T7 of the development plan; numerical, uncertified).

Z(q) = sum_i q_i H_i(q) with each monomial of Z assigned to one variable by a rule; then
Psi(y; q) = sum_i m_i(y) H_i(q). The conjecture needs Z > 0 for alpha < 0, so we want Psi > 0.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sympy as sp, mpmath as mp
from t6_per_point import alphaNum, q
mp.mp.dps = 40

def terms_for(al, t, rule):
    P = sp.Poly(alphaNum(sp.Float(al, 40), sp.Float(t, 40), sp.Integer(1)), *q)
    out = []
    for mon, c in P.terms():
        idx = [i for i in range(5) if mon[i] > 0]
        if not idx: continue
        i = rule(idx, al); e = list(mon); e[i] -= 1
        out.append((i, tuple(e), c))
    return out

def psi(terms, al, y, others, prec=False):
    f = mp.mpf if prec else float
    def mono(z):
        z = f(z); v = z**f(al)
        return [v, v**2, z*v, z*v**2, z*v**3]
    m = mono(y); Q = [sum(c) for c in zip(*([m] + [mono(z) for z in others]))]
    vals = [(mp.mpf(str(c)) if prec else float(c))*m[i]*
            (mp.fprod([Q[j]**e[j] for j in range(5)]) if prec else np.prod([Q[j]**e[j] for j in range(5)]))
            for i, e, c in terms]
    return sum(vals), sum(abs(v) for v in vals)

deg = lambda al: [al, 2*al, 1+al, 1+2*al, 1+3*al]
rules = {
    'index-top (alphaPsi)': lambda idx, al: max(idx),
    'index-bottom': lambda idx, al: min(idx),
    'degree-top': lambda idx, al: max(idx, key=lambda i: deg(al)[i]),
    'degree-bottom': lambda idx, al: min(idx, key=lambda i: deg(al)[i]),
}
rng = np.random.default_rng(10)
for name, rule in rules.items():
    for al in (-0.9, -0.5, -0.1):
        res = []
        for t in (1.01, 2.0, 100.0, 1e4):
            terms = terms_for(al, t, rule)
            worst, arg = np.inf, None  # want Psi > 0: track min of Psi/scale
            for _ in range(3000):
                y = 10**rng.uniform(-4, 4); oth = list(10**rng.uniform(-4, 4, rng.integers(0, 6)))
                s, sc = psi(terms, al, y, oth)
                if s/sc < worst: worst, arg = s/sc, (y, oth)
            if worst < 1e-6:
                s, sc = psi(terms, al, *arg, prec=True); worst = float(s/sc)
            res.append(f't={t}: {worst:+.2e}' + (f' (y={arg[0]:.2g}, oth={[f"{z:.2g}" for z in arg[1]]})'
                                                 if worst < 0 else ''))
        print(f'{name} alpha={al}: ' + '; '.join(res), flush=True)
