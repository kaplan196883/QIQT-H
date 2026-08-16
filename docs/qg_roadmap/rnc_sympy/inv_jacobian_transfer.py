#!/usr/bin/env python3
"""
inv_jacobian_transfer.py  —  J4-797 sympy verification of the INVERSE-FUNCTION-THEOREM
first-jet error transfer that the mixed-sliver hJ3i/hJ3j hypotheses need.

Goal: confirm, symbolically and from scratch, the exponents/constants of the chain
    forward-Jacobian-gap  =>  inverse-Jacobian-gap
so the Lean primitive `invJacobian_sub_one_le` (operator-norm) targets the right shape.

Two independent checks:

 (A) The ALGEBRAIC operator-inverse perturbation:  for a linear map T = I - S with ‖S‖ = s,
     T is invertible (Neumann) and  T^{-1} - I = sum_{k>=1} S^k = S (I - S)^{-1}, so
        ‖T^{-1} - I‖ <= s/(1-s).
     On the coercivity radius s <= 1/2 this gives ‖T^{-1} - I‖ <= 2 s = 2 ‖S‖.
     We verify the geometric-series identity and the 2x bound numerically on random
     matrices (any dim) — this is the reusable kernel of the Lean brick.

 (B) The GEOMETRIC transfer through exp/inverse-chart in RNC:
        f(v) = v + (1/2) Gamma(v,v) + O(v^3)          (forward: exp_p in normal coords, minus base)
        Df(v) = I + Gamma(v, .) + O(v^2)              => ‖Df(v) - I‖ = O(‖v‖),  const ~ ‖Gamma‖
        g = f^{-1},  g(y) = y - (1/2) Gamma(y,y) + O(y^3)
        Dg(y) = (Df(g(y)))^{-1} = I - Gamma(y, .) + O(y^2)  => ‖Dg(y) - I‖ = O(‖y‖), same const
     We verify Dg(y) - I has ZERO constant term and leading term exactly -Gamma(y,.),
     matching hJ3i's exponent 1 with C_P ~ sup‖Gamma‖ (the SAME constant the forward gap carries).
"""
import sympy as sp
import numpy as np

print("="*80)
print("(A) operator-inverse perturbation  T = I - S,  ‖T^{-1}-I‖ <= ‖S‖/(1-‖S‖) <= 2‖S‖")
print("="*80)
rng = np.random.default_rng(0)
worst = 0.0
for dim in (2, 3, 4, 6):
    for _ in range(2000):
        S = rng.standard_normal((dim, dim))
        s = np.linalg.norm(S, 2)            # spectral (operator) norm
        if s > 0.5:                          # restrict to coercivity radius s <= 1/2
            S = S * (0.4 / s)
            s = np.linalg.norm(S, 2)
        T = np.eye(dim) - S
        Tinv = np.linalg.inv(T)
        lhs = np.linalg.norm(Tinv - np.eye(dim), 2)
        rhs_tight = s / (1 - s)
        rhs_2x = 2 * s
        assert lhs <= rhs_tight + 1e-9, (dim, lhs, rhs_tight)
        assert lhs <= rhs_2x + 1e-9,   (dim, lhs, rhs_2x)
        worst = max(worst, lhs / (2*s) if s > 0 else 0.0)
print("  PASS: ‖T^{-1}-I‖ <= s/(1-s) <= 2s on s<=1/2, all dims; worst lhs/(2s) =", round(worst, 4))

# symbolic geometric-series identity  T^{-1} - I = S (I - S)^{-1}
s = sp.symbols('s', nonnegative=True)
series = sp.summation(s**sp.symbols('k', integer=True, positive=True), (sp.symbols('k', integer=True, positive=True), 1, sp.oo))
closed = s/(1-s)
print("  symbolic sum_{k>=1} s^k =", sp.simplify(series - closed), "(0 => identity holds for |s|<1)")
print("  at s=1/2: bound s/(1-s) =", sp.nsimplify(closed.subs(s, sp.Rational(1,2))), " ( = 1 = 2*(1/2), tight)")

print()
print("="*80)
print("(B) RNC geometric transfer:  Dg(y) - I  has zero const term, leading -Gamma(y,.)")
print("="*80)
# 2D symbolic: symmetric bilinear Gamma^k_{ab}, forward f, invert to 2nd order, differentiate.
for ndim in (2, 3):
    y = sp.symbols(f'y0:{ndim}', real=True)
    # Christoffel constants Gamma[k][a][b], symmetric in a,b
    G = [[[sp.symbols(f'G_{k}_{a}_{b}', real=True) for b in range(ndim)] for a in range(ndim)] for k in range(ndim)]
    for k in range(ndim):
        for a in range(ndim):
            for b in range(a):
                G[k][a][b] = G[k][b][a]
    eps = sp.symbols('eps', positive=True)   # bookkeeping order tag on y
    yv = [eps*yi for yi in y]

    def gamma(vec):  # Gamma(vec,vec)^k
        return [sum(G[k][a][b]*vec[a]*vec[b] for a in range(ndim) for b in range(ndim)) for k in range(ndim)]

    # inverse chart to 2nd order:  g(y) = y - 1/2 Gamma(y,y) + O(y^3)
    gy = [yv[k] - sp.Rational(1,2)*gamma(yv)[k] for k in range(ndim)]

    # forward f(v) = v + 1/2 Gamma(v,v);  Df(v) = I + [d/dv (1/2 Gamma(v,v))]
    v = sp.symbols(f'v0:{ndim}', real=True)
    fv = [v[k] + sp.Rational(1,2)*gamma(v)[k] for k in range(ndim)]
    Df = sp.Matrix([[sp.diff(fv[k], v[c]) for c in range(ndim)] for k in range(ndim)])

    # Dg(y) = (Df(g(y)))^{-1}, expanded to O(eps^1)
    Df_at_g = Df.subs({v[c]: gy[c] for c in range(ndim)})
    Dg = Df_at_g.inv()
    Dg_series = Dg.applyfunc(lambda e: sp.series(sp.expand(e), eps, 0, 2).removeO())
    I = sp.eye(ndim)
    diff = sp.simplify(Dg_series - I)
    # const term (eps^0) must be zero:
    const_term = diff.subs(eps, 0)
    # linear term (coeff of eps^1) must equal  -Gamma(y, .)  i.e. -d/dv Gamma at y contracted
    lin = diff.applyfunc(lambda e: sp.expand(e).coeff(eps, 1))
    # expected linear term: -(1/2) d/dv[Gamma(v,v)] evaluated at v=y  == -Gamma(y,.) (symmetric)
    expected = sp.Matrix([[ -sum((G[k][c][a]+G[k][a][c])*sp.Rational(1,2)*y[a] for a in range(ndim))
                            for c in range(ndim)] for k in range(ndim)])
    ok_const = const_term == sp.zeros(ndim, ndim)
    ok_lin = sp.simplify(lin - expected) == sp.zeros(ndim, ndim)
    print(f"  dim {ndim}:  Dg(y)-I const term zero: {ok_const};  leading term = -Gamma(y,.): {ok_lin}")

print()
print("CONCLUSION: hJ3i/hJ3j target  ‖Pi z - e_i‖ <= C_P ‖z‖  with C_P ~ sup‖Gamma‖,")
print("reached from the forward Jacobian gap ‖Df - I‖ <= K‖v‖ via the OPERATOR-INVERSE")
print("perturbation ‖T^{-1}-I‖ <= 2‖T-I‖ (on ‖T-I‖<=1/2).  Exponent 1, constant doubles. QED.")
