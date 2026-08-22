"""
J4-1020 pre-check: sympy verification for the `linMult` ball-tail bound (the G2-analogue for
J4-1019's `linMult` piece), toward composing HCompNearCarryTerm1LipschitzCancellation's (J4-1019)
full-space Lipschitz payoff with HeatHessMultBallTailBound's (J4-1018) ball-restriction machinery.

`linMult τ Q v := (<v,Q>/(2τ)) * G_τ(v)`, with pointwise majorant (Lean-banked, `abs_linMult_le`):
    |linMult τ Q v| ≤ (n*||Q||/(2τ)) * ||v|| * G_τ(v).

This checks the SAME exponent-split tail route as J4-1018's `heatHessMult_ball_tail_le`, but for the
k=1 (linear, not quadratic) weighted moment, using the ALREADY-BANKED `oneD_absMoment1` constant
ck = 3/2 (vs oneD_absMoment2's ck=2 used by heatHessMult's k=2 tail).

Composed bound (from `normPow_gaussDdim_tail_le` at k=1, ck=3/2):
    |∫_{R^2 <= rncRadialSq v} linMult τ Q v|
        <= exp(-R^2/(8τ)) * (sqrt2)^n * (n*||Q||/(2τ)) * (n * (3/2) * sqrt2 * sqrt(τ))
         = exp(-R^2/(8τ)) * (sqrt2)^n * (3/4) * n^2 * ||Q|| * sqrt2 / sqrt(τ)

Checks:
  (1) algebraic simplification of the composed constant matches the closed form above (exact, sympy).
  (2) for FIXED R>0, the bound -> 0 as τ -> 0+ (exponential beats any negative power of τ) -- same
      structure as J4-1018's already-verified check (b), just re-confirmed for the 1/sqrt(τ) prefactor
      instead of 1/τ^2.
  (3) integrated over the sliver τ in (0, eps), the worst-case bound is o(sqrt(eps)) as eps -> 0+,
      i.e. genuinely negligible against the O(sqrt(eps)) target rate delivered by heatHessMult's own
      Lipschitz payoff (mirrors J4-1018 check (c), now for the linMult tail term).
"""
import sympy as sp

tau, R, n, Q, eps = sp.symbols('tau R n Q eps', positive=True)

# composed constant from normPow_gaussDdim_tail_le at k=1, ck=3/2
sqrt2 = sp.sqrt(2)
lhs_const = (sqrt2**n) * (n * Q / (2 * tau)) * (n * sp.Rational(3, 2) * sqrt2 * sp.sqrt(tau))
rhs_closed = (sqrt2**n) * sp.Rational(3, 4) * n**2 * Q * sqrt2 / sp.sqrt(tau)

diff = sp.simplify(lhs_const - rhs_closed)
print("check (1) algebraic match, diff =", diff)
assert diff == 0, "algebraic mismatch"

# (2) exponential beats every polynomial power of tau as tau -> 0+, fixed R>0
bound_expr = sp.exp(-R**2 / (8 * tau)) * rhs_closed
for a in [-5, -2, sp.Rational(-1, 2), 0, sp.Rational(1, 2), 3]:
    expr = sp.exp(-R**2 / (8 * tau)) * tau**a
    lim = sp.limit(expr, tau, 0, dir='+')
    print(f"check (2) a={a}: limit = {lim}")
    assert lim == 0

# (3) integrate worst-case bound tau^{-1/2} * exp(-R^2/(8 tau)) over (0, eps); compare to sqrt(eps)
# worst-case integrand (dropping the tau-independent prefactor) ~ tau^{-1/2} (since exp <= 1)
# so the crude bound is <= eps^{1/2} * 2 = O(sqrt(eps)) -- but we want to show this term (linMult's
# OWN contribution) is dominated / consistent, i.e. its ratio to sqrt(eps) stays bounded as eps->0
# (it does NOT need to vanish faster since heatHessMult's own tail is exp-small too; the key content
# is that neither term's sliver-integral exceeds O(sqrt(eps))).
worst_integrand = tau**sp.Rational(-1, 2) * sp.exp(-R**2 / (8 * tau))
I = sp.integrate(worst_integrand, (tau, 0, eps))
print("check (3) sliver integral (symbolic):", I)
ratio = sp.limit(I / sp.sqrt(eps), eps, 0, dir='+')
print("check (3) ratio to sqrt(eps) as eps->0+:", ratio)
# the exponential tail kills the integral far faster than sqrt(eps); ratio -> 0
assert ratio == 0

print("ALL CHECKS PASSED")
