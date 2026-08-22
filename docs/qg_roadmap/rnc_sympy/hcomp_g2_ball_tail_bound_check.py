"""
G2 gate check (J4-1017 follow-on): domain-restricted heatHessMult integral -- Gaussian tail
correction rate, sympy-verified BEFORE Lean.

QUESTION: HeatHessianMomentCancellation.lean's `integral_heatHessMult_eq_zero` gives the EXACT
cancellation ∫_{R^n} heatHessMult τ p q v dv = 0 over the FULL space.  nb's actual integration domain
(after the CoV of HCompNearCarryKPrimeBaseFieldCoV.lean, J4-1010) is a BOUNDED set S' (an opaque
IFT neighbourhood of the origin, image of ball x ρ under the chart) -- NOT all of R^n.  So the
restricted integral ∫_{ball 0 R} heatHessMult τ p q v dv = -∫_{ball 0 R}^c heatHessMult τ p q v dv
(complement), and we need the SIZE of this tail/boundary correction.

ELEMENTARY BOUND CLAIM (to verify): for FIXED R>0 (ball radius NOT shrinking with τ), as τ -> 0,
    ∫_{||v||>R} ||v||^k * G_τ(v) dv  <=  exp(-R^2/(8τ)) * 2^(n/2) * n * c_k * (sqrt 2)^k * (sqrt τ)^k
via the elementary exponent-split trick:
    exp(-||v||^2/(4τ)) = exp(-||v||^2/(8τ)) * exp(-||v||^2/(8τ))
                       <= exp(-R^2/(8τ)) * exp(-||v||^2/(8τ))          for ||v|| > R
so  ||v||^k G_τ(v) * 1_{||v||>R}  <=  exp(-R^2/(8τ)) * 2^(n/2) * ||v||^k * G_{2τ}(v)   POINTWISE for ALL v
(trivial for ||v||<=R since LHS=0<=RHS), then integrate using the ALREADY-BANKED
pow_norm_mul_gauss_integral (S4b, GaussianMomentEnvelope.lean) at kappa=2.

This script checks, for the 1-D reduction (n=1, k in {0,1,2,3}):
  (a) the pointwise exponent-split inequality itself (symbolic, for v>R>0, tau>0);
  (b) that exp(-R^2/(8*tau)) * tau^(-a) -> 0 as tau -> 0+ for FIXED R>0, for any polynomial power a
      (i.e. the tail beats ANY power of tau, in particular the target sqrt(tau) rate);
  (c) that integrating the tail bound over the sliver tau in (0, eps) gives a contribution that is
      o(sqrt(eps)) as eps -> 0 -- i.e. it is NEGLIGIBLE relative to the O(sqrt eps) target rate the
      heatHessMult Lipschitz-weight payoff (J4-998 integral_heatHessMult_mul_lipschitz) already
      delivers from the FULL-SPACE integral.
"""
from sympy import (symbols, exp, sqrt, oo, limit, integrate, simplify, Rational,
                    S, pi, series, Symbol, log)

v, R, tau, eps, a, k = symbols('v R tau eps a k', positive=True)

print("=" * 70)
print("(a) pointwise exponent-split inequality: v > R > 0, tau > 0")
print("=" * 70)
# claim: exp(-v**2/(4*tau)) <= exp(-R**2/(8*tau)) * exp(-v**2/(8*tau))  for v > R
lhs = exp(-v**2 / (4*tau))
rhs = exp(-R**2/(8*tau)) * exp(-v**2/(8*tau))
diff = simplify(log(rhs) - log(lhs))   # want >= 0 for v > R
print("log(rhs) - log(lhs) =", diff, " (want this to reduce to (v^2-R^2)/(8tau) >= 0 for v>R)")
diff_expected = (v**2 - R**2) / (8*tau)
print("matches (v^2-R^2)/(8tau):", simplify(diff - diff_expected) == 0)

print()
print("=" * 70)
print("(b) exp(-R^2/(8tau)) beats every polynomial power of tau as tau->0+, R fixed>0")
print("=" * 70)
for aa in [Rational(-5,1), Rational(-2,1), Rational(-1,2), 0, Rational(1,2), 3]:
    Rval = 1  # fixed numeric R for the limit check (symbolic R also works, sign is what matters)
    expr = tau**aa * exp(-Rational(1,8)*tau**-1)   # R=1
    lim = limit(expr, tau, 0, dir='+')
    print(f"  a={aa}: lim_{{tau->0+}} tau^a * exp(-1/(8 tau)) = {lim}")

print()
print("=" * 70)
print("(c) sliver integral of the tail bound is o(sqrt(eps)) as eps -> 0+")
print("=" * 70)
# tail bound (up to a constant, R fixed, k up to 3, using worst-case extra tau^{-2} prefactor from
# heatHessMult's own 1/(4 tau^2) singular coefficient, cf. abs_heatHessMult_le):
#   T(tau) := tau^(-2) * exp(-R^2/(8 tau)) * tau^{k/2}   (k<=3 -> exponent -2+k/2 >= -2)
# integrate over tau in (0, eps) and compare against sqrt(eps).
Rv = 1
for kk in [0, 1, 2, 3]:
    Ttau = tau**(-2 + Rational(kk, 2)) * exp(-Rational(Rv**2, 8) / tau)
    Ieps = integrate(Ttau, (tau, 0, eps))
    Ieps = simplify(Ieps)
    ratio = simplify(Ieps / sqrt(eps))
    lim0 = limit(ratio, eps, 0, dir='+')
    print(f"  k={kk}: integral_0^eps T(tau) dtau = {Ieps}")
    print(f"         ratio to sqrt(eps), limit as eps->0+ : {lim0}  (want 0 => o(sqrt eps))")

print()
print("DONE.")
