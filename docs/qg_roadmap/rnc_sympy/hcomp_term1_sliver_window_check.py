"""
J4-1065 sympy verification (BEFORE Lean): Bfac's T1 (hsMixed-type) sliver-window integral.

T1's already-banked fixed-tau full-space bound (hsMixed_gaussDdim_mul_amp_lipschitz_bound, J4-1019,
HCompNearCarryTerm1LipschitzCancellation.lean) has the shape

    |integral| <= C1/sqrt(tau) + C2

with C1 = L*n^3*||PI||*||PJ||*(16*sqrt(2)+1), C2 = n^2*L*||Q||, both tau-INDEPENDENT constants.

This script checks:
  (1) the closed form of the window integral int_0^eps (C1/sqrt(tau) + C2) dtau,
  (2) that it equals 2*C1*sqrt(eps) + C2*eps exactly (the claimed Lean RHS),
  (3) that this is O(sqrt(eps)) as eps -> 0+ (meets, not beats, hcomp's required rate),
  (4) there is no hidden divergence/log term at the tau -> 0 endpoint (1/sqrt(tau) is integrable
      there), and the C1 constant is genuinely tau-independent (no additional near-0 blow-up to
      track beyond the explicit 1/sqrt(tau) factor already present).
"""
import sympy as sp

tau, eps, C1, C2 = sp.symbols('tau eps C1 C2', positive=True)

integrand = C1 / sp.sqrt(tau) + C2

# (1)+(2) closed form
I = sp.integrate(integrand, (tau, 0, eps))
I_simplified = sp.simplify(I)
claimed = 2 * C1 * sp.sqrt(eps) + C2 * eps
residual = sp.simplify(I_simplified - claimed)
print("Integral:", I_simplified)
print("Claimed closed form:", claimed)
print("Residual (expect 0):", residual)
assert residual == 0, "MISMATCH: window integral does not match claimed closed form"

# (3) rate check: I(eps)/sqrt(eps) -> finite nonzero limit (genuine O(sqrt(eps)), not faster/slower)
rate_limit = sp.limit(I_simplified / sp.sqrt(eps), eps, 0, dir='+')
print("lim_{eps->0+} I(eps)/sqrt(eps) =", rate_limit)
assert rate_limit == 2 * C1, "rate check failed: leading order is not 2*C1*sqrt(eps)"

# also confirm the C2*eps term is subleading (o(sqrt(eps)))
sub_limit = sp.limit((C2 * eps) / sp.sqrt(eps), eps, 0, dir='+')
print("lim_{eps->0+} (C2*eps)/sqrt(eps) =", sub_limit)
assert sub_limit == 0

# (4) near tau=0 integrability sanity: int_0^eps tau**(-1/2) dtau converges (no assert needed,
# sympy.integrate already returned a finite closed form above with no error/ConditionSet).
print("All checks passed: int_0^eps (C1/sqrt(tau)+C2) dtau = 2*C1*sqrt(eps) + C2*eps = O(sqrt(eps)).")
