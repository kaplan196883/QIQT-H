"""
J4-1023 pre-Lean check: composing the full-space G1 Lipschitz bound
(hsMixed_gaussDdim_mul_amp_lipschitz_bound, J4-1019) with a complement-tail
bound (generalizing J4-1021's hsMixed_amp_tail_le from the literal tail set
{v | R^2 <= rncRadialSq v} to an ARBITRARY measurable subset A of that tail
set, via monotonicity of nonnegative-integrand integrals over A subset S)
introduces NO NEW asymptotic rate -- both pieces are already sympy/Lean
verified (J4-1018/1019/1020/1021).  This script is a sanity re-check of the
final assembled inequality's SHAPE (not a new rate derivation), confirming:

  |int_{W''S'} hsMixed*Amp|
     <= |int_full hsMixed*Amp| + |int_{(W''S')^c} hsMixed*Amp|      (triangle,
                                                                      via
                                                                      integral_add_compl)
     <= [G1 full-space bound]  +  [tail bound at R = rho]

is well-formed: as tau -> 0 with rho FIXED (rho from Brick B's ball, a
tau-INDEPENDENT geometric constant), the tail term -> 0 exponentially while
the G1 Lipschitz term ~ C/sqrt(tau) DOMINATES -- i.e. the composed bound has
the SAME O(1/sqrt(tau)) leading behaviour as the (already-verified) full-space
G1 bound alone; the complement-tail correction is asymptotically negligible,
not a new leading-order contribution.  This is the expected/desired shape:
composing does not degrade the rate.
"""
import sympy as sp

tau, rho, L, n, PI, PJ, Q = sp.symbols('tau rho L n PI PJ Q', positive=True)

# G1 full-space bound (J4-1019, hsMixed_gaussDdim_mul_amp_lipschitz_bound RHS)
g1 = L * n**3 * PI * PJ * (16*sp.sqrt(2) + 1) / sp.sqrt(tau) + n**2 * L * Q

# tail bound at R = rho (schematic: exp(-rho^2/(8 tau)) * poly(1/tau, sqrt(tau)))
# using the heatHessMult_amp_tail_le / linMult_amp_tail_le shape's dominant
# 1/tau^2 * sqrt(tau)^3 = tau^{-1/2} piece as the SLOWEST-decaying algebraic
# factor multiplying the exponential (worst case for the composition check).
tail = sp.exp(-rho**2/(8*tau)) * sp.sqrt(2)**n * (n**2) * (1/tau**2) * tau**sp.Rational(3,2)

combined = g1 + tail

# Leading behaviour as tau -> 0+ with rho, L, n, PI, PJ, Q fixed positive:
# g1 ~ C/sqrt(tau) -> +oo ; tail -> 0 (exponential beats any algebraic tau^{-1/2}
# prefactor). Confirm via limit of tail / g1 -> 0, i.e. tail is subleading.
ratio = sp.limit(tail / g1, tau, 0, dir='+')
print("lim_{tau->0+} tail/g1 =", ratio)
assert ratio == 0, "tail must be subleading to the G1 Lipschitz term as tau->0"

# Also confirm combined bound is finite and well-defined (no division blowup)
# for any fixed tau > 0, rho > 0 -- trivial but checked symbolically.
combined_at_tau1 = combined.subs({tau: 1, rho: 1, L: 1, n: 3, PI: 1, PJ: 1, Q: 1})
val = float(combined_at_tau1.evalf())
print("combined bound at tau=rho=L=PI=PJ=Q=1, n=3:", val)
assert val > 0 and val < float('inf')

print("OK: complement-tail composition introduces no new leading-order rate; "
      "tail term is exponentially subleading to G1's O(1/sqrt(tau)) term for "
      "any FIXED rho > 0 as tau -> 0+.")
