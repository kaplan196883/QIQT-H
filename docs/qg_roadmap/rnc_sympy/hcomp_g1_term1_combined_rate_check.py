"""
G1 gate combined-rate sympy check (J4-1017 identity + J4-998 heatHessMult Lipschitz payoff +
new linMult analog), toward `nb`'s Bfac term1.

hsMixed(tau, U, PI, PJ, Q) * G_tau(U)  =  heatHessMult(tau,PI,PJ,U)  -  linMult(tau,Q,U)

where linMult(tau,Q,v) := (<v,Q>/(2 tau)) * G_tau(v).

Both heatHessMult and linMult have EXACT full-space zero integral (M0/M1/M2 moments), so for a
Lipschitz (modulus L, at 0) amplitude weight f:

  |int heatHessMult * f|  <=  L * n^3 * ||PI|| * ||PJ|| * (16 sqrt2 + 1) / sqrt(tau)     [BANKED, J4-998]
  |int linMult * f|       <=  n^2 * L * ||Q||                                            [claimed here, O(1)]

Check 1: derive the linMult bound's rate by hand (mirroring the heatHessMult derivation) and confirm
it is O(1) in tau (no blow-up as tau -> 0, and no need for it to decay -- it merely must not dominate
the O(1/sqrt(tau)) heatHessMult term, and must integrate over the sliver tau in (0,eps) to something
o(sqrt(eps))).

Check 2: combined bound is  C1/sqrt(tau) + C2  (heatHessMult O(tau^{-1/2}) + linMult O(1)).  Integrate
worst-case over tau in (0,eps):
    int_0^eps (C1/sqrt(tau) + C2) dtau = C1 * 2*sqrt(eps) + C2*eps.
This is O(sqrt(eps)) overall (C1*2*sqrt(eps) dominates; C2*eps = o(sqrt(eps))) -- i.e. the SAME target
rate `hcomp`'s nb needs, not worsened by the linMult piece.
"""
import sympy as sp

tau, n, Lc, normPI, normPJ, normQ, eps, C1, C2 = sp.symbols(
    'tau n L norm_PI norm_PJ norm_Q eps C1 C2', positive=True)

# --- linMult pointwise bound derivation ---------------------------------------------------------
# |linMult(v)| <= (n*||Q||/(2 tau)) * ||v|| * G_tau(v)      (abs_dot_le: |<v,Q>| <= n*||v||*||Q||)
# |linMult(v)*(f(v)-f(0))| <= (n*||Q||/(2 tau)) * ||v||^2 * G_tau(v) * L      (Lipschitz: |f(v)-f(0)|<=L||v||)
# integral of ||v||^2 * G_tau(v) over R^n  <=  n * 2 * tau     (k=2 sup-norm moment envelope, ck=2, kappa=1)
c1_coef = (n * normQ) / (2 * tau) * Lc
k2_moment_bound = n * 2 * tau
linMult_bound = sp.simplify(c1_coef * k2_moment_bound)
print("linMult Lipschitz bound (raw):", linMult_bound)
# expect: n^2 * L * norm_Q  (tau cancels exactly)
expected_linMult_bound = n**2 * Lc * normQ
print("matches n^2*L*norm_Q exactly:", sp.simplify(linMult_bound - expected_linMult_bound) == 0)

# --- combined worst-case sliver integral --------------------------------------------------------
heatHess_bound = C1 / sp.sqrt(tau)
linMult_bound_tau_indep = C2  # constant in tau, matches derivation above
combined = heatHess_bound + linMult_bound_tau_indep

sliver_integral = sp.integrate(combined, (tau, 0, eps))
print("sliver integral (0,eps) of combined bound:", sp.simplify(sliver_integral))
# expect: 2*C1*sqrt(eps) + C2*eps

# order check: as eps -> 0+, is C2*eps = o(sqrt(eps))?  i.e. limit of (C2*eps)/sqrt(eps) -> 0
ratio = sp.limit(sp.simplify(C2 * eps) / sp.sqrt(eps), eps, 0, dir='+')
print("lim_{eps->0+} (C2*eps)/sqrt(eps) =", ratio, " (expect 0 -> genuinely o(sqrt(eps)), does not worsen rate)")

# sanity: the dominant 2*C1*sqrt(eps) term IS O(sqrt(eps)) (ratio -> const, not 0, not infinite)
ratio2 = sp.limit(sp.simplify(2 * C1 * sp.sqrt(eps)) / sp.sqrt(eps), eps, 0, dir='+')
print("lim_{eps->0+} (2*C1*sqrt(eps))/sqrt(eps) =", ratio2, " (expect 2*C1, confirming O(sqrt(eps)) rate is exact, unchanged)")
