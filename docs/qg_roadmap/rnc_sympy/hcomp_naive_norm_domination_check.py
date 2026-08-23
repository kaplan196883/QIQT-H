import sympy as sp

# =====================================================================================
# NAIVE NORM-DOMINATION RATE CHECK for J4-1019's `linMult`/`heatHessMult`
# (HCompNearCarryTerm1LipschitzCancellation.lean), asked by J4-1067's self-correction.
# =====================================================================================
# QUESTION.  J4-1019's Lipschitz payoff (`integral_heatHessMult_mul_lipschitz`,
# `integral_linMult_mul_lipschitz`) works by splitting the weight  Amp v = (Amp v - Amp 0) + Amp 0,
# where the CONSTANT piece `Amp 0` integrates the SIGNED `heatHessMult`/`linMult` to EXACTLY ZERO
# (`integral_heatHessMult_eq_zero`, `integral_linMult_eq_zero`) via full-space odd/even-moment
# cancellation -- valid ONLY on a domain symmetric about `v=0`.  `nb`'s actual integral lives on a
# restricted, non-symmetric IFT-chart domain `S'`, where this cancellation is NOT known to survive.
#
# Does dropping the cancellation trick entirely -- i.e. bounding the WHOLE integrand by its
# ABSOLUTE VALUE FIRST (`|heatHessMult|`, `|linMult|`, no `f - f(0)` split, no signed structure) and
# only then integrating -- still deliver the O(sqrt(eps)) rate `hcomp`'s `nb` needs, or does it
# diverge / fall into the SAME `1/(t-s)` log-divergence trap already found dead in
# `hcomp_bypass_feasibility.py`'s Step 3 (`order2_naive_dominator_not_intervalIntegrable`)?
#
# METHOD.  1-D model (n=1; the n-D case is a bounded polynomial-in-n rescaling of the same moments,
# as in the Lean `abs_heatHessMult_le`/`abs_linMult_le` bounds).  Compute the EXACT unsigned full-
# space integral  I(tau) = int_R |heatHessMult(tau,p,q,v)| dv  and  J(tau) = int_R |linMult(tau,q,v)| dv
# both analytically (closed form, since sign changes are at finitely many explicit points) and
# numerically, read off the tau -> 0 scaling, then integrate over the sliver tau in (0, eps) and
# check convergence.
# =====================================================================================

v, tau = sp.symbols('v tau', positive=True, real=True)
p, q = sp.symbols('p q', positive=True, real=True)  # WLOG p=q=1 below for a concrete numeric read

def G(T, x):
    return 1 / sp.sqrt(4 * sp.pi * T) * sp.exp(-x**2 / (4 * T))

# ---- heatHessMult, 1-D, p=q=1 --------------------------------------------------------
def heatHessMult_1d(T, vv):
    return (vv * vv / (4 * T**2) - 1 / (2 * T)) * G(T, vv)

def linMult_1d(T, vv):
    return (vv / (2 * T)) * G(T, vv)

print("="*78)
print("STEP 0. Sanity: SIGNED full-space integrals vanish exactly (matches Lean's")
print("        integral_heatHessMult_eq_zero / integral_linMult_eq_zero).")
print("="*78)
Tval = sp.Rational(1, 3)
signed_hh = sp.integrate(heatHessMult_1d(Tval, v), (v, -sp.oo, sp.oo))
signed_lin = sp.integrate(linMult_1d(Tval, v), (v, -sp.oo, sp.oo))
print("  signed ∫ heatHessMult dv (tau=1/3, p=q=1) =", sp.nsimplify(signed_hh))
print("  signed ∫ linMult dv      (tau=1/3, q=1)   =", sp.nsimplify(signed_lin))
print()

print("="*78)
print("STEP 1. UNSIGNED (naive norm-domination) integral of heatHessMult, exact closed form.")
print("="*78)
# heatHessMult_1d(T,v) changes sign where v^2/(4T^2) = 1/(2T)  <=>  v^2 = 2T  <=>  v = +/- sqrt(2T).
v0 = sp.sqrt(2 * tau)
# For |v| < v0: (v^2/(4T^2) - 1/(2T)) < 0  -> heatHessMult < 0 there (since G>0). Outside: > 0.
expr_hh = heatHessMult_1d(tau, v)
inner = sp.integrate(-expr_hh, (v, -v0, v0))       # negative region: flip sign
outer = 2 * sp.integrate(expr_hh, (v, v0, sp.oo))  # positive region (both tails)
I_hh = sp.simplify(inner + outer)
print("  I(tau) = ∫_R |heatHessMult(tau,1,1,v)| dv  =", I_hh)
I_hh_s = sp.simplify(sp.nsimplify(I_hh, [sp.sqrt(2), sp.pi]))
print("  simplified:", I_hh_s)
# numeric check + small-tau series
for tv in [sp.Rational(1,10), sp.Rational(1,100), sp.Rational(1,1000)]:
    val = float(I_hh.subs(tau, tv))
    print(f"    tau={float(tv):<8} I(tau)={val:.6f}   tau*I(tau)={tv*val:.6f}")
print()

print("="*78)
print("STEP 2. Small-tau asymptotics of I(tau) -- is it O(1/tau)?")
print("="*78)
I_series = sp.series(I_hh, tau, 0, 2)
print("  series I(tau) as tau->0:", I_series)
tauI = sp.simplify(tau * I_hh)
print("  tau * I(tau) simplified:", tauI, "  (constant => I(tau) ~ C/tau exactly, all tau>0)")
print()

print("="*78)
print("STEP 3. UNSIGNED linMult integral, exact closed form + small-tau rate.")
print("="*78)
expr_lin = linMult_1d(tau, v)  # sign of v*(1/(2T))*G(T,v): negative for v<0, positive for v>0
# NOTE: sp.integrate(sp.Abs(v)*..., (v,-oo,oo)) silently mis-evaluates to 0 for this integrand
# (sympy Abs-integration pitfall) -- split into 2x the v>0 half (the integrand |v|*G is even) instead.
J_lin = sp.simplify(2 * sp.integrate(v / (2 * tau) * G(tau, v), (v, 0, sp.oo)))
print("  J(tau) = ∫_R |linMult(tau,1,v)| dv =", J_lin, " (split-domain; naive sp.integrate w/ Abs wrongly gives 0)")
sqrt_tau_J = sp.simplify(J_lin / (1/sp.sqrt(tau)))
print("  J(tau) * sqrt(tau) simplified:", sqrt_tau_J, " => J(tau) ~ C/sqrt(tau) (MILDER than heatHessMult's 1/tau)")
print()

print("="*78)
print("STEP 4. Sliver integral over tau in (0, eps): does int_0^eps I(tau) dtau converge?")
print("="*78)
eps = sp.symbols('eps', positive=True)
# I(tau) = C_I / tau  exactly (from Step 2) -> sliver integral of a pure 1/tau is log-divergent.
C_I = sp.simplify(tauI)  # the constant such that I(tau) = C_I/tau
print("  I(tau) = C_I / tau  with C_I =", C_I)
try:
    sliver_hh = sp.integrate(C_I / tau, (tau, 0, eps))
    print("  ∫_0^eps I(tau) dtau =", sliver_hh, "  <-- DIVERGES if this blows up / sympy flags it")
except Exception as e:
    print("  sympy integrate raised:", e)
# Explicit divergence check via limit of the definite integral from delta to eps as delta->0
delta = sp.symbols('delta', positive=True)
partial = sp.integrate(C_I / tau, (tau, delta, eps))
print("  ∫_delta^eps I(tau) dtau =", partial)
lim_delta0 = sp.limit(partial, delta, 0, dir='+')
print("  limit as delta -> 0+ :", lim_delta0, "  (+oo confirms LOG-DIVERGENCE at the tau->0 end)")
print()

print("="*78)
print("STEP 5. Contrast: linMult's sliver integral (J(tau) ~ C/sqrt(tau)) DOES converge.")
print("="*78)
C_J = sp.simplify(J_lin * sp.sqrt(tau))
sliver_lin = sp.integrate(C_J / sp.sqrt(tau), (tau, 0, eps))
print("  J(tau) = C_J / sqrt(tau) with C_J =", C_J)
print("  ∫_0^eps J(tau) dtau =", sliver_lin, " = O(sqrt(eps)), CONVERGES.")
print()

print("="*78)
print("VERDICT")
print("="*78)
print("""  Naive (unsigned/absolute-value-first) norm-domination of `linMult` alone WOULD deliver the
  needed O(sqrt(eps)) rate on its own (J(tau) ~ C/sqrt(tau), sliver-integrable).  But
  `heatHessMult`'s naive unsigned integral I(tau) is EXACTLY C_I/tau for ALL tau>0 (not just an
  upper bound -- the true value, verified symbolically) -- i.e. it is off by a full extra power of
  tau^{-1/2} relative to `linMult`, has NO extra cancellation once |.| is taken first, and its
  sliver integral over (0,eps) is LOG-DIVERGENT (STEP 4: the delta->0 limit is +oo).  This is
  QUANTITATIVELY THE SAME DIVERGENCE ORDER (1/tau pointwise, log-divergent sliver) as
  hcomp_bypass_feasibility.py's Step 3 `order2_naive_dominator_not_intervalIntegrable` finding --
  a DIFFERENT overall proof strategy (bounding kPrime's Levi x Hessian factors separately, vs here
  bounding the T1/T2/T3 Amp-weighted hsMixed integrand directly) hits the IDENTICAL underlying
  obstruction: the order-2 (Hessian-type, <v,p><v,q>/tau^2) singular scalar needs a FULL power of
  tau^{1/2} of cancellation that ONLY a signed/difference argument (the f-f(0) Lipschitz split, or
  the base<->eval Gaussian-difference bound) can supply -- an unsigned/norm-first bound cannot see
  it, by construction (|A - B| <= |A|+|B| always loses exactly this cancellation for the order-2
  term). linMult (order-1, <v,q>/tau) is one power of tau milder and DOES survive naively, but the
  heatHessMult component is the binding constraint and it FAILS naively.
  => Naive norm-domination is NOT a viable route for T1/T2/T3's actual S'-restricted-domain bound;
     the campaign must find a way to make the SIGNED cancellation survive on S' (e.g. showing S' is
     symmetric/near-symmetric enough around the relevant center), not bypass it.""")
