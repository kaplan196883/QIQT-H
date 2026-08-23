"""
hcomp_sliver_leftover_rate.py — J4-106x decisive test (Sol's "option 2" flagged next step).

QUESTION.  VanVleckGatedSpatialSymmetry.hcomp's near-carry `nb` (HCompNearCarryKPrimeBaseFieldCoV,
BRICK 1) has kPrime's on-gate normal form factor as

    (kPrime ... i t s x z)(e_j) = gaussDdim(t-s, U z x) * Bfac(z),
    Bfac(z) = Levi(s,z) * ( T1(z) + T2(z) + T3(z) + LEFTOVER(z) ),
    LEFTOVER(z) := d_j d_i [chartFieldAmp(z)](x)   -- the bare unpaired Hessian term.

J4-1060/1061 found: integrating LEFTOVER's z-integral over the FULL domain (R^n, tau fixed) gives a
generically NONZERO constant  L*c3 = Levi(s,x) * d_j d_i[chartFieldAmp](x)  as tau = t-s -> 0.  Read
naively ("does the density vanish?") this looks like a wall: no companion term cancels it.

BUT hcomp's actual carry is the OUTER s-integral too, over the SHRINKING window s in (t-eps_m, t),
i.e. tau = t-s ranges over (0, eps_m) with eps_m = 1/(m+1) -> 0.  The z-integral is a value of s
(equivalently tau); call it D(tau) := (z-integral of Levi(s,z)*LEFTOVER(z) against the tau-Gaussian).
D(tau) -> L*c3 (finite, generically nonzero) as tau -> 0 -- so D is BOUNDED near tau = 0, not
blowing up.  The question is not "does D(tau) vanish" (it does not) but "does the OUTER integral
  nb_leftover(eps) := | integral_{tau=0}^{eps} D(tau) dtau |
vanish as eps -> 0, and at what rate, relative to the O(sqrt(eps)) rate hcomp needs?"

This script builds a concrete, faithful (n=2) instance: a smooth chart-centred amplitude family
A_z(y) whose mixed Hessian in y, evaluated at y=x, is a genuine non-constant, bounded, smooth
function F(z) := d_j d_i[A_z](x) with F(x) != 0 ("generically nonzero", matching the campaign's
finding), convolved against the standard heat kernel gaussDdim(tau, z-x) (normalised, mass 1), then
integrates the resulting density D(tau) over the shrinking window tau in (0, eps).

Everything below is computed IN CLOSED FORM (Gaussian x cosine char-function identity), not
approximated, so the rate is exact, not a numerical artifact.
"""
from sympy import (symbols, exp, cos, sqrt, pi, integrate, oo, simplify, series,
                    limit, Rational, nsimplify, latex)

tau, eps, z1, z2, k1, k2 = symbols('tau eps z1 z2 k1 k2', positive=True, real=True)
tau = symbols('tau', positive=True)
eps = symbols('eps', positive=True)

# --- Model -------------------------------------------------------------
# n = 2, x := 0 (wlog, translate coordinates so field point x is the origin).
# v = z - x = z  (leading-order normal-coordinate proxy for U(z,x); RNC agrees with z-x to O(|z-x|^2),
#   which only shifts F by higher-order smooth corrections and does not change the rate below).
#
# gaussDdim(tau, v) [n=2] = (4*pi*tau)^{-1} * exp(-(v1^2+v2^2)/(4*tau))   (mass 1 on R^2)
#
# LEFTOVER density (times Levi(s,z), folded together): pick a concrete smooth, BOUNDED, "generically
# nonzero" function of z --  F(z) = cos(z1 + z2)  (F(0) = 1 != 0, matches "L*c3 generically nonzero").
# This stands in for  Levi(s,z) * d_j d_i[chartFieldAmp(z)](x); any smooth bounded choice gives the
# same qualitative/rate conclusion (Riemann-Lebesgue / heat-semigroup smoothing is rate-universal for
# bounded continuous integrands).

n = 2
G = (4*pi*tau)**(-Rational(n, 2)) * exp(-(z1**2 + z2**2) / (4*tau))

Fz = cos(z1 + z2)   # the leftover-term density, "generically nonzero" at z=x=0: Fz(0,0) = 1

integrand = G * Fz

# --- Step 1: inner z-integral (closed form via completing the square / Gaussian char. function) ----
# Standard identity: integral_{R^2} gaussDdim(tau,z) * cos(k.z) dz = exp(-tau*|k|^2)   (here k=(1,1))
Dz1 = integrate(integrand, (z1, -oo, oo))
D_tau = integrate(Dz1, (z2, -oo, oo))
D_tau = simplify(D_tau)
print("D(tau) [z-integral of leftover density against tau-Gaussian] =", D_tau)

D_tau_closed = exp(-2*tau)   # = the exact character-function evaluation, k=(1,1), |k|^2=2
check_match = simplify(D_tau - D_tau_closed)
print("Cross-check D(tau) matches exp(-2 tau):", check_match, "(should be 0)")

# --- Step 2: limit of D(tau) as tau -> 0 : must be finite & nonzero (the "generically nonzero" wall)
D0 = limit(D_tau_closed, tau, 0, dir='+')
print("lim_{tau->0+} D(tau) =", D0, "  (nonzero => matches campaign's 'generically nonzero L*c3' finding)")

# D(tau) is bounded on [0, eps] for any eps (continuous, decaying exponential; sup = D(0) = 1)
print("sup_{tau in [0,eps]} D(tau) = D(0) = 1  (bounded density, no 1/tau or 1/sqrt(tau) blow-up)")

# --- Step 3: OUTER s-window integral over the SHRINKING sliver tau in (0, eps) ----------------------
Total = integrate(D_tau_closed, (tau, 0, eps))
Total = simplify(Total)
print("\nTotal leftover sliver integral  integral_0^eps D(tau) dtau  =", Total)

# --- Step 4: the decisive RATE comparison: expand near eps = 0, compare to O(eps) vs O(sqrt(eps)) ---
Total_series = series(Total, eps, 0, 4).removeO()
print("Small-eps series of Total:", Total_series)

ratio_to_eps = simplify(Total / eps)
lim_ratio_to_eps = limit(ratio_to_eps, eps, 0)
print("lim_{eps->0} Total/eps =", lim_ratio_to_eps, " (finite nonzero => Total = Theta(eps), i.e. O(eps))")

ratio_to_sqrt_eps = simplify(Total / sqrt(eps))
lim_ratio_to_sqrt_eps = limit(ratio_to_sqrt_eps, eps, 0)
print("lim_{eps->0} Total/sqrt(eps) =", lim_ratio_to_sqrt_eps,
      " (=0 => Total = o(sqrt(eps)), i.e. Total decays STRICTLY FASTER than the O(sqrt(eps)) target)")

print("\n=== VERDICT ===")
print("Leftover term's ACTUAL contribution to hcomp's near carry, integrated over the real shrinking")
print("s-window (t - eps_m, t) with eps_m = 1/(m+1) -> 0, is Theta(eps_m) = O(eps_m), which is")
print("asymptotically SMALLER (vanishes FASTER) than the O(sqrt(eps_m)) rate hcomp needs.")
print("The earlier 'generically nonzero' finding was about the DENSITY (a tau -> 0 pointwise limit),")
print("not the actual double integral hcomp bounds; a density that is merely BOUNDED (not necessarily")
print("vanishing) near tau=0, integrated over a window of vanishing LENGTH eps_m, trivially gives an")
print("O(eps_m) total by the crude bound |integral_0^eps D| <= eps * sup|D|. No cancellation needed.")

# --- Robustness check: does a genuinely UNBOUNDED-but-integrable density change the conclusion? -----
# (Sanity: confirm the mechanism relies on BOUNDEDNESS of D near tau=0, not on the specific F chosen.)
print("\n--- Robustness: repeat with a different bounded F (sanity that O(eps) is generic, not a fluke) ---")
Fz2 = cos(2*z1) * cos(3*z2)  # F2(0,0) = 1, different bounded smooth choice
integrand2 = G * Fz2
D2 = simplify(integrate(integrate(integrand2, (z1, -oo, oo)), (z2, -oo, oo)))
print("D2(tau) =", D2)
Total2 = simplify(integrate(D2, (tau, 0, eps)))
print("Total2(eps) =", Total2)
ratio2 = simplify(limit(Total2/eps, eps, 0))
print("lim Total2/eps =", ratio2, "(nonzero finite => again Theta(eps))")
