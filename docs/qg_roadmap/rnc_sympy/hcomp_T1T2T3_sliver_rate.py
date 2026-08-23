"""
hcomp_T1T2T3_sliver_rate.py — J4-106x follow-on: per-term sliver-window rate check for the
OTHER three Bfac summands (T1 quadratic/linear-1/tau^2,1/tau term; T2, T3 the two mixed
1/tau linear terms), besides the bare LEFTOVER term already closed in
HcompLeftoverSliverWindowBound.lean (J4-1063) / hcomp_sliver_leftover_rate.py.

SOURCE OF THE LITERAL SHAPE.  HCompNearCarryKPrimeBaseFieldCoV.lean, BRICK 1
(`kPrime_apply_single_on_gate_eq_baseGaussian_mul_amp`), gives, with U := uniformInverseChart
g gi hC hK z x, tau := t - s, PI, PJ, Q vectors depending on the FIELD point x (constants w.r.t.
the z-integration), A := chartFieldAmp g gi hC hK a b tau z applied at x (a function of z):

  Bfac(z) = Levi(s,z) * (
      T1(z) := ( <U,PI><U,PJ>/(4*tau^2) - (<PI,PJ> + <U,Q>)/(2*tau) ) * A(z)
      T2(z) := ( -<U,PJ>/(2*tau) ) * d_j A(z)
      T3(z) := ( -<U,PI>/(2*tau) ) * d_i A(z)
      LEFTOVER(z) := d_j d_i A(z)                    <- already closed, J4-1063
  )

QUESTION (this script).  For each of T1, T2, T3 individually: is the z-integrated density
  D_k(tau) := integral_z gaussDdim(tau, U) * T_k(z) dz
(a) FINITE for tau in (0, eps] despite the explicit 1/tau, 1/tau^2 prefactor (i.e. does the
    accompanying <U,*> factor's own Gaussian-moment scaling (~sqrt(tau) per power of U) tame the
    singularity), and (b) if finite, does  integral_0^eps D_k(tau) dtau = o(sqrt(eps))  (the rate
    hcomp needs), via the SAME crude "bounded density x shrinking window" mechanism that closed
    LEFTOVER — or does it need a genuine cancellation (e.g. between T1's quadratic <U,PI><U,PJ>
    piece and its own linear <PI,PJ> piece, the classic Wick/Ito-isometry cancellation) that the
    leftover technique does NOT supply.

MODEL.  n = 2, x := 0 (translate coordinates), U(z,x) proxy v = z (RNC agrees with z-x to
O(|z-x|^2), a higher-order correction that does not change the LEADING rate below -- same
convention as hcomp_sliver_leftover_rate.py).  PI = (p1,p2), PJ = (q1,q2), Q = (r1,r2) are
SYMBOLIC CONSTANTS (independent of z, matching the Lean literal shape: they depend on the FIELD
point x, which is fixed, not the base-slot integration variable z).  A(z), d_j A(z), d_i A(z) are
independent concrete bounded smooth stand-ins (any smooth bounded family gives the same
qualitative rate by heat-semigroup smoothing universality, as already checked for LEFTOVER by the
two-different-F robustness test).
"""
from sympy import (symbols, exp, cos, sqrt, pi, integrate, oo, simplify, series,
                    limit, Rational, expand, together, diff, I, re)

tau = symbols('tau', positive=True)
eps = symbols('eps', positive=True)
z1, z2 = symbols('z1 z2', real=True)
p1, p2, q1, q2, r1, r2 = symbols('p1 p2 q1 q2 r1 r2', real=True)

n = 2
G = (4 * pi * tau) ** (-Rational(n, 2)) * exp(-(z1 ** 2 + z2 ** 2) / (4 * tau))

# bounded smooth stand-ins (independent, generic, matching the leftover script's convention)
A0 = cos(z1 + z2)     # stand-in for A(z) = Levi(s,z)*chartFieldAmp(z)(x)
A1 = cos(z1)          # stand-in for d_j A(z) (independent bounded function)
A2 = cos(z2)          # stand-in for d_i A(z) (independent bounded function)

U_PI = z1 * p1 + z2 * p2      # <U,PI>
U_PJ = z1 * q1 + z2 * q2      # <U,PJ>
U_Q = z1 * r1 + z2 * r2       # <U,Q>
PI_PJ = p1 * q1 + p2 * q2     # <PI,PJ>  (constant, no z)


def zintegrate(expr):
    """Double integral over z1,z2 in R^2, closed form."""
    e1 = integrate(expr, (z1, -oo, oo))
    e2 = integrate(e1, (z2, -oo, oo))
    return simplify(e2)


print("=" * 90)
print("### T1 -- quadratic 1/tau^2 term + linear 1/tau term, both times A0(z)")
print("=" * 90)

T1_quad = (U_PI * U_PJ) / (4 * tau ** 2) * A0
T1_lin = -(PI_PJ + U_Q) / (2 * tau) * A0
T1 = T1_quad + T1_lin

D_T1_quad = zintegrate(G * T1_quad)
D_T1_lin = zintegrate(G * T1_lin)
D_T1 = simplify(D_T1_quad + D_T1_lin)

print("D_T1_quad(tau) [the <U,PI><U,PJ>/(4 tau^2) * A0 piece alone] =", D_T1_quad)
print("D_T1_lin(tau)  [the -(<PI,PJ>+<U,Q>)/(2 tau) * A0 piece alone] =", D_T1_lin)
print("D_T1(tau) = D_T1_quad + D_T1_lin =", D_T1)

# limit as tau -> 0+ : does the 1/tau^2 divergence survive, or does the quadratic-moment ~tau
# scaling cancel it down to something finite?
lim_T1_0 = limit(D_T1, tau, 0, dir='+')
print("lim_{tau->0+} D_T1(tau) =", lim_T1_0)

print()
print("=" * 90)
print("### T2 -- linear 1/tau term times A1(z) = d_j A(z) stand-in")
print("=" * 90)

T2 = -(U_PJ) / (2 * tau) * A1
D_T2 = zintegrate(G * T2)
D_T2 = simplify(D_T2)
print("D_T2(tau) =", D_T2)
lim_T2_0 = limit(D_T2, tau, 0, dir='+')
print("lim_{tau->0+} D_T2(tau) =", lim_T2_0)

print()
print("=" * 90)
print("### T3 -- linear 1/tau term times A2(z) = d_i A(z) stand-in")
print("=" * 90)

T3 = -(U_PI) / (2 * tau) * A2
D_T3 = zintegrate(G * T3)
D_T3 = simplify(D_T3)
print("D_T3(tau) =", D_T3)
lim_T3_0 = limit(D_T3, tau, 0, dir='+')
print("lim_{tau->0+} D_T3(tau) =", lim_T3_0)

print()
print("=" * 90)
print("### OUTER shrinking-window integrals int_0^eps D_k(tau) dtau, and rate vs O(sqrt(eps))")
print("=" * 90)

for name, D in [("T1", D_T1), ("T2", D_T2), ("T3", D_T3)]:
    print(f"\n--- {name} ---")
    print(f"D_{name}(tau) =", D)
    # check integrability near tau=0 first (finite limit already printed above)
    Total = integrate(D, (tau, 0, eps))
    Total = simplify(Total)
    print(f"Total_{name}(eps) = int_0^eps D_{name} dtau =", Total)
    if Total is None or Total.has(oo):
        print(f"  ==> {name}: integral DIVERGES / not directly closed-form; needs separate treatment")
        continue
    try:
        ratio_sqrt = simplify(Total / sqrt(eps))
        lim_ratio_sqrt = limit(ratio_sqrt, eps, 0)
        print(f"  lim_{{eps->0}} Total_{name}/sqrt(eps) =", lim_ratio_sqrt)
        ratio_lin = simplify(Total / eps)
        lim_ratio_lin = limit(ratio_lin, eps, 0)
        print(f"  lim_{{eps->0}} Total_{name}/eps =", lim_ratio_lin)
    except Exception as ex:
        print(f"  (limit computation issue: {ex})")

print()
print("=" * 90)
print("### Cross term check: does T1's quadratic piece alone blow up like 1/tau, and does the")
print("### LINEAR <PI,PJ>/(2 tau) piece EXACTLY cancel that blow-up (Wick/Ito-isometry structure)?")
print("=" * 90)
# isolate just the *A0-independent-of-z-oscillation* leading behaviour by testing with A0 -> 1
# (i.e. what if the amplitude were locally constant near z=0 -- the sharpest test of whether the
# 1/tau^2 and 1/tau singularities are a heat-kernel-moment artifact that cancels for ANY smooth A,
# or genuinely needs A's specific structure)
A0c = 1
T1_quad_c = (U_PI * U_PJ) / (4 * tau ** 2) * A0c
T1_lin_c = -(PI_PJ + U_Q) / (2 * tau) * A0c
D_T1_quad_c = zintegrate(G * T1_quad_c)
D_T1_lin_c = zintegrate(G * T1_lin_c)
print("With A0 -> 1 (locally constant amplitude test):")
print("  D_T1_quad_c(tau) =", simplify(D_T1_quad_c))
print("  D_T1_lin_c(tau)  =", simplify(D_T1_lin_c))
print("  sum =", simplify(D_T1_quad_c + D_T1_lin_c), " (should be exactly the <PI,PI> moment structure)")
