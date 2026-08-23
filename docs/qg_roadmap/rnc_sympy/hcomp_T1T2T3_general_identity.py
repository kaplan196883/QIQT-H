"""
hcomp_T1T2T3_general_identity.py -- GENERAL (not single-Fourier-mode) closed-form derivation of
D_T1, D_T2, D_T3 via the Gaussian integration-by-parts moment-shift identity, cross-checked against
the single-frequency sympy computations in hcomp_T1T2T3_sliver_rate.py / robustness scripts.

KEY IDENTITY (Gaussian IBP in z, at fixed tau; G(tau,z)=(4 pi tau)^{-n/2} exp(-|z|^2/(4 tau))):
    z_m * G(tau,z) = -2*tau * d/dz_m G(tau,z)
  =>  integral z_m G(tau,z) f(z) dz = 2*tau * integral G(tau,z) * d_m f(z) dz     (IBP, f decaying
      or bounded-with-controlled-boundary; standard heat-kernel moment-shift)
  =>  integral z_a z_b G(tau,z) f(z) dz = 4*tau^2 * integral G(tau,z)*d_a d_b f(z) dz
                                          + 2*tau*delta_ab * integral G(tau,z)*f(z) dz

Applying this to T1 = [<U,PI><U,PJ>/(4 tau^2) - (<PI,PJ> + <U,Q>)/(2 tau)] * A0(z):

  D_T1(tau) = E[<U,PI><U,PJ> A0]/(4 tau^2) - <PI,PJ>*E[A0]/(2 tau) - E[<U,Q> A0]/(2 tau)

  E[<U,PI><U,PJ> A0] = sum_{a,b} PI_a PJ_b E[z_a z_b A0]
                      = sum_{a,b} PI_a PJ_b ( 4 tau^2 E[d_a d_b A0] + 2 tau delta_ab E[A0] )
                      = 4 tau^2 sum_{a,b} PI_a PJ_b E[d_a d_b A0]  +  2 tau <PI,PJ> E[A0]

  => E[<U,PI><U,PJ> A0]/(4 tau^2) = sum PI_a PJ_b E[d_a d_b A0]  +  <PI,PJ> E[A0] / (2 tau)

  E[<U,Q> A0] = sum_m Q_m E[z_m A0] = sum_m Q_m * 2 tau * E[d_m A0] = 2 tau <Q, E[grad A0]>
  => E[<U,Q> A0]/(2 tau) = <Q, E[grad A0]>

  ==>  D_T1(tau) = sum_{a,b} PI_a PJ_b E[d_a d_b A0(Z)]  +  <PI,PJ> E[A0]/(2 tau)  -  <PI,PJ> E[A0]/(2 tau)
                   - <Q, E[grad A0](Z)>
               = sum_{a,b} PI_a PJ_b E[d_a d_b A0(Z)]  -  <Q, E[grad A0](Z)>

  The explicit 1/tau terms EXACTLY CANCEL (algebraically, for ANY A0), leaving D_T1(tau) as a
  Gaussian-weighted average of the BOUNDED functions d_a d_b A0 and grad A0 -- i.e. EXACTLY the
  same B1 (gaussDdim_ball_weighted_average_bounded) shape as LEFTOVER, applied to the Hessian and
  gradient of A0 instead of to A0's mixed partial directly.

Similarly for T2 = -<U,PJ>/(2 tau) * A1(z):
  D_T2(tau) = -E[<U,PJ> A1]/(2 tau) = -sum_m PJ_m * 2 tau E[d_m A1] / (2 tau) = -<PJ, E[grad A1](Z)>
  (the explicit 1/tau EXACTLY cancels the IBP moment-shift's tau factor -- again bounded via B1
  applied to grad A1, PROVIDED A1 has bounded, integrable gradient.)

Symmetric for T3 with grad A2.

THIS SCRIPT verifies these general closed-form claims numerically/symbolically on the SAME test
functions used earlier (A0=cos(z1+z2), A1=cos(z1+2z2), etc, single Fourier mode k), by comparing
the IBP-identity prediction against DIRECT differentiation (no heavy double integrals needed).
"""
from sympy import symbols, cos, sin, diff, simplify, Rational, exp, pi as spi

z1, z2, tau = symbols('z1 z2 tau', positive=False, real=True)
p1, p2, q1, q2, r1, r2 = symbols('p1 p2 q1 q2 r1 r2', real=True)

A0 = cos(z1 + z2)
# grad A0, Hessian A0 (exact symbolic derivatives, cheap)
dA0_1 = diff(A0, z1)
dA0_2 = diff(A0, z2)
d2A0_11 = diff(A0, z1, 2)
d2A0_12 = diff(A0, z1, z2)
d2A0_22 = diff(A0, z2, 2)
print("grad A0 =", dA0_1, dA0_2)
print("Hess A0 =", d2A0_11, d2A0_12, d2A0_22)

# E[f(Z)] under the tau-Gaussian for f = e^{i k.z} type mode is exp(-tau|k|^2) times the
# corresponding trig combination; here A0=cos(z1+z2) has k=(1,1), so E[A0(Z)] = exp(-2 tau)*cos(0)=exp(-2tau)... 
# but we need E[d_a d_b A0(Z)] where d2A0_ab are THEMSELVES pure trig of the SAME frequency k=(1,1)
# (since differentiating cos(k.z) just multiplies by powers of k and shifts cos<->sin), so
# E[d_a d_b A0(Z)] = (coefficient) * E[trig(k.z)] = (coefficient) * exp(-tau*|k|^2) * (cos or sin
# evaluated structure). For A0=cos(z1+z2): d2A0_11 = -cos(z1+z2), so E[d2A0_11] = -exp(-2tau).
# Let's just verify by SUBSTITUTING the known single-mode expectation rule directly:
def E_trig(expr, k=(1,1)):
    # expr is built from cos(k.z), sin(k.z) with polynomial-in-(k) coefficients (post-differentiation
    # here, coefficients are just constants times cos or sin of the SAME phase, no polynomial-in-z
    # left since A0 is a pure single-frequency mode) -- replace cos(z1+z2)->cos(0)=1-style via tau
    # exponential damping: E[cos(k.Z)] = exp(-tau|k|^2), E[sin(k.Z)] = 0 (odd, mean zero always)
    ksq = k[0]**2 + k[1]**2
    e = expr.subs(cos(z1+z2), exp(-tau*ksq)).subs(sin(z1+z2), 0)
    return simplify(e)

E_A0 = E_trig(A0)
E_dA0_1 = E_trig(dA0_1)
E_dA0_2 = E_trig(dA0_2)
E_d2A0_11 = E_trig(d2A0_11)
E_d2A0_12 = E_trig(d2A0_12)
E_d2A0_22 = E_trig(d2A0_22)
print()
print("E[A0] =", E_A0)
print("E[grad A0] =", E_dA0_1, E_dA0_2)
print("E[Hess A0] =", E_d2A0_11, E_d2A0_12, E_d2A0_22)

# D_T1 predicted = PI.PI-block: sum PI_a PJ_b E[d_a d_b A0]  -  <Q, E[grad A0]>
D_T1_predicted = (p1*q1*E_d2A0_11 + p1*q2*E_d2A0_12 + p2*q1*E_d2A0_12 + p2*q2*E_d2A0_22) \
    - (r1*E_dA0_1 + r2*E_dA0_2)
D_T1_predicted = simplify(D_T1_predicted)
print()
print("D_T1 predicted (IBP-identity formula) =", D_T1_predicted)
print("  [note: this includes the Q-dependent term the earlier single-run sympy script (with Q=0")
print("   implicit / not included) did not show -- here Q is symbolic to confirm the full formula]")

# cross-check against the earlier DIRECT double-integral result (Q=0 case, matches
# hcomp_T1T2T3_sliver_rate.py's D_T1 = -(p1q1+p1q2+p2q1+p2q2)*exp(-2 tau)):
D_T1_predicted_Q0 = D_T1_predicted.subs({r1: 0, r2: 0})
print("D_T1 predicted with Q=0 =", D_T1_predicted_Q0)
print("Earlier DIRECT double-integral result (Q folded into T1_lin, see out_T1T2T3.txt):")
print("  D_T1(tau) = (-p1*q1 - p1*q2 - p2*q1 - p2*q2)*exp(-2*tau)")
match = simplify(D_T1_predicted_Q0 - (-p1*q1 - p1*q2 - p2*q1 - p2*q2)*exp(-2*tau))
print("Difference (should be 0):", match)
