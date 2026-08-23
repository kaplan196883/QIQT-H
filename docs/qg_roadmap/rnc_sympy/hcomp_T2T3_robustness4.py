"""
hcomp_T2T3_robustness4.py -- decompose cos(k.z+phi) = cos(phi)*cos(k.z) - sin(phi)*sin(k.z)
manually (the full symbolic phase-shifted integral timed out sympy) so each piece is a SEPARATE,
lighter integral: the cos(k.z) piece is already known to vanish exactly (z_i*even=odd -> 0); the
NEW content is the sin(k.z) piece:  z_i * sin(k.z) is EVEN (odd*odd), so its Gaussian-weighted
integral is generically NONZERO -- this is the genuine "non-even amplitude" content T2/T3 needs.
"""
from sympy import symbols, exp, cos, sin, sqrt, pi, integrate, oo, simplify, limit, Rational

tau = symbols('tau', positive=True)
eps = symbols('eps', positive=True)
z1, z2 = symbols('z1 z2', real=True)

n = 2
G = (4*pi*tau)**(-Rational(n,2)) * exp(-(z1**2+z2**2)/(4*tau))

def zintegrate(expr):
    e1 = integrate(expr, (z1, -oo, oo))
    e2 = integrate(e1, (z2, -oo, oo))
    return simplify(e2)

p1, p2 = 1, 1
q1, q2 = 1, -1
U_PI = z1*p1 + z2*p2
U_PJ = z1*q1 + z2*q2

print("### T2'' -- odd-amplitude piece: A1_odd = sin(z1+2z2) (the genuinely nonzero-contribution part)")
T2_odd = -(U_PJ)/(2*tau) * sin(z1 + 2*z2)
D_T2_odd = zintegrate(G * T2_odd)
D_T2_odd = simplify(D_T2_odd)
print("D_T2_odd(tau) =", D_T2_odd)
lim0 = limit(D_T2_odd, tau, 0, dir='+')
print("lim_{tau->0+} D_T2_odd(tau) =", lim0)

Total = simplify(integrate(D_T2_odd, (tau, 0, eps)))
print("Total_T2_odd(eps) =", Total)
print("lim Total/sqrt(eps) =", limit(simplify(Total/sqrt(eps)), eps, 0))
print("lim Total/eps =", limit(simplify(Total/eps), eps, 0))

print()
print("### T3'' -- odd-amplitude piece: A2_odd = sin(3z1-z2)")
T3_odd = -(U_PI)/(2*tau) * sin(3*z1 - z2)
D_T3_odd = zintegrate(G * T3_odd)
D_T3_odd = simplify(D_T3_odd)
print("D_T3_odd(tau) =", D_T3_odd)
lim0b = limit(D_T3_odd, tau, 0, dir='+')
print("lim_{tau->0+} D_T3_odd(tau) =", lim0b)

Total3 = simplify(integrate(D_T3_odd, (tau, 0, eps)))
print("Total_T3_odd(eps) =", Total3)
print("lim Total3/sqrt(eps) =", limit(simplify(Total3/sqrt(eps)), eps, 0))
print("lim Total3/eps =", limit(simplify(Total3/eps), eps, 0))
