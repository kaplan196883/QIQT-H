"""
hcomp_T2T3_robustness2.py -- faster robustness check for T2/T3 using NUMERIC (not symbolic)
constants for PI,PJ, to speed up the non-separable Gaussian integrals, still with non-separable
amplitude stand-ins A1,A2 (avoiding the T2T3_robustness.py timeout).
"""
from sympy import symbols, exp, cos, sqrt, pi, integrate, oo, simplify, limit, Rational, nsimplify

tau = symbols('tau', positive=True)
eps = symbols('eps', positive=True)
z1, z2 = symbols('z1 z2', real=True)

n = 2
G = (4*pi*tau)**(-Rational(n,2)) * exp(-(z1**2+z2**2)/(4*tau))

def zintegrate(expr):
    e1 = integrate(expr, (z1, -oo, oo))
    e2 = integrate(e1, (z2, -oo, oo))
    return simplify(e2)

# numeric PI=(1,1), PJ=(1,-1) -- generic, nonzero dot products with the non-separable test funcs
p1, p2 = 1, 1
q1, q2 = 1, -1
U_PI = z1*p1 + z2*p2
U_PJ = z1*q1 + z2*q2

A1 = cos(z1 + 2*z2)
A2 = cos(3*z1 - z2)

print("### T2' with numeric PJ=(1,-1), non-separable A1 = cos(z1+2z2)")
T2p = -(U_PJ)/(2*tau) * A1
D_T2p = zintegrate(G*T2p)
D_T2p = simplify(D_T2p)
print("D_T2'(tau) =", D_T2p)
lim0 = limit(D_T2p, tau, 0, dir='+')
print("lim_{tau->0+} D_T2'(tau) =", lim0)

Total_T2p = simplify(integrate(D_T2p, (tau, 0, eps)))
print("Total_T2'(eps) =", Total_T2p)
print("lim Total_T2'/sqrt(eps) =", limit(simplify(Total_T2p/sqrt(eps)), eps, 0))
print("lim Total_T2'/eps =", limit(simplify(Total_T2p/eps), eps, 0))
