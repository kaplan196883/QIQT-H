import sympy as sp

# Scalar model of the geodesic flow base-perturbation.
# ODE: Y'(tau) = F(Y), base perturbation s enters via IC Y(s,0)=q0+s.
# We verify: rho = Y_s - Y_0 - s*J solves rho' = F'(Y0) rho + N, ||N|| = O(s^2),
# and harem: F'(Y_s) - F'(Y_0) - s * F''(Y0) J = O(s^2).
s, tau = sp.symbols('s tau', real=True)
# take a concrete nonlinear field F(y)=y^2/2 (so F'(y)=y, F''(y)=1) toy; geodesic-like curvature
# Use general smooth F via series; here numeric check with F(y)=sin(y).
q0 = sp.Rational(1,3)

# Build Y(s,tau) as series in s to order 2 by solving ODE Y'=F(Y), Y(0)=q0+s.
F = lambda y: sp.sin(y)
# Y = Y0 + s*J + s^2/2 * H + O(s^3); Y0 solves base ODE with Y0(0)=q0.
# Instead do numeric ODE integration comparison. Use power series in tau around 0 (short time) to fixed order.
# Y0: Y0' = F(Y0), Y0(0)=q0. Expand Y0 in tau.
N=6
def series_flow(ic):
    # returns Y(tau) as truncated series solving Y'=F(Y), Y(0)=ic
    a=[ic]
    Y=ic
    for k in range(1,N):
        # coefficient of tau^k: from Y' = F(Y)
        Yser=sum(a[j]*tau**j for j in range(len(a)))
        rhs=sp.series(sp.sin(Yser),tau,0,N).removeO()
        ck=sp.expand(rhs).coeff(tau,k-1)/k
        a.append(ck)
    return sum(a[j]*tau**j for j in range(N))

Y0=series_flow(q0)
Ys=series_flow(q0+s)   # perturbed base IC
# J = dYs/ds at s=0
J=sp.series(sp.diff(Ys,s),s,0,1).removeO()
rho=sp.expand(Ys-Y0-s*J)
# leading order of rho in s:
rho_s=sp.series(rho,s,0,3).removeO()
print("rho lowest power in s:", sp.expand(rho_s))
# confirm no s^1 term:
c1=sp.expand(rho_s).coeff(s,1)
print("rho s^1 coeff (should be 0):", sp.simplify(c1))
c2=sp.expand(rho_s).coeff(s,2)
print("rho s^2 coeff (nonzero => O(s^2)):", sp.simplify(sp.series(c2,tau,0,3)))

# harem: G(y)=F'(y)=cos(y). LHS = G(Ys)-G(Y0)-s*G'(Y0)*J,  G'(y)=-sin(y)
G=lambda y: sp.cos(y)
Gp=lambda y: -sp.sin(y)
harem=sp.expand(G(Ys)-G(Y0)-s*Gp(Y0)*J)
harem_s=sp.series(harem,s,0,3).removeO()
print("harem s^1 coeff (should be 0):", sp.simplify(sp.series(sp.expand(harem_s).coeff(s,1),tau,0,3)))
print("harem s^2 coeff (O(s^2)):", sp.simplify(sp.series(sp.expand(harem_s).coeff(s,2),tau,0,3)))
