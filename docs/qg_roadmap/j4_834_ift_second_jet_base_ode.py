"""
J4-834 (plan v2, Task B) — sympy de-risking of the INVERSE-CHART SECOND-JET
BASE ODE bridge.

GOAL.  `InverseChartSecondJet.chartW0_secondJet_bound` gives the inverse chart's
second field-jet as an IFT ALGEBRAIC closed form (NOT an ODE):

    Q z = (- mulLeftRight I I) .comp ( D2phi_z .comp I ),   I = Ring.inverse(Dphi_z),

whose applied form is  Q[a,b] = - I . H(I a, I b)   (H = D2phi).

`ChartMixedThirdJetBasepoint.secondFieldJet_basepoint_hasDerivAt` (the consumer)
wants the BASE-POINT derivative of this second jet in the linear-ODE shape
`X'(s) = DF(Y s).X(s) + b(s)`.  This script determines EXACTLY the source term
`b(s)` and the coefficient by DIFFERENTIATING the IFT closed form along the base
parameter `s` (the chart / forward map phi_z depends on s through the base point
z = Y s), BEFORE writing any Lean.

RESULT (verified symbolically, exact residual 0 over a basis):

    Q'(s)[a,b] = M(s) ( Q(s)[a,b] ) + bsrc(s)[a,b]
    M(s)      = - I(s) A'(s)                              (left-mult coefficient)
    bsrc[a,b] = - I H'(Ia,Ib) - I H(I'a,Ib) - I H(Ia,I'b),  I' = -I A' I

with A(s) = Dphi_s, I(s) = A(s)^{-1}, H(s) = D2phi_s, and A', H' the s-jets.

CRUCIAL STRUCTURAL FINDING (drives the Lean design):
  * The base-ODE COEFFICIENT that the IFT closed form produces is M = -I A' — the
    forward-Jacobian s-jet contracted with the inverse jet — NOT the geodesic-field
    Jacobian DF(Y s) that `secondFieldJet_basepoint_hasDerivAt` names.  They differ;
    matching the consumer's exact coefficient would push (M - DF).Q into the source.
  * ALL data on the RHS (I, H, A', H') are FORWARD jets — the forward map phi = uniformFlowExp
    is the smooth, .choose-FREE object.  So this route expresses the base derivative of the
    (opaque) inverse chart's second jet PURELY via forward jets, side-stepping the
    `.choose`-opacity wall that J4-833 identified for the tau-fiber Jacobi-ODE route.
  * The outer-I differentiation term is EXACTLY M.Q; the H', inner-u', inner-v' terms
    are the source.  This clean split is what the Lean theorem proves.
"""
import sympy as sp

n = 2
s = sp.symbols('s', real=True)

A = sp.Matrix([[2 + s + s**2, sp.Rational(1,2)*s],
               [sp.Rational(1,3)*s**2, 3 - s + 2*s**2]])

Hc = [[[None]*n for _ in range(n)] for _ in range(n)]
val = 1
for c in range(n):
    for a in range(n):
        for b in range(a, n):
            expr = sp.Rational(val,7) + sp.Rational(val,5)*s - sp.Rational(val,11)*s**2
            Hc[c][a][b] = expr; Hc[c][b][a] = expr; val += 1

def Happly(u, v, Ht=Hc):
    out = sp.zeros(n,1)
    for c in range(n):
        out[c] = sum(Ht[c][a][b]*u[a]*v[b] for a in range(n) for b in range(n))
    return out

I  = A.inv()
Ip = sp.diff(I, s)
Ap = sp.diff(A, s)
assert sp.simplify(Ip + I*Ap*I) == sp.zeros(n,n)
Hp = [[[sp.diff(Hc[c][a][b], s) for b in range(n)] for a in range(n)] for c in range(n)]

def Qapply(a, b):
    return -(I * Happly(I*a, I*b))

M = -(I*Ap)

def bsrc(a, b):
    Ia, Ib = I*a, I*b
    return -(I*Happly(Ia,Ib,Hp)) - (I*Happly(Ip*a,Ib)) - (I*Happly(Ia,Ip*b))

basis = [sp.Matrix([1,0]), sp.Matrix([0,1])]
maxerr = 0
for a in basis:
    for b in basis:
        Q_ab  = Qapply(a,b)
        Qp_ab = sp.diff(Q_ab, s)
        resid = sp.simplify(Qp_ab - (M*Q_ab + bsrc(a,b)))
        maxerr = max([maxerr] + [sp.Abs(e) for e in resid])
print("MAX symbolic residual over basis pairs:", maxerr)
assert maxerr == 0
print("CONFIRMED  Q'(s)[a,b] = (-I A')(Q[a,b]) + bsrc[a,b]  (exact, residual 0).")
