import sympy as sp

# Faithful (non-toy) n-dimensional check of Sol's J4-1060 "frozen-model
# subtraction" proposal, using BRICK1's ACTUAL 4-term Bfac structure
# (HCompNearCarryChartSurfaceWired.kPrime_apply_single_on_gate_eq_mixedNormalForm,
# HCompNearCarryKPrimeBaseFieldCoV BRICK 1), not the 1D toy simplification of
# r6_frozen_model_check.py.
#
# Concrete n=2 model (sympy can do n=3 too but n=2 already exposes all index
# structure: a<>b symmetric Hessian term, two distinct linear-gradient terms,
# a pure constant term).
#
# Bfac(z) [Lean, BRICK1] :=
#   Levi(s,z) * ( G(v)*hsMixed(v)*A(z)
#                 + G(v)*grj(v)*dA_j(z)
#                 + G(v)*gri(v)*dA_i(z)
#                 + G(v)*d2A_ji(z) )
# where v := U(z,x) (Gaussian argument, varies with z), and
#   hsMixed(v) := <v,PI><v,PJ>/(4 tau^2) - (<PI,PJ> + <v,Q>)/(2 tau)
#   grj(v)     := -<v,PJ>/(2 tau)
#   gri(v)     := -<v,PI>/(2 tau)
# with PI, PJ, Q FIXED vectors (evaluated at the field point x, NOT varying
# with the base variable z -- confirmed from the Lean signature: PI x k,
# PJ x k, Q k, no z-dependence). Only A(z), dA_j(z), dA_i(z), d2A_ji(z),
# Levi(s,z) vary with z; U(z,x) varies with z.
#
# FROZEN MODEL: replace A(z),dA_j(z),dA_i(z),d2A_ji(z),Levi(s,z) by their
# values AT z=x (constants c0,c1,c2,c3,L), keep v=U(z,x) varying. Then
# integrate the frozen kernel over v in R^n (equivalently over a symmetric
# ball, boundary terms -> 0) and check whether it is EXACTLY ZERO.

n = 2
tau = sp.symbols('tau', positive=True)
v = sp.symbols('v0 v1', real=True)
PI_ = sp.symbols('PI0 PI1', real=True)
PJ_ = sp.symbols('PJ0 PJ1', real=True)
Q_ = sp.symbols('Q0 Q1', real=True)
c0, c1, c2, c3, L = sp.symbols('c0 c1 c2 c3 L', real=True)  # frozen A,dAj,dAi,d2A,Levi at z=x

# isotropic n-dim Gaussian in v (matches gaussDdim tau at argument v)
r2 = sum(vi**2 for vi in v)
G = sp.exp(-r2/(4*tau)) / (4*sp.pi*tau)**sp.Rational(n, 2)

def dot(a, b):
    return sum(ai*bi for ai, bi in zip(a, b))

vPI = dot(v, PI_)
vPJ = dot(v, PJ_)
PIPJ = dot(PI_, PJ_)
vQ = dot(v, Q_)

hsMixed = vPI*vPJ/(4*tau**2) - (PIPJ + vQ)/(2*tau)
grj = -vPJ/(2*tau)
gri = -vPI/(2*tau)

# ---- Step 1: confirm G*hsMixed, G*grj, G*gri decompose EXACTLY into
# constant-coefficient linear combinations of partial_a partial_b G and
# partial_a G (the claimed Hessian/gradient-of-Gaussian identity). ----

def d2G(a, b):
    return sp.diff(G, v[a], 1, v[b], 1) if a != b else sp.diff(G, v[a], 2)

def d1G(a):
    return sp.diff(G, v[a])

# Candidate exact identity:
#   G*hsMixed =?= sum_{a,b} PI_a PJ_b * d2G/dv_a dv_b + sum_a Q_a * dG/dv_a
lhs1 = sp.expand(G*hsMixed)
rhs1 = sp.expand(sum(PI_[a]*PJ_[b]*d2G(a, b) for a in range(n) for b in range(n))
                  + sum(Q_[a]*d1G(a) for a in range(n)))
print("hsMixed identity residual (should be 0):", sp.simplify(lhs1 - rhs1))

# G*grj =?= sum_a PJ_a * dG/dv_a
lhs2 = sp.expand(G*grj)
rhs2 = sp.expand(sum(PJ_[a]*d1G(a) for a in range(n)))
print("grj identity residual (should be 0):", sp.simplify(lhs2 - rhs2))

# G*gri =?= sum_a PI_a * dG/dv_a
lhs3 = sp.expand(G*gri)
rhs3 = sp.expand(sum(PI_[a]*d1G(a) for a in range(n)))
print("gri identity residual (should be 0):", sp.simplify(lhs3 - rhs3))

# ---- Step 2: integrate each structural piece over R^n and report. ----
inf = sp.oo

def integrate_all(expr):
    e = expr
    for vi in v:
        e = sp.integrate(e, (vi, -inf, inf))
    return sp.simplify(e)

I_G = integrate_all(G)
print("\nintegral of G over R^n:", I_G)

I_d1 = [integrate_all(d1G(a)) for a in range(n)]
print("integral of dG/dv_a over R^n (each a):", I_d1)

I_d2 = [[integrate_all(d2G(a, b)) for b in range(n)] for a in range(n)]
print("integral of d2G/dv_a dv_b over R^n (each a,b):", I_d2)

# ---- Step 3: assemble the FULL frozen kernel and its total integral. ----
frozen_kernel = L * (G*hsMixed*c0 + G*grj*c1 + G*gri*c2 + G*c3)
I_full = integrate_all(frozen_kernel)
print("\nFULL frozen-kernel integral over R^n:", sp.simplify(I_full))
print("(expected, from term-by-term analysis: L*c3, i.e. NOT zero in general)")

# ---- Step 4: isolate which of the 4 terms vanishes vs survives. ----
I_term_hsMixed = integrate_all(G*hsMixed*c0)
I_term_grj = integrate_all(G*grj*c1)
I_term_gri = integrate_all(G*gri*c2)
I_term_const = integrate_all(G*c3)
print("\nper-term integrals (unscaled by L):")
print("  hsMixed*A term  :", sp.simplify(I_term_hsMixed))
print("  grj*dA_j term   :", sp.simplify(I_term_grj))
print("  gri*dA_i term   :", sp.simplify(I_term_gri))
print("  d2A_ji term     :", sp.simplify(I_term_const), " <-- the UNPAIRED constant term")
