import sympy as sp

# Follow-up to r6_frozen_model_full_bfac_check.py, per gpt-5.6-sol's read
# (J4-1060 consult, dispatch after that script): the INDEPENDENTLY frozen
# 4-term model leaves a bare, non-vanishing residual L*c3 = Levi(x)*d2A(x)
# (the pure Hessian-of-amplitude term has no accompanying Gaussian-derivative
# structure). Sol's proposed "Repair A" is to NOT freeze the 4 amplitude
# slots independently, but substitute a single COHERENT quadratic Taylor
# jet of A around x (so A(z), dA_j(z), dA_i(z), d2A_ji(z) are the actual
# jet of ONE quadratic polynomial, consistent with each other), to see if
# the product-rule structure of Bfac then makes the v-integral vanish
# exactly (matching the 1D sanity fact (G*A)'' integrates to 0 when A is
# the TRUE coherent Taylor data, vs A''(0) when A is frozen independently).
#
# This tests: is there a coherent-jet repair that makes the WHOLE Bfac
# (to leading nontrivial order, i.e. treating A as an exact local quadratic
# and v = z-x exactly, no chart-remainder yet) integrate to zero, before
# even touching chart/CoV/Jacobian/Levi-variation complications?

n = 2
tau = sp.symbols('tau', positive=True)
v0, v1 = sp.symbols('v0 v1', real=True)
v = (v0, v1)
PI_ = sp.symbols('PI0 PI1', real=True)
PJ_ = sp.symbols('PJ0 PJ1', real=True)
Q_ = sp.symbols('Q0 Q1', real=True)
L = sp.symbols('L', real=True)  # Levi frozen (constant) -- only testing the amplitude-jet repair here

# Coherent quadratic Taylor jet of A(z) around x, in v = z - x (leading-order
# identity-chart approx of U(z,x); i,j fixed as (i,j) = (0,1), i.e. hsMixed's
# "mixed" indices are the off-diagonal pair):
c0, dA0, dA1, H00, H01, H11 = sp.symbols('c0 dA0 dA1 H00 H01 H11', real=True)
# H is the symmetric Hessian of A at x: H_kl = d_k d_l A(x).
H = sp.Matrix([[H00, H01], [H01, H11]])
dA = sp.Matrix([dA0, dA1])
vvec = sp.Matrix([v0, v1])

A_z = c0 + (dA.T * vvec)[0] + sp.Rational(1, 2) * (vvec.T * H * vvec)[0]
dA_j_z = sp.diff(A_z, v1)   # index j = 1 ("outer" index matching BRICK1's j)
dA_i_z = sp.diff(A_z, v0)   # index i = 0
d2A_ji_z = sp.diff(A_z, v1, v0)  # = H01, constant as expected for exact quadratic

r2 = v0**2 + v1**2
G = sp.exp(-r2/(4*tau)) / (4*sp.pi*tau)**sp.Rational(n, 2)


def dot(a, b):
    return sum(ai * bi for ai, bi in zip(a, b))


vPI = dot(v, PI_)
vPJ = dot(v, PJ_)
PIPJ = dot(PI_, PJ_)
vQ = dot(v, Q_)

hsMixed = vPI * vPJ / (4 * tau**2) - (PIPJ + vQ) / (2 * tau)
grj = -vPJ / (2 * tau)
gri = -vPI / (2 * tau)

kernel_coherent = L * G * (hsMixed * A_z + grj * dA_j_z + gri * dA_i_z + d2A_ji_z)

inf = sp.oo


def integrate_all(expr):
    e = sp.expand(expr)
    e = sp.integrate(e, (v0, -inf, inf))
    e = sp.integrate(e, (v1, -inf, inf))
    return sp.simplify(e)


I_coherent = integrate_all(kernel_coherent)
print("Coherent-quadratic-jet frozen-kernel integral over R^2:")
print(sp.simplify(I_coherent))
print()
print("Compare: independent-freeze result from prior script was L*c3 = L*H01.")
print("If the coherent-jet result above is IDENTICALLY 0 for all symbols, Repair A")
print("(coherent jet, no external chart/CoV machinery yet) is viable at leading order.")
print("If it reduces to a nonzero multiple of H01 (or anything else O(1)), Repair A")
print("fails too and the frozen-model family is dead at this order regardless of")
print("how the freezing is organized.")

# Also report the coefficient of each H, dA, PI, PJ, Q monomial for diagnosis.
expanded = sp.expand(I_coherent)
print()
print("Expanded form:", expanded)
