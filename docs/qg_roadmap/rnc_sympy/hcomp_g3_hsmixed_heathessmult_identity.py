"""
G3 gate verification (J4-1010 x J4-998 bridge).

Question: is `hsMixed` -- the literal scalar factor appearing in Bfac's term1
in QIQTH/HCompNearCarryKPrimeBaseFieldCoV.lean (BRICK 1) --

    hsMixed(z) := <U,PI>*<U,PJ>/(4*tau^2) - (<PI,PJ> + <U,Q>)/(2*tau)

  (U := uniformInverseChart g gi hC hK z x,  PI := PI x,  PJ := PJ x,
   Q := Q,  tau := t - s)

exactly equal (as bare scalars, before multiplying by gaussDdim) to the
`heatHessMult` scalar multiplier from QIQTH/HeatHessianMomentCancellation.lean:

    heatHessMult tau p q v / gaussDdim tau v
      = <v,p>*<v,q>/(4*tau^2) - <p,q>/(2*tau)

instantiated at v = U, p = PI, q = PJ?

We check this symbolically for general n (using Fin-3 as a stand-in finite
index set, since the sums are just finite linear combinations -- the algebraic
shape does not depend on n).
"""
from sympy import symbols, simplify, Rational, expand, factor

tau = symbols('tau', positive=True)

# n = 3 index stand-in (algebraic shape is n-independent: sums are bilinear)
U1, U2, U3 = symbols('U1 U2 U3')
P1, P2, P3 = symbols('P1 P2 P3')   # PI x
Q1_, Q2_, Q3_ = symbols('R1 R2 R3')  # PJ x  (renamed to avoid clash)
Qc1, Qc2, Qc3 = symbols('Qc1 Qc2 Qc3')  # Q  (the hJetQ correction field)

U = [U1, U2, U3]
P = [P1, P2, P3]      # PI x
Rv = [Q1_, Q2_, Q3_]  # PJ x
Qc = [Qc1, Qc2, Qc3]  # Q

def dot(a, b):
    return sum(ai*bi for ai, bi in zip(a, b))

# --- literal hsMixed from Bfac's term1 (Lean, lines 109-112) ---
hsMixed = (dot(U, P) * dot(U, Rv)) / (4*tau**2) - (dot(P, Rv) + dot(U, Qc)) / (2*tau)

# --- heatHessMult's pure scalar multiplier (before the gaussDdim factor),
#     instantiated v=U, p=PI(=P), q=PJ(=Rv) ---
heatHessMult_scalar = (dot(U, P) * dot(U, Rv)) / (4*tau**2) - dot(P, Rv) / (2*tau)

# --- the claimed correction term ---
correction = dot(U, Qc) / (2*tau)

diff = simplify(expand(hsMixed - (heatHessMult_scalar - correction)))
print("hsMixed - (heatHessMult_scalar - correction) simplifies to:", diff)
assert diff == 0, "IDENTITY FAILS"

# Also check: is hsMixed == heatHessMult_scalar identically (i.e. is Qc always
# forced to 0, making the naive/no-correction claim true)? Answer should be NO
# in general (only when dot(U,Qc) == 0).
diff_naive = simplify(expand(hsMixed - heatHessMult_scalar))
print("hsMixed - heatHessMult_scalar (naive, no correction) simplifies to:", diff_naive)
print("  (nonzero in general -> naive identity FALSE, correction term required)")

print()
print("VERIFIED: hsMixed(z) = heatHessMult_scalar(tau,PI,PJ,U) - <U,Q>/(2*tau)")
print("i.e. hsMixed(z)*gaussDdim(tau,U) = heatHessMult(tau,PI,PJ,U) - <U,Q>/(2*tau) * gaussDdim(tau,U)")
print("This is a PURE ALGEBRAIC IDENTITY (ring-provable), not an approximation.")
print("The Q-correction term is exact and does NOT vanish in general (Q = 0 only")
print("in the degenerate case where PJ has zero i-directional jet derivative at x).")
