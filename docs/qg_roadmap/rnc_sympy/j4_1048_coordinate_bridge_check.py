"""
J4-1048 sympy sanity check (run BEFORE writing EvalBaseSlotCoordinateBridge.lean).

Claim under test: if w_b(z) = -(T_x o w_e)(z) pointwise on a domain (the raw coordinate-bridge
identity extracted from GeodesicReversalRouteAtPoint.baseSlot_eventuallyEq_neg_terminalVel_at), then
by the chain rule:
    D w_b(z) = -D T_x(w_e(z)) o D w_e(z)
    det D w_b(z) = (-1)^n * det(D T_x(w_e(z))) * det(D w_e(z))
i.e. |det D w_b(z)| = |det D T_x(w_e(z))| * |det D w_e(z)|.

This is standard multivariable calculus (chain rule + multiplicativity of det under composition +
det(-A) = (-1)^n det(A)); the check below verifies it holds EXACTLY (no approximation) for a toy 2D
near-identity nonlinear eval-slot chart w_e and near-isometry T_x, confirming there is no subtlety
(sign, orientation, or otherwise) hiding in the composition before committing to the Lean chain-rule
lemma `bridge_hasFDerivAt` / `bridge_det_abs`.
"""

import sympy as sp

z1, z2 = sp.symbols('z1 z2', real=True)
z = sp.Matrix([z1, z2])

# Toy eval-slot chart w_e(z): a nonlinear diffeo near 0 (not the identity -- exercises the chain rule).
we1 = z1 + sp.Rational(1, 10) * z1 * z2
we2 = z2 - sp.Rational(1, 5) * z1**2
we = sp.Matrix([we1, we2])

# Toy near-isometry T_x(w): close to identity plus a curvature-like quadratic correction.
w1, w2 = sp.symbols('w1 w2', real=True)
Tx1 = w1 + sp.Rational(1, 20) * w2**2
Tx2 = w2 - sp.Rational(3, 100) * w1 * w2
Tx = sp.Matrix([Tx1, Tx2])

# The proposed bridge relation: w_b(z) := -T_x(w_e(z)).
Tx_we = Tx.subs({w1: we1, w2: we2})
wb = -Tx_we

Jwe = we.jacobian(z)
JTx = Tx.jacobian(sp.Matrix([w1, w2]))
JTx_at_we = JTx.subs({w1: we1, w2: we2})

# Chain-rule prediction: J(w_b) = -(J T_x at w_e(z)) * J(w_e).
Jwb_predicted = (-JTx_at_we) * Jwe
Jwb_direct = wb.jacobian(z)

diff = sp.simplify(Jwb_direct - Jwb_predicted)
assert diff == sp.zeros(2, 2), f"Jacobian chain-rule mismatch: {diff}"
print("Jacobian chain-rule match: EXACT (zero matrix).")

n = 2
detwb = sp.simplify(Jwb_direct.det())
detpred_signed = sp.simplify(((-1) ** n) * JTx_at_we.det() * Jwe.det())
assert sp.simplify(detwb - detpred_signed) == 0, "signed determinant mismatch"
print("Signed determinant relation det(Dw_b) = (-1)^n det(DT_x) det(Dw_e): EXACT match.")

# Absolute-value form used in the Lean lemma `bridge_det_abs` (compare squares to avoid sign case-split).
lhs2 = sp.expand(detwb ** 2)
rhs2 = sp.expand((JTx_at_we.det() * Jwe.det()) ** 2)
assert sp.simplify(lhs2 - rhs2) == 0, "abs-det-squared mismatch"
print("Absolute-Jacobian relation |det Dw_b| = |det DT_x| * |det Dw_e|: EXACT match (verified via squares).")

print("\nJ4-1048 sympy check PASSED: no hidden sign/orientation subtlety in the chain-rule composition.")
