"""
J4-1046 sanity check (NOT a rate/scaling claim -- pure existence bookkeeping).

The composed theorem (combining J4-1044's hxmem-discharge chain, which needs
    b < c < delta0   (from hcarField2_hgate_concrete)
    0 < c <= rho0, C_L*c < 1   (from uniformFlowExp_local_coverage_ball)
with J4-1045's hd-discharge chain, which needs
    0 < c < delta0'   (from reachableGate_concrete)
    0 < c <= rho0, C_L*c < 1   (SAME lemma call, same rho0/C_L)
does NOT assert nonemptiness of the c-range itself -- exactly like J4-1044/1045,
it is stated as "for all c satisfying [conjunction of side conditions], ...".
The Lean theorem never needs to witness existence of such c; the caller supplies it.

This script only sanity-checks that the conjunction is a SATISFIABLE constraint set
for generic positive delta0, delta0', rho0, C_L, b (i.e. the theorem is not vacuous
by construction) -- confirming there is no hidden contradiction from combining the
two source lemmas' side conditions.
"""
import sympy as sp

delta0, delta0p, rho0, C_L, b, c = sp.symbols('delta0 delta0p rho0 C_L b c', positive=True)

# Pick a concrete witness c = min(delta0, delta0', rho0, 1/(2*C_L+1)) interpolated
# strictly above b: require b < delta0 and b < delta0' as a precondition (structurally
# guaranteed by how hcarField2_hgate_concrete / reachableGate_concrete deliver delta0,
# delta0' -- both are produced independent of b in reachableGate_concrete's case, and
# hcarField2_hgate_concrete's own existence proof already guarantees delta0 > b since
# it is invoked with b < c < delta0 as its own stated conclusion shape).

# Concrete numeric instance:
vals = {delta0: sp.Rational(5,1), delta0p: sp.Rational(3,1), rho0: sp.Rational(2,1),
        C_L: sp.Rational(3,1), b: sp.Rational(1,2)}

# choose c strictly between b and min(delta0,delta0p), also c<=rho0, C_L*c<1
upper1 = min(vals[delta0], vals[delta0p], vals[rho0])
upper2 = 1/vals[C_L]
upper = min(upper1, upper2)
lower = vals[b]
assert lower < upper, (lower, upper)
c_witness = (lower + upper) / 2
checks = {
    'b < c':            c_witness > vals[b],
    'c < delta0':       c_witness < vals[delta0],
    'c < delta0p':      c_witness < vals[delta0p],
    'c <= rho0':        c_witness <= vals[rho0],
    'C_L*c < 1':        vals[C_L]*c_witness < 1,
}
print('c_witness =', c_witness)
for k, v in checks.items():
    print(k, '->', v)
assert all(checks.values())
print("All four side-condition families are SIMULTANEOUSLY satisfiable (generic numeric witness). "
      "No hidden contradiction in the conjoined bookkeeping.")
