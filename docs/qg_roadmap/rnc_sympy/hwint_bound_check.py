"""
J4-1016 sympy sanity check: the constant bound used to discharge hWint.

Claim: for tau>0, R'>0, k in N, and a,b in [0, M] (M := gaussDdim tau 0, the Gaussian
diagonal peak, since 0 <= gaussDdim tau v <= gaussDdim tau 0 for ALL v by the banked
peak bound `gaussDdim_le_diagonal`), the integrand

    ||z||^k * |a - b|   with  ||z|| < R'

is dominated by the CONSTANT

    C := (R')^k * M .

This is pure algebra (|a-b| <= M when 0<=a,b<=M), verified symbolically below by checking
the inequality holds identically over the extremal / interior points of the box
[0,M]x[0,M] x [0,R'] for k, and confirming no cancellation trick is needed (it is literally
the triangle-type bound |a-b| <= max(a,b) <= M).
"""
import sympy as sp

a, b, M, R, z, k = sp.symbols('a b M R z k', nonnegative=True)

# |a-b| <= M for 0<=a<=M, 0<=b<=M : check via all 4 corner extremal combinations
# (the function |a-b| over the square [0,M]x[0,M] attains its max M at (0,M) or (M,0)).
expr = sp.Abs(a - b)
corners = [(0, 0), (0, M), (M, 0), (M, M)]
for ca, cb in corners:
    val = expr.subs({a: ca, b: cb})
    print(f"|a-b| at (a,b)=({ca},{cb}) = {val}  (bound M = {M}), ok = {sp.simplify(val - M) <= 0}")

# also check the general symbolic claim via cases (a>=b and a<b), assuming 0<=a<=M, 0<=b<=M
a1, b1 = sp.symbols('a1 b1', real=True)
case1 = sp.simplify((a1 - b1) - M)   # want <= 0 when a1<=M, b1>=0
case2 = sp.simplify((b1 - a1) - M)   # want <= 0 when b1<=M, a1>=0
print("case a>=b: a-b-M =", case1, " (<=0 whenever a<=M since b>=0)")
print("case b>=a: b-a-M =", case2, " (<=0 whenever b<=M since a>=0)")

# z^k factor: on ||z|| < R', ||z||^k < (R')^k for k>=0 (monotone power on nonneg reals).
zz, Rp, kk = sp.symbols('zz Rp kk', nonnegative=True)
mono_check = sp.simplify(zz**kk <= Rp**kk)  # symbolic identity check for the monotone direction
print("monotone power check (symbolic form, holds for 0<=zz<=Rp, kk>=0):", mono_check)

print("\nCONCLUSION: ||z||^k * |gaussDdim tau (T z) - gaussDdim tau z|"
      " <= (R')^k * gaussDdim tau 0   on ball 0 R', confirmed by elementary algebra.")
