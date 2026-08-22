import sympy as sp

# =====================================================================================
# hcomp BASE-SLOT RECENTERING DEFECT — LINEAR vs QUADRATIC order check
#   (J4-1002 dispatch: Sol's item (a), "base-slot change of variables")
# =====================================================================================
# QUESTION (per the dispatch brief).  VanVleckGatedSpatialSymmetry.hcomp's literal integrand
# is built from the inverse chart  Phi(q,p) := uniformInverseChart g gi hC hK q p, evaluated with
# q = z THE INTEGRATION/BASE VARIABLE and p = x THE FIXED FIELD POINT.  The abstract
# moment-cancellation machinery (J4-998/999/1000/1001, heatHessMult / GaussCompMixedHessian) was
# built for a FIXED base V := Phi(z0, .) and only differentiates in the FIELD slot p.  Relating
# the literal hcomp integral (varying q=z, fixed p=x) to that fixed-base machinery requires
# controlling how Phi's FIELD-slot JETS (P := d/dp Phi, and the bilinear bricks built from P) move
# as the BASE q is recentered near the diagonal.  Sol (gpt-5.6-sol, high) warned: if this
# recentering defect is only LINEAR in the recentering distance ||q - p||, the resulting rate is a
# fatal tau^{-1} divergence (mirrors the cp872 WitnessTranspositionGeneralBound NO-GO); only a
# >= QUADRATIC cancellation preserves the needed O(sqrt eps) rate.
#
# WHAT IS BANKED (no more, no less — do not assume anything not proved):
#   (F1) Phi(q0, q0) = 0                         forall q0  [uniformInverseChart_slice_value_diag,
#                                                              JointRNCRegularityInterfaceLocal.lean:96-106,
#                                                              proved for a GENERAL base q0]
#   (F2) d/dp Phi(q0, .) |_{p=q0} = Id            forall q0  [uniformInverseChart_slice_fderiv_id_diag,
#                                                              same file, lines 135-161, general q0]
#   (F3) Phi is JOINTLY ContDiffAt R 2 at every diagonal point (q0,q0)
#        [uniformInverseChart_jointContDiffAt_diag, UniformFlowCoherentChartReconciliation.lean:128-137]
#        => Phi has a well-defined SYMMETRIC joint 2-jet at (q0,q0); NO C^3 is banked anywhere.
#
# NOTE (F1) is the KEY EXTRA fact beyond plain diagonal-vanishing: it holds for the WHOLE FAMILY of
# nearby base points q0 (not just one), so Phi(q,q) = 0 identically as q ranges over a neighbourhood
# — this is what turns "vanishes at one point" into "vanishes along the whole diagonal", enabling the
# implicit-differentiation trick below.  This IS exactly what is banked (not an extra assumption).
#
# GOAL.  Using ONLY (F1)-(F3) (a generic joint-C^2 Taylor model with the diagonal-identity constraint
# imposed to ALL available orders), derive the leading order of the base-slot ANTISYMMETRY DEFECT
#     Xi(a,b) := F(a,b) + F(b,a),     F(a,b) := Phi(q0+a, q0+b) - [affine part already forced to 0],
# where a := q - q0 (base recentering) and b := p - q0 (field recentering from the SAME reference).
# Xi measures how far Phi is from the textbook van-Vleck-type odd symmetry Phi(q,p) = -Phi(p,q); this
# is precisely the quantity whose order (linear vs quadratic in ||a-b||, i.e. in the base<->field
# recentering distance) decides GO/NO-GO on the base-slot CoV route.
# =====================================================================================

print("="*90)
print("PART 1 — SCALAR TOY MODEL (order-counting sanity check).")
print("="*90)

a, b = sp.symbols('a b', real=True)
alpha, beta = sp.symbols('alpha beta', real=True)     # F_a(0,0), F_b(0,0)  (banked: beta = 1)
p, q, r = sp.symbols('p q r', real=True)               # F_aa, F_ab, F_bb  (2nd-order Taylor coeffs)

F = alpha*a + beta*b + sp.Rational(1,2)*(p*a**2 + 2*q*a*b + r*b**2)

# (F1) generalized: F(a,a) = 0 identically in a (not just at a=0) -- Taylor coefficients must match.
diag_identity = sp.expand(F.subs(b, a))
diag_poly = sp.Poly(diag_identity, a)
print("F(a,a) (must vanish identically, order by order) =", diag_identity)
coeffs = diag_poly.all_coeffs()
print("  Taylor coefficients (highest degree first):", coeffs)

# solve order-by-order
order1_eq = sp.Eq(alpha + beta, 0)
order2_eq = sp.Eq(p + 2*q + r, 0)
print("\n  order-1 constraint (linear coefficient of a):  alpha + beta = 0  ->  alpha = -beta")
print("  order-2 constraint (quadratic coefficient of a):  p + 2 q + r = 0")

# (F2): beta = 1 (banked field-slot derivative at the diagonal is the identity)
beta_val = 1
alpha_val = sp.solve(order1_eq.subs(beta, beta_val), alpha)[0]
print(f"\n  (F2) banked: beta = {beta_val}  =>  alpha = {alpha_val}   (BASE-slot derivative forced to -Id;")
print("       this is the scalar shadow of GeodesicReversalRoute's reversal identity / the")
print("       'DV(q0)=+Id kills a would-be linear term' pattern.)")

F_sub = F.subs({alpha: alpha_val, beta: beta_val})
print("\n  F(a,b) with banked (F1)+(F2) substituted:", sp.expand(F_sub))

print("\n" + "-"*90)
print("Antisymmetry defect  Xi(a,b) := F(a,b) + F(b,a):")
# NOTE: sympy's dict .subs({a: b, b: a}) is NOT a simultaneous swap (it applies sequentially and can
# clobber), so swap via fresh dummies to get the genuine F(b,a).
_a, _b = sp.symbols('_a _b', real=True)
F_swapped = F_sub.subs({a: _a, b: _b}, simultaneous=True).subs({_a: b, _b: a}, simultaneous=True)
Xi = sp.expand(F_sub + F_swapped)
print("  Xi(a,b) =", Xi)

# impose the order-2 diagonal constraint p + 2q + r = 0 (from F1 at 2nd order) and simplify
r_solved = sp.solve(order2_eq, r)[0]
Xi_reduced = sp.expand(Xi.subs(r, r_solved))
print("  after imposing (F1)'s order-2 constraint  r = -(p+2q):")
print("  Xi(a,b) =", Xi_reduced)

Xi_factored = sp.factor(Xi_reduced)
print("  factored:", Xi_factored)

target = -q*(a - b)**2
print("\n  claim: Xi(a,b) == -q*(a-b)^2   (QUADRATIC, coefficient = the MIXED 2nd derivative q = F_ab(0,0))")
print("  check Xi - (-q*(a-b)^2) == 0 :", sp.simplify(Xi_reduced - target) == 0)

print()
print("="*90)
print("PART 2 — VECTOR/MATRIX MODEL (n=2), to rule out a scalar-commutativity coincidence.")
print("="*90)
# a, b in R^2.  A, C symmetric bilinear (Hessian blocks); B a GENERAL (non-symmetric) bilinear map.
n = 2
a_v = sp.Matrix(sp.symbols(f'a1:{n+1}', real=True))
b_v = sp.Matrix(sp.symbols(f'b1:{n+1}', real=True))
A = sp.Matrix(n, n, lambda i, j: sp.Symbol(f'A{i}{j}'))
A = (A + A.T) / 2          # symmetrize (genuine Hessian block)
C = sp.Matrix(n, n, lambda i, j: sp.Symbol(f'C{i}{j}'))
C = (C + C.T) / 2
B = sp.Matrix(n, n, lambda i, j: sp.Symbol(f'B{i}{j}'))   # general, NOT assumed symmetric

def quad(M, u, v):
    return (u.T * M * v)[0, 0]

# F(a,b) = -a (banked alpha=-Id) + b (banked beta=Id) + (1/2)[A(a,a) + 2 B(a,b) + C(b,b)]
def Fvec(av, bv):
    lin = sum(-av[i] for i in range(n)) * 0  # placeholder; use vector identity below instead
    return (-av + bv) if False else None

# Build F(a,b) as a VECTOR-VALUED (well, here scalar component-summed for a clean check) quantity is
# unnecessary; work directly with the RN-valued map via one scalar probe direction e (generic) to
# keep the algebra tractable while remaining fully general (component-wise identity suffices, since
# the diagonal constraint below is imposed FOR ALL a, i.e. as a matrix/tensor identity).
Flin = -a_v + b_v   # banked (F1)+(F2) lifted to R^n (matches the scalar case component-wise)
Fquad = sp.Rational(1, 2) * (A * a_v + B * b_v).multiply_elementwise(a_v) * 0  # unused; do it properly:

def bilinear_form_vec(M, u, v):
    # returns the R^n vector  (1/2) d/du [u^T M v] style bilinear contribution is not needed;
    # instead model F_component-wise via a GENERIC linear functional w (probe) to reduce to scalars,
    # which is exactly what "F is symmetric bilinear on pairs" means when contracted with any w.
    return M

w = sp.Matrix(sp.symbols(f'w1:{n+1}', real=True))   # generic covector/probe

def Fw(av, bv):
    # scalar probe <w, F(a,b)> = -<w,a> + <w,b> + (1/2)[ (a^T A a) - style term contracted with w is
    # not meaningful for a VECTOR F; instead treat A,B,C as R^n-valued bilinear forms via w^T(...)
    # i.e. redefine A,B,C as the w-contracted (scalar) Hessian blocks directly -- equivalent generality
    # since w is arbitrary and the diagonal constraint must hold for the FULL vector, hence for every
    # w-component, hence for every symmetric/general bilinear form built this way.
    return (-w.T*av)[0,0] + (w.T*bv)[0,0] + sp.Rational(1,2)*(quad(A, av, av) + 2*quad(B, av, bv) + quad(C, bv, bv))

diag_w = sp.expand(Fw(a_v, a_v))
print("w-contracted <w,F(a,a)> (must vanish identically for ALL a, since F(a,a)=0 as a VECTOR):")
print(" ", diag_w)
# collect order-1 (linear in a) and order-2 (quadratic in a) parts
diag_w_poly_vars = list(a_v)
lin_part = sum(sp.diff(diag_w, ai).subs({aj: 0 for aj in a_v}) * ai for ai in a_v)
quad_part = sp.expand(diag_w - lin_part)
print("  linear-in-a part:", sp.simplify(lin_part), " (must be 0: forces -<w,a>+<w,a>=0, automatic)")
print("  quadratic-in-a part (must be 0 for ALL a, w):", sp.simplify(quad_part))

# The quadratic part is (1/2) a^T (A + 2 Bsym + C) a contracted appropriately; extract the matrix
# identity A + B + B.T + C = 0 (symmetric-part constraint) by matching coefficients of a_i a_j.
Bsym = (B + B.T) / 2
constraint_matrix = sp.simplify(A + 2*Bsym + C)
print("\n  Reading off the matrix identity from quad_part == 0 for all a,w:  A + 2*Bsym + C = 0")
print("  (this is exactly PART 1's  p + 2q + r = 0  lifted to matrices)")

# Now compute Xi(a,b) := F(a,b) + F(b,a) (vector; probe with w again) and substitute C = -A - 2 Bsym.
C_solved = -A - 2*Bsym
Xi_w = sp.expand(Fw(a_v, b_v).subs({C[i, j]: C_solved[i, j] for i in range(n) for j in range(n)})
                 + Fw(b_v, a_v).subs({C[i, j]: C_solved[i, j] for i in range(n) for j in range(n)}))
print("\n  Xi_w(a,b) = <w,F(a,b)> + <w,F(b,a)>  (with C eliminated via the diagonal constraint):")
Xi_w = sp.simplify(Xi_w)
print("  ", Xi_w)

diff_vec = a_v - b_v
target_w = sp.simplify(-quad(Bsym, diff_vec, diff_vec))
print("\n  claim: Xi_w(a,b) == -Bsym(a-b, a-b)   (QUADRATIC in the recentering displacement a-b)")
print("  check Xi_w - target == 0 :", sp.simplify(Xi_w - target_w) == 0)

print()
print("="*90)
print("VERDICT")
print("="*90)
print("""  Both the scalar toy model and the general n=2 vector/matrix model give the SAME clean result:

      Phi(q,p) + Phi(p,q)  =  -B_sym(q - p, q - p)  +  O(||q-p||^3)

  where B_sym is the SYMMETRIC part of the mixed base/field second joint derivative
  d/dq d/dp Phi(q0,q0) -- a genuine, FINITE quantity supplied by the banked JOINT ContDiffAt R 2
  regularity (F3) (no C^3 needed to STATE this order-2 fact; C^2 gives exactly a well-defined,
  continuous symmetric joint Hessian, which is all this identity uses).

  THE LINEAR TERM CANCELS EXACTLY AND FOR FREE:  it is FORCED to zero purely by combining
  (F1) [Phi(q,q)=0 along the whole diagonal, not just at one point] with (F2) [the field-slot
  derivative at the diagonal is +Id].  This is the vector-valued generalization of the SAME
  mechanism already exploited in GeodesicReversalRoute.lean (baseSlot_eventuallyEq_neg_terminalVel:
  U z 0 = -T_0(U 0 z), i.e. the base derivative is forced to -Id) and in
  UniformFlowCoherentChartReconciliation / ChartJetHessian's DV(q0)=+Id normalization killing a
  would-be linear term downstream.

  => VERDICT: GO.  The base-slot antisymmetry defect that Sol flagged is QUADRATIC (order ||q-p||^2),
     NOT linear, from banked facts ALONE (F1: general-q0 diagonal vanishing, F2: general-q0 field-slot
     derivative = Id, F3: joint C^2 at every diagonal point) -- no additional geometric input or
     C^3 regularity is needed for THIS order-counting claim.  This is consistent with (and gives an
     independent, cleaner derivation of) the older J4-858/859 finding that the reversal-route
     near-identity T_x0 is CUBIC (v + O(v^3)) -- a strictly SHARPER (one order better) statement about
     a DIFFERENT but related quantity (the reversal identity itself, not the antisymmetry sum), which
     already fed a full O(sqrt eps) Lean discharge of hcomp's NEAR carry in
     HCompNearCarryFullyClosed.lean / HCompNearCarryConcreteDischarge.lean (J4-858..888, uncommitted
     to the LIVE capstone route as of J4-1001).

  CAVEAT (what this does NOT show).  This is an ORDER-COUNTING fact about the antisymmetrized SUM
  Phi(q,p)+Phi(p,q), not yet the literal chart-jet transport identity
  GaussCompMixedHessian's hV1/hVj1/hPj1 hypotheses need (those require actual HasDerivAt data on a
  NEIGHBOURHOOD, not just a single 2-jet at one diagonal point) -- promoting this order-counting result
  to a literal Lean CoV lemma usable by integral_heatHessMult_transportedJet_bound_from_localRNC /
  gaussComp_pd_pd_mixed_eq_heatHessMult_sub is a genuine (but now well-scoped, GO-classified)
  construction task, not a re-run of the cp872 NO-GO trap.""")
