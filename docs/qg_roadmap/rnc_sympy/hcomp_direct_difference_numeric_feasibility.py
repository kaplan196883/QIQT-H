import sympy as sp
import time

# J4-1081-commissioned feasibility spike (FAST NUMERIC rerun).  Supersedes the
# uncommitted `hcomp_direct_difference_taylor_feasibility.py`, which used FULLY
# SYMBOLIC Delta coefficients (D000..D111) combined with sp.series to t^6 and
# per-degree sp.integrate over R^2 -- this combinatorially exploded (killed after
# 15+ min stuck in a single sp.series call).  Same mathematical setup (see that
# file's header comment for the full derivation -- G, Bfac, K, Delta, the
# ratio(v,t)*Bfac(v+t*Delta(v)) - Bfac(v) factorization keeping G(v) EXACT), but:
#   * Delta's six coefficients (D000,D001,D011,D100,D101,D111) are NUMERIC
#     rationals, not symbols -- this is legitimate for a feasibility spike since
#     `terminalVelAt_displacementId_quadratic` (HCompNearCarryConcreteDischarge.lean
#     lines 189-218) gives Delta(v) = (1/2) B(v,v) for a SYMMETRIC bilinear B, i.e.
#     exactly the general homogeneous-quadratic shape D000..D111 already assumed
#     (no further Lean-mandated structure beyond symmetry, which is already baked
#     into the D000..D111 parametrization -- there is no "D001 must equal D100"
#     type constraint since d0,d1 are independent components of B(v,v)).
#   * order reduced to t^4 (Delta is homogeneous degree 2, so t^0..t^1 terms are
#     structurally trivial/linear-only; the interesting cancellation window is
#     t^2..t^4).
#   * FOUR independent representative numeric (PI,PJ,Q,coeffs,Delta) sets are run,
#     varying sign patterns of D*** relative to PI/PJ/Q, to check the verdict is
#     robust and not a numeric coincidence (same technique as
#     hcomp_T1T2T3_sliver_rate.py's multi-frequency check).
#
# VERDICT RULE.  GREEN iff, across ALL sets, the t^0 and t^1 orders vanish
# (moment-vanishing at the orders that would otherwise dominate) and the leading
# surviving order is t^2 or later with a tau-power compatible with (or better than)
# O(sqrt(eps)) once combined with the sliver eps~tau bookkeeping (i.e. leading
# surviving order integrates to a genuine tau^{p} with p large enough -- for this
# spike we only check the STRUCTURAL cancellation pattern: which t-orders vanish).


def run(PI_num, PJ_num, Q_num, coeffs, Delta_num, label, order=5):
    print(f"\n########## RUN: {label} (order up to t^{order-1}) ##########", flush=True)
    t0 = time.time()
    n = 2
    tau = sp.symbols('tau', positive=True)
    v0g, v1g = sp.symbols('v0g v1g', real=True)
    t = sp.symbols('t', real=True)

    PI_ = list(PI_num)
    PJ_ = list(PJ_num)
    Q_ = list(Q_num)
    c0, c1, c2, c3, L = coeffs
    D000, D001, D011, D100, D101, D111 = Delta_num
    v = [v0g, v1g]

    def dot(a, b):
        return sum(ai * bi for ai, bi in zip(a, b))

    r2v = dot(v, v)
    Gv = sp.exp(-r2v / (4 * tau)) / (4 * sp.pi * tau)**sp.Rational(n, 2)

    def Bfac(vec):
        vPI = dot(vec, PI_)
        vPJ = dot(vec, PJ_)
        vQ = dot(vec, Q_)
        hsMixed = vPI * vPJ / (4 * tau**2) - (dot(PI_, PJ_) + vQ) / (2 * tau)
        grj = -vPJ / (2 * tau)
        gri = -vPI / (2 * tau)
        return L * (hsMixed * c0 + grj * c1 + gri * c2 + c3)

    d0 = D000 * v0g**2 + D001 * v0g * v1g + D011 * v1g**2
    d1 = D100 * v0g**2 + D101 * v0g * v1g + D111 * v1g**2
    Delta_t = [t * d0, t * d1]

    vTx = [v0g + Delta_t[0], v1g + Delta_t[1]]

    vDelta = dot(v, Delta_t)             # order t^1, degree-3 in v
    DeltaDelta = dot(Delta_t, Delta_t)   # order t^2, degree-4 in v
    ratio_exponent = -(2 * vDelta + DeltaDelta) / (4 * tau)

    ratio_series = sp.series(sp.exp(ratio_exponent), t, 0, order).removeO()
    ratio_series = sp.expand(ratio_series)

    Bfac_shift_exact = sp.expand(Bfac(vTx))   # exact polynomial in t (degree <=4)

    bracket = sp.expand(ratio_series * Bfac_shift_exact - Bfac(v))
    bracket_poly_t = sp.Poly(bracket, t)
    print(f"  bracket built, degrees in t: {sorted({m[0] for m in bracket_poly_t.monoms()})}"
          f" ({time.time()-t0:.1f}s)", flush=True)

    results = {}
    for k in range(0, order):
        if k > bracket_poly_t.degree():
            continue
        coeff = sp.expand(bracket_poly_t.coeff_monomial(t**k))
        if coeff == 0:
            results[k] = sp.Integer(0)
            continue
        Ik = coeff * Gv
        for w in (v0g, v1g):
            Ik = sp.integrate(Ik, (w, -sp.oo, sp.oo))
        Ik = sp.simplify(Ik)
        results[k] = Ik
        print(f"    I_(t^{k})(tau) = {Ik}   ({time.time()-t0:.1f}s)", flush=True)

    nonzero = sorted(k for k, val in results.items() if val != 0)
    zero = sorted(k for k, val in results.items() if val == 0)
    print("  ZERO (moment-vanishing) t-orders:", zero)
    print("  NONZERO (surviving) t-orders:", nonzero)
    if nonzero:
        leading = min(nonzero)
        print(f"  LEADING SURVIVING t-order: t^{leading}, I = {results[leading]}")
    else:
        print("  ALL computed t-orders vanish (need higher order to find leading survivor).")
    print(f"  [{label}] total time {time.time()-t0:.1f}s", flush=True)
    return results


t_start = time.time()

res1 = run(PI_num=(2, -1), PJ_num=(1, 3), Q_num=(-2, 1),
           coeffs=(1, 2, -1, 3, 1),
           Delta_num=(1, -2, 3, -1, 2, 1),
           label="set A: all-positive-ish Delta", order=5)

res2 = run(PI_num=(1, 1), PJ_num=(2, -3), Q_num=(1, -1),
           coeffs=(2, -1, 1, -2, 1),
           Delta_num=(-1, 2, -3, 1, -2, -1),
           label="set B: Delta sign-flipped vs A", order=5)

res3 = run(PI_num=(3, -2), PJ_num=(-1, 2), Q_num=(2, 3),
           coeffs=(-1, 3, 2, 1, -1),
           Delta_num=(2, 1, -1, 3, -2, 1),
           label="set C: mixed magnitudes", order=5)

res4 = run(PI_num=(1, -1), PJ_num=(1, 1), Q_num=(0, 2),
           coeffs=(1, 1, 1, 1, 2),
           Delta_num=(0, 1, -1, 1, 0, 2),
           label="set D: degenerate PI/Q + zero Delta entries", order=5)

print(f"\nTOTAL WALL CLOCK: {time.time()-t_start:.1f}s", flush=True)

all_results = {"A": res1, "B": res2, "C": res3, "D": res4}
print("\n########## SUMMARY ##########")
for lbl, res in all_results.items():
    zero = sorted(k for k, val in res.items() if val == 0)
    nonzero = sorted(k for k, val in res.items() if val != 0)
    print(f"  set {lbl}: zero orders={zero}  nonzero orders={nonzero}")
