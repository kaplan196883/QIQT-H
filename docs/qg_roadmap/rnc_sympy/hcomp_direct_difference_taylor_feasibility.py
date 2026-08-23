import sympy as sp
import time

# J4-1081-commissioned feasibility spike: the DIRECT PAIRED-DIFFERENCE / frozen-model-
# subtraction mechanism for `nb` (VanVleckGatedSpatialSymmetry.hcomp`'s near carry),
# evaluated on the LITERAL 4-term `Bfac` normal form from BRICK 1
# (HCompNearCarryKPrimeBaseFieldCoV.lean, lines ~106-118, itself pulled from
# HCompNearCarryChartSurfaceWired's on-gate mixed normal form), NOT a 1-D toy.
#
# WHAT THIS CHECKS.  `hcomp` needs the ANTISYMMETRIZED difference the reversal identity
# (`GeodesicReversalRouteAtPoint.lean`: `U z x =^f[nhds x] - T_x (U x z)`, `T_x :=
# terminalVelAt`) produces: the base-slot Gaussian argument `v := U(z,x)` gets replaced
# by (up to the established quadratic-displacement near-isometry data,
# `terminalVelAt_displacementId_quadratic`: `||T_x(v) - v|| <= C_W ||v||^2` on a ball)
# `T_x(v) = v + Delta(v)`, `Delta` a GENERIC quadratic (homogeneous degree-2)
# vector-valued map -- six free symbols for n=2 (the fully general symmetric-bilinear
# shape any actual reversal near-isometry has, per the Lean displacement bound; kept
# FULLY SYMBOLIC since genericity of vanishing/non-vanishing is exactly what's tested).
#
# We build the literal frozen-amplitude kernel (A,dA_j,dA_i,d2A_ji frozen at z=x, i.e.
# constants c0,c1,c2,c3, times Levi(s,x)=L; SAME frozen model as
# r6_frozen_model_full_bfac_check.py, reused per "don't re-derive what's already built"),
#     K(v) := G_tau(v) * Bfac(v),   Bfac(v) := L*(hsMixed(v)*c0 + grj(v)*c1 + gri(v)*c2 + c3),
# and compute the difference `DK(v) := K(T_x(v)) - K(v) = K(v + Delta(v)) - K(v)`.
#
# CORRECT EXPANSION (fixes a first-pass bug where grading v itself accidentally
# Taylor-expanded away the reference Gaussian).  Factor
#     DK(v) = G(v) * [ ratio(v) * Bfac(v + Delta(v)) - Bfac(v) ],
#     ratio(v) := G(v+Delta(v))/G(v) = exp( -(2 v.Delta(v) + |Delta(v)|^2) / (4 tau) ),
# keeping G(v) EXACT (never Taylor-expanded -- it is the genuine tau-width reference
# Gaussian whose moments `sp.integrate` computes exactly, giving the correct tau-power
# for every surviving monomial automatically).  Only `ratio` is expanded, via a formal
# bookkeeping parameter `t` marking "one power of Delta" (`Delta -> t*Delta`, `t=1` at
# the end); `Bfac(v+t*Delta(v))` is an EXACT (not truncated) polynomial in `t` since
# Bfac is quadratic in its argument.  Each surviving `t^k` coefficient is then a genuine
# polynomial in `v`, integrated exactly against `G(v;tau)` via Gaussian moments
# (`sp.integrate`), giving the true tau-power of every term with NO approximation.
#
# The exogenous jet data PI, PJ, Q and frozen amplitude coefficients c0..c3, L are
# pinned to representative non-degenerate rationals for tractability -- legitimate for
# a feasibility SPIKE since they only weight the (fully general) v/tau/Delta structure
# under test; two independent representative sets are run to rule out numeric
# coincidence.


def run(PI_num, PJ_num, Q_num, coeffs, label, order=7):
    print(f"\n########## RUN: {label} (order up to t^{order-1}) ##########", flush=True)
    t0 = time.time()
    n = 2
    tau = sp.symbols('tau', positive=True)
    v0g, v1g = sp.symbols('v0g v1g', real=True)
    D000, D001, D011, D100, D101, D111 = sp.symbols(
        'D000 D001 D011 D100 D101 D111', real=True)
    t = sp.symbols('t', real=True)

    PI_ = list(PI_num)
    PJ_ = list(PJ_num)
    Q_ = list(Q_num)
    c0, c1, c2, c3, L = coeffs
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
    Delta_ = [d0, d1]
    Delta_t = [t * d0, t * d1]

    vTx = [v0g + Delta_t[0], v1g + Delta_t[1]]

    vDelta = dot(v, Delta_t)             # order t^1, degree-3 in v
    DeltaDelta = dot(Delta_t, Delta_t)   # order t^2, degree-4 in v
    ratio_exponent = -(2 * vDelta + DeltaDelta) / (4 * tau)

    print(f"  expanding ratio(v,t) exp series ... ({time.time()-t0:.1f}s)", flush=True)
    ratio_series = sp.series(sp.exp(ratio_exponent), t, 0, order).removeO()
    ratio_series = sp.expand(ratio_series)
    print(f"  ratio series done ({time.time()-t0:.1f}s)", flush=True)

    Bfac_shift_exact = sp.expand(Bfac(vTx))   # exact polynomial in t (degree <=4)

    bracket = sp.expand(ratio_series * Bfac_shift_exact - Bfac(v))
    # truncate bracket to the same t-order (drop t^order and above, spurious from the
    # exact*truncated product)
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
    return results


res1 = run(PI_num=(2, -1), PJ_num=(1, 3), Q_num=(-2, 1),
           coeffs=(1, 2, -1, 3, 1), label="generic set A", order=6)

res2 = run(PI_num=(1, 1), PJ_num=(2, -3), Q_num=(1, -1),
           coeffs=(2, -1, 1, -2, 1), label="generic set B", order=6)
