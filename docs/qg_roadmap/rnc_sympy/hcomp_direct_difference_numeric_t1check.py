import sympy as sp
import time

# Cheap confirmatory follow-up to hcomp_direct_difference_numeric_feasibility.py.
# Set A (there) already gave a DECISIVE result: the t^1 order (linear in Delta,
# i.e. -Bfac-cross-term with the *reversal* displacement) does NOT vanish -- it
# integrates to a plain tau-INDEPENDENT constant (-8), not even decaying, let alone
# at O(sqrt(eps)).  Since the full order-5 run costs ~360s PER representative set
# (t^4 alone took +220s), this script only recomputes the t^0 and t^1 orders
# (order=2) for sets B, C, D to check ROBUSTNESS of "t^1 survives and is generically
# nonzero" without paying the t^3/t^4 cost again.


def run_t1_only(PI_num, PJ_num, Q_num, coeffs, Delta_num, label):
    print(f"\n##### {label} (t^0, t^1 only) #####", flush=True)
    t0 = time.time()
    n = 2
    tau = sp.symbols('tau', positive=True)
    v0g, v1g = sp.symbols('v0g v1g', real=True)
    t = sp.symbols('t', real=True)

    PI_ = list(PI_num); PJ_ = list(PJ_num); Q_ = list(Q_num)
    c0, c1, c2, c3, L = coeffs
    D000, D001, D011, D100, D101, D111 = Delta_num
    v = [v0g, v1g]

    def dot(a, b):
        return sum(ai * bi for ai, bi in zip(a, b))

    r2v = dot(v, v)
    Gv = sp.exp(-r2v / (4 * tau)) / (4 * sp.pi * tau)**sp.Rational(n, 2)

    def Bfac(vec):
        vPI = dot(vec, PI_); vPJ = dot(vec, PJ_); vQ = dot(vec, Q_)
        hsMixed = vPI * vPJ / (4 * tau**2) - (dot(PI_, PJ_) + vQ) / (2 * tau)
        grj = -vPJ / (2 * tau)
        gri = -vPI / (2 * tau)
        return L * (hsMixed * c0 + grj * c1 + gri * c2 + c3)

    d0 = D000 * v0g**2 + D001 * v0g * v1g + D011 * v1g**2
    d1 = D100 * v0g**2 + D101 * v0g * v1g + D111 * v1g**2
    Delta_t = [t * d0, t * d1]
    vTx = [v0g + Delta_t[0], v1g + Delta_t[1]]

    # linear order only: DK ~ t * [ dBfac(v).Delta(v) - (v.Delta(v)/(2 tau)) * Bfac(v) ]
    # (obtained by differentiating ratio*Bfac_shift at t=0; do it directly via series
    # to order=2 exactly as the main script does, but STOP there -- cheap.)
    vDelta = dot(v, Delta_t)
    DeltaDelta = dot(Delta_t, Delta_t)
    ratio_exponent = -(2 * vDelta + DeltaDelta) / (4 * tau)
    ratio_series = sp.series(sp.exp(ratio_exponent), t, 0, 2).removeO()
    Bfac_shift = sp.expand(Bfac(vTx))
    bracket = sp.expand(ratio_series * Bfac_shift - Bfac(v))
    bracket_poly_t = sp.Poly(bracket, t)

    for k in (0, 1):
        if k > bracket_poly_t.degree():
            print(f"  t^{k}: absent"); continue
        coeff = sp.expand(bracket_poly_t.coeff_monomial(t**k))
        if coeff == 0:
            print(f"  t^{k}: ZERO"); continue
        Ik = coeff * Gv
        for w in (v0g, v1g):
            Ik = sp.integrate(Ik, (w, -sp.oo, sp.oo))
        Ik = sp.simplify(Ik)
        print(f"  t^{k}: I = {Ik}  (nonzero={Ik != 0})   ({time.time()-t0:.1f}s)", flush=True)
    print(f"  done ({time.time()-t0:.1f}s)")


run_t1_only((1, 1), (2, -3), (1, -1), (2, -1, 1, -2, 1), (-1, 2, -3, 1, -2, -1), "set B")
run_t1_only((3, -2), (-1, 2), (2, 3), (-1, 3, 2, 1, -1), (2, 1, -1, 3, -2, 1), "set C")
run_t1_only((1, -1), (1, 1), (0, 2), (1, 1, 1, 1, 2), (0, 1, -1, 1, 0, 2), "set D")
print("\nALL DONE", flush=True)
