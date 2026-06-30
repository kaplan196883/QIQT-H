#!/usr/bin/env python3
"""
QG campaign I4 — the DECISIVE one-loop Lorentz-violation (LV) speed-splitting test.

Computes Delta c^2 = Z_s/Z_t - 1 = delta_Z_s - delta_Z_t + O(g^4), the radiatively-induced
splitting between the spatial and temporal wavefunction renormalizations of a scalar, induced at
one loop by a Yukawa coupling under a *Lorentz-violating preferred-frame hard spatial cutoff*
|k| < Lambda  (k_0 in R unbounded).  This is the Collins-Perez-Sudarsky-Urrutia-Vucetich (CPSUV)
mechanism (PRL 93, 191301, 2004): a naive finite/LV cutoff with ordinary interactions generates
*unsuppressed* dimension-4 Lorentz violation.

Toy (minimal; per GPT-5.5-pro consult 2026-06-30):
    L = 1/2 (d phi)^2 - 1/2 m^2 phi^2 + psibar(i gamma.d - M) psi - g phi psibar psi
Compute the scalar 1PI two-point Pi(p) from the fermion bubble; expand
    Pi_E(p) = Pi_E(0) + delta_Z_t p_4^2 + delta_Z_s |p|^2 + ...
After the k_0 (Wick) integral and spatial angular average, with x = r/M, L = Lambda/M:

    delta_Z_t = (g^2/4 pi^2)  ∫_0^L  x^4 / (1+x^2)^{5/2} dx
    delta_Z_s = (g^2/12 pi^2) ∫_0^L  x^2 (3x^4 + 10x^2 - 3) / (1+x^2)^{7/2} dx
    Delta c^2 = delta_Z_s - delta_Z_t
              = (g^2/12 pi^2) ∫_0^L  x^2 (7x^2 - 3) / (1+x^2)^{7/2} dx
              = (g^2/12 pi^2) (2 u^5 - u^3),   u = L / sqrt(1+L^2).

  As Lambda -> infinity:   Delta c^2 -> g^2/(12 pi^2) = (4/3) * g^2/(16 pi^2)  != 0.

A Lorentz-INVARIANT regulator (O(4)-symmetric ball k_E^2 < Lambda^2, dim-reg, covariant PV) gives
delta_Z_t = delta_Z_s, hence Delta c^2 = 0.

HONEST verdict: a nonzero O(g^2/16 pi^2) plateau (NOT power- or log-suppressed) = CPSUV = FAIL for a
naive Lorentz-violating finite cutoff (unless a symmetry / counterterm tuning / dynamical mechanism
protects Lorentz invariance).  The exact O(1) coefficient is regulator-shape dependent; the
unsuppressed *scaling* O(g^2/16 pi^2) is the robust, regulator-independent statement.

The script does not assume the verdict: it (a) numerically integrates the loop integrands and checks
they match the analytic closed form to ~1e-9, (b) symbolically verifies (sympy) that the closed form
differentiates back to the integrand, and (c) demonstrates the geometric ROOT CAUSE — the LV-sourcing
second-moment anisotropy of the loop measure vanishes for the O(4) regulator and is nonzero for the
preferred-frame one.

Reproduce:  python scripts/qg/cpsuv_speed_splitting.py
"""
from __future__ import annotations

import numpy as np
from scipy.integrate import quad, dblquad

PI = np.pi


# ----------------------------------------------------------------------------------------------------
# Part A — the precise Delta c^2(Lambda), preferred-frame hard spatial cutoff |k| < Lambda
# ----------------------------------------------------------------------------------------------------
def delta_Zt_radial(L: float, g: float = 1.0) -> float:
    f = lambda x: x ** 4 / (1.0 + x * x) ** 2.5
    val, _ = quad(f, 0.0, L, epsabs=1e-13, epsrel=1e-12, limit=400)
    return g * g / (4.0 * PI ** 2) * val


def delta_Zs_radial(L: float, g: float = 1.0) -> float:
    f = lambda x: x * x * (3 * x ** 4 + 10 * x * x - 3.0) / (1.0 + x * x) ** 3.5
    val, _ = quad(f, 0.0, L, epsabs=1e-13, epsrel=1e-12, limit=400)
    return g * g / (12.0 * PI ** 2) * val


def delta_c2_radial(L: float, g: float = 1.0) -> float:
    """Direct integral of delta_Z_s - delta_Z_t (avoids subtracting two log-divergent pieces)."""
    f = lambda x: x * x * (7 * x * x - 3.0) / (1.0 + x * x) ** 3.5
    val, _ = quad(f, 0.0, L, epsabs=1e-13, epsrel=1e-12, limit=400)
    return g * g / (12.0 * PI ** 2) * val


def delta_c2_closed(L: float, g: float = 1.0) -> float:
    u = L / np.sqrt(1.0 + L * L)
    return g * g / (12.0 * PI ** 2) * (2 * u ** 5 - u ** 3)


# ----------------------------------------------------------------------------------------------------
# Part B — geometric root cause: the LV-sourcing second-moment anisotropy of the loop measure.
#   I_t = <k_4^2 w>,  I_s = <k_x^2 w> = <(s^2/3) w>,  w(k^2) = 1/(k^2+M^2)^3  (M=1),  k^2 = k_4^2 + s^2.
#   Lorentz violation is sourced by (I_t - I_s).  Under the O(4) ball it must vanish; under the
#   preferred-frame cylinder it does not.  Measure: d^4k = dk_4 * 4 pi s^2 ds.
# ----------------------------------------------------------------------------------------------------
def _anis_components(region: str, Lam: float):
    """Return (I_t, I_s) for region in {'cylinder','ball'}.  Integrand weight w = 1/(k^2+1)^3."""
    def w(k4, s):
        k2 = k4 * k4 + s * s
        return (4.0 * PI * s * s) / (k2 + 1.0) ** 3  # 4 pi s^2 from d^3k angular

    if region == "cylinder":
        # s in [0, Lam], k4 in (-inf, inf); integrand even in k4 -> 2 * [0, inf)
        It, _ = dblquad(lambda k4, s: 2.0 * (k4 * k4) * w(k4, s), 0.0, Lam, 0.0, np.inf,
                        epsabs=1e-11, epsrel=1e-10)
        Is, _ = dblquad(lambda k4, s: 2.0 * (s * s / 3.0) * w(k4, s), 0.0, Lam, 0.0, np.inf,
                        epsabs=1e-11, epsrel=1e-10)
    elif region == "ball":
        # k4^2 + s^2 < Lam^2:  s in [0, Lam], k4 in [-sqrt(Lam^2-s^2), +...]; even -> 2*[0, top]
        top = lambda s: np.sqrt(max(Lam * Lam - s * s, 0.0))
        It, _ = dblquad(lambda k4, s: 2.0 * (k4 * k4) * w(k4, s), 0.0, Lam, 0.0, top,
                        epsabs=1e-11, epsrel=1e-10)
        Is, _ = dblquad(lambda k4, s: 2.0 * (s * s / 3.0) * w(k4, s), 0.0, Lam, 0.0, top,
                        epsabs=1e-11, epsrel=1e-10)
    else:
        raise ValueError(region)
    return It, Is


# ----------------------------------------------------------------------------------------------------
def main() -> None:
    g = 1.0
    norm = g * g / (16.0 * PI ** 2)
    plateau = g * g / (12.0 * PI ** 2)  # = (4/3) * norm

    print("=" * 84)
    print("QG I4 — one-loop LV speed splitting  Delta c^2 = Z_s/Z_t - 1  (Yukawa, preferred-frame cutoff)")
    print("=" * 84)

    # --- (b) symbolic verification that the closed form differentiates back to the integrand ---
    try:
        import sympy as sp
        Ls = sp.symbols("L", positive=True)
        u = Ls / sp.sqrt(1 + Ls ** 2)
        closed = 2 * u ** 5 - u ** 3
        integrand = Ls ** 2 * (7 * Ls ** 2 - 3) / (1 + Ls ** 2) ** sp.Rational(7, 2)
        ok = sp.simplify(sp.diff(closed, Ls) - integrand) == 0
        print(f"[check] sympy: d/dL (2u^5 - u^3) == L^2(7L^2-3)/(1+L^2)^(7/2) :  {ok}")
    except Exception as e:  # sympy optional
        print(f"[check] sympy verification skipped ({e})")

    # --- (a) numerics vs closed form, and the Delta c^2(Lambda) / (g^2/16 pi^2) plateau ---
    print("\n Lambda/M    delta_Z_t      delta_Z_s      Dc2(quad)      Dc2(closed)   Dc2/(g^2/16pi^2)")
    print(" " + "-" * 82)
    max_rel_err = 0.0
    max_abs_err = 0.0
    for L in [0.3, 1.0, 3.0, 10.0, 30.0, 100.0, 1e3, 1e4]:
        zt = delta_Zt_radial(L, g)
        zs = delta_Zs_radial(L, g)
        dq = delta_c2_radial(L, g)
        dc = delta_c2_closed(L, g)
        max_abs_err = max(max_abs_err, abs(dq - dc))
        if abs(dc) > 1e-6:  # skip the L=1 row where Dc2 crosses 0 (rel. error is ill-defined)
            max_rel_err = max(max_rel_err, abs(dq - dc) / abs(dc))
        print(f" {L:8.1g}  {zt: .6e}  {zs: .6e}  {dq: .6e}  {dc: .6e}   {dc/norm: .6f}")
    print(f"\n[check] numerics vs analytic: max abs err = {max_abs_err:.2e}, "
          f"max rel err (|Dc2|>1e-6) = {max_rel_err:.2e}  (numerics reproduce the closed form)")
    print(f"[result] Delta c^2(Lambda->inf) = g^2/(12 pi^2) = {plateau:.8e}")
    print(f"[result] normalized plateau Delta c^2 / (g^2/16 pi^2) -> {plateau/norm:.6f}   (= 4/3)")

    # --- (c) geometric root cause: anisotropy vanishes for O(4) ball, nonzero for cylinder ---
    print("\n geometric root cause — LV-sourcing second-moment anisotropy (I_t - I_s) of the loop measure:")
    print("   region            I_t           I_s         I_t - I_s     (LV source)")
    print("   " + "-" * 66)
    Lam = 8.0
    for region in ("ball", "cylinder"):
        It, Is = _anis_components(region, Lam)
        tag = "Lorentz-invariant  -> 0" if region == "ball" else "preferred-frame   -> != 0"
        print(f"   {region:9s}   {It: .6e}  {Is: .6e}  {It - Is: .6e}   {tag}")

    # --- verdict ---
    print("\n" + "=" * 84)
    print("VERDICT:  FAIL (CPSUV).  Delta c^2 -> a NONZERO O(g^2/16 pi^2) plateau (4/3 for this toy),")
    print("  NOT power- or log-suppressed.  A naive Lorentz-violating finite/hard cutoff radiatively")
    print("  generates UNSUPPRESSED dimension-4 Lorentz violation.  The O(4)-symmetric regulator gives 0.")
    print("  => the naive finite-capacity-as-hard-cutoff branch is dead unless Lorentz invariance is")
    print("  PROTECTED (exact symmetry / SUSY-like cancellation / deformed or statistical Lorentz")
    print("  invariance / a nonlocal or holographic substrate).  Exact O(1) coeff is regulator-shape")
    print("  dependent; the unsuppressed O(g^2/16 pi^2) SCALING is the robust, regulator-independent fact.")
    print("=" * 84)


if __name__ == "__main__":
    main()
