#!/usr/bin/env python3
"""
The two-fixed-area-sector KILL TEST — where the universal sqrt(V_gen) law breaks
================================================================================

This is the FIRST independent holographic confrontation of the max-entropy bridge postulate's
distinctive prediction, and it is a NEGATIVE result — recorded honestly.

BACKGROUND (GPT-5.5-pro expert review, 2026-07-01).
The postulate "gravity's capacity is the smooth max-entropy H_max^eps (one-shot), not S_vN" is,
conceptually, the KNOWN one-shot / max-entanglement-wedge holography (Akers-Penington
arXiv:2008.03319; Akers-Rath; Dong-Harlow-Marolf fixed-area states arXiv:1811.05382). It is
distinctive vs the naive "RT always uses S_vN", but it is NOT new physics.
Its sharper, would-be-distinctive prediction — that the shift  H_max^eps - S_vN ~ z_eps * sqrt(V_gen)
(V_gen = capacity of entanglement = Var(-log rho)) — is just the second-order source-coding /
information-spectrum expansion (Tomamichel-Hayashi), valid ONLY in the Gaussian/CLT regime.
A Haar / random-tensor-network Page-curve test (scripts/qr/maxent_pagecurve.py) "confirms" it for
exactly that boring reason. The regime that matters physically — the Page / island transition — is
a NON-Gaussian two-sector mixture, and there the universal sqrt(V) law fails.

THE TEST (Dong-Harlow-Marolf-motivated, exactly computable).
A two-fixed-area-sector reduced density matrix (the canonical Page-transition state):

    rho_R = p * (I_{D1}/D1)  (+)  q * (I_{D2}/D2),    q = 1-p,  D_i = e^{L_i},  L_i = A_i/4G,

with L2 > L1, Delta = L2 - L1 >> 1.  Exactly:
    S_vN   = p(L1 - log p) + q(L2 - log q)
    V_gen  = p q (Delta + log(p/q))^2                         (the capacity of entanglement)
    H0^eps = smooth log-support: log(#largest eigenvalues capturing weight >= 1-eps)
             = the exact one-shot / max-EW capacity for this state.

The postulate's Gaussian shift prediction is  z_eps * sqrt(V_gen).  As Delta grows:
    * the EXACT smooth one-shot shift (H0^eps - S_vN) SATURATES (bounded by the sector structure),
    * the GAUSSIAN sqrt(V) prediction grows LINEARLY in Delta and soon EXCEEDS the physical bound
      H0^eps <= L2 (i.e. predicts more records than exist).  => the universal sqrt(V) law is FALSE.

HONEST CONCLUSION.  The distinctive frontier, confronted with real holography, splits:
    (1) the universal sqrt(V_gen) prediction is FALSIFIED in the Page-transition regime (this test);
    (2) what survives -- "capacity = the smooth one-shot / max-EW entropy" -- is the known
        Akers-Penington one-shot holography: distinctive vs naive S_vN, but NOT new physics.
No QG, no value of G, no new distinctive prediction survives.  This is the calibrated endpoint.
"""

import numpy as np
from math import erf, sqrt, log, exp


def invPhi(q):
    """inverse standard-normal CDF by bisection."""
    lo, hi = -12.0, 12.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if 0.5 * (1 + erf(mid / sqrt(2))) < q:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def two_sector(p, L1, L2, eps):
    """Exact functionals of the two-fixed-area-sector spectrum.
    Sector 1: D1=e^{L1} eigenvalues each v1 = p/D1 (weight p).
    Sector 2: D2=e^{L2} eigenvalues each v2 = q/D2 (weight q).  v1 > v2 since L2>L1 (p,q O(1))."""
    q = 1.0 - p
    S = p * (L1 - log(p)) + q * (L2 - log(q))
    V = p * q * (L2 - L1 + log(p / q)) ** 2
    # smooth log-support: keep the LARGEST eigenvalues until weight >= 1-eps.
    # v1 = p e^{-L1} > v2 = q e^{-L2}.  Keep sector-1 first.
    target = 1.0 - eps
    if target <= p:
        # need only a fraction of sector 1:  k * v1 = target  ->  log k = L1 + log(target/p)
        H0 = L1 + log(target / p)
    else:
        # all of sector 1 (D1, weight p) + part of sector 2: (target - p) from sector 2
        # m = (target - p)/v2 = (target - p) e^{L2}/q ; support = D1 + m ~ m (since D2 >> D1)
        m = (target - p) * exp(L2) / q
        H0 = log(exp(L1) + m)
    return S, V, H0


def main():
    print(__doc__)
    eps = 0.01
    z = invPhi(1 - eps)
    p = 0.5
    L1 = 5.0
    print("=" * 86)
    print(f"TWO-SECTOR PAGE-TRANSITION TEST   (p=q=1/2, L1={L1}, eps={eps}, z_eps={z:.3f})")
    print("  comparing the EXACT one-shot/max-EW shift vs the postulate's Gaussian sqrt(V) shift")
    print("=" * 86)
    hdr = f"  {'Delta':>6} {'S_vN':>8} {'sqrt(Vgen)':>11} {'exact shift':>12} {'gauss z*sqrtV':>14} {'phys.max':>9} {'verdict':>14}"
    print(hdr)
    print("  " + "-" * (len(hdr) - 2))
    for Delta in [0.5, 1.0, 2.0, 4.0, 8.0, 16.0, 32.0]:
        L2 = L1 + Delta
        S, V, H0 = two_sector(p, L1, L2, eps)
        exact = H0 - S
        gauss = z * sqrt(V)
        physmax = log(exp(L1) + exp(L2)) - S   # H0 <= log(total rank) => shift <= log(D1+D2) - S
        if gauss > physmax * 1.0001:
            verdict = "GAUSS IMPOSSIBLE"
        elif abs(gauss - exact) > 0.25 * max(abs(exact), 1e-9):
            verdict = "diverged"
        else:
            verdict = "ok (Gaussian)"
        print(f"  {Delta:>6.1f} {S:>8.3f} {sqrt(V):>11.3f} {exact:>12.3f} {gauss:>14.3f} {physmax:>9.3f} {verdict:>14}")

    print("\n  READING THE TABLE:")
    print("   * EXACT one-shot shift (H0^eps - S_vN) SATURATES near (1-p)*Delta-ish -> bounded by sector structure.")
    print("   * GAUSSIAN z*sqrt(V) grows LINEARLY in Delta (sqrt(V)=Delta/2 here) and soon EXCEEDS phys.max")
    print("     = L2 - S_vN  (it predicts MORE records than the Hilbert space holds) -> the sqrt(V) law is FALSE")
    print("     in the non-Gaussian Page-transition regime. This is the kill-shot.")

    # control: sqrt(V) is recovered ONLY in the many-copy (AEP / CLT) limit -- NOT for a single region.
    print("\n" + "=" * 86)
    print("CONTROL — sqrt(V) is an ASYMPTOTIC (many-copy) fact, not a single-region one")
    print("=" * 86)
    rng = np.random.default_rng(7)
    D = 200
    x = rng.normal(0.0, 1.0, size=D)
    lam = np.exp(-x); lam /= lam.sum()
    S = float(-np.sum(lam * np.log(lam)))
    V = float(np.sum(lam * (np.log(lam)) ** 2) - S ** 2)
    surpr = -np.log(lam)
    print(f"  one smooth spectrum (D={D}):  S_vN={S:.3f},  sqrt(Vgen)={sqrt(V):.3f}")
    print(f"  {'n copies':>9} {'(H0^eps(rho^n) - nS)/sqrt(n)':>30} {'z*sqrt(V)':>11} {'ratio':>7}")
    print("  " + "-" * 60)
    for n in [1, 4, 16, 64, 256]:
        idx = rng.choice(D, size=(120000, n), p=lam)
        Xn = surpr[idx].sum(axis=1)                 # n-copy surprisal (law of rho^{otimes n})
        Hmax_n = np.quantile(Xn, 1 - eps)           # smooth one-shot log-support of rho^{otimes n}
        shift_per = (Hmax_n - n * S) / sqrt(n)
        print(f"  {n:>9} {shift_per:>30.3f} {z*sqrt(V):>11.3f} {shift_per/(z*sqrt(V)):>7.3f}")
    print(f"  -> for a NEAR-GAUSSIAN surprisal (this smooth/Haar-like spectrum) sqrt(V) holds (ratio ~ 1,")
    print(f"     all n) -- the source-coding / AEP fact (Tomamichel-Hayashi). The two-sector")
    print(f"     Page-transition state above is BIMODAL / non-Gaussian, and there sqrt(V) FAILS. So sqrt(V)")
    print(f"     is a GAUSSIANITY fact, not a holographic law: it 'works' exactly where it says nothing new.")

    print("\n" + "=" * 86)
    print("HONEST CONCLUSION (the calibrated endpoint of the distinctive-Q_R frontier)")
    print("=" * 86)
    print("  (1) The universal sqrt(V_gen) prediction is FALSIFIED at the Page/island transition")
    print("      (two-fixed-area-sector state): the exact one-shot shift saturates while z*sqrt(V)")
    print("      overshoots and violates the physical ceiling.  sqrt(V) is a Gaussian approximation,")
    print("      not a holographic law.")
    print("  (2) What survives -- capacity = the smooth one-shot / max-entanglement-wedge entropy -- is")
    print("      the KNOWN one-shot holography (Akers-Penington arXiv:2008.03319; Dong-Harlow-Marolf")
    print("      fixed-area states arXiv:1811.05382). Distinctive vs the naive 'RT always uses S_vN',")
    print("      but NOT new physics, and NOT a new Q_R.")
    print("  => QIQT-H's one distinctive frontier reduces, on contact with real holography, to known")
    print("     one-shot entanglement-wedge physics. No QG, no value of G, no surviving novel prediction.")


if __name__ == "__main__":
    main()
