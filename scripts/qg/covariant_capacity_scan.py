#!/usr/bin/env python3
"""
J4 of COVARIANT_CAPACITY_CPSUV_PLAN.md — full 2D scan of the LV-source anisotropy A_F over the
modular-vs-covariant ratio α = Λ_K/Λ and the cutoff sharpness n, locating the threshold α*(n) above
which the modular cutoff is parametrically inactive (Δc² → 0).

Builds on J1 (`covariant_capacity_regulators.py`): the one-loop speed splitting is sourced purely by
the regulator's frame anisotropy A_F = ⟨k₄² − k_x²⟩_F (=0 ⟺ Lorentz-scalar ⟺ Δc²=0), with weight
w(k²)=1/(k²+M²)³, M=1, k_x² → s²/3.  Reg C is the modular+covariant regulator

    F(k₄,s) = exp[−(k_E²/Λ²)ⁿ] · exp[−(k₄²/Λ_K²)ⁿ],   k_E²=k₄²+s²,   α = Λ_K/Λ.

The first factor is Lorentz-scalar (covariant); the second is a TEMPORAL (k₄) modular cutoff that
sources LV when active (α=O(1)).  As α→∞ the modular factor switches off ⟹ A_F→0 (covariant).  We map
|A_F|(α,n) and define the threshold α*(n) = the smallest α with |A_F| < τ (τ = 1% of the pure-modular
scale ≈ 0.33, i.e. τ = 3.3e-3) — i.e. how parametrically inactive the modular cutoff must be for the
matter loop to be Lorentz-safe.

Reproduce:  python scripts/qg/covariant_capacity_scan.py
"""
from __future__ import annotations

import warnings

import numpy as np

warnings.filterwarnings("ignore", category=DeprecationWarning)
_trapz = getattr(np, "trapezoid", np.trapz)

M = 1.0
TAU = 3.3e-3  # threshold = 1% of the pure-modular anisotropy ≈ 0.33


def anisotropy(F, Kmax: float, Smax: float, nK: int = 801, nS: int = 801) -> float:
    k4 = np.linspace(-Kmax, Kmax, nK)
    s = np.linspace(0.0, Smax, nS)
    K4, S = np.meshgrid(k4, s, indexing="ij")
    w = 1.0 / (K4 * K4 + S * S + M * M) ** 3
    base = (4.0 * np.pi * S * S) * w * F(K4, S)
    Z = _trapz(_trapz(base, s, axis=1), k4)
    It = _trapz(_trapz(base * (K4 * K4), s, axis=1), k4)
    Is = _trapz(_trapz(base * (S * S / 3.0), s, axis=1), k4)
    return float((It - Is) / Z)


def reg_C(alpha: float, n: int, Lam: float = 4.0):
    LK = alpha * Lam
    return lambda k4, s: (np.exp(-((k4 * k4 + s * s) / Lam ** 2) ** n)
                          * np.exp(-((k4 * k4) / LK ** 2) ** n))


def main() -> None:
    Lam = 4.0
    alphas = np.array([0.25, 0.354, 0.5, 0.707, 1.0, 1.414, 2.0, 2.828, 4.0, 5.657, 8.0, 11.3, 16.0])
    ns = [1, 2, 4, 8]
    Kmax = Smax = 9.0 * Lam

    print("=" * 84)
    print("J4 — Reg C anisotropy A_F(α, n) scan  (A_F = ⟨k₄²−k_x²⟩_F ∝ Δc²; 0 ⟺ Lorentz-scalar)")
    print(f"  F = exp[−(k_E²/Λ²)ⁿ]·exp[−(k₄²/Λ_K²)ⁿ], Λ={Lam}, α=Λ_K/Λ, threshold τ=|A_F|<{TAU:.1e}")
    print("=" * 84)
    header = "   α \\ n  " + "".join(f"{('n=%d' % n):>12}" for n in ns)
    print(header)
    print("   " + "-" * (len(header) - 3))

    table = {n: {} for n in ns}
    for a in alphas:
        row = f"   {a:6.3f}  "
        for n in ns:
            AF = anisotropy(reg_C(a, n, Lam), Kmax, Smax)
            table[n][a] = AF
            row += f"{AF:12.2e}"
        print(row)

    print("\n  threshold α*(n) = smallest α with |A_F| < τ (modular cutoff parametrically inactive):")
    print("    n      α*(n)        |A_F| just above / at α*")
    print("    " + "-" * 44)
    for n in ns:
        star = None
        for a in alphas:
            if abs(table[n][a]) < TAU:
                star = a
                break
        if star is None:
            print(f"    {n}      > {alphas[-1]:.1f}     (never crosses τ in scanned range)")
        else:
            print(f"    {n}      {star:6.3f}      |A_F(α*)| = {abs(table[n][star]):.2e}")

    print("\n" + "=" * 84)
    print("VERDICT: |A_F| → 0 only as α=Λ_K/Λ grows past α*(n) (modular cutoff switched off); for α ≲ 1 the")
    print("  temporal modular cutoff is active and A_F ≠ 0 (Δc² ≠ 0).  Sharper cutoffs (larger n) reach safety")
    print("  at a SMALLER α* (8.0→2.8→1.4→1.4 for n=1,2,4,8: a sharper modular factor switches off faster), but")
    print("  in ALL cases α* ≳ 1 — the modular scale Λ_K must EXCEED the covariant UV scale Λ.  So a modular/")
    print("  diamond cutoff is Lorentz-safe ONLY when it does NO UV work below Λ — i.e. it is NOT the matter")
    print("  regulator.  Consistent with J1–J3: escape requires B=0, a genuinely Lorentz-SCALAR matter UV kernel")
    print("  (J6), not a modular/diamond cutoff.")
    print("=" * 84)


if __name__ == "__main__":
    main()
