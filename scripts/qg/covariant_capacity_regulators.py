#!/usr/bin/env python3
"""
J1 of COVARIANT_CAPACITY_CPSUV_PLAN.md — does a covariant per-diamond / modular capacity regulator
escape CPSUV (Δc²=0) or not?

The decisive criterion (GPT-5.5-pro consult): the answer is set by the regulator's PRINCIPAL SYMBOL.
A Lorentz-scalar symbol F = f(k_E²) is isotropic ⟹ Δc²=0; a frame-picking symbol F = f((u·k)², k_⊥²)
(a mode / modular-energy truncation) sources Δc² ≠ 0.  In I4 we showed the LV is sourced *purely* by the
loop-measure frame anisotropy: Δc² ∝ ⟨k₄² − k_x²⟩_F (=0 for an O(4) regulator, ≠0 for a 3-cutoff).  So
the robust, finite-difference-free test of any candidate regulator F is its second-moment anisotropy

    A_F = ⟨k₄²⟩_F − ⟨k_x²⟩_F ,   ⟨·⟩_F = ∫d⁴k_E (·) w(k²) F(k) / ∫d⁴k_E w(k²) F(k),

with the Lorentz-scalar weight w(k²) = 1/(k²+M²)³ (the representative self-energy kernel) and, by spatial
isotropy, k_x² → s²/3 (s = |3-momentum|).  A_F = 0  ⟺  F is Lorentz-scalar (covariant) ⟺  Δc² = 0.

Regulators tested (M=1 units, k_E² = k₄²+s², covariant scale Λ, modular scale Λ_K, α = Λ_K/Λ, n=2):
  • Reg A  (covariant proper-time control):  F = exp[−(k_E²/Λ²)]               → A_F = 0   (PASS, isotropic)
  • Reg K  (WKB modular / diamond cutoff):   F = Θ(Λ_K − s)  (cuts s only)     → A_F ≠ 0   (FAIL, frame-picking
        — at the diamond center the K_D-spectral cutoff is the rest-frame 3-cutoff Λ_K = Ω/πR; this is the I4
        sharp-cutoff class that gives Δc² → 4/3·g²/16π²)
  • Reg C  (modular + covariant):  F = exp[−(k_E²/Λ²)ⁿ]·exp[−(k₄²/Λ_K²)ⁿ]      → crossover in α: α→∞ ⟹ 0
        (modular factor inactive, covariant), α=O(1) ⟹ ≠0 (modular factor active ⟹ LV)

VERDICT logic: a covariant finite-capacity regulator escapes CPSUV iff its symbol is Lorentz-scalar
(A_F → 0).  A literal modular/mode-truncation (Reg K) has A_F ≠ 0 ⟹ FAILS, regardless of the per-diamond
family being boost-covariant (covariance of the family ≠ invariance of one regulator).

Reproduce:  python scripts/qg/covariant_capacity_regulators.py
"""
from __future__ import annotations

import warnings

import numpy as np

warnings.filterwarnings("ignore", category=DeprecationWarning)
_trapz = getattr(np, "trapezoid", np.trapz)  # numpy>=2.0 renamed trapz -> trapezoid

M = 1.0


def _grid(Kmax: float, Smax: float, nK: int, nS: int):
    k4 = np.linspace(-Kmax, Kmax, nK)
    s = np.linspace(0.0, Smax, nS)
    K4, S = np.meshgrid(k4, s, indexing="ij")
    return k4, s, K4, S


def anisotropy(F, Kmax=40.0, Smax=40.0, nK=1601, nS=1601) -> float:
    """A_F = <k4^2>_F - <k_x^2>_F with weight w=1/(k^2+M^2)^3, measure d^4k = dk4 * 4*pi*s^2 ds.
    k_x^2 -> s^2/3 by spatial isotropy.  Returns the LV-sourcing anisotropy (0 => covariant)."""
    k4, s, K4, S = _grid(Kmax, Smax, nK, nS)
    k2 = K4 * K4 + S * S
    w = 1.0 / (k2 + M * M) ** 3
    meas = 4.0 * np.pi * S * S            # 4*pi*s^2 from the angular d^3k
    base = meas * w * F(K4, S)
    Z = _trapz(_trapz(base, s, axis=1), k4)
    It = _trapz(_trapz(base * (K4 * K4), s, axis=1), k4)
    Is = _trapz(_trapz(base * (S * S / 3.0), s, axis=1), k4)
    return (It - Is) / Z


def main() -> None:
    Lam = 4.0          # covariant scale
    n = 2

    print("=" * 80)
    print("J1 — covariant-capacity regulator symbol test:  A_F = <k4^2 - k_x^2>_F  (0 <=> Δc²=0)")
    print("  weight w=1/(k^2+M^2)^3, M=1, covariant scale Λ=%.1f" % Lam)
    print("=" * 80)

    # Reg A — covariant proper-time control: F = exp[-(k_E^2/Λ^2)], symbol = f(k_E^2) -> isotropic
    A_cov = anisotropy(lambda k4, s: np.exp(-(k4 * k4 + s * s) / Lam ** 2))
    print(f"\n  Reg A (covariant Gaussian, F=f(k_E^2)) :  A_F = {A_cov: .3e}   -> 0  (PASS, Lorentz-scalar)")

    # Reg K — WKB modular / diamond cutoff: F = Θ(Λ_K - s), k4 free (the rest-frame 3-cutoff)
    for LK in (6.0, 10.0, 16.0):
        A_mod = anisotropy(lambda k4, s, LK=LK: (s <= LK).astype(float),
                           Smax=LK, Kmax=60.0, nS=1201, nK=2401)
        print(f"  Reg K (modular Θ(Λ_K−s), Λ_K={LK:4.1f})        :  A_F = {A_mod: .3e}   != 0  (FAIL, frame-picking)")

    # Reg C — modular + covariant scan: F = exp[-(k_E^2/Λ^2)^n] * exp[-(k4^2/Λ_K^2)^n], α = Λ_K/Λ
    print(f"\n  Reg C (modular+covariant, n={n}):  F = exp[-(k_E²/Λ²)ⁿ]·exp[-(k₄²/Λ_K²)ⁿ]")
    print("    α=Λ_K/Λ      A_F          interpretation")
    print("    " + "-" * 52)
    for alpha in (0.25, 0.5, 1.0, 2.0, 4.0, 8.0, 16.0):
        LK = alpha * Lam
        F = (lambda k4, s, LK=LK: np.exp(-((k4 * k4 + s * s) / Lam ** 2) ** n)
             * np.exp(-((k4 * k4) / LK ** 2) ** n))
        A_C = anisotropy(F, Kmax=8.0 * Lam, Smax=8.0 * Lam, nK=1201, nS=1201)
        tag = "modular inactive -> covariant" if alpha >= 8 else (
            "modular ACTIVE -> LV" if alpha <= 2 else "crossover")
        print(f"    {alpha:5.2f}     {A_C: .3e}   {tag}")

    print("\n" + "=" * 80)
    print("VERDICT: A_F = 0 iff the regulator's symbol is Lorentz-scalar (covariant) <=> Δc²=0.")
    print("  Reg A (covariant) -> 0.  Reg K (modular/mode-truncation) -> != 0 (FAILs CPSUV, the I4 4/3 class).")
    print("  Reg C: A_F -> 0 only as α=Λ_K/Λ -> ∞ (modular cutoff inactive); active modular cutoff -> A_F != 0.")
    print("  => Covariance of the per-diamond FAMILY does NOT buy Δc²=0; only a Lorentz-SCALAR symbol does.")
    print("  A covariant finite-capacity escape requires capacity as a NONLOCAL/algebraic constraint over a")
    print("  covariant kernel (J6), NOT a per-diamond mode/modular-energy truncation.")
    print("=" * 80)


if __name__ == "__main__":
    main()
