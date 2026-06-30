# J1 — covariant-capacity regulator symbol test: result

**Date:** 2026-06-30. **Reproduce:** `python scripts/qg/covariant_capacity_regulators.py` (data:
`scripts/qg/covariant_capacity_data.txt`). **Plan:** `COVARIANT_CAPACITY_CPSUV_PLAN.md` J1.

## What was tested

Whether a candidate finite-capacity regulator `F` escapes CPSUV (`Δc²=0`) is decided by its **principal symbol**.
I4 established that the one-loop `Δc²` is sourced *purely* by the loop-measure frame anisotropy
`A_F = ⟨k₄²⟩_F − ⟨k_x²⟩_F` (=0 for an O(4) regulator, ≠0 for a 3-cutoff). So `A_F` is a robust,
finite-difference-free proxy: **`A_F = 0 ⟺ F is Lorentz-scalar ⟺ Δc² = 0`.** Weight `w(k²)=1/(k²+M²)³`, `M=1`.

## Result

| Regulator | `A_F` | reading |
|---|---:|---|
| **Reg A** — covariant Gaussian `F=exp[−k_E²/Λ²]` (symbol `f(k_E²)`) | `0.000` | **PASS** — Lorentz-scalar ⟹ Δc²=0 |
| **Reg K** — modular/diamond cutoff `F=Θ(Λ_K−s)` (`Λ_K=6,10,16`) | `0.333, 0.331, 0.323` | **FAIL** — `O(1)`, **un-suppressed in Λ_K** (the I4 `4/3` CPSUV class) |
| **Reg C** — modular+covariant `exp[−(k_E²/Λ²)²]·exp[−(k₄²/Λ_K²)²]`, `α=Λ_K/Λ` | see below | crossover |

Reg C scan (`A_F` vs `α=Λ_K/Λ`): `−0.42 (α=0.25) → −0.22 → −0.045 (α=1) → −3.5e-3 → −2.2e-4 → −1.4e-5 → −8.8e-7
(α=16)`. So `A_F → 0` **only** as the modular cutoff becomes inactive (`α→∞`); whenever the modular factor is
active (`α=O(1)`), `A_F ≠ 0`.

## Verdict

1. The symbol criterion is numerically confirmed: **Lorentz-scalar symbol ⟹ `A_F=0` ⟹ `Δc²=0`** (Reg A);
   **frame-picking symbol ⟹ `A_F≠0` ⟹ CPSUV** (Reg K).
2. The **modular / diamond mode-truncation regulator (Reg K) FAILS**, and its anisotropy is `O(1)` and
   **independent of `Λ_K`** — exactly the un-suppressed CPSUV behaviour (the diamond-center `K_D`-cutoff *is* the
   rest-frame 3-cutoff `Λ_K=Ω/πR`, the I4 `4/3` class).
3. **Covariance of the per-diamond *family* does NOT buy `Δc²=0`** — only a Lorentz-*scalar* symbol does (Reg C
   shows the modular cutoff must be parametrically inactive, `α→∞`, to be safe). This is the GPT-5.5-pro crux,
   now numerically demonstrated.

## Consequence for QIQT-H

A covariant finite-capacity regulator escapes CPSUV **iff** capacity is imposed as a **nonlocal / algebraic
state-count constraint over a Lorentz-scalar UV kernel** (plan J6), **NOT** as a per-diamond mode / modular-energy
truncation. The next, decisive increment is **J2** — the local-symbol *audit* of QIQT-H's *actual* `Q_D = log
#Atoms ≤ A(∂D)/4ℓ_P²`: is it (a) a mode/modular truncation (⟹ FAIL, this section) or (b) an algebraic count over a
covariant kernel (⟹ escape candidate)? That audit decides the answer; J1 only calibrated the criterion. Never
claim QG or the value of `G`; the `1/4` ratio is derived (`SakharovRatio.lean`).
