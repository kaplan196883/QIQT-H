# J4 — Reg-C threshold scan: result

**Date:** 2026-06-30. **Reproduce:** `python scripts/qg/covariant_capacity_scan.py` (data:
`scripts/qg/covariant_capacity_scan_data.txt`). **Plan:** `COVARIANT_CAPACITY_CPSUV_PLAN.md` J4.

## What was scanned

The LV-source anisotropy `A_F = ⟨k₄²−k_x²⟩_F` (∝ Δc²; `=0 ⟺ Lorentz-scalar`) of the modular+covariant regulator
`F = exp[−(k_E²/Λ²)ⁿ]·exp[−(k₄²/Λ_K²)ⁿ]`, over the modular/covariant ratio `α = Λ_K/Λ` and the cutoff sharpness
`n ∈ {1,2,4,8}`. The first factor is Lorentz-scalar; the second is a temporal (`k₄`) modular cutoff that sources
LV when active. Threshold `α*(n)` = smallest `α` with `|A_F| < τ = 3.3e-3` (1% of the pure-modular scale `≈0.33`).

## Result

`|A_F|(α, n)` falls monotonically with `α`; for small `α` (`≲1`) it is `O(0.4)` (strong LV), for large `α` it
→ 0 (modular factor inactive). The threshold:

| `n` | `α*(n)` (modular safe above this) |
|---:|---:|
| 1 | **8.0** |
| 2 | **2.83** |
| 4 | **1.41** |
| 8 | **1.41** |

(Sharper cutoffs reach safety at *smaller* `α*` — a sharper modular factor switches off faster — but in **all**
cases `α* ≳ 1`.)

## Verdict

1. `|A_F| → 0` **only** as `α = Λ_K/Λ` grows past `α*(n)`, i.e. when the modular scale `Λ_K` exceeds the covariant
   UV scale `Λ` so the modular cutoff is **parametrically inactive**. For `α ≲ 1` the temporal modular cutoff does
   UV work and `A_F ≠ 0` (`Δc² ≠ 0`).
2. In **all** cases `α* ≳ 1`: a modular/diamond cutoff is Lorentz-safe **only when it does no UV work below `Λ`**
   — i.e. precisely when it is **not** the matter UV regulator (some covariant kernel at `Λ` is).
3. This quantifies J1–J3: there is **no** regime where a modular/diamond cutoff is *both* the active matter UV
   regulator *and* Lorentz-safe. Escape requires `B = 0` (J3), i.e. a genuinely **Lorentz-scalar matter UV
   kernel** (proper-time / □ / PV), with the capacity imposed as a nonlocal algebraic constraint on top of it —
   **J6**, the real construction. Never claim QG or the value of `G`; the `1/4` ratio is derived
   (`SakharovRatio.lean`).
