# I4 — the decisive one-loop Lorentz-violation test: **result = FAIL (CPSUV)**

**Date:** 2026-06-30. **Reproduce:** `python scripts/qg/cpsuv_speed_splitting.py`. **Status:** the campaign's
decisive de-risking test (`QG_CAMPAIGN_PLAN.md` §1, I4). This is the pass/fail gate for the finiteness bet.

## What was tested

The radiatively-induced Lorentz-violation (LV) **speed splitting** `Δc² = Z_s/Z_t − 1 = δZ_s − δZ_t + O(g⁴)` —
the difference between the spatial and temporal wavefunction renormalizations of a scalar, generated at **one
loop** by a Yukawa coupling under a **Lorentz-violating preferred-frame hard spatial cutoff** `|k| < Λ`,
`k₀ ∈ ℝ`. This is the Collins–Perez–Sudarsky–Urrutia–Vucetich (CPSUV) mechanism (PRL 93, 191301, 2004).

Toy (minimal, per GPT-5.5-pro consult): `L = ½(∂φ)² − ½m²φ² + ψ̄(iγ·∂ − M)ψ − g φ ψ̄ψ`; scalar 1PI two-point
from the fermion bubble; `M = 1`, `g = 1`. (φ⁴ has no external-momentum dependence at one loop; 4D φ³ is
super-renormalizable — neither carries the marginal CPSUV mechanism. Yukawa is the minimal faithful toy.)

## Result

```
 Λ/M     Δc²(quad)      Δc²(closed)   Δc²/(g²/16π²)
 0.3   -1.67e-04      -1.67e-04      -0.0264
 1     ~0             ~0             ~0
 3      5.77e-03       5.77e-03       0.911
 10     8.15e-03       8.15e-03       1.288
 100    8.44e-03       8.44e-03       1.333
 1e4    8.443432e-03   8.443432e-03   1.333333
```

Closed form (analytic): `Δc²(Λ) = (g²/12π²)(2u⁵ − u³)`, `u = L/√(1+L²)`, `L = Λ/M`. As `Λ → ∞`:

> **Δc² → g²/12π² = (4/3)·g²/16π² ≠ 0** — a **nonzero, unsuppressed** `O(g²/16π²)` plateau.
> NOT power-suppressed (`(m/Λ)²`), NOT log-suppressed (`1/log Λ`).

A Lorentz-**invariant** regulator (O(4)-symmetric ball `k_E² < Λ²`, dim-reg, covariant Pauli–Villars) gives
`δZ_t = δZ_s ⇒ Δc² = 0`.

## Honesty checks (the script does not assume the verdict)

1. **Numerics vs analytic:** `scipy.quad` of the loop integrands reproduces the closed form to `max rel err
   ≈ 6e-16` (machine precision).
2. **Symbolic verification:** `sympy` confirms `d/dL (2u⁵ − u³) = L²(7L²−3)/(1+L²)^{7/2}` (the closed form *is*
   the antiderivative of the integrand) — `True`.
3. **Geometric root cause computed, not assumed:** the LV-sourcing second-moment anisotropy `I_t − I_s` of the
   loop measure is `≈ 0` for the O(4) ball (`1.8e-15`, Lorentz-invariant) and `≈ 1.61` for the preferred-frame
   cylinder. The LV is sourced *purely* by the regulator's frame-dependence, exactly as CPSUV requires.

(My earlier Euclidean attempt — an integrand `~(k₄²−k_x²)/k⁶`, UV-absolutely-convergent, whose full ℝ⁴ angular
average is zero, giving a spurious `~1/logΛ` suppression — was **wrong**: it divided the finite LV difference by
the common log-divergent wavefunction renorm. The genuine effect is the *difference* `δZ_s − δZ_t`, finite, never
divided by the log. Recorded so the error isn't repeated.)

## Verdict — FAIL (CPSUV), and what it means for the program

**A naive "finite-capacity = Lorentz-violating hard cutoff" implementation is dead.** Ordinary interactions
radiatively generate **unsuppressed** dimension-4 Lorentz violation (`Δc² ~ O(g²/16π²)`, here `4/3·g²/16π²`),
which is wildly excluded experimentally (Lorentz violation is bounded at `< 10⁻¹⁸`–`10⁻²³` in many channels;
Kostelecký–Russell SME tables). The exact `O(1)` coefficient is regulator-shape dependent; the **unsuppressed
`O(g²/16π²)` scaling is the robust, regulator-independent fact** — that is the part that kills the branch.

**This does NOT kill finite capacity per se** — it kills the *naive realization*. Approximate low-energy Lorentz
invariance from a finite local Hilbert space is established (critical spin chains / QCAs; cf. I3, the free
dispersion's `α=2` no-floor). The escape routes, all of which QIQT-H must now explicitly claim if it wants
Lorentz invariance, are: an **exact protecting symmetry**, **SUSY-like radiative cancellations**, **deformed or
statistical Lorentz invariance** (causal-set-style, no preferred frame in the measure), or a **nonlocal /
holographic substrate** (the finite capacity is *not* a sharp local momentum cutoff).

**Consequence for the campaign.** The finite-capacity postulate (P4) cannot be realized as a sharp Lorentz-
violating UV cutoff. Any Tier-2 substrate (the HaPPY/RTN toy, I7) must demonstrate one of the protection
mechanisms above — its Lorentz-violation error must be shown *suppressed*, not merely small at tree level. This
sharpens the Tier-2 §2.5 "RG control / suppressed Lorentz violation" requirement from a hope into a hard,
measured pass/fail criterion: **measure `Δc²(Λ)` in the substrate; it must vanish parametrically as `Λ → ∞`.**
