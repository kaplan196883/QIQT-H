# I4 — the Lorentz-cutoff stress test: RESULTS (2026-07-02)

**The decisive one-loop naturalness gate of `QG_CAMPAIGN_PLAN.md` has been EXECUTED.**
Design GPT-5.5-pro-verified (2026-07-02); script `scripts/lorentz_stress_test.py`; all quadratures validated
against closed forms to ≤ 2·10⁻¹⁸.

## The test

CPSUV (Collins–Perez–Sudarsky–Urrutia–Vucetich, PRL 93:191301, 2004): a preferred-frame UV cutoff plus
interactions generates a **dimension-4 Lorentz-violating kinetic term at one loop**, `Δc² = O(g²/16π²)`,
**unsuppressed** by `E/Λ`. Toy: Euclidean Yukawa (`m = M = g = 1`); the observable is the scalar speed
splitting from the fermion loop, `Δc²_φ = Z_s/Z_t − 1 = α_s − α_t`, computed as the DIFFERENCE integrand
directly (the individual Z's log-diverge; only the difference is physical).

## Results

| Family | `Δc²` as `Λ→∞` | Verdict |
|---|---|---|
| (A) sharp spatial cutoff `θ(Λ−\|k\|)` | fitted `c₀ = 8.44342·10⁻³` vs analytic `g²/12π² = 8.44343·10⁻³` (fit residual 4.5·10⁻⁸) | **FAIL — unsuppressed constant** |
| (B) smooth spatial profiles `f(\|k\|/Λ)` | `g²/12π²·[1 + 2∫x f′(x)² dx]` — gauss `1.6887·10⁻²`, quartic `2.5330·10⁻²`, fermi `2.2516·10⁻²` (all matched numerically) | **FAIL — every profile ≥ the CPSUV constant** |
| (C) fermion self-energy cross-check (sharp, `M = m`) | `−g²/48π² = −2.11086·10⁻³` (matched to 4·10⁻¹⁹) | **FAIL (independent channel)** |
| (D) covariant O(4) regulator `R(k_E²/Λ²)` | `Π(q) = P(q_E²)` ⟹ `Δc² = 0` **identically by symmetry**; numerical second differences agree to quadrature precision | **PASS** |

Finite-`Λ` behavior of (A) is the closed form
`Δc²(Λ) = g²/(12π²)·[2X⁵/(1+X²)^{5/2} − X³/(1+X²)^{3/2}]`, `X = Λ/m` — approaching the nonzero constant
from below with `O(m²/Λ²)` corrections: the violation does **not** decouple as the cutoff is removed.

## The honest verdict for QIQT-H

1. **A preferred-frame spatial realization of finite capacity is DEAD.** Any QIQT-H implementation equivalent
   to a spatial momentum cutoff generates percent-level (`×g²`) Lorentz violation at one loop, excluded by
   experiment by many orders of magnitude. This branch is falsified — the gate did its job.
2. **The covariant branch survives by symmetry.** A manifestly Lorentz/O(4)-invariant regulator family gives
   `Δc² = 0` exactly (the LV kinetic operator is forbidden by the regulator's symmetry). This singles out the
   OP3b covariant-diamond architecture (per-diamond `Q_D`, boost-invariant `μ`) as the ONLY branch not killed.
3. **The residual danger (named, open):** a causal diamond has tips and hence a natural timelike vector
   `u^μ_D`. If the microscopic capacity truncation uses that vector as a physical rest frame, loops can still
   generate `u^μu^ν∂_μφ∂_νφ` unsuppressed. "The area is invariant" is NOT enough — the actual regulator,
   measure, and state must leave no preferred `u^μ` in the vacuum effective action. Testing THIS (a
   diamond-based covariant spectral/proper-time regulator) is the follow-on experiment.
4. **What this does NOT prove:** that every finite-capacity realization is safe; the value of `G`; anything
   about Tier 2/3. NOT QG. It is a falsification gate that killed one branch and constrained the survivor.

## Lean certification (companion increments)

- `QIQTH/QG/LatticeDispersionBound.lean` (I3): the free lattice dispersion defect bound
  `|E_a(p)² − (m²+p²)| ≤ a²p⁴/12` — the free-field pass (defect suppressed, no floor).
- `QIQTH/QG/CpsuvGate.lean` (I4-cert): the certified closed form and its nonzero limit
  `Δc²_sharp(X) → 1/(12π²) ≠ 0` (the unsuppressed-constant statement, machine-checked), plus the covariant
  symmetry certificate (an O(4)-symmetric two-point function has equal temporal/spatial quadratic
  coefficients — `Δc² = 0` by exchange symmetry).
