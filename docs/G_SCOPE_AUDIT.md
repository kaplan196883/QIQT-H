# G-derivation SCOPE AUDIT — what the induced-`G` + area-law Lean package proves, exactly

**Purpose.** A status firewall for the manuscript: every major induced-`G` / area-law claim, labelled by *what kind*
of statement it is, so the paper quotes theorem types — not paraphrased stronger claims. Generated 2026-07-07 from the
axiom-free Lean sources (all theorems below `#print axioms` = `propext, Classical.choice, Quot.sound` only; budget 0).
This is an AUDIT NOTE, not manuscript prose — the author applies it. GPT-5.5-pro-checklist-driven.

## Legend
- **[THM]** Lean-proven theorem (axiom-free).
- **[DEF]** Definition / normalization convention.
- **[FIELD]** Structure field / free parameter (hand-entered input).
- **[BRIDGE]** Bridge hypothesis / calibration (carried as an explicit hypothesis, NOT derived).
- **[INPUT]** External physics input (a genuine postulate).
- **[FRONTIER]** Research frontier (unbounded / cited).

## Status table

| Claim | Kind | Lean object (file) |
|---|---|---|
| `inducedG N Λs := 1/(N·Λs²)` | **[DEF]** | `InducedNewtonConstant.lean` `inducedG` |
| `1/G = N·Λ_s²` (G is the OUTPUT) | **[THM]** | `inducedG_delivers` |
| `G/a₀² = 1/N` (the genuinely-derived dimensionless content) | **[THM]** | `inducedG_ratio_is_pure_number` |
| `ℓ_P² = G` | **[THM]** | `planckLength_sq_eq_inducedG` |
| Bekenstein exponent `A/4G = A·N·Λs²/4` | **[THM]** | `capacity_exponent_in_primitives` |
| more species ⟹ weaker gravity (`G→0` as `N→∞`) | **[THM]** | `inducedG_strictAntitone_in_N` |
| the granularity scale `Λ_s` (`a₀ = 1/Λ_s`) | **[INPUT]** (F3) | — the one unavoidable dimensionful ruler |
| `N_eff = (n_s c_s + n_f c_f + n_v c_v)/(12π)` | **[DEF]** | `effSpeciesN` |
| the `12π` normalization | **[DEF]** (derived) | `HeatKernelDDim.lean` π-content (`heat_prefactor_fourD`) |
| scalar coefficient `c_scalar = 1` | **[DEF]** (reference normalization) | `SpeciesContent` field |
| Weyl / vector coefficients `c_f, c_v` | **[FIELD]/[FRONTIER]** (F5) | `SpeciesContent` fields (spin-geometry wall) |
| the `1/4` area-law ratio (regulator+matter+π cancel) | **[THM]** | `Sakharov.sakharov_ratio`, `geometric_quarter` |
| species-summed `1/4` (any mixed content) | **[THM]** | `SpeciesCrossCheck.species_sakharov_ratio` |
| regulator power-form `F Λ = F 1·Λ^κ` forced (κ an OUTPUT) | **[THM]** (conditional on pos+cov+mono) | `Rigidity.regulator_forced_power` |
| regulator calibration pins `κ = 2` | **[THM]** | `regulator_dimension_calibration` |
| covariance hypothesis is load-bearing (vacuity guard) | **[THM]** | `dyadic_covariance_insufficient` |
| per-mode entropy IS the von Neumann entropy | **[THM]** | `GaussModeEntropyDerived.gaussModeEntropy_eq_thermal_shannon` |
| **`S ∝ A`** (`S = (A/a₀²)·gaussStateEntropy ν₀`) | **[THM]** (explicit boundary-local model) | `BoundaryGaussianAreaLaw.boundary_entropy_area_law` |
| boundary-locality (homogeneous `ν₀` over boundary sites) | **[BRIDGE]/[FRONTIER]** (F1) | model hypothesis (index type choice) |
| bulk model ⟹ VOLUME law (`= L³·…`) — locality is load-bearing | **[THM]** (guard) | `bulk_entropy_volume_law` |
| `S = A/(4G)` (Bekenstein–Hawking value) | **[THM]** conditional on `hcal` | `boundary_entropy_eq_area_over_4G` |
| the calibration `gaussStateEntropy ν₀ = N_eff/4` | **[BRIDGE]** (F2) | hypothesis `hcal` (boundary-channel↔species) |
| NO numerical `G` without `Λ_s` (scale degeneracy) | **[THM]** (firewall) | `ScopeAudit.inducedG_rescale_degeneracy` |
| every positive `G` realizable (non-identifiability) | **[THM]** (firewall) | `ScopeAudit.any_positive_G_realizable` |
| the conformal a₁ coefficient `κ = 1/6` | **[INPUT]** (F4) | carried; = the `ContDiff³ exp_p` tower |

## Final-theorem types (verbatim — expose ALL remaining inputs; no "from nothing")
- `inducedG_delivers (N Λs : ℝ) (hN : N ≠ 0) (hΛ : Λs ≠ 0) : inducedG N Λs * (N * Λs^2) = 1`
  — exposes `N`, `Λs`.
- `boundary_entropy_area_law (L : ℕ) {m} (ν₀ : Fin m → ℝ) (a₀ : ℝ) (ha₀ : a₀ ≠ 0) : boundaryEntropy (CubeBoundary L) ν₀ = (latticeArea L a₀ / a₀^2) * gaussStateEntropy ν₀`
  — exposes the model (homogeneous `ν₀`) and `a₀`.
- `boundary_entropy_eq_area_over_4G (L : ℕ) {m} (ν₀) (N_eff Λs : ℝ) (hΛ : Λs ≠ 0) (hN : N_eff ≠ 0) (hcal : gaussStateEntropy ν₀ = N_eff / 4) : boundaryEntropy (CubeBoundary L) ν₀ = latticeArea L (granularityLength Λs) / (4 * inducedG N_eff Λs)`
  — exposes the calibration `hcal`, `Λs`, `N_eff`.
- `any_positive_G_realizable (N G : ℝ) (hN : 0 < N) (hG : 0 < G) : ∃ Λ > 0, inducedG N Λ = G`
  — the firewall: no numerical `G` without `Λ`.

## Symbol hygiene (two different `κ`'s — keep distinct in prose)
- `κ = 2` — the **regulator power** (`regulator_forced_power`, `regulator_dimension_calibration`). Suggest prose name
  **`regulatorPower`**. It is the dimensional scaling `F Λ ∝ Λ²`.
- `κ = 1/6` — the **conformal / scalar a₁ heat-kernel coefficient** (carried, `heat_a1_of_RNC`). Suggest prose name
  **`scalarA1Coeff`**. It is the Seeley–DeWitt curvature coefficient. **These are unrelated; do not conflate.**

## Wording guardrails (avoid → use)
- ❌ "we derive the value of Newton's constant" → ✅ "given `N_eff` and the cutoff scale `Λ_s`, the model outputs
  `1/G = N_eff·Λ_s²`; the numerical value of `G` is not predicted without `Λ_s` (`any_positive_G_realizable`)."
- ❌ "we prove the physical vacuum obeys the black-hole area law" → ✅ "we prove `S ∝ A` for an explicit boundary-local
  Gaussian model, with a conditional `S = A/(4G)` bridge; the physical-vacuum realization is F1."
- ❌ "the `1/4` is derived" (unqualified) → ✅ "the `1/4` ratio is regulator- and matter-independent
  (`sakharov_ratio`); the absolute value `G_ind/ℓ_P` (species + cutoff datum) is not."
- "power form forced" = forced **under** the stated positivity/covariance/monotonicity/non-vacuity hypotheses (not a
  universal theorem about all regulators). "Volume-law guard" rules out volume-law contamination **in the model/hypothesis
  class**, not in arbitrary QFT vacua.

## The cited frontiers (unbounded / research-grade — NOT small missing lemmas)
- **F1** — the physical vacuum realizes the boundary-local Gaussian model (area-law model↔reality gap).
- **F2** — the `N_eff/4` calibration (`S=A/4G`): boundary-channel capacity ↔ induced species number.
- **F3** — the value/origin of `Λ_s` (the one unavoidable dimensionful scale).
- **F4** — the scalar conformal coefficient `κ=1/6` (= the `ContDiff³ exp_p` smooth-dependence tower, ~4–8 wk Mathlib gap).
- **F5** — the Weyl/vector relative species coefficients `c_i` (spin bundles / Dirac–Lichnerowicz / gauge-fixing / ghosts).
- **F6** — a finite-capacity substrate producing continuum geometry and `G` (Tier-2 QG; the central open problem).
- **F7** — the physical localization map (`hTkk` is **reduced, not derived**). The free-field GR chain discharges
  `hTkk` via a *calibrated rank-one ansatz* (`localized_mode_hTkk`/`gaussMode_calibration`): amplitude law
  `ff∝∂_v φ` + `(∂φ)²` scaling genuine, but the coefficient `2π/ℏ` is calibrated (not derived from the KG
  two-point/KMS `β=2π`) and the mode shape is free. The physical wedge-smearing one-particle mode (named by
  `IsPhysicalWedgeMode`) is the cited frontier — see `THE_HTKK_PHYSICAL_PLAN.md`, HT1–HT4.

## Bottom line
The induced-`G` package is an **exact axiom-free relation** (`1/G = N·Λ_s²`, G as output) with a genuinely-derived
dimensionless core (`G/a₀²=1/N`), a derived `1/4` ratio, a forced regulator form, a now-**proven** entropy area law
(`S∝A`) for an explicit boundary-local model, and a machine-checked scope firewall (no numerical `G` without `Λ_s`). It
is **induced gravity, not quantum gravity**, and it predicts **no numerical value of `G`**. The remaining gaps (F1–F6)
are genuine physical postulates or research-grade formalization projects — not missing lemmas.
