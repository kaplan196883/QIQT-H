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
- **F7** — the physical localization map (`hTkk`), REFINED status (2026-07-08 audit + HT campaign, bricks 1–3 landed).
  Precise attribution: (a) the `(∂φ)²` null-energy scaling is **derived** (`BL_kgStress_null`); (b) the classical
  boost-charge↔horizon-`T_kk` decomposition `K₀=H_+ + N_+` (flux `N_+` explicit) is **derived** for massive 1+1
  (`kg_boost_charge_decomposition_1p1`, HT1a/b); (c) the **`2π` coefficient IS derived** — it is the machine-checked
  Bisognano–Wichmann/Unruh KMS temperature (`boostUnitary(2π·t)` + `stripKMSrvd_boostUnitary`), and it cancels in `hTkk`;
  (d) the coefficient's **canonical-NORMALIZATION physics is now derived axiom-free** — the KG symplectic form
  (`kgSympl`, HT3 brick-1), the Fourier-side identity `σ = 2ℏ·Im⟨a,a⟩` (`two_hbar_im_inner_posFreq_eq_sigmaK`, brick-2), and
  the **Parseval bridge** `sigmaK∘𝓕 = kgSympl` for real Schwartz data (`parseval_bridge_real`, brick-3, via Plancherel
  `SchwartzMap.integral_inner_fourier_fourier` — honest ∫, no `Lp` classes, no `2π` in Mathlib's unitary convention); so the
  one-particle normalization `2ℏ·Im⟨a,a⟩` equals the classical position-space symplectic form, **coefficient fixed, no free
  constant**; (e) the `1/ℏ` is a **unit convention** (ℏ a free scale, like the value of G). **The single genuinely-open piece
  is now precisely the `Lp` PACKAGING** of the positive-frequency map `j_ℏ` into the existing rapidity convention
  (`niceWedgeGenSet`, `L²(dθ)`): the weighted KG Sobolev phase space with `√ω` unbounded on `L²`, the Fourier `L²→L²` unitary
  matching, and boost covariance — a **named multi-month Mathlib-infrastructure frontier, NOT new physics**. So `hTkk` is NOT
  flatly "reduced not derived": its structure + `2π` + coefficient-normalization are all DERIVED; only the `Lp`/rapidity
  packaging of `j_ℏ` remains a cited frontier — see `THE_HTKK_PHYSICAL_PLAN.md`, HT3 brick-4 / HT4.
  **`Lp` progress (2026-07-09, user-authorized investment — bricks buildable now, wall precisely located):** brick-1 the
  Lorentz-invariant mass-shell measure = rapidity pushforward (`map_rapidityHalfMeasure_eq_massShellMeasure`); brick-2 the
  rapidity change of variables on the one-particle integral (`integral_massShellMeasure_eq_half_rapidity` +
  `rapidity_measurePreserving`); brick-3 the one-particle `L²` ISOMETRY into the flat rapidity `L²` (`rapidityPullL2_isometry`)
  — all axiom-free.  **The FIRST genuine WALL is now precisely located** (GPT-5.5 2026-07-09): the real-Cauchy-data →
  positive-frequency map `(φ,π)↦√ω·φ̂ + i·ω^{-1/2}·π̂` is UNBOUNDED on naive `L²×L²`; its correct domain is `H^{1/2}⊕H^{-1/2}`,
  and formalizing that weighted-Sobolev / unbounded-Fourier-multiplier infrastructure is the multi-month gap.
  **Wall PARTIALLY breached (2026-07-09, user-authorized Sobolev investment — brick-4 `WeightedL2.lean`):** the "√ω is
  unbounded" objection is now DISSOLVED axiom-free — multiplication by a weight `w ≥ 0` is a norm-preserving isometry
  `L²(vol.withDensity w²) → L²(vol)` (`eLpNorm_smul_weight_eq_withDensity`), so `√ω` is bounded once the domain is the
  correctly-weighted KG-Sobolev space. What REMAINS toward `j_ℏ`: assembling the positive-frequency map on the weighted
  domain, the Fourier `L²→L²` step (`fourierTransformCLE`, present), the real-Cauchy-data domain, and boost covariance —
  substantial assembly/bookkeeping, but no longer a hard "unbounded" obstruction. The `Lp` wall must still not be faked.
  **Domain identified (2026-07-09, brick-5 `PosFreqDomain.lean`):** the positive-frequency map is now proved WELL-DEFINED
  `H^{1/2}⊕H^{-1/2} → L²` axiom-free (`kg_posFreq_memLp`) — `a=(ω Ψ+iπ)/√(2ℏω)` lands in flat `L²` exactly when `(Ψ,π)` lie
  in the ω- and ω^{-1}-weighted `L²`, via the weight isometry. The operator's correct DOMAIN (the piece the naive-`L²`
  objection missed) is pinned. Remaining toward the full `j_ℏ`: the Fourier `L²→L²` isometry (Mathlib `Lp.fourierTransformₗᵢ`,
  present), transporting `2ℏ·Im=σ` onto the `L²` inner product, the completed one-particle map, and boost covariance —
  assembly of existing pieces + covariance, no known hard obstruction. Still must not be faked.
  **Coefficient physics COMPLETE at the Hilbert level (2026-07-09, bricks 5–7 + capstone).** `kg_posFreq_memLp` (domain),
  `two_hbar_im_L2_inner_eq_sigmaK` (normalization at Hilbert level), and the capstone
  `two_hbar_im_L2_inner_posFreq_eq_sigmaK` (`σ_K = 2ℏ·Im⟪a_L2,b_L2⟫` for the KG positive-freq coefficients) are all
  axiom-free. **TRACK-A CHECKPOINT (GPT-5.5-triaged):** the remaining pieces toward a fully-packaged covariant
  `j_ℏ : H^{1/2}⊕H^{-1/2} → Fock` are a NEW serious phase, not continuation bricks — the bundled `jHbar` def is cosmetic;
  coefficient-level rapidity-translation is a thin wrapper; the MEANINGFUL boost covariance needs the geometric-boost ↔
  rapidity-translation bridge; and the position-field → on-shell-coefficient Fourier tie has a genuine measure-zero /
  distributional obstruction (the mass shell is Lebesgue-null). So `hTkk`'s coefficient normalization is a machine-checked
  Hilbert-space fact; the full covariant one-particle map is the named next phase (spatial Fourier/Sobolev reconstruction +
  geometric Lorentz covariance), NOT to be faked or wrapper-ground.

## Bottom line
The induced-`G` package is an **exact axiom-free relation** (`1/G = N·Λ_s²`, G as output) with a genuinely-derived
dimensionless core (`G/a₀²=1/N`), a derived `1/4` ratio, a forced regulator form, a now-**proven** entropy area law
(`S∝A`) for an explicit boundary-local model, and a machine-checked scope firewall (no numerical `G` without `Λ_s`). It
is **induced gravity, not quantum gravity**, and it predicts **no numerical value of `G`**. The remaining gaps (F1–F6)
are genuine physical postulates or research-grade formalization projects — not missing lemmas.
