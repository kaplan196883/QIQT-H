# GR scaffolding formalisation — discharge the class-② analytic witnesses (hS / hK / hA) + broaden explicit models

**Status:** PLAN (not started). **Track:** GR. **Goal:** turn the *scaffolding* hypotheses of the GR
capstones — the ones the curation tooling tags `SETUP — derivative existence / null-congruence kinematics`
and the Gaussian-only `REGULARITY` mode block — from **assumed** into **derived**, for the finite-record /
explicit-mode models. These are NOT the physics floor (P4 `hcap`/`hbound`/`hsat`, EOM `hKG`); they are
analytic facts that should follow from smoothness + the finite record law. Discharging them shrinks the
labelled surface of every GR capstone to exactly the irreducible floor.

## 0. Why these (the machine state)

`reports/gr/agent_summary.json`: every GR theorem has `dischargeable: []` (nothing auto-dischargeable at the
current abstraction) and `project_axioms: []` (budget 0). The capstone surface splits three ways:
- **REGULARITY/BACKGROUND** (metric/frame/normalization) — discharged for `ppwave`/`gaussian`.
- **PHYSICS floor** — `hKG` (EOM), `hcap`/`hbound`/`hsat` (= P4), `hTkk` (localization). IRREDUCIBLE
  (proven this conversation: P4 cannot be derived from P1–P3+P5, even via the Type-II crossed product).
- **SETUP — derivative/congruence kinematics**: `hS`, `hK`, `hA` (HasDerivAt for entropy / KE / area),
  `hWx`/`hWC`/`hWgeo`/`hWequil` (congruence). ← **THIS PLAN.** Pure analysis, not physics.

`ClausiusFiniteWitness.clausius_package_from_finite_model` already derives `hbound/hsat/hDnn/hD0` from a
finite record law `p : ℝ → R → ℝ` with `hp_nn/hp1/hp0/hcap`. It does **not** yet output the HasDerivAt
facts `hS` (Shannon derivative) and `hK` (Shannon+KL derivative) — those are still assumed in
`qiqt_gr_freefield_thermo`/`_complete`. Closing that is the cleanest, highest-leverage target.

## 1. Workstream A — entropy / relative-entropy derivative witnesses (PRIMARY)

Pure Mathlib real analysis; removes `hS` and `hK` from **every** GR capstone via the finite-record witness.

### Stage A0 — recon (no commit)
Confirm exact statements: `BranchLedger.Shannon s p = -∑ r∈s, p r * log (p r)`; `RelEntPositivity.KL s p q
= ∑ r∈s, p r * log (p r / q r)`; the precise `hS`/`hK` types in `QiqtGrThermo.lean`/`QiqtGrGaussian.lean`
(`HasDerivAt (fun t => Shannon univ (p t)) (sd x v) 0`, resp. Shannon+KL with rate
`2π/ℏ · BL(kgStress)`). Identify what smoothness of `p : ℝ → R → ℝ` the witness model can supply
(per-component `HasDerivAt (p · r) (p' r) 0` + `p 0 r > 0`). **Risk: none.**

### Stage A1 — `shannon_hasDerivAt`  *(new file `QIQTH/Entropy/EntropyDeriv.lean`)*
Prove: given finite `s`, `p : ℝ → ι → ℝ`, `p' : ι → ℝ`, with `∀ r∈s, HasDerivAt (fun t => p t r) (p' r) 0`
and `∀ r∈s, 0 < p 0 r`,
```
HasDerivAt (fun t => Shannon s (p t)) (-∑ r∈s, (Real.log (p 0 r) + 1) * p' r) 0.
```
Route: `Shannon s (p t) = -∑ r∈s, (p t r) * log (p t r)`; each summand `t ↦ p t r * log (p t r)` has
`HasDerivAt … ((log (p 0 r) + 1) * p' r) 0` via `HasDerivAt.mul` + `Real.hasDerivAt_log (p0 r ≠ 0)` +
`HasDerivAt.comp`/`.log`; sum with `HasDerivAt.sum`; negate. **Risk: low–medium** (the `x log x` derivative
at a positive point; standard Mathlib `Real.hasDerivAt_log`).

### Stage A2 — `KL_hasDerivAt` at the equilibrium reference  *(same file)*
Prove: with the same hypotheses and the reference fixed at `q = p 0`,
```
HasDerivAt (fun t => KL s (p t) (p 0)) 0 0     -- derivative is 0 at t=0 when ∑ p' = 0
```
Reason: `KL s (p t)(p0) = ∑ p t r·(log(p t r) − log(p0 r))`; differentiate termwise → at `t=0` the
`log(pt/p0)` factor is `log 1 = 0` and the surviving `∑ p0 r·(p' r/p0 r) = ∑ p' r`, which is `0` because
`∑ p t r = 1` is constant in `t` ⟹ `∑ p' r = 0` (prove `hsum' : ∑ r∈s, p' r = 0` from differentiating
`hp1`). So `d/dt KL|₀ = 0`. **Corollary `KE_hasDerivAt`:** `HasDerivAt (fun t => Shannon (p t) + KL (p t)(p0))
(shannon-rate) 0` — i.e. **hK's rate equals hS's rate** (KL contributes nothing at equilibrium). This is the
content that makes `hK` derivable from `hS`. **Risk: medium** (the `∑ p' = 0` differentiation-of-constraint
step + termwise KL derivative).

### Stage A3 — extend the finite-record witness  *(extend `ClausiusFiniteWitness.lean`)*
New theorem `clausius_deriv_package_from_finite_model`: given the finite record law + per-component
`HasDerivAt`, output `hS` and `hK` (the two HasDerivAt facts the GR capstones consume), with the rate
identified as the Shannon rate from A1 and the KL-correction `= 0` from A2. Now the finite-model witness
discharges `hS, hK, hbound, hsat, hDnn, hD0` — **everything on the matter/entropy side except `hcap` (FQ,
irreducible)**. Wire a demonstration: a `qiqt_gr_freefield_thermo`-style corollary where `hS`/`hK` are
supplied by the witness rather than assumed. **Risk: medium** (plumbing the rate to match the capstone's
`sd`/`2π/ℏ·BL(kgStress)` exactly).

## 2. Workstream B — area derivative witness `hA` for the explicit congruence (SECONDARY)

`hA : HasDerivAt (A x v) (ad x v) 0` with `ad = −∑ W·pd(expansion)` is the Raychaudhuri area-rate.
For the flat / pp-wave congruence (`W` covariantly constant, `RaychaudhuriCongruence`/`PPWaveMetric` infra),
expansion and its `pd` are explicit, so `hA` is derivable. Stage B1: prove `hA` for
`covDerivVec_constMetric_const` (flat witness) from smoothness of `W` + metric; Stage B2: lift to the
pp-wave (`ppMetric_raychaudhuri_setup`). Discharges `hA` for the explicit models, mirroring how `hWgeo`/
`hWequil` were collapsed to `hcov`. **Risk: medium** (HasDerivAt of `expansion` = `divergence` of `W`).

## 3. Workstream C — a second explicit localization mode (broaden `hTkk`, TERTIARY)

Currently `hTkk` (and the `hf2/hf_int/hfd/hf'_meas/hB` regularity block) is discharged only by `GaussianMode`.
Add a second concrete mode — a normalized Hermite×Gaussian `gaussMode₁` (one node), or factor a
`SchwartzMode` class — proving the regularity block + the calibration `(−2π∫conj·')·im = 2π/ℏ`, to show the
localization discharge is not Gaussian-specific. **Risk: medium–high** (a second hard complex oscillatory
integral; the Gaussian one was the session's hardest). Do ONLY after A+B land.

## 4. Honest scope (stated up front)
This formalises **scaffolding, not floor.** It does NOT touch P4 (`hcap`/`hbound`/`hsat` stay assumed —
proven irreducible) or the EOM (`hKG`). The deliverable is: the GR capstone's *analytic* surface (entropy/
area derivatives, mode regularity) becomes **derived** for the finite-record + explicit-mode models, so the
remaining labelled hypotheses are exactly the irreducible physics floor + EOM. No circularity: A/B/C derive
HasDerivAt/regularity facts from smoothness, never from the Clausius law or the field equations they feed.

## 5. Verification (per stage)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3;
`bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit.lean`; one commit per
stage with the `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>` trailer; push via schannel.
After each landing, run `python scripts/lean-track-refresh.py --skip-unchanged` and commit `reports/` if it
prints CHANGES.

## Progress log
- **Stage A0 ✅** — recon: `Shannon s p = -∑ p·log p`, `KL s p q = ∑ p·log(p/q)`; the witness model supplies
  per-component `HasDerivAt (p·r) (p' r) 0` + `p 0 r > 0` + `∑ p t r = 1`. Confirmed `hS`/`hK` are the only
  entropy-side HasDerivAt facts the capstones assume (`ClausiusFiniteWitness` already gives bound/sat/Dnn/D0).
- **Stage A1 ✅** (`shannon_hasDerivAt`, `QIQTH/EntropyDeriv.lean`) — `d/dt Shannon(p t)|₀ = -∑ (log(p₀ r)+1)·p'(r)`
  from per-component `HasDerivAt` + positivity (chain rule via `HasDerivAt.log`/`.mul`/`.sum`). Axiom-free (std 3).
- **Stage A2 ✅** (`sum_deriv_zero`, `KL_hasDerivAt_self`, `KE_hasDerivAt`) — `∑ p'(r)=0` from `∑ p t r=1`
  (differentiate the constant); hence `d/dt KL(p t‖p 0)|₀ = 0` (KL flat at equilibrium), and the heat-functional
  derivative `Sf+KL` **equals** the Shannon derivative — so the capstone's `hK` is derivable from `hS` (the
  `sd = 2π/ℏ·BL(kgStress)` identification is "KL contributes nothing at equilibrium"). Axiom-free (std 3).
  Wired into `QIQTH.lean` + `AxiomAudit.lean`; `lake build QIQTH.AxiomAudit` green; budget 0.
- **Stage A3 ✅** (`clausius_deriv_package_from_finite_model`, extends `ClausiusFiniteWitness.lean`) — given the
  finite record law + per-component `HasDerivAt` + reference positivity + `∑ p t r = 1`, **both** capstone
  derivative premises `hS` and `hK` are theorems, holding with the **same** rate (`-∑ (log p₀+1)·p'`). So the
  capstone's two HasDerivAt hypotheses are not independent: `hK` follows from `hS` + KL-flatness. What stays
  labelled is only the rate's *value* as a stress flux `2π/ℏ·T_kk` (= the localization/calibration `hTkk`) and
  the FQ capacity `hcap` — the irreducible floor; this lemma touches neither. Axiom-free (std 3); wired into
  AxiomAudit; budget 0.
- **Workstream A COMPLETE.** The entropy-side scaffolding (`hS`, `hK`) is now derived from smoothness for the
  finite-record model. Honest boundary: feeding these into the *concrete* `qiqt_gr_freefield_thermo` requires
  identifying its rates `sd`/`2π·ℏ⁻¹·BL(kgStress)` with the witness rate — that identification is `hTkk`
  (physics/localization), already its own labelled input, not an entropy fact. Full concrete instantiation
  overlaps Workstream C (a model where `pp`/`Sf`/`sd` are explicit).
- **Workstream B ✅** (`expansion_eq_zero_of_covConst`, `pd_expansion_zero_of_covConst`,
  `area_hasDerivAt_of_covConst`; extends `RaychaudhuriCongruence.lean`) — a covariantly-constant congruence
  has identically-zero expansion `θ = ∑_μ ∇_μ V^μ`, so its coordinate derivative vanishes and the Raychaudhuri
  area-rate `-∑_ν V^ν ∂_ν θ = 0`; a constant cross-sectional area then satisfies the capstone's `hA`
  (`HasDerivAt (area) (rate) 0`). This is the `θ=0` case (area preserved along a shear-free, expansion-free
  congruence), discharging `hA` for the flat / pp-wave (∂_v) congruence — the same setting that reduces
  `hWgeo`/`hWequil` via `covCong`. Axiom-free (std 3); wired into AxiomAudit; budget 0. The expanding (θ≠0)
  curved case needs the geodesic-ODE / area-element machinery Mathlib lacks (cited frontier, file header).
- **NEXT: Workstream C** — a second explicit localization mode beyond Gaussian (broaden `hTkk` + the
  `hf2/hf_int/hfd/hf'_meas/hB` regularity block). Hardest; do last.
