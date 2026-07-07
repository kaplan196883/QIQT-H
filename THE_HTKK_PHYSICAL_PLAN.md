# THE hTkk PHYSICAL-LOCALIZATION PLAN — turn `hTkk` from a calibrated ansatz into a physical theorem

**Status:** SCOPED (dual consult: GPT-5.5-pro high + Fable Lean-audit, 2026-07-08). **Track:** QG / free-field induced gravity.
**Commits LOCAL ONLY (no push).**

## Binding verdict (both consults, independent, converging)
The existing `hTkk` discharge (`LocalizedMode.localized_mode_hTkk` + `GaussianMode.gaussMode_calibration` ⟹
`qiqt_gr_freefield_gaussian`/`_complete`, all [AF] std-3, no sorry) is a **calibration-hiding rank-one ANSATZ, not a
physical derivation** of the localization map. It sets `ff x v θ := (∑ᵦ vᵦ ∂ᵦφ(x))·g₀(θ)` (amplitude × universal profile)
and *chooses* `g₀`'s normalization so the boost charge equals `2π/ℏ·T_kk`.
- **GENUINELY DERIVED (keep):** (i) amplitude law `ff ∝ ∂_v φ`; (ii) quadratic `(∂φ)²` null-energy scaling; (iii) the
  per-generator family collapses to ONE universal scalar; (iv) the BW/Hilbert-space fact that the modular-energy rate of
  `D·g₀` is `i·D²·(2π/ℏ)` via genuine (axiom-free) modular flow.
- **NOT ESTABLISHED (the real physics):** that `ff = D·g₀` is the field's ACTUAL one-particle wedge mode, and that the
  coefficient `2π/ℏ` comes from the KMS temperature (β=2π) / KG symplectic norm of the genuine wedge excitation rather than
  a tuned normalization. Fable: the mode SHAPE/WIDTH is free (`GaussianModeFamily` — every width calibrates); only the
  **unit phase `−iθ`** carries `2π/ℏ`, and it is INSERTED. The `nullEnergy` docstring already concedes the wedge-smearing
  construction is "the cited frontier."
- The paper's "localization map is provably not dischargeable by analysis" is therefore **correct against the Gaussian
  discharge** — no contradiction. Honest status: `hTkk` is **REDUCED, not DERIVED**.

## The genuine target (GPT-5.5-pro, known flat-space free-field AQFT — Rindler modular Hamiltonian)
Derive `ff` from the field and fix `2π/ℏ` from Bisognano–Wichmann + the stress-tensor Noether charge, NOT a fitted `g₀`:
1. KG field → one-particle Hilbert space; positive-frequency projection of a smearing of `∂_v φ` near the generator `(x,v)`.
2. BW: wedge modular generator = Lorentz boost (ALREADY unconditional: `freeField_secondQuant_BW_unconditional`, `m>0`).
3. Noether: `K_W = (2π/ℏ)∫_{x¹>0,t=0} x¹ T₀₀ d³x  =  (2π/ℏ)∫_{H⁺} λ·T_kk dλ d²y` (boost charge = horizon `T_kk` integral).
4. Match to the one-particle rapidity boost charge `Q[f_phys] = (−2π∫ conj(f)·f').im` for `f_phys` = the transform of the
   ACTUAL horizon data (shape determined, not guessed).
5. **Local limit** (GPT-5.5-pro honesty correction): the POINTWISE `hTkk` is "too sharp" — QFT gives distributions. Prove a
   SMEARED version first, then a regulated approximate-identity local limit `χ_ε → δ_{(x,v)}` ⟹ pointwise `hTkk` as a
   corollary. Coefficient `2π/ℏ` fixed by BW + stress-tensor normalization.
Territory: Rindler modular Hamiltonian; Casini–Huerta half-space modular H; Ceyhan–Faulkner (QNEC/ANEC). Known physics,
hard formalization — the corpus's own docstring flags the mode-expansion as "beyond current Mathlib reach."

## Honest difficulty (binding — do NOT over-promise)
This is a research-grade, possibly multi-week formalization; the one-particle wedge mode-expansion + KG two-point
infrastructure is largely absent from Mathlib and only partially in QIQTH (Fock/StandardSubspace machinery exists). Expect
to CHECKPOINT at the mode-expansion wall. The near-term, genuinely-landable value is Stages 0–2 (honesty + the CLASSICAL
boost-charge identity + the KMS coefficient), which are real and tighten the story even if Stage 3 (the physical mode)
stalls. NEVER claim the physical localization map is discharged until `f_phys` is built from φ with the coefficient derived.

## The plan (sequenced, axiom-free, ship-green; new file `QIQTH/HTkkPhysical.lean` unless noted)

- [ ] **HT0 — HONESTY RELABEL + INTERFACE (tractable NOW; soundness fix).** In `LocalizedMode.lean`/`GaussianMode.lean`:
  rename/alias the Gaussian result to **`calibrated_rank_one_hTkk`** with a docstring stating it is a calibrated rank-one
  ANSATZ realizing the `(∂φ)²` scaling + single-scalar calibration, NOT the physical KG localization map. Introduce a named
  predicate **`IsPhysicalWedgeMode m φ x v ff : Prop`** (the mode is the positive-frequency wedge smearing of `∂_v φ`, to be
  defined) so the frontier is an EXPLICIT Prop, not a hidden ansatz. Update `LEAN_RESULTS_INVENTORY.md` + the `nullEnergy`
  scope note: `hTkk` is REDUCED (scaling+scalar), the physical map is the cited frontier. [AF] std-3. Small, high-value.
- [ ] **HT1 — the CLASSICAL boost-charge = horizon-`T_kk` identity (real physics, classical, no quantization).**
  `boost_charge_eq_horizon_nullEnergy`: for the classical KG stress tensor, `∫_{x¹>0,t=0} x¹ T₀₀[φ] = ∫_{H⁺} λ T_kk[φ]`
  (change to null coordinates `u=t−x¹, v=t+x¹` + integration by parts; `T_kk=(∂_v φ)²` already proven via `BL_kgStress_null`).
  This is the Noether-charge content of step 3 at the classical level — genuinely derivable, fixes the boost-charge ↔
  null-energy STRUCTURE (not yet the one-particle coefficient). Mathlib: `MeasureTheory` integration, change of variables,
  `intervalIntegral` IBP. CONSULT GPT-5.5-pro on the exact null-coordinate change + boundary terms before attempting.
- [ ] **HT2 — the KMS coefficient `β=2π` (fix `2π/ℏ` from the temperature, not a phase choice).** Show the one-particle
  rapidity boost charge's coefficient is the KMS/Unruh `2π` — i.e. the unit-phase value in the Gaussian is FORCED by the
  wedge KMS temperature `β=2π`, tying it to `stripKMSrvd_boostUnitary`/`freeField_oneParticle_hFlux` rather than a free
  normalization. This converts Fable's "the unit phase carries 2π/ℏ, inserted" into "2π is the KMS temperature, derived."
  CONSULT GPT-5.5-pro on whether this is reachable from the existing strip-KMS machinery.
- [ ] **HT3 — build `f_phys` from φ (the wedge one-particle mode; the HARD brick, likely Mathlib-blocked).** Define the
  positive-frequency wedge smearing of `∂_v φ` at `(x,v)` from the KG field / two-point function, and prove
  `IsPhysicalWedgeMode m φ x v f_phys`. This is the continuum mode-expansion content the corpus calls "beyond current Mathlib
  reach." Reuse QIQTH `Fock/`, `StandardSubspace*`, `oneParticleBW` machinery. CONSULT GPT-5.5-pro + survey what one-particle
  infrastructure exists before attempting; CHECKPOINT honestly with the exact gap if blocked.
- [ ] **HT4 — SMEARED physical hTkk + local limit (the capstone).** `physical_hTkk_smeared`:
  `Q[f_phys(χ_ε)] = (2π/ℏ)∫ χ_ε·T_kk`; then `physical_hTkk` by the approximate-identity limit `χ_ε → δ_{(x,v)}` ⟹ the
  pointwise `hTkk` for `f_phys`, coefficient DERIVED. Feed it into a `qiqt_gr_freefield_physical` capstone replacing the
  calibrated ansatz. [AF] std-3.

## Verbatim HAVE / HAVE-NOT (target after HT4)
- **HAVE (target):** "The free-field induced-gravity chain's localization map `hTkk` is a THEOREM: the one-particle wedge
  mode is CONSTRUCTED from φ (positive-frequency wedge smearing), and its boost charge equals `(2π/ℏ)·T_kk` with the
  coefficient DERIVED from Bisognano–Wichmann + the KG stress-tensor Noether charge (KMS β=2π) — no fitted profile, no free
  calibration. Einstein's equations for the free KG field follow with the localization map derived, not assumed."
- **HAVE-NOT (binding):** "Still free-field, flat/pp-wave, linearized-matter; does NOT discharge the Clausius/area law, the
  FQ capacity bound (`hbound`, P4), the reference-state identification (`hcap`), or the numerical value of `G` (η carried);
  NOT interacting matter, NOT the continuum Type III₁ limit, NOT emergent spacetime, NOT QG."

## Discipline (every increment)
`cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<mod>` GREEN; every new theorem `#print axioms` std-3; `bash
scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire into `QIQTH.lean`; ONE commit per HT-step LOCAL ONLY (no push)
with the `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>` trailer; update this plan +
`LEAN_RESULTS_INVENTORY.md`; check sibling jobs FIRST (git log/status, ps for lake — a website-SEO sibling job commits on top,
DO NOT touch `website/`); explicit git paths only (never `-A`). NO `sorry`; carried inputs as HYPOTHESES/struct fields NEVER
axioms; NO vacuous/calibration-hiding discharge (that is the very defect being fixed); CONSULT GPT-5.5-pro before HT1/HT2/HT3;
NEVER claim the physical localization map discharged until `f_phys` is built from φ and the coefficient derived — honest
HAVE/HAVE-NOT; checkpoint with the EXACT Lean error / the precise Mathlib gap if a step stalls after a real attempt.

## Progress log
- **2026-07-08 (scoped):** dual consult. GPT-5.5-pro: the Gaussian discharge is a calibration-hiding relabel; genuine target
  = physical wedge mode from KG two-point + stress-tensor boost charge (Rindler modular H), smeared-then-local-limit. Fable
  Lean-audit: verdict "reduced, not derived" — mode shape/width free (`GaussianModeFamily`), only the unit phase carries the
  inserted `2π/ℏ`; `qiqt_gr_freefield_complete` residuals catalogued (hKG, hcap, hbound, hpp0, hK=Clausius, Raychaudhuri,
  a=2π/ℏη=G). Both converge: re-open `hTkk` as the physical-localization theorem; keep the Gaussian as a labelled lemma.
