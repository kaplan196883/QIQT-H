# Plan — Discharge `hKMS` and complete the FREE-FIELD QIQT→GR derivation

**Created 2026-06-23.** Sequel to `QIQT_GR_DISCHARGE_PLAN.md` (done) and `QIQT_GR_DISCHARGEABLE_PLAN.md` (done: Tier A
discharged; Tiers B/C found already-derived). This plan closes the LAST genuinely-mechanical gap so the explicit
free-field QIQT→GR capstone rests on **only the physics floor** (Clausius/area law + matter EOM + Lorentzian/smooth
background) and the QIQT-H **H2** area-law crux — with the modular/Type-III input `hKMS` also discharged.

---

## Corrected current state (verified 2026-06-23)

The Type-III / modular apparatus IS formalised; the free-field wedge-KMS inputs are THEOREMS, axiom-free:

| Input | Discharged by | File |
|---|---|---|
| `hStrip` (wedge-KMS, `StripKMSrvd`) | `stripKMSrvd_boostUnitary` | `Fock/BoostKMS.lean:2651` |
| `hUniq` (RvD Thm 3.8, modular uniqueness) | `gConstancy_of_inputs` (+ `HalfStripReal` from `StripKMSrvd`, `√R`-density) | `Fock/OneParticleBW.lean:719` |
| standardness (separating + cyclic) | `oneParticleBW_niceWedge_unconditional` | `Fock/CyclicWitness.lean` |
| `hBoostCharge`/`hTkk` (boost-charge = stress-flux) | `boostEnergy_eq_neg_stressFlux` (`T_kk := −(ℏ/2π)·stressFluxKK`) | `Fock/StressTensor/HorizonParseval.lean:459` |
| modular flow = boost (Fock) | `secondQuantModFlowH_acts_as_boost` | `Fock/OneParticleBW.lean:921` |
| modular energy = stress flux | `modularEnergy_eq_stressFlux`, `oneParticle_hFlux`, `component_hFlux_of_wedgeKMS` | `Fock/OneParticleBW.lean:959,978,1020` |
| coherent-state rel. entropy `= cgpEntropy ≥ 0` (`hDnn`) | `hasDerivAt_relModFlow_vacuum`, `cgpEntropy_nonneg` | `Fock/RelativeModularFlow.lean` |
| matter conservation `conserv` (`T=kgStress`) | `kg_conserv_of_contDiff` | `QIQTH/KGStressConservation.lean` |
| `hC`/`hric_symm`/`hreg` | `christoffel_contDiff`/`ricci_symm`/`hreg_kg` | `ChristoffelSmooth`/`RicciSymm`/`HregExplicitKG` |

**Target:** `hKMS : WedgeKMSFlux_complete g (kgStress…) kd ħ` =
`∀ x v, BL(g x)v=0 → ∃ m S V ξ, (carrier=closure span wedgeGenSet) ∧ … ∧ (modular-flux conditions)`.
`component_hFlux_of_wedgeKMS` already reduces the per-generator flux to `kd=(2π/ℏ)T_kk` GIVEN the discharged inputs +
`hbridge`. So discharging `hKMS` for the free field needs exactly the items in the next section.

---

## The two genuinely-remaining gaps

### Gap 1 — the `±2π` sign convention *(small; a convention audit, not a proof)*
`oneParticle_hFlux` / `oneParticleBW_wedge` are stated with `V t = boostUnitary(−(2πt))` (MINUS), and consume
`hUniq`/`hStrip` as hypotheses.  The UNCONDITIONAL theorem `oneParticleBW_niceWedge_unconditional` proves
`modUnitary S t = boostUnitary(+(2πt))` (PLUS).  To wire the unconditional BW into `hFlux`, reconcile the sign.

### Gap 2 — the localization map `hbridge` *(the dynamical-realization modeling step)*
`WedgeKMSFlux_complete` is an EXISTENTIAL: per null horizon generator `(x,v)`, exhibit a wedge mode `ξ_{x,v}` (and
`m, S, V`) whose one-particle modular energy IS the chain's per-generator `kd`.  `hbridge` is exactly that:
`HasDerivAt (t ↦ ⟨ξ, modUnitary S t ξ⟩) (i·kd) 0`.  Choosing `ξ_{x,v}` (the QIQT realization of the local horizon by
a wedge coherent mode) is the genuine dynamical-realization input — possibly a canonical free-field construction,
possibly an honest modeling identification.

---

## Phases

### Phase 1 — `±2π` sign reconciliation *(1–3 fires; HIGH-to-MODERATE confidence)*
Decide and execute ONE of:
- **(a) Re-derive the unconditional BW in the `−2π` convention.** Restate `oneParticleBW_niceWedge_unconditional`
  with `V t = boostUnitary(−(2πt))`; check whether the separating/cyclic/KMS proofs are orientation-symmetric (the
  rapidity reflection `θ→−θ` and `p(θ+iπ)=−p(θ)` are sign-robust; the modular-flow direction picks the sign). Likely
  a clean variant.
- **(b) Prove the equivalence `boostUnitary(2πt) ↔ boostUnitary(−2πt)` route.** Audit `boostUnitary`/`modUnitary`/
  `rvdRC`/`modChar` orientations and show the two BW theorems are the same physical statement (the `+2π`/`−2π` is a
  convention of `J`/`Δ` orientation). Then a one-line bridge supplies either sign.
- **Deliverable:** `oneParticleBW_niceWedge_unconditional_neg` (or a sign-bridge lemma) giving
  `modUnitary S t = boostUnitary(−(2πt))` unconditionally — the form `oneParticle_hFlux` consumes.
- **First brick:** state the `−2π` variant and attempt the proof by mirroring the `+2π` proof with the reflection;
  if a sign obstruction appears, root-cause it to a specific `J`/`Δ` orientation lemma and audit that.

### Phase 2 — supply `hUniq`/`hStrip`/standardness to `oneParticle_hFlux` from the discharged theorems *(1–2 fires)*
`oneParticle_hFlux` takes `hUniq`, `hStrip`, `hcarrier` as hypotheses.  Build `freeField_oneParticle_hFlux` that
SUPPLIES them for the nice-wedge standard subspace `S = niceWedgeStandardSubspace`:
- `hStrip` ← `stripKMSrvd_boostUnitary` (repackaged to the `StripKMS V D` shape `oneParticle_hFlux` wants — check the
  `StripKMS` vs `StripKMSrvd` interface; `stripKMSrvd_halfStripReal` etc. bridge them).
- `hUniq` ← `gConstancy_of_inputs` + `comparisonDatum_of_gConstancy` (RvD Thm 3.8), its inputs met for the free field.
- `hcarrier` ← definitional for `niceWedgeStandardSubspace` (`niceWedgeClosedSubmodule_coe`).
- `hVboost` ← the (sign-reconciled, Phase 1) BW.
- **Deliverable:** `freeField_oneParticle_hFlux (m hm) (ξ) (Tkk) (hBoostCharge) : HasDerivAt … = i·(2π/ℏ)T_kk` — the
  one-particle hFlux with NO labelled wedge-KMS hypotheses (only `hBoostCharge`, itself discharged in Phase 3).

### Phase 3 — supply `hBoostCharge` from `boostEnergy_eq_neg_stressFlux` *(1 fire)*
`boostEnergy_eq_neg_stressFlux` gives the boost-energy = `−stressFluxKK` identity for a wedge mode.  Wire it to the
`hBoostCharge : HasDerivAt (t ↦ ⟨ξ, boostUnitary(−2πt) ξ⟩) (i·(2π/ℏ)T_kk) 0` shape with `T_kk := −(ℏ/2π)·stressFluxKK`.
- **Deliverable:** `freeField_hBoostCharge` — `hBoostCharge` discharged for the wedge mode `ξ = KrepL2 f`.

### Phase 4 — assemble `WedgeKMSFlux_complete` for the free field *(2–4 fires; depends on Gap 2)*
Per null generator `(x,v)`, choose the wedge mode `ξ_{x,v}` (the localization map — Gap 2) and assemble the existential
`∃ m S V ξ, …` from the Phase 2–3 deliverables + `component_hFlux_of_wedgeKMS`.
- **The honest fork:** if `hbridge`/`ξ_{x,v}` is a CANONICAL free-field construction (the wedge mode localized at the
  horizon generator), build it and Gap 2 closes → `hKMS` fully discharged. If it is a genuine MODELING identification
  (which horizon ↔ which QIQT mode), then `hKMS` reduces to that single labelled localization input — still a major
  narrowing (the entire modular content discharged, only the realization map labelled).
- **Deliverable:** `freeField_hKMS : WedgeKMSFlux_complete g (kgStress…) kd ħ` (unconditional, or conditional on the
  single localization map).

### Phase 5 — drop `hKMS` from the capstone *(1 fire; analogous to the `conserv`/`hreg` drops)*
Refactor `qiqt_gr_explicit_kg(_lorentzian)` to supply `hKMS` internally from `freeField_hKMS` (Phase 4).
- **Deliverable:** `qiqt_gr_freefield` — the QIQT→GR Einstein equations for the explicit free KG field with `hKMS`
  AND `conserv` AND the geometric debt all discharged; resting on `{Clausius/area law, EOM, Lorentzian frame,
  G/η, the localization map (if Gap 2 stays labelled)}`.

---

## Honest boundary — what this plan does NOT attempt (genuine physics, separate)
- **The Clausius/area-saturation law** (`hbound`/`hsat`) — the Jacobson thermodynamic postulate, the honest floor.
- **H2 — the area law from finite `Q_max`** — QIQT-H's central open scientific claim; the one thing between
  "conditional Jacobson theorem" and "QIQT predicts gravity." Deserves its own plan.
- The matter EOM (`hKG`), the Lorentzian/smooth-metric background, the coupling `η`/`G` — irreducible inputs.

After this plan: the free-field QIQT→GR rests on EXACTLY those physical/structural inputs + (possibly) the single
localization map — every modular, entropy, conservation, and geometric input machine-checked axiom-free.

---

## Verification discipline (every increment)
`~/.elan/bin/lake build QIQTH.<Module>` green; each new theorem `#print axioms = [propext, Classical.choice,
Quot.sound]`; `bash scripts/axiom_budget_check.sh` stays `raw axiom count: 0 (budget 0)`; one commit per brick on
`main` with the `Co-Authored-By: Claude Opus 4.8` trailer; `AxiomAudit.lean` entry per new theorem; after each phase
re-verify the end-to-end `lake build QIQTH`.

## Honest scale
- **Phase 1 (sign):** 1–3 fires. The unblocker; risk is a genuine `J`/`Δ` orientation subtlety (then it's an audit).
- **Phases 2–3 (wire discharged inputs):** 2–3 fires. Mechanical composition of existing axiom-free theorems; the
  only friction is interface shapes (`StripKMS` vs `StripKMSrvd`, the `ξ=KrepL2 f` packaging).
- **Phase 4 (assemble `hKMS`):** 2–4 fires; HINGES on Gap 2 (localization map). If canonical → full discharge; if
  modeling → narrows `hKMS` to one labelled map.
- **Phase 5 (drop from capstone):** 1 fire.
- **Total to a free-field-complete `qiqt_gr_freefield`:** ~1–2 weeks of focused increments, modulo Gap 2's nature.
