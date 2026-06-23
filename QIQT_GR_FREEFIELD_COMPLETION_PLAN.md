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

### Gap 1 — the `±2π` sign convention *(✅ RESOLVED 2026-06-23 — `Fock/FreeFieldHFlux.lean`)*
`oneParticle_hFlux` / `oneParticleBW_wedge` are stated with `V t = boostUnitary(−(2πt))` (MINUS), and consume
`hUniq`/`hStrip` as hypotheses.  The UNCONDITIONAL theorem `oneParticleBW_niceWedge_unconditional` proves
`modUnitary S t = boostUnitary(+(2πt))` (PLUS).
**Resolution:** rather than reconcile to the unsatisfiable `−2π`, I rebuilt the modular-energy step in the
satisfiable `+2π` convention. `hasDerivAt_modularEnergy_of_boost_pos` is the sign-flipped copy of
`hasDerivAt_modularEnergy_of_boost`; `freeField_modularEnergy_eq_boostCharge` then gives, for the nice-wedge `S` and
ANY mode `ξ`, `HasDerivAt (t ↦ ⟨ξ, modUnitary S t ξ⟩) c 0` from the `+2π` boost-charge derivative — with the BW
identification supplied INTERNALLY by `oneParticleBW_niceWedge_unconditional` (axiom-free, no labelled
`hUniq`/`hStrip`, no sign mismatch, no density lemma needed). Both new theorems `#print axioms` = standard three,
budget 0. **The only remaining input on this path is the `+2π` boost-charge derivative (Phase 3 below).**

### Gap 2 — the localization map `hbridge` *(the dynamical-realization modeling step)*
`WedgeKMSFlux_complete` is an EXISTENTIAL: per null horizon generator `(x,v)`, exhibit a wedge mode `ξ_{x,v}` (and
`m, S, V`) whose one-particle modular energy IS the chain's per-generator `kd`.  `hbridge` is exactly that:
`HasDerivAt (t ↦ ⟨ξ, modUnitary S t ξ⟩) (i·kd) 0`.  Choosing `ξ_{x,v}` (the QIQT realization of the local horizon by
a wedge coherent mode) is the genuine dynamical-realization input — possibly a canonical free-field construction,
possibly an honest modeling identification.

---

## Phases

### Phase 1 — `±2π` sign reconciliation *(1–3 fires; HIGH-to-MODERATE confidence)*

**★ ROOT-CAUSE DIAGNOSIS (2026-06-23, fire 1).** Two things differ between the unconditional BW and the `hFlux`
machinery:
1. **Generator set:** `niceWedgeGenSet m ⊆ wedgeGenSet m` (`BoostKMS.lean:2202`) — my `oneParticleBW_niceWedge_unconditional`
   is over the *nice* (smooth, compact-support) generators; `oneParticleBW_wedge(_complete)` is over the full
   `wedgeGenSet`. Whether they give the SAME standard subspace `S` hinges on **`closure(span niceWedgeGenSet) =
   closure(span wedgeGenSet)`** (density of nice in full). `niceWedgeCyclic_pos_mass` proves the nice generators are
   cyclic — strong evidence the closures coincide; CONFIRM this (a `niceWedge_dense_in_wedge` lemma) as brick 1.
2. **Sign:** my theorem proves the **satisfiable** `modUnitary S t = boostUnitary(+2πt)`; `oneParticleBW_wedge_complete`'s
   `−2πt` is the *labelled "expected convention"* — by the at-most-one-sign fact it cannot also hold for the true
   `modUnitary` (unless vacuous). So the `hFlux` machinery (`modularEnergy_eq_stressFlux`, `oneParticle_hFlux`,
   `boostEnergy_eq_neg_stressFlux`) is written in the `−2π` convention that the REAL modular flow does NOT satisfy.

**Resolution path (the honest fix):** build the `+2π` variants of the `hFlux` chain and re-derive the GR-chain sign
consistently — the boost direction `boostUnitary(±2πt)` only flips the sign of the energy derivative, hence of the
*defined* `T_kk := ∓(ℏ/2π)·stressFluxKK`; the physical `kd = (2π/ℏ)T_kk` is convention-covariant as long as `hbw`,
`hBoostCharge`, and the `T_kk` sign all use the SAME orientation. So:
- **Brick 1:** `niceWedge_dense_in_wedge` (or: the nice-wedge standard subspace = the wedge standard subspace), so the
  unconditional `+2π` BW applies to the SAME `S` the `hFlux` chain uses.
- **Brick 2:** `modularEnergy_eq_stressFlux_pos` / `oneParticle_hFlux_pos` / `boostEnergy_eq_neg_stressFlux` with the
  `+2π` orientation and `T_kk := +(ℏ/2π)·stressFluxKK` (sign chosen so `kd = (2π/ℏ)T_kk` matches the GR chain).
- This REPLACES the original sub-options below (which assumed a re-derivation in `−2π` — wrong direction, since `−2π`
  is the unsatisfiable convention). Original sub-options retained for reference:

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

### Phase 2 — supply `hUniq`/`hStrip`/standardness ✅ DONE 2026-06-23 (`Fock/FreeFieldHFlux.lean`)
**Folded into the BW, not into `oneParticle_hFlux`.** Rather than feed `hUniq`/`hStrip`/`hcarrier` as the labelled
inputs of the `−2π` `oneParticle_hFlux`, the `+2π` `freeField_modularEnergy_eq_boostCharge` supplies the BW
identification `modUnitary S = boostUnitary(+2π·)` INTERNALLY from `oneParticleBW_niceWedge_unconditional` — which
already discharges separating + cyclic + RvD-uniqueness for the nice-wedge `S`. So `hUniq`/`hStrip`/standardness
never appear as hypotheses. Axiom-free, budget 0. (Original per-hypothesis route, now moot, retained below.)

Original plan: `oneParticle_hFlux` takes `hUniq`, `hStrip`, `hcarrier` as hypotheses.  Build `freeField_oneParticle_hFlux` that
SUPPLIES them for the nice-wedge standard subspace `S = niceWedgeStandardSubspace`:
- `hStrip` ← `stripKMSrvd_boostUnitary` (repackaged to the `StripKMS V D` shape `oneParticle_hFlux` wants — check the
  `StripKMS` vs `StripKMSrvd` interface; `stripKMSrvd_halfStripReal` etc. bridge them).
- `hUniq` ← `gConstancy_of_inputs` + `comparisonDatum_of_gConstancy` (RvD Thm 3.8), its inputs met for the free field.
- `hcarrier` ← definitional for `niceWedgeStandardSubspace` (`niceWedgeClosedSubmodule_coe`).
- `hVboost` ← the (sign-reconciled, Phase 1) BW.
- **Deliverable:** `freeField_oneParticle_hFlux (m hm) (ξ) (Tkk) (hBoostCharge) : HasDerivAt … = i·(2π/ℏ)T_kk` — the
  one-particle hFlux with NO labelled wedge-KMS hypotheses (only `hBoostCharge`, itself discharged in Phase 3).

### Phase 3 — supply `hBoostCharge` ✅ DONE 2026-06-23 (`Fock/FreeFieldHFlux.lean`)
The `+2π` boost-charge derivative `hasDerivAt_inner_boostUnitary_imaginary_pos` is obtained by the `t→−t` reflection
(`HasDerivAt.comp_const_sub`) of the existing `−2π` `hasDerivAt_inner_boostUnitary_imaginary` — reusing the hard
dominated-convergence proof, no re-derivation. Composed with Phase 2's BW into the headline
**`freeField_oneParticle_hFlux`**: for any smooth wedge state `ξ = f.toLp`,
`HasDerivAt (t ↦ ⟪ξ, modUnitary S t ξ⟫) (i·(2π/ℏ·T_kk)) 0` with EVERYTHING operator/analytic discharged axiom-free —
the ONLY labelled input is the scalar identification `hTkk : (2π/ℏ)·T_kk = (−(2π·∫ conj(f)·f')).im` (the boost
Killing charge = stress flux, `+2π` orientation). Budget 0. **This is the free-field `oneParticle_hFlux` with no sign
mismatch and no labelled modular hypotheses — Gap 1 + Phases 2–3 all closed in one file.**
- Original deliverable `freeField_hBoostCharge` subsumed by `hasDerivAt_inner_boostUnitary_imaginary_pos` +
  `freeField_oneParticle_hFlux`.

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
