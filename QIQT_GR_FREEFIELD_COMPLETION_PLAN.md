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

### Phase 4 — route the free-field flux into the GR derivation *(core brick DONE 2026-06-23)*
**★ KEY DISCOVERY: no `−2π` bundle needed.** `qiqt_gr_from_wedge_kms_complete` uses `hKMS` only by calling
`hFlux_of_wedgeKMS_complete hKMS` to produce the per-generator equation `kd x v = (2π/ℏ)·BL(T x)v`, then feeds THAT to
the underlying `qiqt_bekenstein_gives_gr` — which takes the **kd-equation directly**, not the bundle. So
`WedgeKMSFlux_complete` (`−2π`/`wedgeGenSet`) is just ONE way to supply the kd-equation; the free-field `+2π` route is
another, landing at the same entry point.

**✅ Core brick (`Fock/FreeFieldHFlux.lean`):** `freeField_component_hFlux` — the `+2π`/nice-wedge analog of
`component_hFlux_of_wedgeKMS_complete`. For the nice-wedge `S` and smooth wedge state `ξ = f.toLp`, derivative
uniqueness against `freeField_oneParticle_hFlux` gives `kd = (2π/ℏ)·T_kk` from exactly two per-generator hypotheses:
- `hbridge` : `HasDerivAt (t ↦ ⟪ξ, modUnitary S t ξ⟫) (i·kd) 0` — that the abstract capstone coefficient `kd` IS the
  modular energy of the localized mode (the dynamical-realization identification);
- `hTkk` : `(2π/ℏ)·T_kk = (−(2π·∫ conj(f)·f')).im` — the localization map (Gap 2): the horizon stress component =
  the chosen mode's rapidity stress flux.
Everything modular/BW/boost discharged axiom-free; budget 0. **Gap 2 is now isolated to precisely `(hbridge, hTkk)`.**

**Remaining:** package a localization structure `FreeFieldHorizonData g T kd ħ` supplying, per null generator `(x,v)`,
the smooth mode `f_{x,v}` + `(hbridge, hTkk)`, and prove
`freeField_kd_conclusion : FreeFieldHorizonData … → ∀ x v, BL(g x)v=0 → kd x v = (2π/ℏ)·BL(T x)v` (a `∀`-wrap of
`freeField_component_hFlux`).
- **The honest fork (unchanged):** if `(hbridge, hTkk)` come from a CANONICAL free-field construction (the wedge mode
  localized at the horizon generator) → fully discharged. If a MODELING identification → the GR derivation reduces to
  that single labelled localization datum, the entire modular/BW/boost/stress content machine-checked.

### Phase 5 — the free-field capstone ✅ DONE 2026-06-23 (`QIQTH/QiqtGrFreeField.lean`)
Built (axiom-free, budget 0):
- **`qiqt_gr_from_flux_complete`** (`WedgeKMSToGR.lean`): the GR theorem taking the per-generator flux equation
  `kd x v = (2π/ℏ)·BL(T x)v` directly — what `qiqt_bekenstein_gives_gr` consumes — instead of the
  `WedgeKMSFlux_complete` bundle. Convention-agnostic entry point.
- **`freeField_kd_conclusion`**: the `∀`-wrap of `freeField_component_hFlux` — per null generator, the localization
  datum `(hbridge, hTkk)` + `freeField_oneParticle_hFlux` gives the flux equation.
- **`qiqt_gr_freefield`**: ★★★★★★ THE FREE-FIELD QIQT→GR CAPSTONE. `a·kgStress_μν = G_μν + Λ·g_μν` with the wedge-KMS
  modular flux supplied by the axiom-free `+2π` one-particle BW machinery. Geometry (`hC`/`hric_symm`/`hreg`), matter
  (`conserv`), and `hT_symm` all discharged internally for `kgStress`. Only labelled inputs: the Clausius/area-
  saturation physics + the per-generator localization map `(hbridge, hTkk)` (Gap 2).

---

## ✅ COMPLETION SUMMARY (2026-06-23)

The free-field QIQT→GR derivation is **complete modulo exactly the honest physics floor + the localization map**.
The full chain is machine-checked axiom-free (`[propext, Classical.choice, Quot.sound]`, budget 0):

`oneParticleBW_niceWedge_unconditional` (modular flow = +2π boost, NO Reeh–Schlieder hyps)
  → `freeField_oneParticle_hFlux` (modular energy = i·(2π/ℏ)·T_kk, BW + boost-charge supplied internally)
  → `freeField_component_hFlux` (kd = (2π/ℏ)·T_kk per generator)
  → `freeField_kd_conclusion` (∀ null generators)
  → `qiqt_gr_from_flux_complete` / `qiqt_gr_freefield` (Einstein's equations for the explicit free KG field).

**What remains labelled (the honest boundary — all genuine, none mechanical):**
1. **Gap 2 — the localization map `(hbridge, hTkk)`**: per null horizon generator, which wedge mode realizes it, and
   that its rapidity stress flux = the horizon stress component. The dynamical-realization input.
2. **The Clausius/area-saturation law** (`hbound`/`hsat`/`hDnn`/`hD0`) — the Jacobson thermodynamic postulate.
3. **H2 — the area law from finite `Q_max`** — QIQT-H's central open scientific claim (separate plan).
4. Matter EOM (`hKG`), Lorentzian/smooth background, coupling `η`/`G`, focusing `hFocus` — irreducible inputs.

Every modular, Bisognano–Wichmann, boost-charge, stress-flux, conservation, and curvature step beneath these is
machine-checked. The `±2π` sign obstruction is fully resolved (the `+2π` route is the satisfiable one).

### Gap 2 investigation (2026-06-23) — confirmed IRREDUCIBLE modeling, not a missing construction
Surveyed the localization apparatus (`Fock/Localization.lean`, `LocalizedCovariance`, `LocalizedWitness`):
- There is **`Krep`** (rapidity rep of a `V → ℂ` test function) but **NO** canonical map from a null horizon
  generator `(x,v)` to a wedge mode. So `(hbridge, hTkk)` cannot be discharged mechanically — choosing which wedge
  mode realizes a given local Rindler horizon, and identifying its rapidity stress flux with the horizon stress, is
  the genuine dynamical-realization (physics modeling) step. This is the honest, irreducible Gap 2.
- The **soft** sub-hypotheses (`MemLp`/`Integrable`/`AEStronglyMeasurable`/`HasDerivAt`/bounded-`‖f'‖`) ARE
  satisfiable in principle (Schwartz/Gaussian/compact-support modes — the codebase has the `Krep`/`horizonAmp`
  integrability machinery, e.g. `stressFluxKK_eq_neg_rapMom_cptSupp`). But discharging them generically would be a
  SEPARATE sub-project: Mathlib lacks ready `SchwartzMap.memLp`/`integrable`, and `freeField_component_hFlux` is
  stated for a generic `f : ℝ → ℂ` (not `Krep m (·)`), so a `_schwartz`/`_cptSupp` convenience wrapper would require
  bridging the generic-`f` and `Krep` pictures. It is NOT part of completing this plan (it only narrows the SOFT
  shell of Gap 2; the irreducible core `(hbridge, hTkk)` remains regardless).

### PLAN STATUS: COMPLETE — no mechanical work remains
All 5 phases are discharged and machine-checked axiom-free (budget 0). What remains is exactly the genuine physics
floor (Clausius/area law, H2, EOM/background/couplings) + the Gap-2 modeling input — none of it mechanical Lean work.

### Optional strengthening DONE 2026-06-23 — soft-shell non-vacuity (`Fock/FreeFieldHFlux.lean`)
`freeField_softData_nonvacuous` — the analytic hypotheses of `freeField_component_hFlux`
(`MemLp`/`Integrable`/`AEStronglyMeasurable`/`HasDerivAt`/globally-bounded `‖f'‖`) are simultaneously satisfiable,
witnessed by the Gaussian mode `θ ↦ exp(−θ²)` with derivative bound `B = 1` (`2|x| ≤ x²+1 ≤ exp(x²)`). Confirms the
localization datum's analytic shell is inhabited (guards against vacuity); only the modeling core `(hbridge, hTkk)`
stays labelled. Axiom-free, budget 0.
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
