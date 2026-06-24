# T3-3 — Localization / the bridge map (Gap 2): discharge `hFocus`, `hbridge`, `hTkk`

**Status:** ✅ COMPLETE (Stages 0–2 full discharge; Stage 3 = documented-stop, the honest outcome).
**Track:** GR. **Goal capstone:** `QIQTH.WedgeKMSToGR.qiqt_gr_freefield`
(`lean/mathlib/QIQTH/QiqtGrFreeField.lean`).

### Outcome — Gap-2 localization map went from **4 abstract identities → 1 transparent physical law**
`hbridge` and `hFocus` are **genuinely discharged** (reduced to axiom-free one-particle BW machinery and the
proved Raychaudhuri focusing law). `hTkk` is **not eliminated** — it is the single irreducible physical input
(the Unruh/BW localization map), now stated transparently as *classical null energy = mode boost charge*.
Eliminating it would require either continuum mode-expansion machinery Mathlib lacks, or constructing an
*arbitrary* mode with the right charge — which would be physically vacuous (a soundness hole), so it was
deliberately **not** done. Final capstone: `qiqt_gr_freefield_nullEnergy`. All stages axiom-free, budget 0.

### Progress log
- **Stage 0 ✅** (`BL_kgStress_null`, `QiqtGrFreeField.lean`) — null-stress simplification
  `BL(kgStress) v = (∑ₐ vₐ ∂ₐφ)²` on `BL(g x)v=0`. Axiom-free, budget 0.
- **Stage 1 ✅** (`qiqt_gr_freefield_localized`) — **`hbridge` discharged.** Fixes `kd := (2π/ℏ)·BL(kgStress)v`
  and derives `hbridge` from `freeField_oneParticle_hFlux`; `hK` now states heat rate IS `(2π/ℏ)·T_kk`.
  Axiom-free, budget 0.
- **Stage 2 ✅** (`qiqt_gr_freefield_localized'`) — **`hFocus` discharged.** The Raychaudhuri focusing law
  `ad = R_kk` derived from a per-generator smooth geodesic congruence `W` at equilibrium (`hFocus_of_raychaudhuri`),
  christoffel smoothness itself discharged (`christoffel_contDiff`). **Gap-2 surface now = `hTkk` ALONE.**
  Axiom-free `[propext, Classical.choice, Quot.sound]`, budget 0.
- **Stage 3 ✅ (documented-stop)** (`qiqt_gr_freefield_nullEnergy`) — `hTkk` **reduced to transparent form** via
  Stage 0: the lone surviving input now reads `2π/ℏ·(∑ₐ vₐ ∂ₐφ)² = (−2π∫conj(ff)·ff').im` (classical null
  energy = mode boost charge), the genuine Unruh/BW localization map. Not discharged (would need continuum
  mode-expansion, or a vacuous arbitrary-mode construction — deliberately avoided). Axiom-free, budget 0.
  **T3-3 complete.**

## 0. What this is

The free-field QIQT→GR capstone `qiqt_gr_freefield` derives Einstein's equations `a·kgStress = G + Λ·g`
axiom-free, but leaves **four** per-null-generator identities labelled as inputs — together the **localization
map** (Gap 2: the dynamical realization of horizon generators by wedge modes):

| Hyp | Statement (on the null cone `BL(g x) v = 0`) | What it bridges |
|---|---|---|
| `hTkk` | `2π/ℏ · BL(kgStress m φ g gi x) v = (−2π ∫ conj(ff x v)·ff' x v).im` | classical KG null-stress `T_kk` ↔ one-particle rapidity-momentum integral |
| `hbridge` | `HasDerivAt (t ↦ ⟨ξ, modUnitary S t ξ⟩) (i·kd x v) 0`, `ξ = (ff x v).toLp` | abstract heat coefficient `kd` ↔ modular energy of the localized mode |
| `hFocus` | `ad x v = BL (ricci g gi · x) v` | area first-variation rate ↔ Ricci focusing `R_kk` (Raychaudhuri) |
| (`hflux`) | `kd x v = 2π/ℏ · BL(T x) v` | derived *inside* `freeField_kd_conclusion` from `hTkk`+`hbridge`; not separately labelled in the free-field capstone |

`ff`, `ff'`, `mw`, `kd`, `ad` enter the capstone as **abstract parameters**; `hTkk`/`hbridge`/`hFocus` link them.
T3-3 = **construct** these objects for the free Klein–Gordon field so the three identities become *theorems*,
yielding a strictly stronger capstone `qiqt_gr_freefield_localized` whose only labelled inputs are the genuine
Clausius/area physics (`hbound`/`hsat`/`hDnn`/`hD0`, the heat-functional link `hK`) plus machine-checkable
congruence kinematics.

## 1. What is already machine-checked (build on, do not touch)

All in `lean/mathlib/QIQTH/`:

- **`Fock/CyclicWitness.lean:701` `oneParticleBW_niceWedge_unconditional`** — axiom-free Bisognano–Wichmann:
  `modUnitary (niceWedge…) t = boostUnitary (+2π t)`. No labelled hypotheses.
- **`Fock/FreeFieldHFlux.lean:69` `hasDerivAt_inner_boostUnitary_imaginary_pos`** — axiom-free:
  `d/dt ⟨ξ, boostUnitary(2πt) ξ⟩|₀ = i·(−2π ∫ conj(f)·f').im`.
- **`Fock/FreeFieldHFlux.lean:114` `freeField_oneParticle_hFlux`** — combines the two: **given `hTkk`**,
  `d/dt ⟨ξ, modUnitary S t ξ⟩|₀ = i·(2π/ℏ · Tkk)`. **This is exactly `hbridge` with `kd := 2π/ℏ·Tkk`.**
- **`Fock/FreeFieldHFlux.lean:144` `freeField_component_hFlux`** — `HasDerivAt.unique` of the above two ⟹
  `kd = 2π/ℏ·Tkk`. (The `hflux` derivation.)
- **`QiqtToGR.lean:41` `hFocus_of_raychaudhuri`** — axiom-free: **derives `ad = BL(Ric) v`** from a smooth
  geodesic null congruence `V` (`hgeo`), the **equilibrium** condition `hequil` (shear–expansion quadratic
  `∑ ∇V·∇V = 0`, a stationary/bifurcation horizon), and the **area↔θ** identification
  `harea : ad = −∑ V·∂(expansion)`. The Raychaudhuri kinematics are proved (`Raychaudhuri.lean:272`
  `raychaudhuri_focusing_at_equilibrium`).

**Consequence:** `hbridge` and `hFocus` are *already reducible* to existing axiom-free lemmas — they are wiring,
not new mathematics. The genuine remaining physics is concentrated in **`hTkk`** (Stage 3).

## 2. Key simplification (the lever for `hTkk`)

On the null cone `BL(g x) v = ∑ᵢⱼ g x i j · vᵢ vⱼ = g(v,v) = 0`. The KG stress is
`kgStress = ∂_aφ ∂_bφ − ½ g_ab·L` (`KGStressConservation.lean:33`). Contracting with `v`:

```
BL(kgStress m φ g gi x) v = (∑ₐ vₐ · pd φ a x)² − ½ · (BL(g x) v) · kgLagr…  =  (∑ₐ vₐ ∂ₐφ)²
```

because the second term carries the factor `BL(g x) v = 0`. So on the cone the null energy `T_kk` is the
**squared directional derivative** `(v^a ∂_a φ)²`. `hTkk` then reads, concretely:

```
2π/ℏ · (∑ₐ vₐ ∂ₐφ(x))²  =  (−2π ∫ conj(ff x v)·ff' x v).im
```

i.e. *the classical null-energy flux of the KG field equals the one-particle modular boost charge of the
localized mode* — the concrete Unruh/BW content of Gap 2.

## 3. Stages (each an axiom-free, green-building commit)

### Stage 0 — Null-stress simplification *(warm-up, pure computation; ~1 lemma)*
New lemma in `KGStressConservation.lean` (or a small `QIQTH/NullStress.lean`):
```lean
theorem BL_kgStress_null (m : ℝ) (φ : Point 4 → ℝ) (g gi …) (x v) (hnull : BL (g x) v = 0) :
    BL (kgStress m φ g gi x) v = (∑ a, v a * pd φ a x) ^ 2
```
Route: unfold `kgStress`, `BL`; the `g`-term collects `BL(g x) v`; `rw [hnull]`; `ring`. Independent + reusable.
**Risk: low.** Acceptance: `#print axioms` = standard 3; budget 0. **✅ DONE** — `BL_kgStress_null`, axiom-free, budget 0.

### Stage 1 — discharge `hbridge` *(architecture/wiring; removes one labelled input)*
Set the heat coefficient to the stress flux: in the new capstone, **define** (don't take as parameter)
`kd x v := 2 * π / ℏ · BL (kgStress m φ g gi x) v`. Then `hbridge` is *exactly* the conclusion of
`freeField_oneParticle_hFlux (hmw x v) (ff x v) (ff' x v) … hbar (kd x v) (BL (kgStress…) v) (hTkk x v hnull)`.
So provide `hbridge` internally instead of as a hypothesis.
- The thermodynamic premise `hK : HasDerivAt (KE x v) (kd x v) 0` now says "the heat functional's rate **is**
  `2π/ℏ·T_kk`" — a genuine Clausius-side input, correctly **kept** labelled (it is physics, not Gap 2).
- Net surface change: **`hbridge` removed**; `kd` no longer free.
**Risk: low** (it is the existing lemma). Acceptance: capstone builds without the `hbridge` binder; axiom-free.
**✅ DONE** — `qiqt_gr_freefield_localized` (no `hbridge` binder; `kd` fixed), axiom-free, budget 0.

### Stage 2 — discharge `hFocus` *(wire in Raychaudhuri; trade physics-looking hyp for proved kinematics)*
Provide a null congruence and apply `hFocus_of_raychaudhuri`. Two sub-steps:
- **2a.** Add congruence data to the localized capstone: `V : Point 4 → Fin 4 → ℝ` with smoothness `hVC`,
  Christoffel smoothness `hC` (already a discharged theorem for `kgStress`/smooth `g`), geodesic `hgeo`, the
  equilibrium `hequil`, and the area↔θ identification `harea : ad x v = −∑ν V x ν · pd (expansion …) ν x`.
- **2b.** `have hFocus := fun x v hnull => hFocus_of_raychaudhuri g gi hsymm V hVC hC hgeo x (hequil x v) (ad x v) (harea x v)`.
  Removes the `hFocus` binder; replaces it with `(V, hVC, hgeo, hequil, harea)`.
**Honest note:** this *trades* one labelled identity for geometric kinematic inputs (`hgeo`, `hequil`, `harea`).
`hgeo`/`hequil` are the standard Jacobson stationary-horizon setup (machine-checkable for a concrete `V`);
`harea` is the area-vs-expansion modelling identification. The *Raychaudhuri content* (`ad = R_kk`) becomes
proved — the residue is kinematics, not the focusing law. **Risk: medium** (constructing a `V` that satisfies
`hgeo`+`hequil` concretely; fallback: keep `V` + its three kinematic premises as the labelled surface — still
strictly better, since the focusing *law* is discharged).
**✅ DONE** (fallback form, the honest one) — `qiqt_gr_freefield_localized'` takes the per-generator congruence
`W` + (`hWx`,`hWC`,`hWgeo`,`hWequil`,`hWarea`) and *derives* `hFocus`; christoffel smoothness discharged via
`christoffel_contDiff`. Axiom-free, budget 0. Focusing law proved; residue is pure kinematics, no Einstein.

### Stage 3 — `hTkk`: the genuine localization map *(the hard core; the real Gap-2 physics)*
Construct the mode and prove the stress identity. Two sub-steps:
- **3a — the localization map `ff x v`.** Define `ff x v : ℝ → ℂ`, the wedge-localized one-particle
  wavefunction of `φ` along the generator `(x,v)` in **rapidity** coordinates `θ` (the boost parameter). Natural
  candidate: the positive-frequency part of `θ ↦ ∂_v φ` pulled to the rapidity line of the wedge through `x`
  with null tangent `v` (the Unruh mode). Must land in `MemLp · 2`, `Integrable`, `HasDerivAt`, bounded `f'`
  (the `hf2`/`hf_int`/`hfd`/`hf'_meas`/`hB` data the chain already consumes).
- **3b — the stress identity (`hTkk`).** Prove
  `(−2π ∫ conj(ff x v)·ff' x v).im = 2π/ℏ·(∑ₐ vₐ ∂ₐφ)²` (using Stage 0's RHS). This is the one-particle
  modular-energy = classical-null-energy computation. Likely needs: Parseval/Plancherel on the rapidity line,
  the boost-charge integral `∫ conj(f)·f' = i·⟨f, −i∂_θ f⟩`, and that the rapidity momentum of the Unruh mode
  reproduces the squared directional derivative.

**Honest risk: HIGH.** 3b is the genuine physical identification (Unruh/BW). Outcomes, best→fallback:
1. **Full discharge:** 3a+3b both close ⟹ `hTkk` becomes a theorem; capstone's Gap-2 surface is **empty**.
2. **Reduced axiom:** 3a closes but 3b is an irreducible identification ⟹ keep a *single* clean labelled
   lemma `kg_localization_stress` (mode constructed, identity posited) instead of an abstract `hTkk` over an
   abstract `ff` — the surface shrinks from "abstract mode + abstract identity" to "one concrete physical law."
3. **Documented stop:** if 3a itself needs continuum machinery Mathlib lacks (full QFT mode expansion), stop at
   Stages 0–2 (hbridge+hFocus discharged) and leave `hTkk` labelled with the Stage-0 simplification applied
   (so it reads as the concrete `(v^a∂_aφ)²` identity, not the opaque integral form).

**✅ OUTCOME = #3 (documented stop), and it is the honest one.** `qiqt_gr_freefield_nullEnergy` applies Stage 0
so `hTkk` reads as the transparent `2π/ℏ·(∑ₐ vₐ ∂ₐφ)² = (−2π∫conj(ff)·ff').im`. We deliberately did **not**
take route #1/trivial-3a (construct an arbitrary mode with the prescribed boost charge): that would discharge
`hTkk` syntactically while being physically vacuous — exactly the kind of soundness hole to avoid. The genuine
localization map (deriving `ff` from `φ` by wedge smearing) is the cited continuum frontier.

## 4. Deliverable

`QIQTH.WedgeKMSToGR.qiqt_gr_freefield_localized` (new theorem; keep `qiqt_gr_freefield` as the more-general
form). Best case: signature drops `hbridge`, `hFocus`, `hTkk` (gains `V`+kinematics + the constructed `ff`),
leaving only Clausius/area physics + matter EOM `hKG` + geometry scaffolding. Minimum case: drops `hbridge` and
`hFocus`, with `hTkk` reduced to one concrete constructed-mode identity. Update `tracks/gr.toml` manifest +
re-run `lean-track` so the surface reduction is recorded.

## 5. Verification discipline (per stage, non-negotiable)

- `cd /d/ROOT/qiqt/lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green.
- `#print axioms <new thm>` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no new project axioms).
- `bash scripts/axiom_budget_check.sh` stays `raw axiom count: 0 (budget 0)`.
- One commit per stage (ship-green-increments), `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
- After the final stage, `python scripts/lean-track.py report -c tracks/gr.toml` to confirm the GR surface shrank.

## 6. Order of attack (leverage-first)

**Stage 0 → 1 → 2** are high-confidence wins (the null simplification, then `hbridge` and `hFocus` discharged
from existing axiom-free lemmas) — do these first; they remove two of the three labelled identities and are
low/medium risk. **Stage 3** is the genuine research core (the Unruh localization) — attempt 3a (mode
construction) before committing to 3b, and fall back per §3 if the continuum identification proves
Mathlib-out-of-reach. Net even in the fallback: Gap-2's surface drops from four abstract identities to one
concrete physical law.
