# Plan — Formalize ALL the *dischargeable* hypotheses of the QIQT→GR capstone

**Created 2026-06-23.** Companion to `QIQT_GR_DISCHARGE_PLAN.md` (now complete: the one-particle Bisognano–Wichmann,
the Reeh–Schlieder `S`-construction, and `conserv` are discharged; the end-to-end capstone `qiqt_gr_explicit_kg`
is axiom-free). After the GPT-5.5-pro audit (`qiqth_gr_conditional_verdict`), the capstone is an **axiom-free
CONDITIONAL Jacobson/KG theorem** resting on 31 hypotheses. They split into:

- **FUNDAMENTAL (irreducible physics — NOT targeted here):** the value of `G`/`η` (`a = 2π/ħη`); the matter EOM
  (`hKG`); the local-equilibrium idealization (`hequil`, saturation-at-the-bifurcation `hsat`); the background
  existence of a smooth Lorentzian spacetime + matter; and **the area-entropy / Clausius law `hbound`/`hsat`** —
  which in *Jacobson's* framing is irreducible but in *QIQT-H's* ambition is the **H2 crux** to be derived from
  finite `Q_max` (a separate, deeper program — NOT this plan).
- **DISCHARGEABLE (math, geometry, or should-be-constructed QFT — the target of THIS plan).**

**Goal of this plan:** turn every dischargeable hypothesis into a proved, axiom-free theorem, so the capstone rests
on EXACTLY the irreducible physics (the `G`/`η` value, the matter EOM, local equilibrium) + the H2 area-law crux.
This does **not** attempt H2 (the area law from `Q_max`) — that is the genuinely-open core, scoped elsewhere.

---

## Inventory of the dischargeable hypotheses (with current codebase status)

| Hypothesis | Class | Codebase status (2026-06-23) | Tier |
|---|---|---|---|
| `hric_symm` (Ricci symmetry `R_{σν}=R_{νσ}`) | pure geometry | ✅ **DONE `11a3af1`** — `ricci_symm` in `QIQTH/RicciSymm.lean` | **A1 ✓** |
| `hFocus` / Raychaudhuri identity | pure geometry | **DONE** — `raychaudhuri_focusing`, `raychaudhuri_geodesic`, `raychaudhuri_focusing_at_equilibrium` (`hFocus_of_raychaudhuri`). Residual `harea`/`hequil` is the physical floor, not dischargeable. | **A2 (verify only)** |
| `P,Pinv,hPP,hPP',hcong` (Sylvester tetrad `g=Pᵀ·gm·P`) | **background structure** (NOT pure debt) | ⚠️ **RECLASSIFIED + CONSOLIDATED `b7704a2`** — the tetrad IS "g is Lorentzian" (Sylvester); the 5 hyps collapse to ONE `hLor` (`qiqt_gr_explicit_kg_lorentzian`) but the input is irreducible structure | **A3 ~** |
| `hreg` (focusing-function regularity) | technical | ✅ **DONE `68e0c9a`** — `hreg_kg` in `QIQTH/HregExplicitKG.lean`; DROPPED from both capstones | **A4 ✓** |
| `hC` (Christoffel `C^∞` from `g,gi` `C^∞`) | technical geometry | ✅ **DONE `2ef2a81`** — `christoffel_contDiff` (via `contDiff_pd`) in `QIQTH/ChristoffelSmooth.lean` | **A5 ✓** |
| `Sf,KE,A` + `hDnn`/`hD0` (entropy/energy) | quantum information | ⚠️ **LARGELY DERIVED** — coherent-state Araki rel. entropy = `cgpEntropy ≥ 0` (`hasDerivAt_relModFlow_vacuum`, `cgpEntropy_nonneg`, Connes cocycle), axiom-free; only the spacetime↔one-particle localization bridge (Type-III₁) remains | **B ~** |
| `hKMS` (`WedgeKMSFlux_complete` — modular-flux dynamical realization) | QFT | ⚠️ **LARGELY DERIVED** — Fock modular flow=boost, modular energy=stress flux, `component_hFlux_of_wedgeKMS` gives `kd=(2π/ℏ)T_kk` axiom-free; residual = cited Type-III₁ wedge standardness + boost-charge + localization bridge | **C ~** |

Items NOT in this table (`g`, `hsymm`, `hCg`, `hCgi`, `φ`, `hφ`, `hKG`, `m,η,ħ,a`, `hbound`, `hsat`, `hequil`) are
the fundamental/background inputs and are deliberately out of scope.

---

## Tier A — Pure geometry & linear algebra *(near-term, high-confidence, self-contained; weeks)*

These need NO QFT/operator-algebra. They are the cleanest wins and should be done first.

### A1 — `ricci_symm` : `R_{σν} = R_{νσ}` — ✅ **DONE (`11a3af1`, 2026-06-23, axiom-free)**
`QIQTH/RicciSymm.lean`: `lowered_riemann_pair_symm` (`R_{abcd}=R_{cdab}` from the two antisymmetries + the first
Bianchi, the 4-cyclic-Bianchi `linarith`) → `ricci_symm` (Ricci as the gi-raised lowered-Riemann trace
`ricci_eq_trace` + termwise pair-symmetry + `Finset.sum_comm` + gi-symmetry). **Discharges `hric_symm`.** Original
sketch below for reference:
### A1 (sketch) — `ricci_symm` : `R_{σν}(x) = R_{νσ}(x)`
`ricci g gi σ ν x = ∑μ riemann g gi μ σ μ ν x`.  Symmetry follows from the **pair-symmetry of the lowered Riemann
tensor** `R_{abcd} = R_{cdab}`, contracted with `gi`.  The codebase already has `lowered_riemann_eq` (the explicit
`∂Γ−∂Γ+ΓΓ−ΓΓ` lowered form), `lowered_riemann_antisymm` (antisymmetry in each pair), and `riemann_first_bianchi`.
- **Brick 1:** `lowered_riemann_pair_symm` — `R_{ρσμν} = R_{μνρσ}` from the two antisymmetries + the first Bianchi
  identity (the standard 4-line algebraic permutation argument: write the first Bianchi for all four index rotations,
  add with signs).
- **Brick 2:** `ricci_symm` — contract `lowered_riemann_eq` + `pair_symm`, raise/lower with `gi` (`gi_g_delta`),
  collapse via `inv_contract`.  Discharges `hric_symm`.

### A2 — Raychaudhuri / `hFocus` : **already DONE — verify & wire** *(< 1 fire)*
`raychaudhuri_focusing`/`raychaudhuri_geodesic`/`raychaudhuri_focusing_at_equilibrium` already prove the focusing
equation axiom-free.  The labelled `hFocus` is replaced by these in `qiqt_gr_from_wedge_kms_raychaudhuri`
(and the explicit-KG form `qiqt_gr_explicit_kg_raychaudhuri`).  **Action:** confirm the kinematic-Raychaudhuri
capstone's remaining inputs (`hgeo`/`hequil`/`harea`) are exactly the physical floor (geodesic congruence +
local-equilibrium + area-rate modelling), and document that the *geometric* content is fully discharged.

### A3 — Sylvester tetrad — ⚠️ **RECLASSIFIED as background structure + CONSOLIDATED (`b7704a2`, 2026-06-23)**
**Honest finding:** the tetrad `g = Pᵀ·gm·P` (`hcong`, used in `EinsteinEquationOfState` via `BL g v = BL gm(Pv)`)
IS Sylvester's law of inertia — i.e. exactly the statement "`g` is Lorentzian (signature `(−,+,+,+)`)".  It is
therefore **genuine background structure (#5), not pure technical debt** like `hric_symm`/`hC`/`hreg`.  "`g` symmetric
+ invertible" does NOT imply congruence to `gm` (could be Euclidean), so the signature is an irreducible input.
**What WAS done:** `qiqt_gr_explicit_kg_lorentzian` collapses the five tetrad hypotheses `P/Pinv/hPP/hPP'/hcong` into
a SINGLE `hLor` (`g` admits an invertible Minkowski frame).  That is the honest endpoint — repackage 5 → 1; the input
remains the Lorentzian-metric assumption.  (A full Mathlib Sylvester `signature ⟹ congruence` theorem is possible but
just moves the input to "`g` has signature `(1,3)`" — equivalent structure, large effort, not pursued.)  Original
sketch below for reference:
### A3 (sketch) — Sylvester tetrad existence : `∃ P Pinv, g = Pᵀ·gm·P` (pointwise)
For a smooth Lorentzian metric, at each point the symmetric nondegenerate bilinear form `g x` is congruent to the
constant Minkowski form `gm` (Sylvester's law of inertia, fixed signature `(−,+,+,+)`).  Mathlib has bilinear-form
diagonalization (`LinearMap.BilinForm` / `Matrix.isHermitian` spectral theory).
- **Brick 1:** pointwise `∃ P, P` invertible and `g x = Pᵀ · gm · P` for a symmetric matrix of Lorentzian signature
  (reduce to Mathlib's congruence/diagonalization; signature handled by ordering eigenvalues).
- **Brick 2:** package as `P, Pinv : Point4→Fin4→Fin4→ℝ` with `hPP`, `hPP'`, `hcong`.  (Smooth dependence of `P` on
  `x` is NOT needed if the GR derivation uses the tetrad only pointwise — verify; if smoothness IS needed, that is a
  harder partition-of-unity / smooth-Gram–Schmidt argument, flag as a sub-frontier.)
- Discharges `P,Pinv,hPP,hPP',hcong`.  NB: the existing `EinsteinEquationOfState`/`ClausiusToPernull` Sylvester
  null-cone lemma may already give most of this — audit first.

### A4 — `hreg` — ✅ **DONE (`68e0c9a`, 2026-06-23, axiom-free)**
`QIQTH/HregExplicitKG.lean`: `hreg_kg`.  The `gi`-trace of `a·kgStress = Ric + f·g` fixes `f = (a·tr(kgStress)
− R)/4` uniquely (via `metric_contraction_trace` `∑gi·g = 4`), and that explicit `f` is `C^∞` (`kgStress_contDiff`/
`kgLagr_contDiff` + the curvature `C^∞` chain `riemann/ricci/scalarCurv_contDiff` in `ChristoffelSmooth.lean`).
**Discharges `hreg`; DROPPED from both capstones.**

### A5 — `hC` : Christoffel smoothness — ✅ **DONE (`2ef2a81`, 2026-06-23, axiom-free)**
`QIQTH/ChristoffelSmooth.lean`: `contDiff_pd` (∂ of a `C^∞` scalar is `C^∞`, via `pd_eq_fderiv` +
`ContDiff.fderiv_right` + `ContDiff.clm_apply`) → `christoffel_contDiff` (finite combination via `ContDiff.sum`/
`.mul`/`.add`/`.sub`).  **Discharges `hC`.**  GOTCHA: `ContDiff.differentiable` wants `⊤ ≠ 0` (`by simp`), not
`1 ≤ ⊤`, in the current `WithTop ℕ∞` API.

**Tier A deliverable:** a refactored capstone whose hypotheses no longer include `hric_symm`, `hC`, `hreg`, or the
tetrad block — only the genuinely-physical + entropy/modular inputs remain.
**★★★ TIER A COMPLETE (2026-06-23).** `qiqt_gr_explicit_kg` and `qiqt_gr_explicit_kg_raychaudhuri` now DROP `hC`,
`hric_symm`, AND `hreg` (discharged outright — `christoffel_contDiff` + `ricci_symm` + `hreg_kg`). A2 (Raychaudhuri)
was already done. A3 (tetrad) is reclassified as background Lorentzian structure and CONSOLIDATED 5→1 in
`qiqt_gr_explicit_kg_lorentzian`. **Every pure-technical-debt hypothesis GPT flagged is now a machine-checked
theorem.** What remains on the capstone is exactly: the physics floor (`hbound`/`hsat`, the EOM `hKG`), the
background structure (smooth metric `g`/`gi`, the Lorentzian frame `hLor`), the coupling `η`/`a`, and the
entropy/modular inputs (`Sf/KE/A`, `hDnn`/`hD0`, `hKMS`) — i.e. Tiers **B** and **C**, which are the research-grade
frontiers gated on the continuum Tomita–Takesaki / Araki-entropy programs (see below).

---

## Tier B — Quantum-information entropy objects `Sf, KE, A`, `hDnn`, `hD0` *(research-grade; months; overlaps Type-III)*

**⚠️ MAJOR CORRECTION (2026-06-23): Tier B is LARGELY ALREADY DISCHARGED in the codebase, axiom-free.** The earlier
assessment ("only `relEntropy_nonneg` in hand, gated on Type-III") was badly wrong. The continuum modular theory is
substantially built (`QIQTH/Fock/RelativeModularFlow.lean`, `SecondQuantModularFlow.lean`, `ModularRelativeEntropy`):
- The **relative modular operator** of a coherent state `W(f)Ω` and its **Connes cocycle** are CONSTRUCTED, with the
  cocycle in closed Weyl-product form (`connesCocycle_eq`) and the cocycle chain rule (`connesCocycleH_chain`,
  Connes' Radon–Nikodym) — all axiom-free.
- **`hasDerivAt_relModFlow_vacuum`** (axiom-free): the Fock-level Araki relative entropy of a coherent excitation
  `S(ω_{W(f)Ω}‖ω_Ω) = cgpEntropy(f)` — the one-particle CGP relative entropy — and `cgpEntropy_nonneg` proves it
  `≥ 0`. **So `hDnn` (relative entropy ≥ 0) is DERIVED at the one-particle/Fock level**, and `hD0` (vanishing at the
  KMS reference, `t=0`) is the `connesCocycleH_zero`/`relModFlowH_zero` identity.
- **`Sf`/`KE`/`A` are no longer "oracles"** in spirit: the modular entropy and modular energy are constructed objects
  whose relation IS the proven relative-entropy positivity.

**Genuine remaining gap (shared with Tier C):** the IDENTIFICATION of the *spacetime* GR functions `Sf/KE/A` (defined
along a null horizon generator in `WedgeKMSToGR`) with these *Fock/one-particle* entropy objects — i.e. the
localization bridge "the chain's null-generator entropy IS the one-particle relative entropy of the wedge state
`ξ_{x,v}`". That bridge is the cited Type-III₁ wedge-localization input (see Tier C), NOT a mechanical Klein gap.

---

## Tier C — The dynamical-realization bridge `hKMS` *(the deepest; multi-month→year; overlaps Type-III)*

**⚠️ MAJOR CORRECTION (2026-06-23): Tier C is LARGELY ALREADY DERIVED in the codebase, axiom-free.** The earlier
"multi-month, second-quantize from scratch" assessment was wrong — the Fock-level dynamical realization is built
(`QIQTH/Fock/SecondQuantModularFlow.lean`, `OneParticleBW.lean`):
- **C1 (second quantization) DONE:** `secondQuantModFlowH` = Γ(Δ^{it}) on the Fock Hilbert space (isometric,
  vacuum-invariant, one-parameter group), with Weyl covariance `Γ(A)W(u)=W(Au)Γ(A)` — all axiom-free.
  `secondQuantModFlowH_acts_as_boost` lifts the one-particle BW to the Fock modular flow = boost.
- **C2/C3 (modular energy = stress flux) DONE:** `modularEnergy_eq_stressFlux` / `hasDerivAt_modularEnergy_of_boost`
  give modular-energy derivative `= (2π/ℏ)·T_kk`. `oneParticle_hFlux` assembles the one-particle `hFlux`, and
  **`component_hFlux_of_wedgeKMS`** (axiom-free) descends it to the *component-level* `kd = (2π/ℏ)·T_kk` — EXACTLY
  the `hFlux` that `qiqt_bekenstein_gives_gr` / `WedgeKMSFlux_complete` consume. So `hKMS`'s modular content is
  DERIVED.
- **The genuine remaining LABELLED inputs** (per `OneParticleBW.lean` docstrings + `AxiomAudit`): the wedge-KMS
  property `hUniq`/`hStrip`/standardness (BGL §2/§4) = **the Type-III₁ wedge standardness** — explicitly CITED as
  Mathlib-unprovable physics (never a Lean axiom); the boost-charge = stress-flux identity `hBoostCharge` (the
  Killing/Noether identity); and the localization bridge `hbridge` (chain null-generator energy = one-particle
  modular energy). These three are "the single wedge-KMS-property + standard-localization input" — the genuine,
  irreducible Type-III₁ frontier, NOT a mechanical gap.

So **Tier C is not a multi-month construction task — its mechanical content is already DERIVED**; what remains is the
cited Type-III₁ physics (the same `hFlux`/dynamical-realization input the foundational papers label, by design).

---

## Ordering, dependencies, and relationship to existing plans

```
Tier A (geometry/linear-algebra)  ── independent, do NOW ──►  qiqt_gr_explicit_kg_geom (fewer hypotheses)
       A1 ricci_symm
       A2 raychaudhuri (verify, done)
       A3 Sylvester tetrad
       A4 hreg
       A5 hC

Tier B (entropy: Sf/KE/A, hDnn, hD0) ──► gated on Araki relative-entropy + Type-III modular Hamiltonian
Tier C (hKMS dynamical realization)  ──► gated on continuum Type-III (PVM keystone, Δ^{it}, algebraic BW)
```

- **Tier A** is self-contained and should be executed under THIS plan (near-term, ship-green increments, budget 0).
- **Tier B** = the Araki relative-entropy roadmap (`qiqth_araki_entropy_roadmap`) + the DPI/entropy side; record the
  GR hypotheses it discharges but pursue under that program.
- **Tier C** = the continuum **Tomita–Takesaki / Type-III** plan (`agile-pondering-naur.md`, Type-III section);
  record the GR hypothesis it discharges but pursue under that program.

**After Tier A:** the capstone rests on `{G/η value, matter EOM, smooth-spacetime background, local equilibrium,
Clausius/area law}` + `{Sf/KE/A, hDnn/hD0, hKMS}`.  After Tiers B+C: only the irreducible physics + the **H2 area-law
crux** (QIQT-H's to derive from `Q_max`, the genuinely-open core) remain.

---

## Verification discipline (every increment)

- `~/.elan/bin/lake build QIQTH.<Module>` green; every new theorem `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`; `bash scripts/axiom_budget_check.sh` stays `raw axiom count: 0 (budget 0)`; one commit per brick on
  `main` with the `Co-Authored-By: Claude Opus 4.8` trailer; `AxiomAudit.lean` entry per new theorem.
- After each Tier-A item, refactor the capstone to drop the discharged hypothesis and re-verify the end-to-end build.

## ★★★ PLAN STATUS (2026-06-23): essentially COMPLETE — every MECHANICALLY-dischargeable hypothesis is discharged.

- **Tier A — DONE.** `hric_symm` (A1), `hC` (A5), `hreg` (A4) discharged outright and DROPPED from the capstone;
  Raychaudhuri (A2) already done; the tetrad (A3) reclassified as Lorentzian *structure* and consolidated 5→1.
- **Tier B — already DERIVED in the codebase (axiom-free).** Coherent-state Araki relative entropy = `cgpEntropy ≥ 0`
  (`hasDerivAt_relModFlow_vacuum`, `cgpEntropy_nonneg`, Connes cocycle in `RelativeModularFlow.lean`). `hDnn`/`hD0`
  are derived at the one-particle/Fock level.
- **Tier C — already DERIVED in the codebase (axiom-free).** Fock modular flow = boost
  (`secondQuantModFlowH_acts_as_boost`), modular energy = stress flux, `component_hFlux_of_wedgeKMS` →
  `kd = (2π/ℏ)T_kk` (exactly the GR `hFlux`).
- **The genuine residual is NOT mechanical — it is the CITED, irreducible physics:** (i) the Type-III₁ wedge-KMS
  standardness (BGL `hUniq`/`hStrip`/standardness — Mathlib-unprovable by design, the dynamical-realization input);
  (ii) the spacetime↔one-particle localization bridge (`hbridge`, `hBoostCharge`); (iii) the Clausius/area law
  (`hbound`/`hsat`) + matter EOM + Lorentzian/smooth-metric background. These are the honest physical floor, shared
  with the foundational-paper's labelled inputs.
- **NOT in this plan, the ONE real open frontier:** H2 — the area law from finite `Q_max` — the irreducible QIQT-H
  core, the single thing between "conditional Jacobson theorem" and "QIQT predicts gravity". Deserves its own plan.

**Bottom line:** the dischargeable surface of the QIQT→GR capstone is exhausted. Tier A was discharged here; Tiers B
and C were found already discharged (axiom-free) in the continuum modular-theory files. What remains is exactly the
labelled Type-III₁ physics + the QIQT-H area-law crux (H2) — genuine science, not formalization debt.
