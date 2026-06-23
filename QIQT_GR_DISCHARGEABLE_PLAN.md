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
| `hric_symm` (Ricci symmetry `R_{σν}=R_{νσ}`) | pure geometry | `lowered_riemann_eq` + lowered-Riemann antisymmetry machinery EXIST; no `ricci_symm` yet | **A1** |
| `hFocus` / Raychaudhuri identity | pure geometry | **DONE** — `raychaudhuri_focusing`, `raychaudhuri_geodesic`, `raychaudhuri_focusing_at_equilibrium` (`hFocus_of_raychaudhuri`). Residual `harea`/`hequil` is the physical floor, not dischargeable. | **A2 (verify only)** |
| `P,Pinv,hPP,hPP',hcong` (Sylvester tetrad `g=Pᵀ·gm·P`) | linear algebra | Sylvester is currently a LABELLED hypothesis in several files (`ClausiusToPernull`, `EinsteinEquationOfState`); a "Sylvester null-cone lemma" exists | **A3** |
| `hreg` (focusing-function regularity) | technical | used as-is; the explicit `f = a·T·gi-trace − ½R` is concrete | **A4** |
| `hC` (Christoffel `C^∞` from `g,gi` `C^∞`) | technical geometry | currently assumed; derivable from `hCg`/`hCgi` since `christoffel` is a smooth algebraic combination of `∂g, gi` | **A5** |
| `Sf,KE,A` + `hDnn`/`hD0` (entropy/energy oracles) | quantum information | `relEntropy_nonneg` (Klein) DONE; `ArakiEntropy`/`ArakiInterface` exist; spacetime bridge missing | **B** |
| `hKMS` (`WedgeKMSFlux_complete` — modular-flux dynamical realization) | QFT | one-particle BW DONE; Fock infrastructure (`Fock/`, `ContinuumLambdaFock`) exists; the BW→stress-flux bridge missing | **C** |

Items NOT in this table (`g`, `hsymm`, `hCg`, `hCgi`, `φ`, `hφ`, `hKG`, `m,η,ħ,a`, `hbound`, `hsat`, `hequil`) are
the fundamental/background inputs and are deliberately out of scope.

---

## Tier A — Pure geometry & linear algebra *(near-term, high-confidence, self-contained; weeks)*

These need NO QFT/operator-algebra. They are the cleanest wins and should be done first.

### A1 — `ricci_symm` : `R_{σν}(x) = R_{νσ}(x)` *(1–3 fires; HIGH confidence)*
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

### A3 — Sylvester tetrad existence : `∃ P Pinv, g = Pᵀ·gm·P` (pointwise) *(2–5 fires; MODERATE)*
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

### A4 — `hreg` : derive from the explicit focusing function *(1–2 fires)*
`hreg` asserts the focusing function `f` (defined by `a·T = Ricci + f·g`) is `PdiffAt` everywhere and `f + ½R` is
differentiable.  For `T = kgStress` and smooth `g,gi,φ`, `f` is an explicit smooth algebraic combination
(`f = (a·g^{ab}kgStress_{ab} − R)/n`-type trace).  **Brick:** compute `f` explicitly and prove its regularity from
`hCg/hCgi/hφ`.  Discharges `hreg` for the explicit KG field.

### A5 — `hC` : Christoffel smoothness from metric smoothness *(1 fire)*
`christoffel g gi = ½ gi·(∂g + ∂g − ∂g)` is a smooth algebraic combination of `gi` and first derivatives of `g`.
**Brick:** `hC` from `hCg`, `hCgi` via `ContDiff.mul`/`ContDiff.sum` + `ContDiff` of `pd` (`contDiff_top_iff_fderiv`
or the existing `pd`/`PdiffAt_pd` machinery lifted to `ContDiff`).  Discharges `hC`.

**Tier A deliverable:** a refactored capstone `qiqt_gr_explicit_kg_geom` whose hypotheses no longer include
`hric_symm`, `hC`, `hreg`, or the tetrad block — only the genuinely-physical + entropy/modular inputs remain.

---

## Tier B — Quantum-information entropy objects `Sf, KE, A`, `hDnn`, `hD0` *(research-grade; months; overlaps Type-III)*

The abstract thermodynamic oracles must be replaced by *constructed* quantities of the QIQT wedge state:
`Sf` = (entanglement/modular) entropy of the wedge-restricted state along the null generator; `KE` = modular energy
(boost Hamiltonian expectation); `A` = horizon cross-section area.  Then:
- `hDnn` (`KE − Sf ≥ 0`) becomes **Klein's inequality / relative-entropy positivity** — the engine `relEntropy_nonneg`
  already EXISTS (used in `ArakiEntropy`).  The work is to identify `KE − Sf` with a relative entropy
  `S(ρ‖ρ_eq) ≥ 0`.
- `hD0` (`(KE − Sf)(0) = 0`) becomes the vanishing of relative entropy at the equilibrium (KMS) reference state.

### B1 — Relative-entropy identification *(deep; the Araki relative-entropy program)*
Build `KE − Sf = S_rel(ρ‖ρ_KMS)` for the wedge state.  Heavily overlaps the **Araki relative-entropy roadmap**
(`qiqth_araki_entropy_roadmap`: relative modular operator on Hilbert–Schmidt, CGP one-particle sweet spot) and the
**continuum Type-III / Tomita–Takesaki plan**.  This is where the modular Hamiltonian lives.
- **First brick:** state `hDnn`/`hD0` for a CONCRETE finite/Type-I truncation where `relEntropy_nonneg` applies
  directly, then extend.  Honest: full continuum identification is multi-month and gated on Type-III.

**Tier B is essentially the Araki/Type-III program viewed through the GR-discharge lens.** Pursue under that plan;
this document only records WHICH GR hypotheses it discharges.

---

## Tier C — The dynamical-realization bridge `hKMS` *(the deepest; multi-month→year; overlaps Type-III)*

`hKMS : WedgeKMSFlux_complete g (kgStress…) kd ħ` asserts the boost-modular flux of the stress tensor equals the
entropy-derivative `kd`.  This is the formal link the one-particle BW does NOT yet supply.  Closing it:
- **C1 — Second quantization:** lift `oneParticleBW_niceWedge_unconditional` (one-particle modular flow = boost) to
  the **Fock-space / local von Neumann algebra** modular flow.  Fock infrastructure exists (`Fock/`,
  `ContinuumLambdaFock`); needs the algebraic BW (`σ_t = Ad(Δ^{it})`, `JMJ=M'`).
- **C2 — Stress-energy operator:** define the free-field stress tensor `T_{μν}` as an operator / regularized
  expectation; relate its wedge flux to the boost Noether charge.
- **C3 — Modular Hamiltonian = boost stress flux:** the algebraic Bisognano–Wichmann statement
  `K = 2π·(boost generator) = 2π·∫ T_{00} flux`, then identify with `WedgeKMSFlux_complete`.
- **C4 — Wedge → local Rindler horizon:** the global-Minkowski wedge statement to the local-horizon statement used
  in the Jacobson step (the equivalence-principle / local-Rindler approximation).
- This is the **dynamical-realization gap** of the 4-gap map.  Pursue under the **continuum Type-III plan**; gated on
  the bounded spectral theorem / PVM keystone, Δ^{it}, KMS at the continuum.

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

## Honest scale

- **Tier A:** weeks. High confidence, pure math, self-contained. `ricci_symm`, `hC`, `hreg` are near-certain;
  Sylvester-tetrad is moderate (pointwise easy, smooth-frame harder — flag if needed).
- **Tier B:** months. Gated on Araki relative entropy / Type-III; `relEntropy_nonneg` (Klein) is the only piece
  fully in hand.
- **Tier C:** multi-month to year. Research-grade; the dynamical-realization bridge; gated on the continuum
  Tomita–Takesaki keystone.
- **NOT in this plan:** H2 (area law from finite `Q_max`) — the irreducible QIQT-H core, the single thing between
  "conditional Jacobson theorem" and "QIQT predicts gravity."  That is the real frontier and deserves its own plan.
