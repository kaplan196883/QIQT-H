# QIQT-H → Quantum Gravity: the tiered roadmap

**Status:** strategic roadmap, GPT-5.5-pro-reviewed (2026-06-28).
**Honest headline:** QIQT-H today is *induced/entropic gravity* (Jacobson–Sakharov–Verlinde
tradition) — a **conditional, classical, free-scalar, background-dependent** Einstein-*form*
result, machine-checked in Lean. It is **not** quantum gravity. These five plans lay out, honestly
and in dependency order, what it would take to get there — and which sub-items are genuinely
"solve quantum gravity"-hard so we never overclaim.

---

## Why this is a *recut*, not the first ladder I proposed

The first draft of this roadmap was a 4-tier ladder **A → B → C → D**:

- **A** finish the conditional classical result (discharge Gap-2; derive capacity ∝ A; beyond free field)
- **B** make geometry dynamical/quantum via the CPW/Witten **crossed-product Type II** algebra
- **C** the UV-complete finite "Quantized Information" substrate
- **D** empirical signatures

GPT-5.5-pro's review (full text archived in `paper_strategy/` review log) found **two structural errors** in that ladder:

1. **A2 was mis-tiered.** "Derive `log N_R ∝ A` from finiteness" is *not* a Tier-A cleanup item.
   **Finiteness alone gives a VOLUME law**, not an area law — a finite local lattice with on-site
   dimension `d` has `log dim 𝓗_R = n·log d ∝ Vol(R)`. Getting *area* capacity requires something
   that destroys tensor-factor independence (gravitational constraints, holographic QEC redundancy,
   finite causal-diamond Hilbert spaces, a screen postulate). That is **Tier-C-hard**, not Tier A.
   This sharpens the existing memo `qiqth_one_quarter_status` / `qiqth_capacity_qr_vs_qmax`: the
   Sakharov bridge derives the area *form* **conditionally** (local QFT on a smooth background + a
   covariant cutoff); it does **not** derive area capacity from bare finiteness.

2. **Tier B was circular.** The CPW/Witten crossed-product Type II construction *presupposes* a
   semiclassical bulk geometry (it is a `1/N`, `G→0` gravitational *dressing* of an existing QFT in
   curved spacetime). So it is a **description** of subregion algebras *once geometry exists* — it
   **cannot be the source** of "emergent spacetime." Using CPW Type II to *derive* the geometry it
   assumes is circular. B4 ("reconstruct geometry") and B5 ("crossed-product area operator") were
   therefore in tension.

The recut below fixes both: it **separates "assumes geometry" tiers from "derives geometry" tiers**,
and demotes the area-capacity law and the value of `G` to the microscopic tier where they actually
live.

---

## The five tiers (dependency-ordered)

| Tier | File | One line | Assumes geometry? | Hardest category |
|---|---|---|---|---|
| **0** | [TIER_0_OBSTRUCTIONS_AND_LEDGER.md](TIER_0_OBSTRUCTIONS_AND_LEDGER.md) | Finite-dim obstruction theorems + machine-readable assumption ledger | n/a | (a) near-term |
| **1** | [TIER_1_SEMICLASSICAL_GEOMETRIC_CODE.md](TIER_1_SEMICLASSICAL_GEOMETRIC_CODE.md) | The semiclassical geometric-code skeleton (fixed-area, JLMS, edge/bulk, Type II) — **proved conditionally, assuming geometry** | **YES** | (b) frontier |
| **2** | [TIER_2_FINITE_QI_SUBSTRATE.md](TIER_2_FINITE_QI_SUBSTRATE.md) | The actual finite-capacity microscopic theory — **the real QIQT-H novelty** | NO (builds it) | (c) QG-core |
| **3** | [TIER_3_EMERGENCE_AND_MATCHING.md](TIER_3_EMERGENCE_AND_MATCHING.md) | Derive Tier-1 structures (metric, RT, JLMS, gravitons, Einstein) *from* Tier 2 | NO (derives it) | (c) QG-core |
| **4** | [TIER_4_BLACK_HOLES_COSMOLOGY_PHENO.md](TIER_4_BLACK_HOLES_COSMOLOGY_PHENO.md) | Black-hole microstates, information paradox, singularities, cosmology, empirical tests | NO | (c) + (a) pheno |

**The non-circularity rule (read this twice):**
Tier 1 **assumes** a geometric code subspace and proves the holographic skeleton *within* it.
Tier 2 **builds** a finite substrate with no geometry assumed. Tier 3 **derives** the Tier-1
skeleton *from* Tier 2. Never use a Tier-1 construction (fixed-area sectors, CPW crossed product,
RT) as evidence for emergence — that is the circularity the recut exists to forbid.

### Category legend (used throughout)
- **(a)** genuine near-term formal/analytic work (a Lean theorem or a short paper in weeks–months)
- **(b)** open research frontier — hard but plausibly tractable in a few years by a focused group
- **(c)** "this *is* the central quantum-gravity problem" — no existing program has done it.
  `(c)` does **not** mean "don't attempt"; it means "don't call it a cleanup item, and don't
  promise a timeline."

---

## Mapping the old ladder onto the recut (so nothing is lost)

| Old item | New home | Note |
|---|---|---|
| A1 Gap-2 joint reference-state | **Tier 0** (finite obstruction thm) + **Tier 1** (physical horizon realization) | Finite-dim version is near-term; physical discharge needs edge-mode/fixed-area structure → Tier 1 |
| A2 derive capacity ∝ A | **Tier 2/3** | Mis-tiered; area capacity is *not* a consequence of finiteness — it must emerge from the substrate |
| A3a beyond free scalar | **Tier 1** (analytic, BW is generic) / **Tier 2** (formalization) | BW modular flow is not special to KG |
| A3b fix value of G | **Tier 2** | Needs the UV spectrum/cutoff — microscopic |
| B4 RT + first law ⇒ linearized Einstein | **Tier 1** (conditional, assumes holography) → **Tier 3** (from substrate) | Standard in AdS/CFT *conditionally*; "from finite capacity" is Tier 3 |
| B5 CPW Type II area operator | **Tier 1** | A *description* on a semiclassical background, NOT a source of emergence |
| B6 nonlinear quantum Einstein | **Tier 3** | Essentially full QG |
| C7 finite QI spectrum | **Tier 2** | The core novelty point |
| C8 BH / info / singularities / cosmology | **Tier 4** | Core QG tests |
| D9 empirical | **Tier 4** | Phenomenology |

---

## The single highest-value first deliverable per tier (de-risking order)

1. **Tier 0** — *KMS–capacity compatibility & obstruction theorem* (Lean): a `β>0` Gibbs state is
   maximally mixed on a record subsystem **iff** the modular Hamiltonian acts trivially there;
   edge⊗bulk fixed-area decomposition is sufficient. **This makes Gap-2 precise instead of hand-wavy.**
2. **Tier 1** — *finite-dimensional JLMS / operator-algebra-QEC theorem* with a central area operator
   `L_A = Σ ℓ_α P_α`: `K_A = L_A + K_bulk` on the code subspace. Captures the whole semiclassical
   lesson (area is an edge/center operator; fixed-area sectors solve Gap-2) without continuum CPW.
3. **Tier 2** — *a minimal finite-capacity toy substrate with a continuum/RG knob* (hyperbolic
   tensor-network / QEC, or finite spin-chain→CFT): can finite record capacity coexist with an
   approximate continuum QFT limit *without* breaking locality/unitarity/Lorentz beyond bounded error?
   **This de-risks the program more than any further continuum-entropy manipulation.**
4. **Tier 3** — *metric/causal-structure reconstruction* from the Tier-2 substrate's entanglement
   data (min-cut → distance), matched against the Tier-1 RT skeleton.
5. **Tier 4** — *parameterized-phenomenology bounds paper*: the most general low-energy deformation
   compatible with complete positivity + no-signaling + approximate Lorentz, confronted with
   oscillation data. (Likely outcome: most effects are Planck-suppressed or already constrained —
   which is itself a useful, honest result.)

---

## Standing honesty constraints (apply to every tier)
- No `sorry` in Lean; `#print axioms` = standard 3 (`propext`, `Classical.choice`, `Quot.sound`);
  budget 0. New physical inputs enter as **typeclass hypotheses**, never as Lean axioms, and are
  labelled in the assumption ledger.
- Never claim the **value of G** is derived (only the `1/4` *ratio* is). Never claim "axiom-free area
  law derived from finiteness" — finiteness gives only `S_vN ≤ log N_R`; the area *form* is the
  conditional Sakharov bridge.
- Never present a Tier-1 (geometry-assumed) result as evidence of emergence.
- Free scalar only until Tier 2/3 explicitly extend matter content.
- "Quantum gravity solved" requires **all of Tier 2 + Tier 3** (and the Tier-4 tests). Tier 0–1 are
  *not* quantum gravity; they are the honest skeleton and the conditional semiclassical description.

---

## Related existing plans (already in the repo)
- `P4_TO_GR_MASTER_PLAN.md`, `P4_MICRO_PLAN.md`, `P4_DERIVATION_JLMS_PLAN.md` — the current classical
  conditional chain (feeds Tier 0/1).
- `STONE_THEOREM_PLAN.md`, `TOMITA_TAKESAKI_ROADMAP.md` — continuum modular-flow infrastructure
  (feeds Tier 1 B5 and Tier 3).
- `K_LOCALIZATION_PLAN.md`, `T3-3_LOCALIZATION_MAP_PLAN.md` — Gap-2 localization (feeds Tier 0/1).
- `SAKHAROV_KG_PLAN.md` + `docs/SAKHAROV_KG_STAGE_B.md` — the conditional area-form/1/4 bridge.
- `paper_strategy/08_Neutrino_Decoherence_Prediction.md` — feeds Tier 4 D9.
