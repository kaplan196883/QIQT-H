# XL-step plan — from the finite cylinder premeasure to the continuum covariant μ

*Written 2026-06-08, grounded in the existing Lean formalization and a Mathlib API audit.
Difficulty key: **S** = hours, **M** = days, **L** = weeks, **XL** = months / new Mathlib
infrastructure. The "XL step" is the one remaining gap after the finite covariant-μ
construction (P0–P3, `NoSignalingGeneral` + `CoarseGrainNaturality` + `CylinderTypicality`,
all axiom-free, budget 33): turn the consistent finite **premeasure** on cylinder events into a
genuine **σ-additive measure μ∞ on the projective limit** = the space of global selectors λ
(full histories). That measure IS the prize's Lorentz-covariant typicality measure μ over λ.*

---

## 0. Where we stand (the input to this plan)

`CylinderTypicality.BornProjSystem` packages a finite-dim state `ρ` + a **directed projective
system** of finite POVM measurement contexts with coarse-graining maps `π`, and proves
(axiom-free): Kolmogorov **consistency** `μ_i = (π)_* μ_j`, normalization + nonnegativity
(`μ_total`, `μ_nonneg`), **stage-independence** of the cylinder measure (`cylinder_refine`,
`cylinder_common_refine`), and **covariance** under a unitary symmetry (`μ_covariant`). General
bipartite **no-signaling for arbitrary (entangled) states** is `NoSignalingGeneral`.

What is missing: the σ-additive extension to the limit, and the physical (continuum/Type III₁)
state that supplies the Born weights `ω(E)` instead of `tr(ρE)`.

## 0a. Mathlib reality check (verified 2026-06-08)

- ✅ `MeasureTheory.IsProjectiveMeasureFamily`, `IsProjectiveLimit`, `projectiveFamilyContent`
  (additive content on measurable cylinders) **+ σ-subadditivity** `projectiveFamilyContent_iUnion_le`
  (`MeasureTheory/Constructions/Projective.lean`, `ProjectiveFamilyContent.lean`). Index = `Finset ι`;
  spaces = products `∀ j : J, α j`.
- ✅ **`MeasureTheory.infinitePi`** — full Kolmogorov extension for **product (independent)** families
  over `Finset ι` (`Probability/ProductMeasure.lean`). ⇒ **the i.i.d. case is reachable NOW.**
- ✅ **Ionescu–Tulcea** (ℕ-indexed Markov kernels, `Probability/Kernel/IonescuTulcea/`).
- ❌ The **general** Kolmogorov extension (correlated / non-product content → measure, over `Finset ι`,
  standard-Borel) is **not packaged** — only the content + subadditivity exist. This is the single
  genuine Mathlib gap the XL step must close (or work around for finite fibers).

The step splits into two largely-separable halves: **Phase A** (the σ-additive extension — measure
theory, Lean-tractable, reuses everything) and **Phase B** (the physical realization — operator-algebra
continuum, mostly cited).

---

## Phase A — the σ-additive extension (Lean-tractable)

### A0 — Abstract the state functional. **(S, do first.)**
Generalize `bornW ρ E = Re tr(ρ E)` to a **positive normalized linear functional**
`ω : EffectAlg → ℝ` (`0 ≤ ω E` for effects, `ω 1 = 1`). The matrix case `ω = Re ∘ tr ∘ (ρ * ·)` is one
instance; the future continuum normal state another. All of P1–P3 uses only linearity + positivity +
`∑ E = 1` + coarse-graining, so this is cheap and **decouples Phase A from Phase B** — once a continuum
state exists, all of A applies verbatim.
- *Lean target:* `EffectState` structure (or a `class`), re-prove `consistent`/`μ_total`/`μ_nonneg`
  generically; `bornW` becomes the matrix instance.

### A1 — Recast as a Mathlib projective family. **(M.)**
Take `ι` = a countable set of elementary local measurements; `J : Finset ι` = a finite context;
`α j` = outcome space of measurement `j`; the context space is `∀ j : J, α j`; coarse-graining
`J ⊆ J'` is the canonical restriction `(∀ j:J', α j) → (∀ j:J, α j)`. Build `μ_J : Measure (∀ j:J, α j)`
(finite, from the Born weights) and prove **`IsProjectiveMeasureFamily μ`** from P3's `consistent`.
- *Hooks:* `IsProjectiveMeasureFamily`, `Measure.map`, finite-measure-from-Fintype (weighted counting).
- *Dep:* A0 (so the family is state-agnostic).

### A2a — Product / i.i.d. case via `infinitePi`. **(M; REACHABLE NOW — the immediate milestone.)**
When `ω` factorizes over independent measurements (product preparation — exactly the `indep`/`w p` case
the finite layer already uses), `μ_J = ∏_{j∈J} μ_j`, and **Mathlib's `infinitePi` gives μ∞ directly** as a
σ-additive probability measure with `IsProjectiveLimit μ∞ μ`. Combined with the existing Chebyshev
typicality (`BornTypicalityFinite`), this yields **"Born frequencies are μ∞-typical at the continuum"**
for independent measurements — the first citable continuum typicality measure, **no new Mathlib
infrastructure**.
- *Hooks:* `MeasureTheory.infinitePi`, `Probability/ProductMeasure.lean`.

### A2b — General (correlated/entangled) case: the Kolmogorov extension. **(XL; the Mathlib contribution.)**
Two routes:
- **(i) Finite-fiber route (leaner, fits us).** Each `α j` is *finite discrete*, so the projective limit
  is a **closed subset of the compact product** `∏ α j`; compactness ⇒ inner regularity ⇒ the
  `projectiveFamilyContent` is σ-additive ⇒ a measure via `MeasureTheory.Measure.ofAddContent` /
  `Content.measure`. Reuses Mathlib's content + subadditivity; adds only the σ-additivity-from-compactness
  step. *Hooks:* `projectiveFamilyContent_iUnion_le`, `AddContent`, `Measure.ofAddContent`,
  `IsCompact`/inner-regular, discrete `MeasurableSpace`.
- **(ii) General standard-Borel route.** Contribute the full Kolmogorov extension theorem to Mathlib.
- → **Recommend (i):** finite fibers make it a bounded, self-contained project.

### A3 — Born marginals at the limit. **(M; after A2.)**
`μ∞.map (restrict J) = μ_J` — "Born for every finite decoherent record partition," at the continuum.
Immediate from `IsProjectiveLimit`.

### A4 — Covariance of μ∞. **(M; after A2.)**
Lift P2's `μ_covariant` to `μ∞.map Φ_g = μ∞` via **uniqueness of the projective limit** (pushforward of
the extension = extension of the pushforward). A measure-preserving Poincaré action on the typicality
measure.

### A5 — No-signaling at the limit. **(M.)**
Lift P0 (`NoSignalingGeneral.local_marginal_indep_remote`) to μ∞ marginals.

---

## Phase B — the physical realization (operator-algebra continuum; mostly cited)

### B1 — Continuum state. **(M given the algebra; Mathlib gap on normal states.)**
Replace matrices by a **normal state `ω`** on a net of local von Neumann algebras (`ω(E)`, NOT
`tr(ρE)`). The Born family `μ_J(a) = ω(E^J_a)` is *automatically* projective (ω linear), so Phase A
applies. *Mathlib gap:* constructive normal states / predual of `B(H)` — interface input.

### B2 — Haag–Kastler net + cited physics. **(XL; cited.)**
Local algebras on diamonds (isotony, microcausality, Poincaré covariance via genuine automorphisms
`α_g`), vacuum/KMS state existence, **Type III₁** (Buchholz–Wichmann), **Bisognano–Wichmann** boost
action. Clearly-labelled cited inputs (Mathlib has `VonNeumannAlgebra` only structurally).

### B3 — Holographic cutoff. **(M.)**
Wire the finite-record capacity bound (Layer A, `CoreNoCollapse`/`CapacityModel`) to bound the
per-region index (finite `N` per diamond) — connects the measure to the capacity core and keeps each
stage finite (which is what makes A2b's finite-fiber route apply).

---

## Honest boundary, kill-criteria, first move

- **Cited, not proved (B2):** Type III₁-ness, vacuum/normal-state existence, Bisognano–Wichmann. The
  arXiv claim must read "σ-additive covariant typicality measure on histories, *given* a normal state on
  the net," NOT "derived from QFT."
- **Kill-criterion for A2b(i):** if compact inner-regularity of `projectiveFamilyContent` over finite
  fibers turns out to need the full general extension anyway, ship A2a (product) as the result and mark
  A2b as a standalone Mathlib contribution.
- **Recommended first move:** **A0 → A1 → A2a** — abstract the state, recast as a projective family, and
  get the **i.i.d. continuum measure via `infinitePi`** (reachable now, axiom-free, a genuine continuum
  Born-typicality milestone). Then attempt A2b(i) for the correlated case.

**Net.** Phase A converts the finite premeasure into the actual measure μ over λ (the prize object) —
**product case reachable now**, general case = one finite-fiber Kolmogorov-extension contribution.
Phase B is the operator-algebra wall, staged with cited inputs. This is the first concrete, mostly
Mathlib-supported path to the continuum μ, replacing the former blank "long pole."
