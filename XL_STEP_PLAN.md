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

## 0b. GPT-5.5-pro review (2026-06-08) — corrections folded in

A blunt adversarial review caught one **soundness-critical** issue and several scope fixes:

1. **★ The index `ι` MUST denote *compatible/decoherent/actual record* variables — NOT arbitrary
   counterfactual measurement settings.** Recasting over `Finset ι` of *all* elementary measurements
   asserts a joint law on every finite subset; for incompatible POVMs this is **FALSE by Fine's theorem**
   (Bell/CHSH-violating Born marginals admit no joint distribution; no-signaling gives one-party marginals
   only, never a global selector measure). This is exactly right for QIQT-H — the selector λ ranges over
   *actual decoherent records*, which ARE jointly classical — but it must be made an explicit, enforced
   hypothesis: `ι` = one consistent (commuting/decoherent) history framework. **Mandatory:** add a
   CHSH/Fine **sanity check** — if the construction would produce a global-selector measure for
   Bell-violating pair marginals on `(A₀,A₁,B₀,B₁)`, it has smuggled in a non-quantum assumption.
2. **A2b is NOT "M" — it is L/XL (well-scoped).** Re-estimated. And: do **not** start with inner
   regularity (a Lean tarpit). Use the **compact-open cylinder** argument (finite discrete fibers ⇒
   compact product ⇒ a countable disjoint cylinder cover of a compact cylinder is *finite* ⇒ finite
   additivity gives countable additivity). **Try first the topology-free route:** `projectiveFamilyContent`
   subadditivity (`_iUnion_le`) `c s ≤ ∑' c sₙ` + finite-additivity/monotonicity `∑_{F} c sₙ ≤ c s` ⇒
   equality. If that closes, A2b is mostly `Content.measure`/`Measure.ofAddContent` plumbing + marginal ext.
3. **Terminology:** what we have is a cylinder **content** (finitely additive), NOT yet a "premeasure"
   (a premeasure is already countably additive). Rename accordingly throughout the writeup.
4. **Projective limit ≠ full product.** The genuine selector space is the *inverse-limit subtype*
   `{x : ∀ i, X_i // ∀ i≤j, π_{ij}(x_j)=x_i}` — a *closed* (hence compact, for finite discrete `X_i`)
   subset of `∀ i, X_i`, NOT Mathlib's product-shaped `IsProjectiveLimit`. Construct the measure directly
   on the subtype; cleanest with **surjective bonding maps** (drop empty coarse outcomes first). Avoid
   encoding it as the full product (support/regularity headaches for uncountably many compatibility eqns).
5. **A2a is plumbing, not the prize.** It validates the Mathlib shape and gives the i.i.d. continuum
   measure, but the real physics (entangled correlations, QFT vacuum, correlated histories) lives in
   A2b + Phase B. Don't oversell. Also: Chebyshev gives finite-`n` frequency bounds; *almost-sure* limiting
   frequencies need Borel–Cantelli/SLLN — state which one is claimed.
6. **B1 true only narrowly.** `p(x)=ω(E_x)` with finite POVM needs no trace and Type III is NOT a problem
   for finite POVMs; microcausality ⇒ spacelike local effects commute ⇒ `E^A_x E^B_y` are positive joint
   effects ⇒ entangled ω gives correlated but no-signaling Born. The real danger is again **joint
   measurability/contextuality**, not Type III — require commuting local effects / decoherent histories /
   classical record algebra.
7. **Resequence (first = zero quantum content):** smoke-test a pure `FiniteMarginals` structure + the
   product case via `infinitePi` to confirm the `Finset ι` shape works against Mathlib; THEN the
   finite-fiber correlated extension; THEN marginals/covariance/no-signaling; THEN refactor Born weights
   through A0; Phase B stays cited.

The corrected difficulties and the compatibility constraint are reflected inline below.

---

## Phase A — the σ-additive extension (Lean-tractable)

> **PROGRESS (2026-06-08, all axiom-free, budget 33).** A2a/A3/A4/A5/A0 DONE; A2b is the sole remaining
> crux. `QIQTH/FiniteMarginals.lean` (`QIQTH.HistoryMeasure`): `FiniteMarginals` shape + `IsLimit`/
> `limit_unique`; **A2a** product case via `infinitePi` (`productMarginals_isProjectiveLimit/_marginal`);
> **A3** `isLimit_marginal`, **A5** `isLimit_marginal_mono` (no-signaling), **A4** `isLimit_map_eq`
> (covariance via uniqueness). `QIQTH/QuantumHistoryMeasure.lean`: **A0** `bornPMF` (matrix Born law =
> PMF) + `quantumHistoryMeasure` (i.i.d. continuum quantum Born measure, σ-additive, Born marginals).
> **A2b remaining** = existence for the correlated case ⇐ `(projectiveFamilyContent F.proj).IsSigmaSubadditive`
> (then `MeasureTheory.AddContent.measure`); Mathlib has the Carathéodory machinery (`OfAddContent.lean`)
> but NOT the general σ-subadditivity — for finite discrete fibers it follows from compactness/FIP
> (`tendsto`-to-zero on decreasing empty-intersection cylinders), the analog of Mathlib's
> `piContent_tendsto_zero` — a genuine multi-hundred-line Mathlib-grade contribution. Not faked.


### A0 — Abstract the state functional. **(S, do first.)**
Generalize `bornW ρ E = Re tr(ρ E)` to a **positive normalized linear functional**
`ω : EffectAlg → ℝ` (`0 ≤ ω E` for effects, `ω 1 = 1`). The matrix case `ω = Re ∘ tr ∘ (ρ * ·)` is one
instance; the future continuum normal state another. All of P1–P3 uses only linearity + positivity +
`∑ E = 1` + coarse-graining, so this is cheap and **decouples Phase A from Phase B** — once a continuum
state exists, all of A applies verbatim.
- *Lean target:* `EffectState` structure (or a `class`), re-prove `consistent`/`μ_total`/`μ_nonneg`
  generically; `bornW` becomes the matrix instance.

### A1 — Recast as a Mathlib projective family. **(M — but conditional on the compatibility constraint.)**
**★ Constraint (soundness-critical, per review §0b.1):** `ι` must index a *single consistent
(commuting/decoherent) family of actual record variables*, NOT arbitrary counterfactual settings — else
a joint law on `Finset ι` is FALSE (Fine/Bell). Enforce this as an explicit hypothesis and add the
CHSH/Fine sanity-check countermodel. Also (review §0b.4): the target is the inverse-limit *subtype*
`{x // ∀ i≤j, π(x_j)=x_i}`, not the full product; prefer surjective bonding maps.
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

### A2b — General (correlated/entangled) case: the Kolmogorov extension. **(L/XL, well-scoped — NOT M.)**
Finite-fiber route (the one to take). Each `α j` is *finite discrete*. **Do NOT start with inner
regularity** (Lean tarpit). Two sub-routes, try the first:
- **(i-a) Topology-free (try first).** From `projectiveFamilyContent_iUnion_le`: `c s ≤ ∑' c sₙ`; from
  finite additivity + monotonicity: `∑_{n∈F} c sₙ ≤ c s` for every finite `F`, so `∑' c sₙ ≤ c s`; hence
  equality ⇒ countable additivity on the cylinder algebra. Then `Content.measure`/`Measure.ofAddContent`
  plumbing + "measure agrees with content on cylinders" + marginal ext.
- **(i-b) Compact-open (fallback).** Finite discrete fibers ⇒ compact product; cylinders are clopen
  compact; a countable disjoint cylinder cover of a compact cylinder is *finite* (finite subcover +
  disjointness ⇒ the rest empty) ⇒ finite additivity gives countable additivity. Key lemma:
  `compact C, open Dₙ, disjoint, C = ⋃ Dₙ ⟹ ∃ finite F, C = ⋃_{F} Dₙ ∧ ∀ n∉F, Dₙ=∅`.
- *Hooks:* `projectiveFamilyContent_iUnion_le`, `AddContent`, `Measure.ofAddContent`/`Content.measure`,
  discrete `MeasurableSpace`/`DiscreteTopology`+`CompactSpace` (only for i-b). Construct on the
  inverse-limit subtype (review §0b.4), not the full product.
- *(ii) General standard-Borel Kolmogorov extension — DROP for now* (broad Mathlib contribution; not needed
  for finite fibers).

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
- **Recommended first move (resequenced per review §0b.7):** start with a **zero-quantum-content smoke
  test** — a pure `FiniteMarginals` structure (`μ : ∀ J:Finset ι, ProbabilityMeasure (∀ j:J, α j)` +
  restriction-consistency) and prove the **product case via `infinitePi`** with `μ∞.map (eval J) = μ_J`.
  This confirms the `Finset ι` shape is compatible with Mathlib BEFORE wiring in Born/quantum content.
  THEN: A2b finite-fiber correlated extension (i-a first) → marginals/covariance/no-signaling → refactor
  Born weights through A0 (with the §0b.1 compatibility constraint + CHSH/Fine sanity check) → Phase B cited.
  *Do not* claim A2a (i.i.d.) as the prize result, and *do not* claim entangled no-signaling data alone
  determine a global selector measure.

**Net.** Phase A converts the finite premeasure into the actual measure μ over λ (the prize object) —
**product case reachable now**, general case = one finite-fiber Kolmogorov-extension contribution.
Phase B is the operator-algebra wall, staged with cited inputs. This is the first concrete, mostly
Mathlib-supported path to the continuum μ, replacing the former blank "long pole."
