# BORN-A1 — Actuality Projective Consistency: grounding the Born additivity bridge

**Status:** PLAN (not started). **Track:** Born. **Goal:** replace the bare effect-algebra additivity premise
(the "Born in disguise" input) with a more primitive, **amplitude-free** principle — *Actuality Projective
Consistency* (APC): the actuality selector λ is refinement/prefix-consistent (no-signaling at the selector
layer). Prove **APC ⟹ additivity ⟹ Born**, reframing Born's discriminating premise as selector microcausality
rather than an algebraic Born postulate.

## 0. The exact target

The Born capstone `QIQTH.BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality`
(`BornJoinGleason.lean:49`) consumes `M : EffectMeasure d` whose load-bearing field is
```lean
-- EffectGleason.lean:396
structure EffectMeasure (d) where
  μ : Matrix (Fin d) (Fin d) ℂ → ℝ
  normalized : μ 1 = 1
  nonneg : ∀ E, IsEffect E → 0 ≤ μ E
  additive : ∀ E F, IsEffect E → IsEffect F → IsEffect (E + F) → μ (E + F) = μ E + μ F
```
`finite_effect_gleason` (`EffectGleason.lean:839`) proves **additive ⟹ trace/Born form**.  The discriminating
power is entirely in `additive`: `WeakStrongSplit.weak_underdetermines_born` (`WeakStrongSplit.lean:92`) shows
relabelling-naturality is `f`-blind (the α-family `f=(·)²` satisfies it but is non-Born), and
`RefinementBorn.refinementNatural_additive` (`RefinementBorn.lean:156`) + `continuous_additive_fMeasure_eq_born`
(`:95`) show **refinement-naturality ⟹ f additive ⟹ Born**.  So additivity ≈ Born.  The honest question: is
there an amplitude-free principle on the *selector* that *implies* this additivity without itself being an
algebraic Born postulate?

## 1. The lever — selector-layer refinement consistency

`SelectorRefinement.lean` already has the Born-free no-signaling primitive:
```lean
-- SelectorRefinement.lean:46
theorem readout_invariant_marg (μ : Ω → ℝ) (XL : Ω → K) (R : Ω → Ω)
    (hloc : ∀ ω, XL (R ω) = XL ω) (k : K) : marg μ (fun ω => XL (R ω)) k = marg μ XL k
```
and a *separation*: the α=2 selector on 15 uniform microstates gives coarse marginal `12/15` but fine marginals
summing to `10/15` (`SelectorRefinement.lean:81`) — so **selector no-signaling FAILS for α≠1**.  This is exactly
a discriminator that is amplitude-free and physically motivated (microcausality at the selector layer, a
principle QIQT-H independently holds), and the α-family violates it.

## 2. Stages (each axiom-free, green-building, one commit)

### Stage 1 — define APC `QIQTH/BornActualityConsistency.lean` *(definition + basic lemmas)*
Define **Actuality Projective Consistency**: an amplitude-free condition on the actuality measure stating that,
under any refinement `R` that leaves the coarse readout invariant (`XL ∘ R = XL`), the coarse actuality marginal
equals the refined marginal (Kolmogorov/prefix consistency).  Phrase it on the existing
`SelectorRefinement`/`CoarseGrainNaturality` substrate so it composes.  Prove the trivial sanity lemmas (Born/α=1
satisfies APC; the structure is non-degenerate).  **Risk: low.**

### Stage 2 — APC ⟹ additivity *(the crux)*
Prove the key lemma: APC (selector refinement-consistency) forces the induced weight rule to be
**refinement-additive** (`f(a+b)=f(a)+f(b)`, i.e. `WeakStrongSplit.RefinementAdditive` /
`RefinementBorn.refinementNatural`).  Route: a refinement that splits one coarse atom into two fine atoms,
readout-invariant on the rest; APC equates the coarse marginal with the sum of the two fine marginals; unfolding
the `f`-rule gives the additivity functional equation.  **Risk: medium–high** — this is where the real content
is, and where it may turn out APC is *equivalent* to additivity rather than strictly weaker (see §4 fallback).

### Stage 3 — APC ⟹ Born *(compose)*
Compose Stage 2 with the existing `refinementNatural_additive` + `continuous_additive_fMeasure_eq_born` (and/or
`finite_effect_gleason`) to get **APC ⟹ Born weights**.  Deliver a Born statement conditional on APC instead of
bare additivity — ideally a variant of the capstone taking an APC hypothesis that internally builds the
`EffectMeasure.additive` field.  **Risk: medium** (wiring).

### Stage 4 — non-vacuity + honest analysis
Prove the α=2 selector **violates** APC (reuse/extend the `SelectorRefinement.lean:81` 15-microstate
separation), certifying APC is a genuine discriminator, not vacuous.  Document the honest limit (see §4).

## 3. Honest outcome

This **reframes** the Born bridge: from "assume effect-algebra additivity" (an algebraic Born postulate) to
"assume the actuality selector is microcausal / no-signaling under refinement" — a principle QIQT-H already
holds for independent (Lorentz/locality) reasons.  Born then follows.  The α-family violating APC certifies it
is non-trivial.

## 4. The honest limit (stated up front, not hidden)

APC is expected to be **logically equivalent** to additivity at the linear level (any principle strong enough to
give Born is "Born in disguise" somewhere).  So the deliverable is a **grounding/reframing** — Born from selector
no-signaling, with the discriminating premise relocated to a physically-motivated, amplitude-free, independently-
held principle — **not** a strict from-nothing derivation.  If Stage 2 shows strict equivalence (APC ⟺ additive),
that equivalence theorem + the non-vacuity witness (Stage 4) IS the honest result; we do **not** dress up a
circular derivation as a discharge.  This is the same discipline as the GR localization (construct, don't fake).

## 5. Verification (per stage)
- `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green.
- `#print axioms <thm>` = `[propext, Classical.choice, Quot.sound]`; `bash scripts/axiom_budget_check.sh` budget 0.
- Wire new file into `QIQTH.lean` + `AxiomAudit`. One commit per stage, `Co-Authored-By` trailer.

### Progress log
- **Stage 1 ✅** (`marg_coarseGrain`, `QIQTH/BornActualityConsistency.lean`) — the structural foundation of APC:
  a genuine coarse-graining selector `π ∘ selF` has Kolmogorov-consistent marginals (coarse marginal = sum of
  fine marginals over the merge fiber) — selector no-signaling under refinement, automatic, NO Born input. The
  α=2 rule fails this (`alphaSq_selector_signals`) because its coarse/fine realizations aren't genuine
  refinements — the non-vacuity witness. Axiom-free, budget 0.
- **Stage 2 ✅ — §4 limit reached** (`apc_iff_positiveAdditive`, same file) — **APC ⟺ additivity**: for a rule
  `p ∝ f` positive on positive weights, `RefinementNatural f` (selector no-signaling under outcome-refinement)
  is *logically equivalent* to additivity of `f`. So APC is the honest §4 outcome — a **grounding/reframing**
  (Born's discriminating premise relocated to "the actuality selector is microcausal/no-signaling under
  refinement," a principle QIQT-H independently holds), **not** a strict from-nothing derivation. Axiom-free,
  budget 0.

### COMPLETE — the honest result
The chain is **APC ⟺ additive ⟹ Born**: `apc_iff_positiveAdditive` (APC ⟺ additive) + the existing
`RefinementBorn.continuous_additive_fMeasure_eq_born` (additive ⟹ Born), with `marg_coarseGrain` (honest
refinements satisfy APC automatically) and `RefinementBorn.alphaSq_refinement_violation` (the α=2 rule violates
APC — non-vacuity). Per §4, we **stop at the equivalence** rather than dress up a circular "from-nothing"
derivation: APC is logically equivalent to additivity, so the deliverable is the equivalence + the physical
reframing + the non-vacuity witness. Stages 3 (a packaged `apc ⟹ Born` needs the Cauchy `ℝ→+ℝ` hom-extension —
not pursued, it would only re-package `continuous_additive_fMeasure_eq_born`) and 4 (non-vacuity, already in
`RefinementBorn`) are folded into this. **Born's additivity bridge is now grounded in selector no-signaling.**
