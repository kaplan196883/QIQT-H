---
layout: ../../layouts/Deep.astro
title: QIQTH.HregExplicitKG
eyebrow: HregExplicitKG · section of the QIQT-H book
description: QIQTH.HregExplicitKG — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← GaussianMode](/browser/qiqth-gaussianmode) · [KGStressConservation →](/browser/qiqth-kgstressconservation) </small>

<small>HregExplicitKG · entries 445–447 of 1000</small>

<a id="d-qiqth-curvature-kglagr-contdiff"></a>
**Lemma 445** (`kgLagr_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/HregExplicitKG.lean#L23)</small>

The KG Lagrangian scalar is `C^∞`.

$$
({\varphi})\in C^{\infty} \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to ({\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr}{\mathrm{kgLagr}}\,m\,\varphi\,\mathrm{gi}})\in C^{\infty}
$$

*Proof.* By [`contDiff_pd`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-contdiff-pd), [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd). $\square$

<small>Used by [`kgStress_contDiff`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-kgstress-contdiff).</small>

<a id="d-qiqth-curvature-kgstress-contdiff"></a>
**Lemma 446** (`kgStress_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/HregExplicitKG.lean#L35)</small>

The KG stress tensor component `y ↦ kgStress m φ g gi y a b` is `C^∞`.

$$
({\varphi})\in C^{\infty} \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({y})\,a\,b}})\in C^{\infty}
$$

*Proof.* By [`contDiff_pd`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-contdiff-pd), [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`kgLagr_contDiff`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-kglagr-contdiff), [`kgLagr`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr). $\square$

<small>Used by [`hreg_kg`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-hreg-kg).</small>

<a id="d-qiqth-curvature-hreg-kg"></a>
**Lemma 447** (`hreg_kg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/HregExplicitKG.lean#L47)</small>

**The `hreg` input, DISCHARGED for the explicit free Klein–Gordon field (Tier A4).**  For any focusing scalar `f` satisfying `a·kgStress = Ric + f·g`, the `gi`-trace fixes `f = (a·tr(kgStress) − R)/4` (using `∑ gi·g = 4`), which is `C^∞`; hence `f` is differentiable everywhere and `f + ½R` is differentiable.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to ({\varphi})\in C^{\infty} \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (f : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}), (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({y})\,a^{\prime}\,b} = \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (\rho : \mathrm{Fin}\,4), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \wedge \mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({y})}
$$

*Proof.* By [`scalarCurv_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-scalarcurv-contdiff), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`metric_contraction_trace`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-metric-contraction-trace), [`kgStress_contDiff`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-kgstress-contdiff). $\square$

<small>Used by [`qiqt_gr_explicit_kg`](/browser/qiqth-qiqtgrexplicitkg#d-qiqth-wedgekmstogr-qiqt-gr-explicit-kg), [`qiqt_gr_freefield`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

---
<small>[← all sections](/browser) · [← GaussianMode](/browser/qiqth-gaussianmode) · [KGStressConservation →](/browser/qiqth-kgstressconservation) </small>