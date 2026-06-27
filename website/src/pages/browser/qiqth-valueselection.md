---
layout: ../../layouts/Deep.astro
title: QIQTH.ValueSelection
eyebrow: ValueSelection · section of the QIQT-H book
description: QIQTH.ValueSelection — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← StripUniqueness](/browser/qiqth-stripuniqueness) · [WedgeKMSToGR →](/browser/qiqth-wedgekmstogr) </small>

<small>ValueSelection · entries 993–996 of 1000</small>

<a id="d-qiqth-pointervalue-valuecontext"></a>
**Lemma 993** (`ValueContext`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ValueSelection.lean#L26)</small>

A capacity-limited measurement context whose records carry **pointer values** in `α`. The physical premise is value-level distinguishability: two records of DIFFERENT value jointly exceed the capacity `Q_max` (different macroscopic outcomes cannot be co-stored). Many records may carry the SAME value — redundancy is allowed.

$$
Type\mathrm{u\_1} \to Type(max1 \mathrm{u\_1})
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`J`](/browser/qiqth-valueselection#d-qiqth-pointervalue-valuecontext-j), [`ctx`](/browser/qiqth-valueselection#d-qiqth-pointervalue-valueselection-ctx).</small>

<a id="d-qiqth-pointervalue-valuecontext-j"></a>
**Definition 994** (`J`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ValueSelection.lean#L31)</small>

$$
J\,\alpha\,\mathrm{self} \;:=\; \mathrm{self}.1
$$

<small>Used by [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality).</small>

<a id="d-qiqth-pointervalue-valueselection"></a>
**Lemma 995** (`ValueSelection`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ValueSelection.lean#L36)</small>

A **run** of a value context: a coactual configuration (capacity-bounded active set) made nonempty by the actuality selector `λ`.

$$
Type\mathrm{u\_1} \to Type(max1 \mathrm{u\_1})
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`ctx`](/browser/qiqth-valueselection#d-qiqth-pointervalue-valueselection-ctx).</small>

<a id="d-qiqth-pointervalue-valueselection-ctx"></a>
**Definition 996** (`ctx`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ValueSelection.lean#L39)</small>

$$
\mathrm{ctx}\,\alpha\,\mathrm{self} \;:=\; \mathrm{self}.1
$$

<small>Used by [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality).</small>

---
<small>[← all sections](/browser) · [← StripUniqueness](/browser/qiqth-stripuniqueness) · [WedgeKMSToGR →](/browser/qiqth-wedgekmstogr) </small>