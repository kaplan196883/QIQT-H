---
layout: ../../layouts/Deep.astro
title: QIQTH.CoreNoCollapse
eyebrow: CoreNoCollapse · section of the QIQT-H book
description: QIQTH.CoreNoCollapse — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← ClausiusToPernull](/browser/qiqth-clausiustopernull) · [Curvature →](/browser/qiqth-curvature) </small>

<small>CoreNoCollapse · entries 13–14 of 1000</small>

<a id="d-qiqth-corenocollapse-jointrecordcontext"></a>
**Lemma 13** (`JointRecordContext`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/CoreNoCollapse.lean#L158)</small>

A **finite record context with subadditive (monotone) joint capacity**.  `jointCost A` is the genuine joint information cost of a set `A` of simultaneously-actual records — monotone, but NOT assumed additive.  `pair_exceeds` is the physical input: any two distinct (objective) records jointly exceed the capacity `Q_max`.

$$
Type1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`Rec`](/browser/qiqth-corenocollapse#d-qiqth-corenocollapse-jointrecordcontext-rec), [`J`](/browser/qiqth-valueselection#d-qiqth-pointervalue-valuecontext-j).</small>

<a id="d-qiqth-corenocollapse-jointrecordcontext-rec"></a>
**Definition 14** (`Rec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/CoreNoCollapse.lean#L163)</small>

$$
\mathrm{Rec}\,\mathrm{self} \;:=\; \mathrm{self}.1
$$

<small>Used by [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality).</small>

---
<small>[← all sections](/browser) · [← ClausiusToPernull](/browser/qiqth-clausiustopernull) · [Curvature →](/browser/qiqth-curvature) </small>