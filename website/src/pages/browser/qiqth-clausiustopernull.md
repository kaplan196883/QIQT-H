---
layout: ../../layouts/Deep.astro
title: QIQTH.ClausiusToPernull
eyebrow: ClausiusToPernull · section of the QIQT-H book
description: QIQTH.ClausiusToPernull — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← ClausiusFiniteWitness](/browser/qiqth-clausiusfinitewitness) · [CoreNoCollapse →](/browser/qiqth-corenocollapse) </small>

<small>ClausiusToPernull · entries 12–12 of 1000</small>

<a id="d-qiqth-curvature-bl-smul-sub"></a>
**Lemma 12** (`BL_smul_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ClausiusToPernull.lean#L35)</small>

**`BL` is linear in its tensor argument**: `BL(a·T − R) = a·BL T − BL R`. The bilinear form `∑_{ij} C_{ij} v^i v^j` distributes over the heat tensor `a·T − Ric`.

$$
\href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({\lambda i j \mapsto a \cdot T\,i\,j - R\,i\,j})({v},{v})} = a \cdot \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({T})({v},{v})} - \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({R})({v},{v})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`bl_pernull_of_modular`](/browser/qiqth-qiqttogr#d-qiqth-qiqttogr-bl-pernull-of-modular).</small>

---
<small>[← all sections](/browser) · [← ClausiusFiniteWitness](/browser/qiqth-clausiusfinitewitness) · [CoreNoCollapse →](/browser/qiqth-corenocollapse) </small>