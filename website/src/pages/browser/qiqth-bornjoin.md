---
layout: ../../layouts/Deep.astro
title: QIQTH.BornJoin
eyebrow: BornJoin · section of the QIQT-H book
description: QIQTH.BornJoin — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [BornJoinGleason →](/browser/qiqth-bornjoingleason) </small>

<small>BornJoin · entries 1–3 of 1000</small>

<a id="d-qiqth-bornjoin-actualensemble"></a>
**Lemma 1** (`ActualEnsemble`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/BornJoin.lean#L64)</small>

**The join model.**  A finite ensemble of worlds; in each world every trial runs a capacity-limited value selection; the single-trial Born law `p` calibrates the one-site mass (`oneSite`); trials are independent (`indep`).

$$
\mathbb{N} \to \mathbb{N} \to Type1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`Ω`](/browser/qiqth-bornjoin#d-qiqth-bornjoin-actualensemble), [`p`](/browser/qiqth-bornjoin#d-qiqth-bornjoin-actualensemble-p), [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality).</small>

<a id="d-qiqth-bornjoin-actualensemble"></a>
**Definition 2** (`Ω`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/BornJoin.lean#L68)</small>

$$
\Omega\,m\,n\,\mathrm{self} \;:=\; \mathrm{self}.1
$$

<small>Used by [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality).</small>

<a id="d-qiqth-bornjoin-actualensemble-p"></a>
**Definition 3** (`p`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/BornJoin.lean#L75)</small>

the single-trial Born law (e.g. `OneSiteBorn.bornVec ψ`)

$$
p\,m\,n\,\mathrm{self} \;:=\; \mathrm{self}.6
$$

<small>Used by [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality).</small>

---
<small>[← all sections](/browser) · [BornJoinGleason →](/browser/qiqth-bornjoingleason) </small>