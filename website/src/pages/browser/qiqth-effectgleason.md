---
layout: ../../layouts/Deep.astro
title: QIQTH.EffectGleason
eyebrow: EffectGleason · section of the QIQT-H book
description: QIQTH.EffectGleason — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← DifferentialAreaLaw](/browser/qiqth-differentialarealaw) · [EinsteinEquationOfState →](/browser/qiqth-einsteinequationofstate) </small>

<small>EffectGleason · entries 74–76 of 1000</small>

<a id="d-qiqth-effectgleason-iseffect"></a>
**Definition 74** (`IsEffect`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EffectGleason.lean#L36)</small>

An **effect** is a positive-semidefinite matrix `E` with `1 - E` also PSD, i.e. `0 ≤ E ≤ 1` in the Löwner order — the yes-part of a POVM.

$$
\mathrm{IsEffect}\,d\,E \;:=\; E.\mathrm{PosSemidef} \wedge (1 - E).\mathrm{PosSemidef}
$$

<small>Used by [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality).</small>

<a id="d-qiqth-effectgleason-effectmeasure"></a>
**Lemma 75** (`EffectMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EffectGleason.lean#L392)</small>

A **finite effect measure** (generalized probability measure on effects): normalized, nonnegative, and **effect-algebra (partially) additive** — additive on *coexistent* pairs `E, F` (those with `E + F` still an effect, i.e. `E + F ≤ 1`).  This is the standard Busch/CFMR hypothesis; effect-Gleason gives `μ E = tr(ρ E)`.

$$
\mathbb{N} \to Type
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality), [`μ`](/browser/qiqth-effectgleason#d-qiqth-effectgleason-effectmeasure).</small>

<a id="d-qiqth-effectgleason-effectmeasure"></a>
**Definition 76** (`μ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EffectGleason.lean#L397)</small>

$$
\mu\,d\,\mathrm{self} \;:=\; \mathrm{self}.1
$$

<small>Used by [`finite_noCollapseBorn_fromNoncontextuality`](/browser/qiqth-bornjoingleason#d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality).</small>

---
<small>[← all sections](/browser) · [← DifferentialAreaLaw](/browser/qiqth-differentialarealaw) · [EinsteinEquationOfState →](/browser/qiqth-einsteinequationofstate) </small>