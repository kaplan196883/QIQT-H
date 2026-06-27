---
layout: ../../layouts/Deep.astro
title: QIQTH.LocalizedMode
eyebrow: LocalizedMode · section of the QIQT-H book
description: QIQTH.LocalizedMode — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← KMSCorrelation](/browser/qiqth-kmscorrelation) · [ModularRelativeEntropy →](/browser/qiqth-modularrelativeentropy) </small>

<small>LocalizedMode · entries 490–490 of 1000</small>

<a id="d-qiqth-wedgekmstogr-localized-mode-htkk"></a>
**Lemma 490** (`localized_mode_hTkk`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/LocalizedMode.lean#L32)</small>

**The localization mode from the field — `hTkk` from one universal calibration.**  With the mode taken to be the field's directional derivative `D = ∑ₐ vₐ ∂ₐφ(x)` times a reference profile `g₀` (and `ff' = D·g₀'`), the transparent `hTkk` identity holds for the generator `(x,v)` as soon as `g₀` satisfies the single calibration `(−2π ∫ conj(g₀)·g₀').im = 2π/ℏ`.  The boost charge scales as `D²` (quadratic in the mode), so the classical `(∂φ)²` null energy is reproduced.  No regularity of `g₀` is needed for the identity itself — only the value of its boost-charge integral.

$$
(-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,\theta) \cdot \mathrm{g}^{\prime}\,\theta)).\mathrm{im} = 2 \cdot \pi / \hbar \to 2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({x})})}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,((\sum_{b} v\,b \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({x})}) \cdot \mathrm{g}\,\theta) \cdot ((\sum_{b} v\,b \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({x})}) \cdot \mathrm{g}^{\prime}\,\theta))).\mathrm{im}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian).</small>

---
<small>[← all sections](/browser) · [← KMSCorrelation](/browser/qiqth-kmscorrelation) · [ModularRelativeEntropy →](/browser/qiqth-modularrelativeentropy) </small>