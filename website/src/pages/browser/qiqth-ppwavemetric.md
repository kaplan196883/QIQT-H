---
layout: ../../layouts/Deep.astro
title: QIQTH.PPWaveMetric
eyebrow: PPWaveMetric · section of the QIQT-H book
description: QIQTH.PPWaveMetric — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← ModularRelativeEntropy](/browser/qiqth-modularrelativeentropy) · [QiqtGrComplete →](/browser/qiqth-qiqtgrcomplete) </small>

<small>PPWaveMetric · entries 534–545 of 1000</small>

<a id="d-qiqth-curvature-ppmetric"></a>
**Definition 534** (`ppMetric`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L23)</small>

The **pp-wave metric** `ds² = 2 du dv + H du² + dx² + dy²`, coords `(u,v,x,y) = (0,1,2,3)`: `g₀₀ = H`, `g₀₁ = g₁₀ = 1`, `g₂₂ = g₃₃ = 1`, rest `0`.

$$
g^{\mathrm{pp}}\,H\,x\,a\,b \;:=\; \text{if }a = 0 \wedge b = 0\text{ then }H\,x\text{ else }\text{if }a = 0 \wedge b = 1 \vee a = 1 \wedge b = 0\text{ then }1\text{ else }\text{if }a = 2 \wedge b = 2 \vee a = 3 \wedge b = 3\text{ then }1\text{ else }0
$$

<small>Used by [`ppMetric_symm`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric-symm), [`ppMetric_inv`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric-inv), [`ppMetric_contDiff`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric-contdiff), [`ppFrame_cong`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe-cong), [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave), [`qiqt_gr_ppwave_showcase`](/browser/qiqth-qiqtgrshowcase#d-qiqth-wedgekmstogr-qiqt-gr-ppwave-showcase).</small>

<a id="d-qiqth-curvature-ppmetricinv"></a>
**Definition 535** (`ppMetricInv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L31)</small>

The **inverse pp-wave metric**: `gi₀₁ = gi₁₀ = 1`, `gi₁₁ = −H`, `gi₂₂ = gi₃₃ = 1`, rest `0`.

$$
(g^{\mathrm{pp}})^{-1}\,H\,x\,a\,b \;:=\; \text{if }a = 0 \wedge b = 1 \vee a = 1 \wedge b = 0\text{ then }1\text{ else }\text{if }a = 1 \wedge b = 1\text{ then }-H\,x\text{ else }\text{if }a = 2 \wedge b = 2 \vee a = 3 \wedge b = 3\text{ then }1\text{ else }0
$$

<small>Used by [`ppMetric_inv`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric-inv), [`ppMetricInv_symm`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetricinv-symm), [`ppMetricInv_contDiff`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetricinv-contdiff), [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave), [`qiqt_gr_ppwave_showcase`](/browser/qiqth-qiqtgrshowcase#d-qiqth-wedgekmstogr-qiqt-gr-ppwave-showcase).</small>

<a id="d-qiqth-curvature-ppmetric-symm"></a>
**Lemma 536** (`ppMetric_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L38)</small>

$$
\href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric}{g^{\mathrm{pp}}}\,H\,x\,a\,b = \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric}{g^{\mathrm{pp}}}\,H\,x\,b\,a
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppmetric-inv"></a>
**Lemma 537** (`ppMetric_inv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L42)</small>

$$
\sum_{\sigma} \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric}{g^{\mathrm{pp}}}\,H\,x\,a\,\sigma \cdot \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetricinv}{(g^{\mathrm{pp}})^{-1}}\,H\,x\,\sigma\,b = \delta_{ab}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppmetricinv-symm"></a>
**Lemma 538** (`ppMetricInv_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L47)</small>

$$
\href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetricinv}{(g^{\mathrm{pp}})^{-1}}\,H\,x\,a\,b = \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetricinv}{(g^{\mathrm{pp}})^{-1}}\,H\,x\,b\,a
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppmetric-contdiff"></a>
**Lemma 539** (`ppMetric_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L129)</small>

The pp-wave metric components are `C^∞` when `H` is (`hCg`): each is `H` or a constant.

$$
({H})\in C^{\infty} \to \forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric}{g^{\mathrm{pp}}}\,H\,y\,a\,b})\in C^{\infty}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppmetricinv-contdiff"></a>
**Lemma 540** (`ppMetricInv_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L135)</small>

The inverse pp-wave metric components are `C^∞` when `H` is (`hCgi`): each is `−H` or a constant.

$$
({H})\in C^{\infty} \to \forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetricinv}{(g^{\mathrm{pp}})^{-1}}\,H\,y\,a\,b})\in C^{\infty}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppframe"></a>
**Definition 541** (`ppFrame`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L149)</small>

The pp-wave **coframe** `P_{ab} = e^a_b`.

$$
\mathrm{ppFrame}\,H\,x\,a\,b \;:=\; \text{if }a = 0 \wedge b = 0\text{ then }(H\,x - 1) / 2\text{ else }\text{if }a = 1 \wedge b = 0\text{ then }(H\,x + 1) / 2\text{ else }\text{if }a = 0 \wedge b = 1 \vee a = 1 \wedge b = 1\text{ then }1\text{ else }\text{if }a = 2 \wedge b = 2 \vee a = 3 \wedge b = 3\text{ then }1\text{ else }0
$$

<small>Used by [`ppFrame_cong`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe-cong), [`ppFrame_pp`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe-pp), [`ppFrame_pp'`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe-pp), [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppframeinv"></a>
**Definition 542** (`ppFrameInv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L157)</small>

The inverse frame `Pinv = P⁻¹`.

$$
\mathrm{ppFrameInv}\,H\,x\,a\,b \;:=\; \text{if }a = 0 \wedge b = 0\text{ then }-1\text{ else }\text{if }a = 0 \wedge b = 1\text{ then }1\text{ else }\text{if }a = 1 \wedge b = 0\text{ then }(H\,x + 1) / 2\text{ else }\text{if }a = 1 \wedge b = 1\text{ then }-(H\,x - 1) / 2\text{ else }\text{if }a = 2 \wedge b = 2 \vee a = 3 \wedge b = 3\text{ then }1\text{ else }0
$$

<small>Used by [`ppFrame_pp`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe-pp), [`ppFrame_pp'`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe-pp), [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppframe-cong"></a>
**Lemma 543** (`ppFrame_cong`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L166)</small>

**`hcong` for the pp-wave**: `g_{ij} = ∑_{kl} P_{ki} gm_{kl} P_{lj}` (the metric is the Minkowski reference pulled back by the tetrad).

$$
\href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric}{g^{\mathrm{pp}}}\,H\,x\,i\,j = \sum_{k} \sum_{l} \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe}{\mathrm{ppFrame}}\,H\,x\,k\,i \cdot \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe}{\mathrm{ppFrame}}\,H\,x\,l\,j
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppframe-pp"></a>
**Lemma 544** (`ppFrame_pp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L173)</small>

**`hPP` for the pp-wave**: `∑_k P_{ik} Pinv_{kj} = δ_{ij}`.

$$
\sum_{k} \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe}{\mathrm{ppFrame}}\,H\,x\,i\,k \cdot \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframeinv}{\mathrm{ppFrameInv}}\,H\,x\,k\,j = \delta_{ij}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

<a id="d-qiqth-curvature-ppframe-pp"></a>
**Lemma 545** (`ppFrame_pp'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/PPWaveMetric.lean#L179)</small>

**`hPP'` for the pp-wave**: `∑_k Pinv_{ik} P_{kj} = δ_{ij}`.

$$
\sum_{k} \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframeinv}{\mathrm{ppFrameInv}}\,H\,x\,i\,k \cdot \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe}{\mathrm{ppFrame}}\,H\,x\,k\,j = \delta_{ij}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave).</small>

---
<small>[← all sections](/browser) · [← ModularRelativeEntropy](/browser/qiqth-modularrelativeentropy) · [QiqtGrComplete →](/browser/qiqth-qiqtgrcomplete) </small>