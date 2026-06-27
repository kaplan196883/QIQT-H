---
layout: ../../layouts/Deep.astro
title: QIQTH.ModularRelativeEntropy
eyebrow: ModularRelativeEntropy · section of the QIQT-H book
description: QIQTH.ModularRelativeEntropy — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← LocalizedMode](/browser/qiqth-localizedmode) · [PPWaveMetric →](/browser/qiqth-ppwavemetric) </small>

<small>ModularRelativeEntropy · entries 491–533 of 1000</small>

<a id="d-qiqth-rvdspecmeasure"></a>
**Definition 491** (`rvdSpecMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L44)</small>

**The scalar spectral measure of `R = P + Q` at the one-particle vector `ξ`** — a finite measure on `spectrum ℝ R`, with total mass `‖ξ‖²`.

$$
\mu^{R}\,H\,S\,\xi \;:=\; (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots ).\mu\,\xi
$$

<small>Used by [`borelFC_congr_ae`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), [`borelFC_apply_norm_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-apply-norm-sq), [`rvdSpec_borelFC_diag`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspec-borelfc-diag), [`rvdSpecMeasure_zero_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-zero-levelset), [`rvdSpecMeasure_two_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-two-levelset), [`rvdSpecMeasure_endpoints`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-endpoints), and 6 more.</small>

<a id="d-qiqth-devspecreal"></a>
**Definition 492** (`devSpecReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L434)</small>

The **device spectral symbol on the real axis** `ω ↦ d_t(ω) = u_t(ω)·√ω`, the bounded measurable function of `R` whose functional calculus is the real-axis device operator `Δ^{it}·√R`.

$$
\chi_{\mathrm{dev}}\,H\,S\,t\,\omega \;:=\; \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,t\,\omega
$$

<small>Used by [`devSpecReal_measurable`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-measurable), [`devSpecReal_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-norm-le), [`deviceOpReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-devspecreal-measurable"></a>
**Lemma 493** (`devSpecReal_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L439)</small>

$$
\mathrm{Measurable}\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal}{\chi_{\mathrm{dev}}}\,S\,t)
$$

*Proof.* By [`devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar), [`measurable_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-devchar). $\square$

<small>Used by [`deviceOpReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-devspecreal-norm-le"></a>
**Lemma 494** (`devSpecReal_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L442)</small>

$$
\|\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal}{\chi_{\mathrm{dev}}}\,S\,t\,\omega\| \le \sqrt 2
$$

*Proof.* By [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`devChar_norm_le_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-le-icc). $\square$

<small>Used by [`deviceOpReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-deviceopreal"></a>
**Definition 495** (`deviceOpReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L447)</small>

The **real-axis device operator** `Δ^{it}·√R = d_t(R)`, the bounded Borel functional calculus of `R` at the device symbol `devSpecReal` (`‖d_t‖ ≤ √2` on the spectrum, no regular window).

$$
\mathrm{dev}\,H\,S\,t \;:=\; \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots \,\cdots \,\mathrm{\_proof\_1}\,\cdots
$$

<small>Used by [`deviceOpC_ofReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-ofreal), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), [`deviceVecF_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-real-eq).</small>

<a id="d-qiqth-deviceopc"></a>
**Definition 496** (`deviceOpC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L453)</small>

The **complex-`z` device operator** `d_z(R) = (2−R)^{iz} R^{−iz+1/2}` for `z` in the half-strip `−1/2 ≤ Im z ≤ 0`, where `‖d_z‖ ≤ √2` on `σ(R) ⊆ [0,2]` (no regular window, `devChar_norm_le_Icc` + `rvdRC_spectrum_mem_Icc`).  This is RvD's Proposition 3.7 *device* (verified against the rendered source): the operator whose `J`-image `J·(d_z(R) ζ)` is the (anti-holomorphic, since `J` is antilinear) second-slot vector of the Theorem 3.8 g-function `g(z) = ⟨h(z), J d_z(R) ζ⟩`.  Generalizes `deviceOpReal` (the `z = t` real-axis case) to the whole half-strip.

$$
\mathrm{dev}_{\mathbb{C}}\,H\,S\,z \;:=\; \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots \,\cdots \,\mathrm{\_proof\_1}\,\cdots
$$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`modConj_deviceOpC_neg_half`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [`modConj_deviceVecF_bottom_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq), [`deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf), [`deviceVecF_eq_of_mem`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-eq-of-mem), [`deviceOpC_ofReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-ofreal), [`deviceOpC_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-norm-le), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), and 9 more.</small>

<a id="d-qiqth-devicevecf"></a>
**Definition 497** (`deviceVecF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L465)</small>

**Total device-vector function** `z ↦ deviceOpC(z)ζ` (piece 4 of the strong holomorphy): a `dite`-total function on all of `ℂ`, equal to `deviceOpC(z)ζ` on the closed half-strip `{−1/2 ≤ Im z ≤ 0}` (where the device operator's `√2` bound holds) and `0` outside.  The totality sidesteps the `deviceOpC`-takes-proofs friction: `HasDerivAt (deviceVecF S ζ)` is a statement about a genuine `ℂ → H` function, provable at every interior `z₀` because `deviceVecF` agrees with the `borelFC` branch on a neighborhood.  Its Fréchet derivative is `borelFC(ω ↦ i·log((2−ω)/ω)·d_{z₀}(ω))ζ`, with `‖slope − deriv‖² = ∫‖Δ_z − ∂d‖² dμ^R_ζ → 0` (`borelFC_sub` + `borelFC_smul` + `borelFC_apply_norm_sq` + `tendsto_integral_devChar_remainder_sq`).

$$
\mathrm{dev}\,H\,S\,\zeta\,z \;:=\; ifh : z.\mathrm{im} \le 0 \wedge -(1/2) \le z.\mathrm{im}then(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\cdots \,\cdots )\,\zetaelse0
$$

<small>Used by [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire), [`gFunction_top_edge_real_all`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [`gConstancy_entire_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), and 22 more.</small>

<a id="d-qiqth-devicevecf-eq-of-mem"></a>
**Lemma 498** (`deviceVecF_eq_of_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L475)</small>

On the closed half-strip, `deviceVecF` is the device operator applied to `ζ` (proof-irrelevant `dite`).

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z = (\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1})\,\zeta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`hasDerivAt_deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-hasderivat-devicevecf), [`deviceVecF_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-real-eq), [`deviceVecF_bottom_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-bottom-eq), [`deviceVecF_continuousOn`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-continuouson).</small>

<a id="d-qiqth-deviceopc-ofreal"></a>
**Lemma 499** (`deviceOpC_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L480)</small>

**`deviceOpC` at a real point is `deviceOpReal`** (`d_{(t:ℂ)} = d_t`): the half-strip device operator restricts to the real-axis device operator `Δ^{it}·√R` on the boundary `Im z = 0`.

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,t\,\cdots \,\cdots = \href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal}{\mathrm{dev}}\,S\,t
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`deviceVecF_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-real-eq).</small>

<a id="d-qiqth-deviceopc-norm-le"></a>
**Lemma 500** (`deviceOpC_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L485)</small>

**Operator-norm bound for the complex-`z` device operator**: `‖d_z(R)‖ ≤ 2√2` uniformly on the half-strip `−1/2 ≤ Im z ≤ 0` (the bounded-FC norm bound `‖borelFC f‖ ≤ 2·sup‖f‖` applied to the device symbol bound `‖d_z‖ ≤ √2`).  This is the operator-level boundedness the g-function `g(z) = ⟨h(z), J d_z(R) ζ⟩` consumes: `‖g(z)‖ ≤ ‖h(z)‖·‖d_z(R)ζ‖ ≤ ‖h(z)‖·2√2·‖ζ‖`, uniform over the half-strip.

$$
\|\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1}\| \le 2 \cdot \sqrt 2
$$

*Proof.* By [`boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [`boundedFC_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar). $\square$

<small>Used by [`deviceVecF_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-norm-le).</small>

<a id="d-qiqth-deviceopreal-zero"></a>
**Lemma 501** (`deviceOpReal_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L495)</small>

**The device operator at `z = 0` is `√R`** (`deviceOpReal 0 = rvdSqrtR`, the device interpolation start). `devChar 0 = √·`, so `deviceOpReal 0 = borelFC(√·) = cfcCont(√·)`, and `cfcCont(√·)` is the *positive* square root of `R`: `(cfcCont √·)² = R` (`cfcCont_mul` + `cfcCont_coord`, since `√ω·√ω = ω` on `σ(R)⊆[0,∞)`), and `cfcCont(√·) = (cfcCont ∜·)² ≥ 0` (`cfcCont ∜·` self-adjoint as a real symbol).  `CFC.sqrt_unique` then identifies it with `CFC.sqrt R = rvdSqrtR`.  Hence `deviceOpReal 0 ζ = R^{1/2}ζ = ξ`, so the g-function's value at the origin is `g(0) = ⟪η, Jξ⟫` — the right-hand side of `GConstancy`.

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal}{\mathrm{dev}}\,S\,0 = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S
$$

*Proof.* By [`devSpecReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal), [`devSpecReal_measurable`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-measurable), [`devSpecReal_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-norm-le), [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`cfcCont_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-mul), [`cfcCont_star`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-star), [`cfcCont_coord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-coord), [`devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar), [`devChar_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-zero). $\square$

<small>Used by [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-cfccont-sqrttwosub-eq"></a>
**Lemma 502** (`cfcCont_sqrtTwoSub_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L541)</small>

**The continuous symbol `√(2−·)` gives `√(2−R)`**: `cfcCont(√(2−·)) = rvdSqrtTwoSubR` (the bottom-edge analogue of `deviceOpReal_zero`, which does `cfcCont(√·) = √R`).  Route: the square is `2−R` (`cfcCont_mul` + `cfcCont(2−coord) = 2−R` via `cfcCont_add`/`_smul`/`_one`/`_coord`, since `√(2−ω)·√(2−ω) = 2−ω` on `σ(R) ⊆ [0,2]`), and `cfcCont(√(2−·)) = (cfcCont ∜(2−·))² ≥ 0`; `CFC.sqrt_unique` then identifies it with `CFC.sqrt(2−R) = rvdSqrtTwoSubR`.  This is the CONTINUOUS half of `deviceOpC(−i/2) = √(2−R)`; the device character `d_{−i/2}` then matches `√(2−·)` only μ-a.e. (they swap at the spectral endpoints `{0,2}`), closed by `borelFC_congr_ae` + `rvdSpecMeasure_endpoints`.

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,\{\mathrm{toFun} :=\lambda \omega \mapsto \sqrt (2 - \omega) , \mathrm{continuous\_toFun} :=\cdots \} = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S
$$

*Proof.* By [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`cfcCont_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-one), [`cfcCont_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-mul), [`cfcCont_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-add), [`cfcCont_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-smul), [`cfcCont_star`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-star), [`cfcCont_coord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-coord). $\square$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq).</small>

<a id="d-qiqth-deviceopreal-eq"></a>
**Lemma 503** (`deviceOpReal_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L605)</small>

**The real-axis device operator factors as `Δ^{it}·√R`**: `deviceOpReal t = modUnitary S t · rvdSqrtR` (the general top-edge operator identity, `deviceOpReal_zero` is the `t = 0` case).  `devChar(↑t) = u_t·√·` (`devChar_ofReal`), so `borelFC(devChar ↑t) = borelFC(u_t)·borelFC(√·) = Δ^{it}·√R` (`borelFC_mul` + `modUnitary = borelFC(u_t)` + `borelFC(√·) = rvdSqrtR` from `deviceOpReal_zero`).  Hence the device vector at the real axis is `deviceVec(t) = deviceOpReal t ζ = Δ^{it}(√R ζ) = Δ^{it}ξ`, so the g-function's top edge is `g(t) = ⟪U_t η, J Δ^{it} ξ⟫` (`gTopEdge_real`, real).

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal}{\mathrm{dev}}\,S\,t = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S
$$

*Proof.* By [`devSpecReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal), [`devSpecReal_measurable`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-measurable), [`devSpecReal_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-norm-le), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`modChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`modSpecFun`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun), [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable), [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`devChar_ofReal`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-ofreal), [`devChar_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-zero). $\square$

<small>Used by [`deviceVecF_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-real-eq).</small>

<a id="d-qiqth-borelfc-inner-self"></a>
**Lemma 504** (`borelFC_inner_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L632)</small>

**`L²` identity for the bounded Borel FC**: `⟪f(R)ζ, f(R)ζ⟫ = ∫ conj(f)·f dμ^R_ζ` (`= ∫|f|² dμ`, so `‖f(R)ζ‖² = ∫|f|² dμ^R_ζ`).  Via `⟪Aζ,Aζ⟫ = ⟪ζ, A*Aζ⟫` (`adjoint_inner_right`), `A* = borelFC(conj f)` (`borelFC_adjoint`), `A*·A = borelFC(conj f·f)` (`borelFC_mul`), then the spectral bridge `⟪ζ, g(R)ζ⟫ = ∫ g dμ^R_ζ` (`inner_borelFC`).  This is the linchpin for the strong (Fréchet) holomorphy of `z ↦ d_z(R)ζ`: the difference-quotient remainder `q − d` satisfies `‖q − d‖² = ∫|Δ_z − ∂_z d|² dμ^R_ζ → 0` by dominated convergence (the derivative is dominated by the `devChar_deriv_norm_le` constant).

$$
\langle {(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots \,\mathrm{hg}\,\mathrm{hC0}\,\mathrm{hC})\,\zeta},{(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots \,\mathrm{hg}\,\mathrm{hC0}\,\mathrm{hC})\,\zeta}\rangle = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S))), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,\omega) \cdot g\,\omega \partial \href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`inner_borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-borelfc), [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul), [`borelFC_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-adjoint). $\square$

<small>Used by [`borelFC_apply_norm_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-apply-norm-sq).</small>

<a id="d-qiqth-borelfc-apply-norm-sq"></a>
**Lemma 505** (`borelFC_apply_norm_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L656)</small>

**`L²` isometry (real form)**: `‖f(R)ζ‖² = ∫ ‖f(ω)‖² dμ^R_ζ`.  The real-valued restatement of `borelFC_inner_self` (`⟪f(R)ζ,f(R)ζ⟫ = ↑‖f(R)ζ‖²`, and `conj(f)·f = ↑‖f‖²`).  This is the form the strong-holomorphy difference-quotient argument uses directly: `‖q_z − d‖² = ∫‖Δ_z − ∂_z d‖² dμ^R_ζ → 0`.

$$
{\|(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots \,\mathrm{hg}\,\mathrm{hC0}\,\mathrm{hC})\,\zeta\|}^{2} = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S))), {\|g\,\omega\|}^{2} \partial \href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta
$$

*Proof.* By [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self). $\square$

<small>Used by [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq), [`deviceOpC_diff_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-diff-normsq).</small>

<a id="d-qiqth-rvdspec-borelfc-diag"></a>
**Lemma 506** (`rvdSpec_borelFC_diag`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L677)</small>

**Diagonal of the bounded Borel FC against the spectral measure**: `⟪x, f(R)x⟫ = ∫ f dμ^R_x`.  The linear (un-conjugated) companion to `borelFC_inner_self`, via the spectral bridge (`inner_borelFC` + `bilinDiag_self` + `diagInt`).  This is the bridge for `borelFC_congr_ae` (`borelFC` depends only on the `μ^R_x`-a.e. class of `f`): combined with `clm_eq_of_inner_self_eq` it gives `borelFC(f) = borelFC(g)` whenever `f =ᵐ g` for every spectral measure — the tool for `deviceOpC(−i/2) = √(2−R)` (the device character and `√(2−r)` differ only on the `E`-null endpoints).

$$
\langle {x},{(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots \,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC})\,x}\rangle = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S))), f\,\omega \partial \href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`inner_borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-borelfc). $\square$

<small>Used by [`borelFC_congr_ae`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-borelfc-congr-ae).</small>

<a id="d-qiqth-rvdspecmeasure-zero-levelset"></a>
**Lemma 507** (`rvdSpecMeasure_zero_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L690)</small>

**No spectral atom at `0`**: `μ^R_x({λ = 0}) = 0`, from `E({0}) = 0` (`rvdRC_E_zero_levelSet`).

$$
(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x)\,\{\omega|\omega = 0\} = 0
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`rvdRC_E_zero_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset). $\square$

<small>Used by [`rvdSpecMeasure_endpoints`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-endpoints).</small>

<a id="d-qiqth-rvdspecmeasure-two-levelset"></a>
**Lemma 508** (`rvdSpecMeasure_two_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L701)</small>

**No spectral atom at `2`**: `μ^R_x({λ = 2}) = 0`, from `E({2}) = 0` (`rvdRC_E_two_levelSet`).

$$
(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x)\,\{\omega|\omega = 2\} = 0
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`rvdRC_E_two_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset). $\square$

<small>Used by [`rvdSpecMeasure_endpoints`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-endpoints).</small>

<a id="d-qiqth-rvdspecmeasure-endpoints"></a>
**Lemma 509** (`rvdSpecMeasure_endpoints`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L712)</small>

**The device-character endpoints are `μ^R_x`-null**: `μ^R_x({λ ∈ {0,2}}) = 0`.  This is exactly the a.e.-equality input for `borelFC_congr_ae` needed for `deviceOpC(−i/2) = √(2−R)`: the device character `d_{−i/2}` and the symbol `√(2−r)` of `√(2−R)` differ ONLY at the spectral endpoints `{0,2}`, which carry no spectral mass (no atom at `0` or `2`, as `R` and `2−R` are injective).

$$
(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x)\,\{\omega|\omega = 0 \vee \omega = 2\} = 0
$$

*Proof.* By [`rvdSpecMeasure_zero_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-zero-levelset), [`rvdSpecMeasure_two_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-two-levelset). $\square$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq).</small>

<a id="d-qiqth-deviceopc-bottomedge-eq"></a>
**Lemma 510** (`deviceOpC_bottomEdge_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L724)</small>

**Bottom-edge `t`-translation of the device operator**: `deviceOpC(t − i/2) = Δ^{it}·deviceOpC(−i/2)` (the bottom-edge analogue of `deviceOpReal_eq`).  `devChar(↑t − i/2) = u_t·devChar(−i/2)` EVERYWHERE (via `modCharC_add`: `u_{↑t + (−i/2)} = u_{↑t}·u_{−i/2}`, no endpoint issue), so `borelFC` factors through `borelFC_mul` into `modUnitary t · deviceOpC(−i/2)`.  Hence the device vector along the bottom edge is `deviceVec(t − i/2) = Δ^{it}·deviceVec(−i/2)` — the modular flow translating the fixed bottom-edge vector.

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(t - i / 2)\,\cdots \,\cdots = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t \cdot \href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`modChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`modSpecFun`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun), [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable), [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`modCharC_ofReal`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-ofreal), [`modCharC_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-add), [`devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar), [`measurable_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-devchar), [`devChar_norm_le_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-le-icc). $\square$

<small>Used by [`deviceVecF_bottom_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-bottom-eq).</small>

<a id="d-qiqth-devcharderiv-norm-le-slab"></a>
**Lemma 511** (`devCharDeriv_norm_le_slab`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L778)</small>

**Derivative-norm bound of the device character on a slab** (the `‖∂_z d_z(ω)‖ ≤ C` companion to `devChar_slope_norm_le`): on `{−β₁ < Im w < −β₀}`, `‖i·log((2−ω)/ω)·d_w(ω)‖ ≤ C` uniformly in `ω` (`devChar_deriv_norm_le` for `ω ∈ (0,2)`; the coefficient vanishes for `ω ∈ {0,2}`).  This bounds the candidate Fréchet derivative `∂_z d` at every slab point — used as the second half of the dominating constant `4C²` in the strong-holomorphy dominated-convergence step.

$$
0 < \beta_{0} \to \beta_{1} < 1/2 \to \forall \{w : \mathbb{C}\}, w \in \mathrm{im} ^{-1}{}' ({-\beta_{1}},{-\beta_{0}}) \to \|i \cdot (\log\,((2 - \omega) / \omega)) \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,w\,\omega\| \le \sqrt 2 \cdot (2 / \beta_{0} + \log\,2) + \sqrt 2 \cdot (2 / (1/2 - \beta_{1}) + \log\,2)
$$

*Proof.* By [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`devChar_deriv_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le). $\square$

<small>Used by [`tendsto_integral_devChar_remainder_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-remainder-sq), [`deviceDerivOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicederivopc), [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq).</small>

<a id="d-qiqth-devchar-slope-norm-le"></a>
**Lemma 512** (`devChar_slope_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L807)</small>

**Uniform slope (Lipschitz) bound of the device character on a slab** (piece 2 of the strong-holomorphy dominated-convergence argument): on the open slab `s = {−β₁ < Im z < −β₀} ⊂ (−1/2,0)`, `‖d_z(ω) − d_{z₀}(ω)‖ ≤ C·‖z − z₀‖` with `C = √2(2/β₀+log2) + √2(2/(1/2−β₁)+log2)` the `devChar_deriv_norm_le` constant — UNIFORM in the spectral point `ω`.  Via the complex mean-value inequality `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` (`hasDerivAt_devChar_Icc` on the convex slab + the `devChar_deriv_norm_le` derivative bound, with `ω ∈ {0,2}` giving `d_z` `z`-constant ⇒ derivative `0 ≤ C`).  Hence `‖Δ_z(ω)‖ ≤ C` uniformly: the dominating constant for the dominated-convergence step.

$$
0 < \beta_{0} \to \beta_{1} < 1/2 \to \forall \{z z_{0} : \mathbb{C}\}, z \in \mathrm{im} ^{-1}{}' ({-\beta_{1}},{-\beta_{0}}) \to z_{0} \in \mathrm{im} ^{-1}{}' ({-\beta_{1}},{-\beta_{0}}) \to \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\| \le (\sqrt 2 \cdot (2 / \beta_{0} + \log\,2) + \sqrt 2 \cdot (2 / (1/2 - \beta_{1}) + \log\,2)) \cdot \|z - z_{0}\|
$$

*Proof.* By [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`devChar_deriv_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le), [`hasDerivAt_devChar_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc). $\square$

<small>Used by [`tendsto_integral_devChar_remainder_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-remainder-sq).</small>

<a id="d-qiqth-tendsto-devchar-slope"></a>
**Lemma 513** (`tendsto_devChar_slope`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L857)</small>

**Pointwise difference-quotient convergence of the device character** (piece 1 of the strong-holomorphy dominated-convergence argument): for each spectral point `ω`, the slope `(d_z(ω) − d_{z₀}(ω))/(z − z₀) → i·log((2−ω)/ω)·d_{z₀}(ω)` as `z → z₀` (`z ≠ z₀`).  Immediate from `hasDerivAt_devChar_Icc` via `hasDerivAt_iff_tendsto_slope` (`slope_def_field`).  Fed into `tendsto_integral_filter_of_dominated_convergence` to drive `∫‖Δ_z − ∂_z d‖² dμ^R_ζ → 0`, hence the Fréchet derivative of `z ↦ deviceOpC(z)ζ` (via `borelFC_sub` + `borelFC_apply_norm_sq`).

$$
\mathrm{Tendsto}\,(\lambda z \mapsto (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega) / (z - z_{0}))\,(\mathcal{N}\,z_{0}\,\{z_{0}\}^{c})\,(\mathcal{N}\,(i \cdot (\log\,((2 - \omega) / \omega)) \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega))
$$

*Proof.* By [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`hasDerivAt_devChar_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc). $\square$

<small>Used by [`tendsto_integral_devChar_remainder_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-remainder-sq).</small>

<a id="d-qiqth-tendsto-integral-devchar-remainder-sq"></a>
**Lemma 514** (`tendsto_integral_devChar_remainder_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L874)</small>

**Strong-holomorphy dominated convergence** (piece 3 — the heart): the `L²` remainder of the device-vector difference quotient vanishes, `∫‖(d_z(ω)−d_{z₀}(ω))/(z−z₀) − ∂_z d_{z₀}(ω)‖² dμ^R_ζ → 0` as `z → z₀` (`z ≠ z₀`), for `z₀` in the slab.  Lebesgue dominated convergence (`tendsto_integral_filter_of_dominated_convergence`): the integrand `→ 0` pointwise (`tendsto_devChar_slope`, piece 1) and is dominated by the constant `4C²` (`devChar_slope_norm_le` + `devCharDeriv_norm_le_slab`, piece 2: `‖Δ_z(ω)‖ ≤ C`, `‖∂d(ω)‖ ≤ C`), integrable on the finite measure `μ^R_ζ`.  Combined with `borelFC_sub` + `borelFC_apply_norm_sq` (`‖slope − d‖² = ∫‖Δ_z − ∂d‖² dμ`), this gives the Fréchet derivative of `z ↦ deviceOpC(z)ζ`.

$$
0 < \beta_{0} \to \beta_{1} < 1/2 \to \forall \{z_{0} : \mathbb{C}\}, z_{0} \in \mathrm{im} ^{-1}{}' ({-\beta_{1}},{-\beta_{0}}) \to \mathrm{Tendsto}\,(\lambda z \mapsto \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S))), {\|(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega) / (z - z_{0}) - i \cdot (\log\,((2 - \omega) / \omega)) \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\|}^{2} \partial \href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta)\,(\mathcal{N}\,z_{0}\,\{z_{0}\}^{c})\,(\mathcal{N}\,0)
$$

*Proof.* By [`devCharDeriv_norm_le_slab`](/browser/qiqth-modularrelativeentropy#d-qiqth-devcharderiv-norm-le-slab), [`devChar_slope_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devchar-slope-norm-le), [`tendsto_devChar_slope`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-devchar-slope), [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`instIsFiniteMeasure_scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`measurable_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-devchar). $\square$

<small>Used by [`hasDerivAt_deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-hasderivat-devicevecf).</small>

<a id="d-qiqth-deviceopc-sub"></a>
**Lemma 515** (`deviceOpC_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L950)</small>

**Device-operator difference as a single `borelFC`** (first step of the slope operator-algebra): `deviceOpC(z) − deviceOpC(z₀) = borelFC(d_z − d_{z₀})`.  Just `borelFC_sub` read backwards, using that `deviceOpC` is definitionally a `borelFC` with the `√2` bound.

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1} - \href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z_{0}\,\mathrm{hz02}\,\mathrm{hz01} = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots \,\cdots \,\cdots \,\cdots
$$

*Proof.* By [`borelFC_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-sub). $\square$

<small>Used by [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq), [`deviceOpC_diff_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-diff-normsq).</small>

<a id="d-qiqth-devicederivopc"></a>
**Definition 516** (`deviceDerivOpC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L972)</small>

**Candidate Fréchet derivative operator of the device** at an interior point: `∂_z d_{z₀}(R) = borelFC(ω ↦ i·log((2−ω)/ω)·d_{z₀}(ω))`, the spectral operator whose symbol is the `z`-derivative of the device character at `z₀`.  Bounded by the `devCharDeriv_norm_le_slab` constant `C(β₀,β₁)` (the operator is independent of the slab `(β₀,β₁) ∋ Im z₀`, by `borelFC_congr`).  Applied to `ζ` it is the Fréchet derivative of `deviceVecF S ζ` at `z₀` (`hasDerivAt_deviceVecF`).

$$
\mathrm{dev}'\,H\,S\,z_{0}\,\beta_{0}\,\beta_{1} \;:=\; \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,\cdots \,\cdots \,\cdots \,\cdots
$$

<small>Used by [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq), [`hasDerivAt_deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-hasderivat-devicevecf), [`differentiableOn_deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-differentiableon-devicevecf).</small>

<a id="d-qiqth-deviceopc-slope-normsq"></a>
**Lemma 517** (`deviceOpC_slope_normSq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L991)</small>

**`L²` identity for the device-vector slope remainder** (the operator-algebra heart of piece 4): `‖(z−z₀)⁻¹·(deviceOpC(z)ζ − deviceOpC(z₀)ζ) − deviceDerivOpC(z₀)ζ‖² = ∫‖Δ_z(ω) − ∂d(ω)‖² dμ^R_ζ`, the integrand of `tendsto_integral_devChar_remainder_sq`.  The slope-minus-derivative vector is a single `borelFC` applied to `ζ` (`deviceOpC_sub` + `borelFC_smul` + `borelFC_sub`, pushed through the CLM `sub_apply`/`smul_apply`), so `borelFC_apply_norm_sq` turns its norm² into the spectral `L²` integral.

$$
{\|{(z - z_{0})}^{-1} \cdot ((\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1})\,\zeta - (\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z_{0}\,\mathrm{hz02}\,\mathrm{hz01})\,\zeta) - (\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicederivopc}{\mathrm{dev}{}'}\,S\,z_{0}\,h\beta_{0}\,h\beta_{1}\,\mathrm{hz}_{0})\,\zeta\|}^{2} = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S))), {\|(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega) / (z - z_{0}) - i \cdot (\log\,((2 - \omega) / \omega)) \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\|}^{2} \partial \href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta
$$

*Proof.* By [`borelFC_apply_norm_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-apply-norm-sq), [`devCharDeriv_norm_le_slab`](/browser/qiqth-modularrelativeentropy#d-qiqth-devcharderiv-norm-le-slab), [`deviceOpC_sub`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-sub), [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`borelFC_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-smul), [`borelFC_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-sub), [`measurable_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-devchar), [`devChar_norm_le_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-le-icc). $\square$

<small>Used by [`hasDerivAt_deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-hasderivat-devicevecf).</small>

<a id="d-qiqth-hasderivat-devicevecf"></a>
**Lemma 518** (`hasDerivAt_deviceVecF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1015)</small>

**Strong (Fréchet) holomorphy of the device vector** (piece 4 COMPLETE): `z ↦ deviceOpC(z)ζ` is complex-differentiable at every interior point `z₀` of the open half-strip, with derivative `deviceDerivOpC(z₀)ζ`.  The slope-minus-derivative norm `→ 0`: its square is the remainder integral (`deviceOpC_slope_normSq`) which `→ 0` (`tendsto_integral_devChar_remainder_sq`), so `‖slope − deriv‖ = √(remainder) → √0 = 0` (`Real.sqrt` continuity), hence `slope → deriv` (`tendsto_iff_norm_sub_tendsto_zero`).  This defeats the holomorphy wall WITHOUT Mathlib's missing weak⟹strong (Dunford): the H-valued derivative is obtained from a scalar dominated-convergence integral.

$$
({\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta})'({z_{0}})={(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicederivopc}{\mathrm{dev}{}'}\,S\,z_{0}\,h\beta_{0}\,h\beta_{1}\,\mathrm{hz}_{0})\,\zeta}
$$

*Proof.* By [`rvdSpecMeasure`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure), [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), [`deviceVecF_eq_of_mem`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-eq-of-mem), [`tendsto_integral_devChar_remainder_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-remainder-sq), [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar). $\square$

<small>Used by [`differentiableOn_deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-differentiableon-devicevecf).</small>

<a id="d-qiqth-differentiableon-devicevecf"></a>
**Lemma 519** (`differentiableOn_deviceVecF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1048)</small>

**The device vector is holomorphic on the open half-strip** (piece 4 ⇒ `DifferentiableOn`): immediate from `hasDerivAt_deviceVecF` at every interior point (choosing the slab `β₀ = −Im z₀/2`, `β₁ = (1/2 − Im z₀)/2` around `z₀`).  This is the strong-holomorphic half-strip input the g-function Phragmén–Lindelöf constancy consumes — now available for the device vector of EVERY standard subspace.

$$
\mathrm{DifferentiableOn}\,\mathbb{C}\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta)\,(\mathrm{im} ^{-1}{}' ({-(1/2)},{0}))
$$

*Proof.* By [`deviceDerivOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicederivopc), [`hasDerivAt_deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-hasderivat-devicevecf). $\square$

<small>Used by [`differentiableOn_gFunction`](/browser/qiqth-modularrelativeentropy#d-qiqth-differentiableon-gfunction).</small>

<a id="d-qiqth-devicevecf-real-eq"></a>
**Lemma 520** (`deviceVecF_real_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1062)</small>

**Real-axis value of the device vector**: `deviceVecF(t) = Δ^{it}·√R ζ` (the top-edge value of the g-function).  Via `deviceVecF_eq_of_mem` (the strip contains the real axis), `deviceOpC_ofReal` (`d_{(t:ℂ)} = d_t`), and `deviceOpReal_eq` (`d_t = Δ^{it}·√R`).  With `ξ = √R ζ`, `J·deviceVecF(t) = JΔ^{it}ξ = Δ^{it}(Jξ)` is the second slot of the g-function on its real edge `g(t) = ⟪V_t η, Δ^{it}Jξ⟫`.

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,t = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)
$$

*Proof.* By [`deviceOpReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal), [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), [`deviceVecF_eq_of_mem`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-eq-of-mem), [`deviceOpC_ofReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-ofreal), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq). $\square$

<small>Used by [`deviceVecF_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-zero), [`gFunction_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-real-eq).</small>

<a id="d-qiqth-differentiableon-gfunction"></a>
**Lemma 521** (`differentiableOn_gFunction`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1072)</small>

**The device-vector RvD g-function is HOLOMORPHIC on the open half-strip** (piece 2 of the endgame): `g(z) = ⟪J·d_z(R)ζ, V_z η⟫ = modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)` is complex-differentiable on `{−1/2 < Im z < 0}`.  It is the continuous ℂ-bilinear form `modConjBilin` (`= ⟪J·,·⟫`, holomorphic by the J-cancellation) applied to the two HOLOMORPHIC curves: the device vector `deviceVecF` (`differentiableOn_deviceVecF`, the strong-holomorphy result) and the entire V-orbit `gaussSmearC` (`differentiable_gaussSmearC`).  Bilinear chain rule (`DifferentiableOn.clm_apply`).  This is the holomorphic strip function the Phragmén–Lindelöf constancy `g(t) = g(0) ⟹ GConstancy` consumes.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{DifferentiableOn}\,\mathbb{C}\,(\lambda z \mapsto ((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z))\,(\mathrm{im} ^{-1}{}' ({-(1/2)},{0}))
$$

*Proof.* By [`differentiableOn_deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-differentiableon-devicevecf), [`differentiable_gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-differentiable-gausssmearc). $\square$

<small>Used by [`diffContOnCl_gFunction`](/browser/qiqth-modularrelativeentropy#d-qiqth-diffcontoncl-gfunction).</small>

<a id="d-qiqth-devicevecf-zero"></a>
**Lemma 522** (`deviceVecF_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1089)</small>

**Device vector at the origin**: `deviceVecF(0) = √R ζ` (`= ξ`, the comparison point).  From `deviceVecF_real_eq` at `t = 0` (`Δ^{i·0} = 1`, `modUnitary_zero`).

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,0 = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta
$$

*Proof.* By [`deviceVecF_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-real-eq), [`modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary), [`modUnitary_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-zero). $\square$

<small>Used by [`gFunction_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-zero).</small>

<a id="d-qiqth-gfunction-zero"></a>
**Lemma 523** (`gFunction_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1098)</small>

**g-function value at the origin** `g(0) = ⟪J ξ, η_n⟫` (`ξ = √R ζ`, `η_n = gaussSmear`): the comparison point of the Phragmén–Lindelöf constancy.  With `g` constant this equals `g(t)`, the top-edge matrix element — the heart of RvD Theorem 3.8.  Via `deviceVecF_zero` + `gaussSmearC_zero`.

$$
((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,0))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,0) = \langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)},{\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta}\rangle
$$

*Proof.* By [`deviceVecF_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-zero), [`modConjBilin_apply`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin-apply), [`gaussSmearC_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-zero). $\square$

<small>Used by [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire).</small>

<a id="d-qiqth-gfunction-real-eq"></a>
**Lemma 524** (`gFunction_real_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1107)</small>

**g-function value on the real axis (top edge)** `g(t) = ⟪Δ^{it}(J ξ), V_t η_n⟫` (`ξ = √R ζ`): via `deviceVecF_real_eq` (`d_t ζ = Δ^{it}√R ζ`), `gaussSmearC_ofReal` (`h(t) = V_t η_n`), and `modConj_commute_modUnitary` (`JΔ^{it} = Δ^{it}J`).  Its conjugate is the GConstancy LHS `⟪V_t η_n, Δ^{it}Jξ⟫`; reality (RvD top edge) makes `g(t)` equal to it.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to \forall (t : \mathbb{R}), ((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,t))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,t) = \langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))},{(V\,t)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)}\rangle
$$

*Proof.* By [`deviceVecF_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-real-eq), [`modConjBilin_apply`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin-apply), [`modConj_commute_modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-commute-modunitary), [`gaussSmearC_ofReal`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-ofreal). $\square$

<small>Used by [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire), [`gFunction_top_edge_real`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-top-edge-real).</small>

<a id="d-qiqth-gfunction-top-edge-real"></a>
**Lemma 525** (`gFunction_top_edge_real`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1120)</small>

**Top-edge reality of the g-function** (RvD Theorem 3.8, the real-axis edge): for `ξ = √R ζ ∈ 𝒦` and the V-orbit staying in `𝒦`, `g(t) = ⟪Δ^{it}(Jξ), V_t η_n⟫` is REAL.  `Δ^{it}(Jξ) = J(Δ^{it}ξ)` (`modConj_commute_modUnitary`) with `Δ^{it}ξ ∈ 𝒦` (`modUnitary_mapsTo_K`), so `J(Δ^{it}ξ) ⊥ i𝒦` (`projIK_modConj_eq_zero_of_mem_K`, `J𝒦 = (i𝒦)^⊥`); pairing it against the `𝒦`-vector `V_t η_n` is real (`inner_real_of_mem_K_perp_IK`, RvD Prop 2.3) — and `g(t)` is the conjugate of that.  Geometric, no analysis; the real-axis edge of the holomorphic strip g-function feeding the Phragmén–Lindelöf constancy.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (t : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)\,((V\,t)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,t)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta) \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,t))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,t)).\mathrm{im} = 0
$$

*Proof.* By [`gFunction_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-real-eq), [`modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj), [`projIK_modConj_eq_zero_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k), [`inner_real_of_mem_K_perp_IK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik), [`modUnitary_mapsTo_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [`modConj_commute_modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-commute-modunitary). $\square$

<small>Used by [`gFunction_top_edge_real_all`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all).</small>

<a id="d-qiqth-devicevecf-bottom-eq"></a>
**Lemma 526** (`deviceVecF_bottom_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1138)</small>

**Bottom-edge value of the device vector**: `deviceVecF(t − i/2) = Δ^{it}·deviceOpC(−i/2) ζ`, the modular flow translating the FIXED bottom vector `deviceOpC(−i/2) ζ` (`= √(2−R) ζ` off the spectral endpoints `{0,2}`).  Via `deviceVecF_eq_of_mem` (the closed half-strip contains the mid-line `Im z = −1/2`) and `deviceOpC_bottomEdge_eq`.  This is the second-slot device vector on the bottom edge of the g-function, whose reality is the KMS input (`HalfStripReal`) feeding the Phragmén–Lindelöf constancy.

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2) = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots )\,\zeta)
$$

*Proof.* By [`deviceVecF_eq_of_mem`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-eq-of-mem), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq). $\square$

<small>Used by [`modConj_deviceVecF_bottom`](/browser/qiqth-modularrelativeentropy#d-qiqth-modconj-devicevecf-bottom).</small>

<a id="d-qiqth-modconj-devicevecf-bottom"></a>
**Lemma 527** (`modConj_deviceVecF_bottom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1156)</small>

**Device/J commute on the bottom edge**: `J·deviceVecF(t − i/2) = Δ^{it}·(J·deviceOpC(−i/2) ζ)`.  The modular conjugation pulls through `Δ^{it}` (`modConj_commute_modUnitary`) after `deviceVecF_bottom_eq`. With `deviceOpC(−i/2) = √(2−R)` and `J √(2−R) ζ = √R ζ` (`modConj_rvdSqrtTwoSubR_of_fixed`, `J ζ = ζ`) this becomes `Δ^{it}·√R ζ = Δ^{it}ξ` — the second slot of the g-function bottom edge `g(t − i/2)`, whose reality is the KMS input (RvD's `(2−R)^{1/2}ζ = Jξ` device argument).

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)) = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots )\,\zeta))
$$

*Proof.* By [`deviceVecF_bottom_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-bottom-eq), [`modConj_commute_modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-commute-modunitary). $\square$

<small>Used by [`modConj_deviceVecF_bottom_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq).</small>

<a id="d-qiqth-devicevecf-norm-le"></a>
**Lemma 528** (`deviceVecF_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1170)</small>

**Uniform bound of the device vector** `‖deviceVecF z‖ ≤ 2√2·‖ζ‖` for EVERY `z` (the device operator's `2√2` operator-norm bound, `deviceOpC_norm_le`, applied to `ζ`; `0` off the strip).  The bounded factor of the g-function `‖g(z)‖ ≤ 2√2·‖ζ‖·‖h(z)‖`, the bound input the Phragmén–Lindelöf constancy needs.

$$
\|\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z\| \le 2 \cdot \sqrt 2 \cdot \|\zeta\|
$$

*Proof.* By [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), [`deviceOpC_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-norm-le). $\square$

<small>Used by [`gFunction_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-norm-le).</small>

<a id="d-qiqth-gfunction-norm-le"></a>
**Lemma 529** (`gFunction_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1182)</small>

**Pointwise bound of the g-function** `‖g(z)‖ ≤ 2√2·‖ζ‖·‖h(z)‖` (`h(z) = gaussSmearC`): `J` is an isometry (`modConj_norm`) and `‖d_z(R)ζ‖ ≤ 2√2·‖ζ‖` (`deviceVecF_norm_le`), so the inner product is bounded by the product (`norm_inner_le_norm`).  Combined with the Gaussian bound on `‖h(z)‖` this gives the uniform strip bound the Phragmén–Lindelöf constancy consumes.

$$
\|((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)\| \le 2 \cdot \sqrt 2 \cdot \|\zeta\| \cdot \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z\|
$$

*Proof.* By [`deviceVecF_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-norm-le), [`modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj), [`modConj_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-norm), [`modConjBilin_apply`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin-apply). $\square$

<small>Used by [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const).</small>

<a id="d-qiqth-deviceopc-diff-normsq"></a>
**Lemma 530** (`deviceOpC_diff_normSq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1198)</small>

**`L²` identity for the device-vector difference**: `‖deviceOpC(z)ζ − deviceOpC(z₀)ζ‖² = ∫‖d_z(ω) − d_{z₀}(ω)‖² dμ^R_ζ`.  The difference is a single `borelFC` applied to `ζ` (`deviceOpC_sub`), so `borelFC_apply_norm_sq` turns its norm² into the spectral `L²` integral.  Feeds the device-vector continuity (`∫‖d_z − d_{z₀}‖² → 0` by dominated convergence, `d_z` continuous + dominated by `2√2`) — the continuity-to-closure half of `DiffContOnCl` for the g-function.

$$
{\|(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1})\,\zeta - (\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z_{0}\,\mathrm{hz02}\,\mathrm{hz01})\,\zeta\|}^{2} = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S))), {\|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\|}^{2} \partial \href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta
$$

*Proof.* By [`borelFC_apply_norm_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-apply-norm-sq), [`deviceOpC_sub`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-sub), [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`measurable_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-devchar), [`devChar_norm_le_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-le-icc). $\square$

<small>Used by [`deviceVecF_continuousOn`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-continuouson).</small>

<a id="d-qiqth-tendsto-integral-devchar-diff-sq"></a>
**Lemma 531** (`tendsto_integral_devChar_diff_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1213)</small>

**Device-character `L²` continuity** (dominated convergence): `∫‖d_z(ω) − d_{z₀}(ω)‖² dμ^R_ζ → 0` as `z → z₀` within the closed half-strip `{−1/2 ≤ Im z ≤ 0}`.  The integrand `→ 0` pointwise (`d_z` continuous in `z`, `hasDerivAt_devChar_Icc.continuousAt`) and is dominated by `(√2+√2)² = 8` (`devChar_norm_le_Icc`), integrable on the finite spectral measure.  With `deviceOpC_diff_normSq` this gives the device-vector continuity `‖deviceVecF z − deviceVecF z₀‖ = √(∫…) → 0` — the continuity-to-closure half of `DiffContOnCl`.

$$
z_{0}.\mathrm{im} \le 0 \to -(1/2) \le z_{0}.\mathrm{im} \to \mathrm{Tendsto}\,(\lambda z \mapsto \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S))), {\|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\|}^{2} \partial \href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta)\,(\mathcal{N}\,z_{0}\,(\mathrm{im} ^{-1}{}' [{-(1/2)},{0}]))\,(\mathcal{N}\,0)
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`instIsFiniteMeasure_scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`measurable_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-devchar), [`devChar_norm_le_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-le-icc), [`hasDerivAt_devChar_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc). $\square$

<small>Used by [`deviceVecF_continuousOn`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-continuouson).</small>

<a id="d-qiqth-devicevecf-continuouson"></a>
**Lemma 532** (`deviceVecF_continuousOn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1257)</small>

**The device vector is continuous on the closed half-strip** (the `DiffContOnCl` continuity-to-closure): `ContinuousOn (deviceVecF S ζ) {−1/2 ≤ Im z ≤ 0}`.  At each `z₀`, `‖deviceVecF z − deviceVecF z₀‖ = √(∫‖d_z − d_{z₀}‖² dμ^R_ζ)` (`deviceVecF_eq_of_mem` + `deviceOpC_diff_normSq` + `Real.sqrt_sq`), which `→ √0 = 0` (`tendsto_integral_devChar_diff_sq` + `Real.sqrt` continuity).  Together with `differentiableOn_deviceVecF` this is the device-vector half of `DiffContOnCl` for the g-function.

$$
\mathrm{ContinuousOn}\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta)\,(\mathrm{im} ^{-1}{}' [{-(1/2)},{0}])
$$

*Proof.* By [`rvdSpecMeasure`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure), [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), [`deviceVecF_eq_of_mem`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-eq-of-mem), [`deviceOpC_diff_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-diff-normsq), [`tendsto_integral_devChar_diff_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-diff-sq), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar). $\square$

<small>Used by [`diffContOnCl_gFunction`](/browser/qiqth-modularrelativeentropy#d-qiqth-diffcontoncl-gfunction).</small>

<a id="d-qiqth-diffcontoncl-gfunction"></a>
**Lemma 533** (`diffContOnCl_gFunction`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1279)</small>

**The g-function is bounded-holomorphic (`DiffContOnCl`) on the half-strip** (the full analytic regularity for Phragmén–Lindelöf): holomorphic on the open half-strip (`differentiableOn_gFunction`) and continuous up to the closure `{−1/2 ≤ Im z ≤ 0}` (the bilinear `modConjBilin` of the continuous device vector `deviceVecF_continuousOn` and the continuous V-orbit `gaussSmearC`).  With the uniform bound (`gFunction_norm_le`) and the two edge realities this is the exact input the half-strip constancy consumes.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{DiffContOnCl}\,\mathbb{C}\,(\lambda z \mapsto ((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z))\,(\mathrm{im} ^{-1}{}' ({-(1/2)},{0}))
$$

*Proof.* By [`differentiableOn_gFunction`](/browser/qiqth-modularrelativeentropy#d-qiqth-differentiableon-gfunction), [`deviceVecF_continuousOn`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-continuouson), [`differentiable_gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-differentiable-gausssmearc). $\square$

<small>Used by [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const).</small>

---
<small>[← all sections](/browser) · [← LocalizedMode](/browser/qiqth-localizedmode) · [PPWaveMetric →](/browser/qiqth-ppwavemetric) </small>