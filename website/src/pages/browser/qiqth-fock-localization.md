---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.Localization
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.Localization — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← FreeFieldHFlux](/browser/qiqth-fock-freefieldhflux) · [OneParticle →](/browser/qiqth-fock-oneparticle) </small>

<small>Fock · entries 236–269 of 1000</small>

<a id="d-qiqth-fock-localization-v"></a>
**Definition 236** (`V`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L33)</small>

1+1D Minkowski spacetime (coordinates `(t, x) = (z 0, z 1)`).

$$
V \;:=\; \mathrm{Fin}\,2 \to \mathbb{R}
$$

<small>Used by [`inner_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-krepl2), [`inner_KrepL2_general`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-krepl2-general), [`inner_boostUnitary_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [`symm_edge_eq_shifted`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-shifted), [`symm_edge_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-inner), [`kmsFun`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun), [`kmsFun_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal), [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), and 158 more.</small>

<a id="d-qiqth-fock-localization-minkowskidot"></a>
**Definition 237** (`minkowskiDot`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L36)</small>

**The Minkowski pairing** `η(p, x) = p₀x₀ − p₁x₁` (signature `(+,−)`).

$$
\eta\,p\,x \;:=\; p\,0 \cdot x\,0 - p\,1 \cdot x\,1
$$

<small>Used by [`minkowskiFourier_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-minkowskifourier-smul), [`minkowskiFourier_bumpCW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [`minkowskiDot_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot-boost), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier), [`minkowskiFourier_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-boost), [`minkowskiFourier_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-zero), [`continuous_minkowskiDot_fst`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-continuous-minkowskidot-fst), [`continuous_minkowskiDot_snd`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-continuous-minkowskidot-snd), and 5 more.</small>

<a id="d-qiqth-fock-localization-massshell"></a>
**Definition 238** (`massShell`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L42)</small>

**The positive mass shell** in rapidity coordinates: `p_m(θ) = (m cosh θ, m sinh θ)`.

$$
\mathrm{MS}\,m\,\theta \;:=\; ![m \cdot \cosh\,\theta , m \cdot \sinh\,\theta]
$$

<small>Used by [`Krep_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krep-smul), [`Krep_bumpCW_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [`massShell_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-zero), [`massShell_one`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-one), [`massShell_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-boost), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost), [`Krep_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-zero), and 8 more.</small>

<a id="d-qiqth-fock-localization-lorentzboost"></a>
**Definition 239** (`lorentzBoost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L45)</small>

**The proper rapidity-`a` Lorentz boost** on `V`.

$$
\mathrm{L}\,a\,z \;:=\; ![\cosh\,a \cdot z\,0 + \sinh\,a \cdot z\,1 , \sinh\,a \cdot z\,0 + \cosh\,a \cdot z\,1]
$$

<small>Used by [`lorentzBoost_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-zero), [`lorentzBoost_one`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-one), [`massShell_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-boost), [`minkowskiDot_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot-boost), [`lorentzBoostₗ_apply`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-apply), [`measurePreserving_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurepreserving-lorentzboost), [`measurableEmbedding_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurableembedding-lorentzboost), [`boostTest`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest), and 6 more.</small>

<a id="d-qiqth-fock-localization-massshell-zero"></a>
**Lemma 240** (`massShell_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L49)</small>

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta\,0 = m \cdot \cosh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`massShell_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-boost).</small>

<a id="d-qiqth-fock-localization-massshell-one"></a>
**Lemma 241** (`massShell_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L50)</small>

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta\,1 = m \cdot \sinh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`massShell_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-boost).</small>

<a id="d-qiqth-fock-localization-lorentzboost-zero"></a>
**Lemma 242** (`lorentzBoost_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L51)</small>

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,z\,0 = \cosh\,a \cdot z\,0 + \sinh\,a \cdot z\,1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`massShell_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-boost).</small>

<a id="d-qiqth-fock-localization-lorentzboost-one"></a>
**Lemma 243** (`lorentzBoost_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L53)</small>

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,z\,1 = \sinh\,a \cdot z\,0 + \cosh\,a \cdot z\,1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`massShell_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-boost).</small>

<a id="d-qiqth-fock-localization-massshell-boost"></a>
**Lemma 244** (`massShell_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L56)</small>

**The boost shifts rapidity on the mass shell**: `Λ_a (p_m θ) = p_m (θ + a)`.  This is the geometric heart of boost-equivariance (the boost acts as translation `θ ↦ θ + a` on the shell).

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta) = \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,(\theta + a)
$$

*Proof.* By [`massShell_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-zero), [`massShell_one`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-one), [`lorentzBoost_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-zero), [`lorentzBoost_one`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-one). $\square$

<small>Used by [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost).</small>

<a id="d-qiqth-fock-localization-minkowskidot-boost"></a>
**Lemma 245** (`minkowskiDot_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L67)</small>

**The Minkowski pairing is boost-invariant**: `η(Λ_a p, Λ_a x) = η(p, x)`.

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot}{\eta}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,p)\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,x) = \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot}{\eta}\,p\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`minkowskiFourier_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-boost).</small>

<a id="d-qiqth-fock-localization-lorentzboostmat"></a>
**Definition 246** (`lorentzBoostMat`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L84)</small>

The boost matrix `[[cosh a, sinh a], [sinh a, cosh a]]`.

$$
\mathrm{lorentzBoostMat}\,a \;:=\; !![\cosh\,a , \sinh\,a ; \sinh\,a , \cosh\,a]
$$

<small>Used by [`lorentzBoostₗ`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost), [`lorentzBoostₗ_apply`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-apply), [`det_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-det-lorentzboost).</small>

<a id="d-qiqth-fock-localization-lorentzboost"></a>
**Definition 247** (`lorentzBoostₗ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L88)</small>

The boost packaged as an `ℝ`-linear endomorphism of `V` (via its standard matrix).  Typed on `Fin 2 → ℝ` (rather than the abbrev `V`) so the `volume` Haar instance synthesizes for the measure change-of-variables.

$$
\mathrm{L}\,a \;:=\; \mathrm{toLin}^{\prime}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboostmat}{\mathrm{lorentzBoostMat}}\,a)
$$

<small>Used by [`lorentzBoostₗ_apply`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-apply), [`det_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-det-lorentzboost), [`measurePreserving_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurepreserving-lorentzboost), [`lorentzBoostLE`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboostle), [`measurableEmbedding_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurableembedding-lorentzboost).</small>

<a id="d-qiqth-fock-localization-lorentzboost-apply"></a>
**Lemma 248** (`lorentzBoostₗ_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L102)</small>

$$
(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a)\,z = \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,z
$$

*Proof.* By [`lorentzBoostMat`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboostmat). $\square$

<small>Used by [`measurePreserving_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurepreserving-lorentzboost), [`measurableEmbedding_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurableembedding-lorentzboost).</small>

<a id="d-qiqth-fock-localization-det-lorentzboost"></a>
**Lemma 249** (`det_lorentzBoost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L108)</small>

**The boost is unimodular**: `det Λ_a = cosh²a − sinh²a = 1` — the change of variables `y = Λ_a x` in the spacetime Fourier integral has unit Jacobian (no measure correction).

$$
\mathrm{det}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a) = 1
$$

*Proof.* By [`lorentzBoostMat`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboostmat). $\square$

<small>Used by [`measurePreserving_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurepreserving-lorentzboost).</small>

<a id="d-qiqth-fock-localization-measurepreserving-lorentzboost"></a>
**Lemma 250** (`measurePreserving_lorentzBoost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L114)</small>

**The boost preserves the Lebesgue volume** (unit Jacobian) — the measure-preservation needed for the Fourier change of variables in boost-equivariance.  (Stated on `Fin 2 → ℝ` explicitly so the `volume` Haar instance synthesizes; `V` is the same type but the reducible abbrev blocks instance search.)

$$
\mathrm{MeasurePreserving}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a)\,\mathrm{volume}\,\mathrm{volume}
$$

*Proof.* By [`lorentzBoostₗ`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost), [`lorentzBoostₗ_apply`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-apply), [`det_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-det-lorentzboost). $\square$

<small>Used by [`minkowskiFourier_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-boost).</small>

<a id="d-qiqth-fock-localization-lorentzboostle"></a>
**Definition 251** (`lorentzBoostLE`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L145)</small>

The boost as a (continuous) linear equivalence of `Fin 2 → ℝ` — gives a measurable embedding.

$$
\mathrm{lorentzBoostLE}\,a \;:=\; \mathrm{ofLinear}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a)\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,(-a))\,\cdots \,\cdots
$$

<small>Used by [`measurableEmbedding_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurableembedding-lorentzboost).</small>

<a id="d-qiqth-fock-localization-measurableembedding-lorentzboost"></a>
**Lemma 252** (`measurableEmbedding_lorentzBoost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L153)</small>

The boost is a measurable embedding (it is a continuous linear equivalence).

$$
\mathrm{MeasurableEmbedding}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a)
$$

*Proof.* By [`lorentzBoostₗ`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost), [`lorentzBoostₗ_apply`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost-apply), [`lorentzBoostLE`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboostle). $\square$

<small>Used by [`minkowskiFourier_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-boost).</small>

<a id="d-qiqth-fock-localization-minkowskifourier"></a>
**Definition 253** (`minkowskiFourier`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L165)</small>

**The Minkowski-space Fourier transform** `f̂_M(p) = ∫ e^{−i η(p,x)} f(x) dx`, with the Minkowski pairing in the exponent (signature `(+,−)`; soundness trap #2).

$$
\mathcal{F}\,f\,p \;:=\; \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \exp\,(-i \cdot (\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot}{\eta}\,p\,x)) \cdot f\,x
$$

<small>Used by [`minkowskiFourier_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-minkowskifourier-smul), [`Krep_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krep-smul), [`minkowskiFourier_bumpCW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [`Krep_bumpCW_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [`minkowskiFourier_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-boost), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost), [`minkowskiFourier_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-zero), and 7 more.</small>

<a id="d-qiqth-fock-localization-boosttest"></a>
**Definition 254** (`boostTest`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L170)</small>

**The boost action on test functions** `(β_a f)(x) = f(Λ_a x)`.

$$
\phi_{B}\,a\,f\,x \;:=\; f\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,x)
$$

<small>Used by [`inner_boostUnitary_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [`symm_edge_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-inner), [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [`memLp_Krep_boostTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-memlp-krep-boosttest), [`boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-boost), [`minkowskiFourier_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-boost), [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost), [`boostUnitary_KrepL2`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), and 2 more.</small>

<a id="d-qiqth-fock-localization-minkowskifourier-boost"></a>
**Lemma 255** (`minkowskiFourier_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L173)</small>

**Boost-equivariance of the localization (Fourier) map**: `f̂_M ∘ β_a = U_a ∘ f̂_M`, i.e. `(β_a f)^_M(p) = f̂_M(Λ_a p)`.  A clean change of variables `y = Λ_a x` (unit Jacobian, the boost is volume-preserving and a measurable embedding) plus the Minkowski-pairing boost-invariance.  This is the Phase-1c keystone: it makes the localization intertwine the spacetime boost with the one-particle action.  Holds for ANY `f` (no integrability hypothesis — `MeasurePreserving.integral_comp`).

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,a\,f)\,p = \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,p)
$$

*Proof.* By [`minkowskiDot`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot), [`minkowskiDot_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot-boost), [`measurePreserving_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurepreserving-lorentzboost), [`measurableEmbedding_lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-measurableembedding-lorentzboost). $\square$

<small>Used by [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost).</small>

<a id="d-qiqth-fock-localization-krep"></a>
**Definition 256** (`Krep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L190)</small>

**The localized rapidity amplitude** `(K f)(θ) = 2^{-1/2} · f̂_M(p_m θ)` — the value of the localization map on the positive mass shell, in rapidity coordinates (before the `L²` packaging).  The `1/√2` is the invariant-measure normalization `dp/(2ω) = dθ/2` (soundness trap #1: omitting it scales the symplectic form by 2).

$$
\mathrm{Krep}\,m\,f\,\theta \;:=\; 1 / \sqrt 2 \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta)
$$

<small>Used by [`inner_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-krepl2), [`inner_KrepL2_general`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-krepl2-general), [`inner_boostUnitary_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [`symm_edge_eq_shifted`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-shifted), [`symm_edge_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-inner), [`kmsFun_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal), [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [`kmsFun_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-i), and 68 more.</small>

<a id="d-qiqth-fock-localization-krep-boost"></a>
**Lemma 257** (`Krep_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L197)</small>

**The localization is boost-covariant at the amplitude level**: boosting the spacetime test function *translates* the localized rapidity amplitude, `(K (β_a f))(θ) = (K f)(θ + a)`.  So the Lorentz boost acts on the localized one-particle amplitude as the rapidity translation `θ ↦ θ + a` — exactly the action implemented by the one-particle unitary `OneParticle.boostUnitary`.  Immediate from the Phase-1c keystone `minkowskiFourier_boost` and the shell geometry `massShell_boost`.

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,a\,f)\,\theta = \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta + a)
$$

*Proof.* By [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost), [`massShell_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell-boost), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier), [`minkowskiFourier_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-boost). $\square$

<small>Used by [`inner_boostUnitary_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [`memLp_Krep_boostTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-memlp-krep-boosttest), [`boostUnitary_KrepL2`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [`boostUnitary_mapsTo_wedgeGenSet`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgegenset).</small>

<a id="d-qiqth-fock-localization-minkowskifourier-zero"></a>
**Lemma 258** (`minkowskiFourier_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L306)</small>

The Minkowski-Fourier transform of the zero function is zero.

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,(\lambda x \mapsto 0)\,p = 0
$$

*Proof.* By [`minkowskiDot`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot). $\square$

<small>Used by [`Krep_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-zero).</small>

<a id="d-qiqth-fock-localization-krep-zero"></a>
**Lemma 259** (`Krep_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L310)</small>

The localized amplitude of the zero function is the zero function.

$$
(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,\lambda x \mapsto 0) = 0
$$

*Proof.* By [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier), [`minkowskiFourier_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-zero). $\square$

<small>Used by [`zero_vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-zero-vec).</small>

<a id="d-qiqth-fock-localization-continuous-minkowskidot-fst"></a>
**Lemma 260** (`continuous_minkowskiDot_fst`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L341)</small>

`p ↦ η(p,x)` is continuous.

$$
\mathrm{Continuous}\,\lambda p \mapsto \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot}{\eta}\,p\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`minkowskiFourier_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-continuous).</small>

<a id="d-qiqth-fock-localization-continuous-minkowskidot-snd"></a>
**Lemma 261** (`continuous_minkowskiDot_snd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L345)</small>

`x ↦ η(p,x)` is continuous.

$$
\mathrm{Continuous}\,\lambda x \mapsto \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot}{\eta}\,p\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`minkowskiFourier_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-continuous).</small>

<a id="d-qiqth-fock-localization-minkowskifourier-continuous"></a>
**Lemma 262** (`minkowskiFourier_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L349)</small>

**The Minkowski-Fourier transform of an integrable function is continuous** (Riemann–Lebesgue continuity, via dominated convergence; the exponential has modulus one and `f` dominates).

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{Continuous}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f)
$$

*Proof.* By [`minkowskiDot`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot), [`continuous_minkowskiDot_fst`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-continuous-minkowskidot-fst), [`continuous_minkowskiDot_snd`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-continuous-minkowskidot-snd). $\square$

<small>Used by [`Krep_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-continuous).</small>

<a id="d-qiqth-fock-localization-continuous-massshell"></a>
**Lemma 263** (`continuous_massShell`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L368)</small>

The mass-shell embedding `θ ↦ p_m(θ)` is continuous.

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`Krep_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-continuous).</small>

<a id="d-qiqth-fock-localization-krep-continuous"></a>
**Lemma 264** (`Krep_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L374)</small>

**The localized rapidity amplitude is continuous** for an integrable test function, hence (part (a) of `MemLp`) almost-everywhere strongly measurable.  The remaining part (b) — the `L²` bound from Schwartz–Fourier decay on the mass shell — is the isolated multi-week analytic core.

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{Continuous}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)
$$

*Proof.* By [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier), [`minkowskiFourier_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier-continuous), [`continuous_massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-continuous-massshell). $\square$

<small>Used by [`Krep_bumpCW_ne_zero_of`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of), [`Krep_aestronglyMeasurable`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-aestronglymeasurable), [`integrable_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-krep), [`integrable_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-ftkrep), [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-localization-krep-aestronglymeasurable"></a>
**Lemma 265** (`Krep_aestronglyMeasurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L380)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{AEStronglyMeasurable}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{volume}
$$

*Proof.* By [`Krep_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-continuous). $\square$

<small>Used by [`Krep_memLp_of_decay`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-memlp-of-decay).</small>

<a id="d-qiqth-fock-localization-one-add-sq-le-cosh-sq"></a>
**Lemma 266** (`one_add_sq_le_cosh_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L386)</small>

The mass-shell hyperbola dominates the parabola: `1 + θ² ≤ cosh²θ` (since `cosh²=1+sinh²` and `θ² ≤ sinh²θ`).

$$
1 + {\theta}^{2} \le {\cosh\,\theta}^{2}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`integrable_cosh_inv_sq`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-integrable-cosh-inv-sq).</small>

<a id="d-qiqth-fock-localization-integrable-cosh-inv-sq"></a>
**Lemma 267** (`integrable_cosh_inv_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L399)</small>

`1/cosh²` is integrable on `ℝ` (dominated by the Cauchy density `(1+θ²)⁻¹`).

$$
\mathrm{Integrable}\,(\lambda \theta \mapsto {({\cosh\,\theta}^{2})}^{-1})\,\mathrm{volume}
$$

*Proof.* By [`one_add_sq_le_cosh_sq`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-one-add-sq-le-cosh-sq). $\square$

<small>Used by [`memLp_cosh_inv`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-memlp-cosh-inv).</small>

<a id="d-qiqth-fock-localization-memlp-cosh-inv"></a>
**Lemma 268** (`memLp_cosh_inv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L410)</small>

`1/cosh ∈ L²(ℝ)` — the comparison function for the localized-amplitude boundedness.

$$
\mathrm{MemLp}\,(\lambda \theta \mapsto {(\cosh\,\theta)}^{-1})\,2\,\mathrm{volume}
$$

*Proof.* By [`integrable_cosh_inv_sq`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-integrable-cosh-inv-sq). $\square$

<small>Used by [`Krep_memLp_of_decay`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-memlp-of-decay).</small>

<a id="d-qiqth-fock-localization-krep-memlp-of-decay"></a>
**Lemma 269** (`Krep_memLp_of_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L419)</small>

**Boundedness from a `1/cosh` decay bound**: if the localized rapidity amplitude is dominated by `C/cosh θ`, then it lies in `L²(ℝ)`.  This reduces the `MemLp` obligation of `LocalTest` to the sharp pointwise Fourier-decay estimate `‖(K f)(θ)‖ ≤ C/cosh θ` — the genuine remaining analytic content (the Fourier transform of a smooth test function decays on the mass shell).  The integrability is fully discharged here.

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \forall \{C : \mathbb{R}\}, (\forall (\theta : \mathbb{R}), \|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\| \le C \cdot {(\cosh\,\theta)}^{-1}) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume}
$$

*Proof.* By [`Krep_aestronglyMeasurable`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-aestronglymeasurable), [`memLp_cosh_inv`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-memlp-cosh-inv). $\square$

<small>Used by [`schwartz_Krep_memLp`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-memlp).</small>

---
<small>[← all sections](/browser) · [← FreeFieldHFlux](/browser/qiqth-fock-freefieldhflux) · [OneParticle →](/browser/qiqth-fock-oneparticle) </small>