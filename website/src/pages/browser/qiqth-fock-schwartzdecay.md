---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.SchwartzDecay
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.SchwartzDecay — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← OneParticleBW](/browser/qiqth-fock-oneparticlebw) · [WedgeAnalyticity →](/browser/qiqth-fock-wedgeanalyticity) </small>

<small>Fock · entries 320–325 of 1000</small>

<a id="d-qiqth-fock-localization-minkbilin"></a>
**Definition 320** (`minkBilin`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L35)</small>

The continuous bilinear Minkowski pairing rescaled by `1/(2π)`: `L v w = (v₀ w₀ − v₁ w₁) / (2π)`.  Writing the bespoke `minkowskiFourier` as a `VectorFourier.fourierIntegral` for this `L` lets us borrow Mathlib's Fourier-decay machinery.

$$
\eta \;:=\; (1 / (2 \cdot \pi)) \cdot ((\mathrm{proj}\,0).\mathrm{smulRight}\,(\mathrm{proj}\,0) - (\mathrm{proj}\,1).\mathrm{smulRight}\,(\mathrm{proj}\,1))
$$

<small>Used by [`minkBilin_apply`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkbilin-apply), [`minkowskiFourier_eq_fourierIntegral`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [`schwartz_Krep_memLp`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-memlp), [`schwartz_Krep_decay_sq`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-decay-sq).</small>

<a id="d-qiqth-fock-localization-minkbilin-apply"></a>
**Lemma 321** (`minkBilin_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L43)</small>

$$
(\href{/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkbilin}{\eta}\,v)\,w = (v\,0 \cdot w\,0 - v\,1 \cdot w\,1) / (2 \cdot \pi)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`minkowskiFourier_eq_fourierIntegral`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [`schwartz_Krep_memLp`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-memlp), [`schwartz_Krep_decay_sq`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-decay-sq).</small>

<a id="d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral"></a>
**Lemma 322** (`minkowskiFourier_eq_fourierIntegral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L49)</small>

**Bridge**: the bespoke Minkowski-Fourier transform IS a `VectorFourier.fourierIntegral` for the bilinear form `minkBilin` (with the standard `2π` Fourier character).  This is what lets us import Mathlib's decay estimates.

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f\,p = \mathcal{F}\,\mathrm{e}\,\mathrm{volume}\,\href{/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkbilin}{\eta}.\mathrm{toLinearMap}_{12}\,f\,p
$$

*Proof.* By [`minkowskiDot`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot), [`minkBilin_apply`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkbilin-apply). $\square$

<small>Used by [`schwartz_Krep_memLp`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-memlp), [`schwartz_Krep_decay_sq`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-decay-sq).</small>

<a id="d-qiqth-fock-localization-abs-sinh-le-cosh"></a>
**Lemma 323** (`abs_sinh_le_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L67)</small>

`|sinh θ| ≤ cosh θ`.

$$
|\sinh\,\theta| \le \cosh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`schwartz_Krep_memLp`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-memlp), [`schwartz_Krep_decay_sq`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-decay-sq).</small>

<a id="d-qiqth-fock-localization-schwartz-krep-memlp"></a>
**Lemma 324** (`schwartz_Krep_memLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L74)</small>

**General Schwartz `1/cosh` decay** of the localized amplitude.  For any Schwartz `f` and `m ≠ 0`, `‖Krep m f θ‖ ≤ C · (cosh θ)⁻¹` with `C = 4πS / (√2·|m|)`, where `S = ∫‖f‖ + ∫‖D f‖` is a finite Schwartz constant.  Hence `Krep m f ∈ L²(ℝ)`.

$$
m \ne 0 \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume}
$$

*Proof.* By [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier), [`Krep_memLp_of_decay`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-memlp-of-decay), [`minkBilin`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkbilin), [`minkBilin_apply`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkbilin-apply), [`minkowskiFourier_eq_fourierIntegral`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [`abs_sinh_le_cosh`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-abs-sinh-le-cosh). $\square$

<small>Used by [`fourierL2_Krep_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-localization-schwartz-krep-decay-sq"></a>
**Lemma 325** (`schwartz_Krep_decay_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L165)</small>

**General Schwartz `1/cosh²` decay** of the localized amplitude (one derivative more than `schwartz_Krep_memLp`).  For any Schwartz `f` and `m ≠ 0`, `‖Krep m f θ‖ ≤ 16π²·S₂/(√2·m²) · (cosh θ)⁻²` with `S₂ = ∫‖f‖ + ∫‖Df‖ + ∫‖D²f‖`.  The `(cosh θ)⁻²` decay (via the `n = 2` Fourier-decay estimate) is what makes the horizon amplitude `L¹` and differentiable at the bifurcation surface `x = 0` (the softer Route-B regularity).

$$
m \ne 0 \to \forall (\theta : \mathbb{R}), \|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f)\,\theta\| \le 16 \cdot {\pi}^{2} \cdot (((\int (v : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|f\,v\|) + \int (v : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|\mathrm{D}\,\mathbb{R}\,1\,(f)\,v\|) + \int (v : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|\mathrm{D}\,\mathbb{R}\,2\,(f)\,v\|) / (\sqrt 2 \cdot {m}^{2}) \cdot {({\cosh\,\theta}^{2})}^{-1}
$$

*Proof.* By [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier), [`minkBilin`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkbilin), [`minkBilin_apply`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkbilin-apply), [`minkowskiFourier_eq_fourierIntegral`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [`abs_sinh_le_cosh`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-abs-sinh-le-cosh). $\square$

<small>Used by [`integrable_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-krep), [`norm_Krep_le_exp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-krep-le-exp).</small>

---
<small>[← all sections](/browser) · [← OneParticleBW](/browser/qiqth-fock-oneparticlebw) · [WedgeAnalyticity →](/browser/qiqth-fock-wedgeanalyticity) </small>