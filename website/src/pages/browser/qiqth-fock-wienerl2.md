---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.WienerL2
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.WienerL2 — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← WedgeAnalyticity](/browser/qiqth-fock-wedgeanalyticity) · [GaussianMode →](/browser/qiqth-gaussianmode) </small>

<small>Fock · entries 384–427 of 1000</small>

<a id="d-qiqth-fock-wienerl2-schwartztranslate"></a>
**Definition 384** (`schwartzTranslate`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L31)</small>

**Wiener brick 1 — the Schwartz translation operator** `τ_a : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ)`, `f ↦ f(·+a)`. Built via `SchwartzMap.compCLM` with the temperate-growth affine map `x ↦ x + a` (`HasTemperateGrowth.id' + .const`, and the moderate-decay bound `‖x‖ ≤ (1+‖a‖)(1+‖x+a‖)`).  The foundational operator for the L²-translate↔modulation intertwining `𝓕 ∘ τ_a = M_a ∘ 𝓕` behind Wiener's L² Tauberian theorem.

$$
\tau\,a \;:=\; \mathrm{compCLM}\,\mathbb{C}\,\cdots \,\cdots
$$

<small>Used by [`schwartzTranslate_apply`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-schwartztranslate-apply), [`boostUnitary_toLp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-boostunitary-tolp), [`fourier_schwartzTranslate`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourier-schwartztranslate), [`fourierL2_boostUnitary`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-boostunitary).</small>

<a id="d-qiqth-fock-wienerl2-schwartztranslate-apply"></a>
**Lemma 385** (`schwartzTranslate_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L45)</small>

$$
((\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-schwartztranslate}{\tau}\,a)\,f)\,x = f\,(x + a)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boostUnitary_toLp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-boostunitary-tolp), [`fourier_schwartzTranslate`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourier-schwartztranslate).</small>

<a id="d-qiqth-fock-wienerl2-boostunitary-tolp"></a>
**Lemma 386** (`boostUnitary_toLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L49)</small>

**Wiener brick 3 — the boost unitary IS the Schwartz translation, at `L²`**: `boostUnitary a (f.toLp) = (schwartzTranslate (−a) f).toLp` (both `=ᵐ θ ↦ f(θ−a)`, via `coeFn_boostUnitary`, the measure-preserving translated-`ae`, and `schwartzTranslate_apply`).  This connects the QIQT rapidity-boost group to the generic Schwartz translation, so the Schwartz-level Fourier translate→modulation lemma transfers to `boostUnitary` (the next brick toward the intertwining `𝓕 ∘ boostUnitary_a = M_a ∘ 𝓕`).

$$
(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,(f.\mathrm{toLp}\,2\,\mathrm{vol}) = ((\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-schwartztranslate}{\tau}\,(-a))\,f).\mathrm{toLp}\,2\,\mathrm{vol}
$$

*Proof.* By [`coeFn_boostUnitary`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [`schwartzTranslate_apply`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-schwartztranslate-apply). $\square$

<small>Used by [`fourierL2_boostUnitary`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-boostunitary).</small>

<a id="d-qiqth-fock-wienerl2-modchar"></a>
**Definition 387** (`modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L73)</small>

The unit Fourier character `ξ ↦ e^{i c ξ}` (modulus 1).

$$
\chi_{\mathrm{mod}}\,c\,\xi \;:=\; \exp\,(i \cdot (c \cdot \xi))
$$

<small>Used by [`norm_modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-modchar), [`continuous_modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-modchar), [`memLp_modChar_smul`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-memlp-modchar-smul), [`modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2), [`coeFn_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-coefn-modl2), [`norm_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-modl2), [`fourier_schwartzTranslate`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourier-schwartztranslate), [`modL2_sub`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2-sub), and 4 more.</small>

<a id="d-qiqth-fock-wienerl2-norm-modchar"></a>
**Lemma 388** (`norm_modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L76)</small>

$$
\|\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c\,\xi\| = 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`memLp_modChar_smul`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-memlp-modchar-smul), [`norm_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-modl2).</small>

<a id="d-qiqth-fock-wienerl2-continuous-modchar"></a>
**Lemma 389** (`continuous_modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L80)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`memLp_modChar_smul`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-memlp-modchar-smul).</small>

<a id="d-qiqth-fock-wienerl2-memlp-modchar-smul"></a>
**Lemma 390** (`memLp_modChar_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L83)</small>

`e^{icξ}·g ∈ L²` whenever `g ∈ L²` (modulus-1 multiplier, via `MemLp.of_le_mul`).

$$
\mathrm{MemLp}\,(\lambda \xi \mapsto \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c\,\xi \cdot g\,\xi)\,2\,\mathrm{vol}
$$

*Proof.* By [`norm_modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-modchar), [`continuous_modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-modchar). $\square$

<small>Used by [`modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2), [`coeFn_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-coefn-modl2).</small>

<a id="d-qiqth-fock-wienerl2-modl2"></a>
**Definition 391** (`modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L91)</small>

**Wiener brick 2 — the L² modulation operator** `M_c : g ↦ (ξ ↦ e^{icξ} g(ξ))`.


<small>Used by [`coeFn_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-coefn-modl2), [`norm_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-modl2), [`modL2_sub`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2-sub), [`isometry_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-isometry-modl2), [`continuous_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-modl2), [`fourierL2_boostUnitary`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-boostunitary), [`inner_boostUnitary_eq_integral`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral).</small>

<a id="d-qiqth-fock-wienerl2-coefn-modl2"></a>
**Lemma 392** (`coeFn_modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L95)</small>

$$
(\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,g) =[\mathrm{vol}] \lambda \xi \mapsto \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c\,\xi \cdot g\,\xi
$$

*Proof.* By [`memLp_modChar_smul`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-memlp-modchar-smul). $\square$

<small>Used by [`norm_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-modl2), [`modL2_sub`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2-sub), [`fourierL2_boostUnitary`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-boostunitary), [`inner_boostUnitary_eq_integral`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral).</small>

<a id="d-qiqth-fock-wienerl2-norm-modl2"></a>
**Lemma 393** (`norm_modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L107)</small>

`M_c` is an `L²`-isometry: `‖M_c g‖ = ‖g‖` (the character has modulus 1).

$$
\|\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,g\| = \|g\|
$$

*Proof.* By [`modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar), [`norm_modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-modchar), [`coeFn_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-coefn-modl2). $\square$

<small>Used by [`isometry_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-isometry-modl2).</small>

<a id="d-qiqth-fock-wienerl2-fourier-schwartztranslate"></a>
**Lemma 394** (`fourier_schwartzTranslate`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L125)</small>

**Wiener brick 4a — the Schwartz translate→modulation identity (pointwise).** `𝓕(f(·−a))(w) = e^{−2πi a w} · 𝓕f(w)` — the Fourier dual of translation is modulation by the unit character `modChar (−2πa)`.  Via `fourier_coe` (Schwartz `𝓕` = integral `𝓕` on the coeFn) and `VectorFourier.fourierIntegral_comp_add_right`.

$$
(\mathcal{F}\,((\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-schwartztranslate}{\tau}\,(-a))\,f))\,w = \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,(-(2 \cdot \pi \cdot a))\,w \cdot (\mathcal{F}\,f)\,w
$$

*Proof.* By [`schwartzTranslate_apply`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-schwartztranslate-apply). $\square$

<small>Used by [`fourierL2_boostUnitary`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-boostunitary).</small>

<a id="d-qiqth-fock-wienerl2-modl2-sub"></a>
**Lemma 395** (`modL2_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L148)</small>

`M_c` is subtractive (companion to `modL2_add`), giving the isometry below.

$$
\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,(g - h) = \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,g - \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,h
$$

*Proof.* By [`modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar), [`coeFn_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-coefn-modl2). $\square$

<small>Used by [`isometry_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-isometry-modl2).</small>

<a id="d-qiqth-fock-wienerl2-isometry-modl2"></a>
**Lemma 396** (`isometry_modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L156)</small>

`M_c` is an isometry of `L²` (modulus-1 multiplier), hence continuous.

$$
\mathrm{Isometry}\,(\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c)
$$

*Proof.* By [`norm_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-modl2), [`modL2_sub`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2-sub). $\square$

<small>Used by [`continuous_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-modl2).</small>

<a id="d-qiqth-fock-wienerl2-continuous-modl2"></a>
**Lemma 397** (`continuous_modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L161)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c)
$$

*Proof.* By [`isometry_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-isometry-modl2). $\square$

<small>Used by [`fourierL2_boostUnitary`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-boostunitary).</small>

<a id="d-qiqth-fock-wienerl2-fourierl2-boostunitary"></a>
**Lemma 398** (`fourierL2_boostUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L163)</small>

**Wiener brick 4b — the `L²` translate→modulation intertwining.** `𝓕 (boostUnitary a g) = M_{−2πa} (𝓕 g)` for *all* `g ∈ L²` — the boost (a translation) becomes multiplication by the unit character under the `L²` Fourier unitary.  Proven on the dense Schwartz range (brick 4a + `toLp_fourier_eq` + `boostUnitary_toLp`) and extended by `DenseRange.equalizer` (both sides continuous: `𝓕`/`boostUnitary` are isometry-equivs, `M_c` is `continuous_modL2`).

$$
\mathcal{F}\,((\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,g) = \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,(-(2 \cdot \pi \cdot a))\,(\mathcal{F}\,g)
$$

*Proof.* By [`schwartzTranslate`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-schwartztranslate), [`boostUnitary_toLp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-boostunitary-tolp), [`modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar), [`coeFn_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-coefn-modl2), [`fourier_schwartzTranslate`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourier-schwartztranslate), [`continuous_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-modl2). $\square$

<small>Used by [`inner_boostUnitary_eq_integral`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral).</small>

<a id="d-qiqth-fock-wienerl2-conj-modchar"></a>
**Lemma 399** (`conj_modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L192)</small>

The unit character conjugates to its inverse: `conj (e^{icξ}) = e^{−icξ}`.

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c\,\xi) = \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,(-c)\,\xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`inner_boostUnitary_eq_integral`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral).</small>

<a id="d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral"></a>
**Lemma 400** (`inner_boostUnitary_eq_integral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L200)</small>

**Wiener brick 5 — the bridge.**  Via Plancherel (`inner_fourier_eq`) and the intertwining (brick 4), the boost-orbit inner product is the integral (inverse) Fourier transform of `k(ξ) = conj(𝓕g₀ ξ)·𝓕h ξ ∈ L¹`: `⟪boostUnitary a g₀, h⟫ = ∫ e^{+2πi a ξ}·conj(𝓕g₀ ξ)·𝓕h ξ dξ`. So the orbit-orthogonality condition `∀a, ⟪…⟫ = 0` becomes the vanishing of the FT of `k` — the exact hypothesis of the L¹ uniqueness theorem (next brick).

$$
\langle {(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,g_{0}},{h}\rangle = \int (\xi : \mathbb{R}), \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,(2 \cdot \pi \cdot a)\,\xi \cdot ((\mathrm{starRingEnd}\,\mathbb{C})\,((\mathcal{F}\,g_{0})\,\xi) \cdot (\mathcal{F}\,h)\,\xi)
$$

*Proof.* By [`modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modl2), [`coeFn_modL2`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-coefn-modl2), [`fourierL2_boostUnitary`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-boostunitary), [`conj_modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-conj-modchar). $\square$

<small>Used by [`fourier_correlation_eq`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourier-correlation-eq).</small>

<a id="d-qiqth-fock-wienerl2-fourier-correlation-eq"></a>
**Lemma 401** (`fourier_correlation_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L223)</small>

**Wiener brick 6a — the reduction.**  The function Fourier transform of `k(ξ) = conj(𝓕g₀ ξ)·𝓕h ξ` at `w` equals the boost-orbit correlation `⟪boostUnitary (−w) g₀, h⟫` (brick 5 at `a = −w`, matching the `𝓕`-character `𝐞(−⟪ξ,w⟫) = modChar(2π(−w))ξ`).  Hence `(∀a, ⟪boost_a g₀,h⟫ = 0) ⟹ 𝓕 k ≡ 0`.

$$
\mathcal{F}\,(\lambda \xi \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,((\mathcal{F}\,g_{0})\,\xi) \cdot (\mathcal{F}\,h)\,\xi)\,w = \langle {(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-w))\,g_{0}},{h}\rangle
$$

*Proof.* By [`modChar`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-modchar), [`inner_boostUnitary_eq_integral`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral). $\square$

<small>Used by [`boost_orbit_total_of_fourier_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-ae-eq-zero-of-fourier-eq-zero"></a>
**Lemma 402** (`ae_eq_zero_of_fourier_eq_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L239)</small>

**Wiener brick 6b — Fourier injectivity on L¹.**  If `k ∈ L¹(ℝ)` and its (function) Fourier transform vanishes identically, then `k = 0` a.e.  Proof: it suffices (`AEEqOfIntegralContDiff`) that `∫ g·k = 0` for every real smooth compactly-supported test `g`; package its complexification `G:=↑∘g` as a Schwartz map, write `G = 𝓕(𝓕⁻G)` (Schwartz inversion) and apply the multiplication formula `∫ 𝓕(𝓕⁻G)·k = ∫ (𝓕⁻G)·𝓕k` (`integral_fourierIntegral_smul_eq_flip`, `innerₗ` symmetric) `= 0` since `𝓕 k = 0`.

$$
\mathrm{Integrable}\,k\,\mathrm{vol} \to (\forall (w : \mathbb{R}), \mathcal{F}\,k\,w = 0) \to k =[\mathrm{vol}] 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boost_orbit_total_of_fourier_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero), [`fourierL2_toLp_ne_zero_of_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero"></a>
**Lemma 403** (`boost_orbit_total_of_fourier_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L268)</small>

**Wiener brick 7 — the Tauberian conclusion.**  If `𝓕 g₀ ≠ 0` a.e. and `h` is orthogonal to the entire boost orbit of `g₀`, then `h = 0`.  Chains 6a (orbit-orthogonality ⟹ `𝓕 k ≡ 0`, `k=conj(𝓕g₀)·𝓕h ∈ L¹`) with 6b (`𝓕 k = 0 ⟹ k=ᵐ0`); then `𝓕g₀≠0` a.e. forces `𝓕 h = 0` a.e. `⟹ 𝓕 h = 0 ⟹ h = 0` (`𝓕` an isometry).

$$
(\forall (\xi : \mathbb{R}), (\mathcal{F}\,g_{0})\,\xi \ne 0) \to (\forall (a : \mathbb{R}), \langle {(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,g_{0}},{h}\rangle = 0) \to h = 0
$$

*Proof.* By [`fourier_correlation_eq`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourier-correlation-eq), [`ae_eq_zero_of_fourier_eq_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ae-eq-zero-of-fourier-eq-zero). $\square$

<small>Used by [`niceWedgeCyclic_of_fourier_ne_zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-ae-ne-zero-of-analyticonnhd"></a>
**Lemma 404** (`ae_ne_zero_of_analyticOnNhd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L291)</small>

**Wiener brick 8c — a nonzero real-analytic function is `≠ 0` a.e.**  The zero set of a function analytic on all of `ℝ` (and not identically zero) is co-discrete, hence Lebesgue-null (`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` + `ae_restrict_le_codiscreteWithin`). This is the final step turning "the boost-orbit generator's Fourier transform is entire and `≢ 0`" into the Wiener hypothesis `𝓕 g₀ ≠ 0` a.e. of brick 7.

$$
\mathrm{AnalyticOnNhd}\,\mathbb{R}\,F \to (\exists x, F\,x \ne 0) \to \forall (x : \mathbb{R}), F\,x \ne 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`fourierL2_toLp_ne_zero_of_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-integrable-exp-neg-mul-abs"></a>
**Lemma 405** (`integrable_exp_neg_mul_abs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L324)</small>

**Wiener brick 8a-foundation — `exp(−b|x|)` is integrable on `ℝ`** for `b > 0`.  The reusable both-ends exponential building block: `f =O[atBot] exp(b·)` and `f =O[atTop] exp(−b·)`, each integrable at its end (`exp_neg_integrableOn_Ioi` + reflection), via `LocallyIntegrable.integrable_of_isBigO_atBot_atTop`. Dominates the `1/cosh²θ` decay of `Krep`, giving `Krep ∈ L¹` and its finite exponential moments.

$$
0 < b \to \mathrm{Integrable}\,(\lambda x \mapsto \exp\,(-b \cdot |x|))\,\mathrm{vol}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`integrable_abs_mul_exp_neg_mul_abs`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-abs-mul-exp-neg-mul-abs), [`integrable_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-krep), [`integrable_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-ftkrep).</small>

<a id="d-qiqth-fock-wienerl2-integrable-abs-mul-exp-neg-mul-abs"></a>
**Lemma 406** (`integrable_abs_mul_exp_neg_mul_abs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L348)</small>

**`|θ|·exp(−d|θ|)` is integrable on `ℝ`** for `d > 0` — the derivative-domination building block for the FT-holomorphy (8b): `|θ| ≤ (2/d)·exp((d/2)|θ|)` (from `t ≤ exp t`) absorbs the `|θ|` into a slower exponential dominated by `integrable_exp_neg_mul_abs (d/2)`.

$$
0 < d \to \mathrm{Integrable}\,(\lambda \theta \mapsto |\theta| \cdot \exp\,(-d \cdot |\theta|))\,\mathrm{vol}
$$

*Proof.* By [`integrable_exp_neg_mul_abs`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-exp-neg-mul-abs). $\square$

<small>Used by [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-inv-cosh-sq-le-exp"></a>
**Lemma 407** (`inv_cosh_sq_le_exp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L369)</small>

`(cosh θ)⁻² ≤ 4·exp(−2|θ|)` — from `exp|θ| ≤ 2cosh θ` (one of `e^{±θ}` equals `e^{|θ|}`).

$$
{({\cosh\,\theta}^{2})}^{-1} \le 4 \cdot \exp\,(-2 \cdot |\theta|)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`integrable_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-krep), [`norm_Krep_le_exp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-krep-le-exp).</small>

<a id="d-qiqth-fock-wienerl2-integrable-krep"></a>
**Lemma 408** (`integrable_Krep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L386)</small>

**Wiener brick 8a — `Krep m f ∈ L¹(ℝ)`** for a Schwartz test `f`: the localized rapidity amplitude is integrable, since `‖Krep m f θ‖ ≤ C·(cosh θ)⁻²` (`schwartz_Krep_decay_sq`) `≤ 4C·exp(−2|θ|)`, dominated by the integrable `exp(−2|θ|)` (`integrable_exp_neg_mul_abs`).  Makes the function Fourier transform of `Krep` well-defined and is the base for the L²↔L¹ agreement and the FT-holomorphy (8b).

$$
m \ne 0 \to \mathrm{Integrable}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f)\,\mathrm{vol}
$$

*Proof.* By [`Krep_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-continuous), [`schwartz_Krep_decay_sq`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-decay-sq), [`integrable_exp_neg_mul_abs`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-exp-neg-mul-abs), [`inv_cosh_sq_le_exp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-inv-cosh-sq-le-exp). $\square$

<small>Used by [`fourierL2_Krep_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-ftkrep"></a>
**Definition 409** (`ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L410)</small>

The complexified Fourier integrand `exp(−2π i θ ζ)·Krep(θ)`.

$$
\mathrm{ftKrep}\,m\,f\,\zeta\,\theta \;:=\; \exp\,(-2 \cdot \pi \cdot i \cdot \theta \cdot \zeta) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f\,\theta
$$

<small>Used by [`ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrepf), [`hasDerivAt_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrep), [`norm_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-ftkrep), [`continuous_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-ftkrep), [`integrable_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-ftkrep), [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf), [`ftKrepF_eq_fourier`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrepf-eq-fourier).</small>

<a id="d-qiqth-fock-wienerl2-ftkrep"></a>
**Definition 410** (`ftKrep'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L414)</small>

Its `ζ`-derivative `−2π i θ exp(−2π i θ ζ)·Krep(θ)`.

$$
\hat{K}\,m\,f\,\zeta\,\theta \;:=\; -2 \cdot \pi \cdot i \cdot \theta \cdot \exp\,(-2 \cdot \pi \cdot i \cdot \theta \cdot \zeta) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f\,\theta
$$

<small>Used by [`hasDerivAt_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrep), [`norm_ftKrep'`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-ftkrep), [`continuous_ftKrep'`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-ftkrep), [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf), [`analyticOnNhd_ftKrepF_real`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real).</small>

<a id="d-qiqth-fock-wienerl2-ftkrepf"></a>
**Definition 411** (`ftKrepF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L419)</small>

The complexified Fourier transform `F(ζ) = ∫ exp(−2π i θ ζ)·Krep(θ) dθ`.

$$
\hat{K}\,m\,f\,\zeta \;:=\; \int (\theta : \mathbb{R}), \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,f\,\zeta\,\theta
$$

<small>Used by [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf), [`analyticOnNhd_ftKrepF_real`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real), [`ftKrepF_eq_fourier`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrepf-eq-fourier), [`analyticOnNhd_fourier_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep).</small>

<a id="d-qiqth-fock-wienerl2-hasderivat-ftkrep"></a>
**Lemma 412** (`hasDerivAt_ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L422)</small>

The integrand is `ζ`-holomorphic pointwise, with derivative `ftKrep'`.

$$
({\lambda \zeta \mapsto \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,f\,\zeta\,\theta})'({\zeta_{0}})={\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\hat{K}}\,m\,f\,\zeta_{0}\,\theta}
$$

*Proof.* By [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep). $\square$

<small>Used by [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-ftkrep-exp-re"></a>
**Lemma 413** (`ftKrep_exp_re`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L434)</small>

The exponent's real part: `Re(−2π i θ ζ) = 2π θ (Im ζ)`.

$$
(-2 \cdot \pi \cdot i \cdot \theta \cdot \zeta).\mathrm{re} = 2 \cdot \pi \cdot \theta \cdot \zeta.\mathrm{im}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`norm_ftKrep'`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-ftkrep), [`norm_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-ftkrep).</small>

<a id="d-qiqth-fock-wienerl2-norm-ftkrep"></a>
**Lemma 414** (`norm_ftKrep'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L443)</small>

The norm of the integrand's `ζ`-derivative.

$$
\|\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\hat{K}}\,m\,f\,\zeta\,\theta\| = 2 \cdot \pi \cdot |\theta| \cdot \exp\,(2 \cdot \pi \cdot \theta \cdot \zeta.\mathrm{im}) \cdot \|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f\,\theta\|
$$

*Proof.* By [`ftKrep_exp_re`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep-exp-re). $\square$

<small>Used by [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-norm-ftkrep"></a>
**Lemma 415** (`norm_ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L455)</small>

The norm of the integrand itself.

$$
\|\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,f\,\zeta\,\theta\| = \exp\,(2 \cdot \pi \cdot \theta \cdot \zeta.\mathrm{im}) \cdot \|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f\,\theta\|
$$

*Proof.* By [`ftKrep_exp_re`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep-exp-re). $\square$

<small>Used by [`integrable_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-ftkrep).</small>

<a id="d-qiqth-fock-wienerl2-norm-krep-le-exp"></a>
**Lemma 416** (`norm_Krep_le_exp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L461)</small>

The decay constant for `Krep`, factored: `‖Krep m f θ‖ ≤ C·exp(−2|θ|)` for some `C ≥ 0`.

$$
m \ne 0 \to \exists C, 0 \le C \wedge \forall (\theta : \mathbb{R}), \|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,(f)\,\theta\| \le C \cdot \exp\,(-2 \cdot |\theta|)
$$

*Proof.* By [`schwartz_Krep_decay_sq`](/browser/qiqth-fock-schwartzdecay#d-qiqth-fock-localization-schwartz-krep-decay-sq), [`inv_cosh_sq_le_exp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-inv-cosh-sq-le-exp). $\square$

<small>Used by [`integrable_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-ftkrep), [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-continuous-ftkrep"></a>
**Lemma 417** (`continuous_ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L475)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f) \to \forall (\zeta : \mathbb{C}), \mathrm{Continuous}\,\lambda \theta \mapsto \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,f\,\zeta\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`integrable_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-ftkrep), [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-continuous-ftkrep"></a>
**Lemma 418** (`continuous_ftKrep'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L479)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f) \to \forall (\zeta : \mathbb{C}), \mathrm{Continuous}\,\lambda \theta \mapsto \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\hat{K}}\,m\,f\,\zeta\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-integrable-ftkrep"></a>
**Lemma 419** (`integrable_ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L484)</small>

The integrand is integrable at any strip point `|Im ζ| < 1/π`.

$$
m \ne 0 \to \forall \{\zeta : \mathbb{C}\}, |\zeta.\mathrm{im}| < 1 / \pi \to \mathrm{Integrable}\,(\lambda \theta \mapsto \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,(f)\,\zeta\,\theta)\,\mathrm{vol}
$$

*Proof.* By [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`Krep_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-continuous), [`integrable_exp_neg_mul_abs`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-exp-neg-mul-abs), [`norm_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-ftkrep), [`norm_Krep_le_exp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-krep-le-exp), [`continuous_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-ftkrep). $\square$

<small>Used by [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-hasderivat-ftkrepf"></a>
**Lemma 420** (`hasDerivAt_ftKrepF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L506)</small>

**Wiener brick 8b — the FT of `Krep` is holomorphic on the strip.**  At every `ζ₀` with `|Im ζ₀| < 1/π`, `F(ζ) = ∫ exp(−2π i θ ζ)·Krep(θ) dθ` is complex-differentiable, with derivative `∫ ftKrep'`.  Via the dominated-derivative theorem (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `𝕜 = ℂ`): the integrand is pointwise `ζ`-holomorphic (`hasDerivAt_ftKrep`), `L¹` at `ζ₀` (`integrable_ftKrep`), and its derivative is dominated on a ball by `2πC·|θ|·exp(−d|θ|) ∈ L¹` (`integrable_abs_mul_exp_neg_mul_abs`).

$$
m \ne 0 \to \forall \{\zeta_{0} : \mathbb{C}\}, |\zeta_{0}.\mathrm{im}| < 1 / \pi \to ({\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrepf}{\hat{K}}\,m\,f})'({\zeta_{0}})={\int (\theta : \mathbb{R}), \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep}{\hat{K}}\,m\,(f)\,\zeta_{0}\,\theta}
$$

*Proof.* By [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`Krep_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-continuous), [`integrable_abs_mul_exp_neg_mul_abs`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-abs-mul-exp-neg-mul-abs), [`ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep), [`hasDerivAt_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrep), [`norm_ftKrep'`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-ftkrep), [`norm_Krep_le_exp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-norm-krep-le-exp), [`continuous_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-ftkrep), [`continuous_ftKrep'`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-continuous-ftkrep), [`integrable_ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-ftkrep). $\square$

<small>Used by [`analyticOnNhd_ftKrepF_real`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real).</small>

<a id="d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real"></a>
**Lemma 421** (`analyticOnNhd_ftKrepF_real`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L559)</small>

**Wiener brick 8b-fin — the FT of `Krep`, on `ℝ`, is real-analytic.**  `F` is holomorphic on the open strip `|Im ζ| < 1/π` (brick 8b), which contains `ℝ`; restricting to the real axis gives `AnalyticOnNhd ℝ (ξ ↦ F ξ) univ` (the same `DifferentiableOn.analyticOnNhd` + `restrictScalars`/`ofRealCLM` route as `8c′`).  Feeds brick 8c: combined with `≢ 0` it yields `F ≠ 0` a.e. on `ℝ`.

$$
m \ne 0 \to \mathrm{AnalyticOnNhd}\,\mathbb{R}\,(\lambda \xi \mapsto \href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrepf}{\hat{K}}\,m\,f\,\xi)
$$

*Proof.* By [`ftKrep'`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep), [`hasDerivAt_ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-hasderivat-ftkrepf). $\square$

<small>Used by [`analyticOnNhd_fourier_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep).</small>

<a id="d-qiqth-fock-wienerl2-ftkrepf-eq-fourier"></a>
**Lemma 422** (`ftKrepF_eq_fourier`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L577)</small>

**Wiener brick 8b-bridge (function FT) — `F` restricts to the function Fourier transform of `Krep`.** `ftKrepF m f ξ = 𝓕(Krep m f) ξ` for real `ξ` (matching the character `exp(−2πiθξ) = 𝐞(−⟨θ,ξ⟩)`, `Real.fourier_eq`/`Real.fourierChar_apply`).  With `analyticOnNhd_ftKrepF_real` this gives `AnalyticOnNhd ℝ (𝓕 Krep) univ`.

$$
\href{/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrepf}{\hat{K}}\,m\,f\,\xi = \mathcal{F}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f)\,\xi
$$

*Proof.* By [`ftKrep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrep). $\square$

<small>Used by [`analyticOnNhd_fourier_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep).</small>

<a id="d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep"></a>
**Lemma 423** (`analyticOnNhd_fourier_Krep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L591)</small>

**The function Fourier transform of `Krep` is real-analytic on `ℝ`** (combining `ftKrepF_eq_fourier` with `analyticOnNhd_ftKrepF_real`).  Combined with `≢ 0`, brick 8c yields `𝓕(Krep) ≠ 0` a.e.

$$
m \ne 0 \to \mathrm{AnalyticOnNhd}\,\mathbb{R}\,(\lambda \xi \mapsto \mathcal{F}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f)\,\xi)
$$

*Proof.* By [`ftKrepF`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrepf), [`analyticOnNhd_ftKrepF_real`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real), [`ftKrepF_eq_fourier`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ftkrepf-eq-fourier). $\square$

<small>Used by [`fourierL2_Krep_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-integral-smul-fourierl2-eq"></a>
**Lemma 424** (`integral_smul_fourierL2_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L602)</small>

**The integral pairing identity.**  For `g ∈ L¹∩L²` and Schwartz `φ`: `∫ φ·⇑(𝓕_{L²}(g.toLp)) = ∫ φ·𝓕_{int}(g)` — via the tempered-distribution Fourier transform (`fourier_toTemperedDistribution_eq` + `fourier_apply` + the `Lp` pairing `toTemperedDistribution_apply`) and the multiplication formula (`integral_fourierIntegral_smul_eq_flip`).

$$
\mathrm{Integrable}\,g\,\mathrm{vol} \to \forall (\mathrm{hg2} : \mathrm{MemLp}\,g\,2\,\mathrm{vol}) (\varphi : \mathrm{SchwartzMap}\,\mathbb{R}\,\mathbb{C}), \int (x : \mathbb{R}), \varphi\,x \cdot (\mathcal{F}\,(\mathrm{toLp}\,g\,\mathrm{hg2}))\,x = \int (x : \mathbb{R}), \varphi\,x \cdot \mathcal{F}\,g\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`fourierL2_toLp_ae_eq`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-tolp-ae-eq).</small>

<a id="d-qiqth-fock-wienerl2-fourierl2-tolp-ae-eq"></a>
**Lemma 425** (`fourierL2_toLp_ae_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L633)</small>

**Wiener brick 8b-bridge (L²↔L¹) — the L² FT coeFn agrees a.e. with the function FT.** For `g ∈ L¹∩L²`, `⇑(𝓕_{L²}(g.toLp)) =ᵐ 𝓕_{int}(g)`.  From the pairing identity `integral_smul_fourierL2_eq` (both pair equally with every Schwartz `φ`) + the variational lemma `ae_eq_of_integral_contDiff_smul_eq` (testing against real `C^∞_c` functions, packaged as Schwartz).

$$
\mathrm{Integrable}\,g\,\mathrm{vol} \to \forall (\mathrm{hg2} : \mathrm{MemLp}\,g\,2\,\mathrm{vol}), (\mathcal{F}\,(\mathrm{toLp}\,g\,\mathrm{hg2})) =[\mathrm{vol}] \mathcal{F}\,g
$$

*Proof.* By [`integral_smul_fourierL2_eq`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integral-smul-fourierl2-eq). $\square$

<small>Used by [`fourierL2_toLp_ne_zero_of_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero"></a>
**Lemma 426** (`fourierL2_toLp_ne_zero_of_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L654)</small>

**The Wiener nonvanishing, assembled.**  For `g ∈ L¹∩L²` with `𝓕 g` real-analytic on `ℝ` and `g ≢ 0`, the `L²` FT coeFn `⇑(𝓕_{L²}(g.toLp)) ≠ 0` a.e.  Chains: `g ≢ 0 ⟹ ∃ x, 𝓕g(x)≠0` (brick 6b contrapositive) ⟹ `𝓕 g ≠ 0` a.e. (brick 8c) ⟹ (L²↔L¹ agreement) `⇑(𝓕_{L²}(g.toLp)) ≠ 0` a.e.

$$
\mathrm{Integrable}\,g\,\mathrm{vol} \to \forall (\mathrm{hg2} : \mathrm{MemLp}\,g\,2\,\mathrm{vol}), \mathrm{AnalyticOnNhd}\,\mathbb{R}\,(\lambda \xi \mapsto \mathcal{F}\,g\,\xi) \to \neg g =[\mathrm{vol}] 0 \to \forall (\xi : \mathbb{R}), (\mathcal{F}\,(\mathrm{toLp}\,g\,\mathrm{hg2}))\,\xi \ne 0
$$

*Proof.* By [`ae_eq_zero_of_fourier_eq_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ae-eq-zero-of-fourier-eq-zero), [`ae_ne_zero_of_analyticOnNhd`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-ae-ne-zero-of-analyticonnhd), [`fourierL2_toLp_ae_eq`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-tolp-ae-eq). $\square$

<small>Used by [`fourierL2_Krep_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero"></a>
**Lemma 427** (`fourierL2_Krep_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L669)</small>

**The Wiener nonvanishing for `Krep`.**  If the localized amplitude `Krep m fS` of a Schwartz wedge test `fS` is not a.e. zero, then the `L²` Fourier transform of its one-particle vector is `≠ 0` a.e. — the Wiener hypothesis of brick 7, ready to feed `niceWedgeCyclic_of_fourier_ne_zero`.

$$
\neg \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,\mathrm{fS} =[\mathrm{vol}] 0 \to \forall (\xi : \mathbb{R}), (\mathcal{F}\,(\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,\mathrm{fS})\,\cdots ))\,\xi \ne 0
$$

*Proof.* By [`integrable_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-integrable-krep), [`analyticOnNhd_fourier_Krep`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep), [`fourierL2_toLp_ne_zero_of_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero). $\square$

<small>Used by [`niceWedgeCyclic_bumpW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw).</small>

---
<small>[← all sections](/browser) · [← WedgeAnalyticity](/browser/qiqth-fock-wedgeanalyticity) · [GaussianMode →](/browser/qiqth-gaussianmode) </small>