---
layout: ../../layouts/Deep.astro
title: QIQTH.GaussianMode
eyebrow: GaussianMode · section of the QIQT-H book
description: QIQTH.GaussianMode — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← WienerL2](/browser/qiqth-fock-wienerl2) · [HregExplicitKG →](/browser/qiqth-hregexplicitkg) </small>

<small>GaussianMode · entries 428–444 of 1000</small>

<a id="d-qiqth-wedgekmstogr-gaussc"></a>
**Definition 428** (`gaussC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L22)</small>

Normalization constant `C = (ℏ√π)^{−1/2}` of the Gaussian reference profile.

$$
\mathrm{gaussC}\,\hbar \;:=\; {(\sqrt (\hbar \cdot \sqrt \pi))}^{-1}
$$

<small>Used by [`gaussMode`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode), [`gaussC_sq_mul_sqrt`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc-sq-mul-sqrt), [`gaussMode_normSq`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-normsq), [`gaussMode_conj_mul`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-conj-mul), [`gaussMode_integrable`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-integrable), [`gaussMode_calibration`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-calibration), [`gaussC_pos`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc-pos), [`gaussMode_norm`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm), and 7 more.</small>

<a id="d-qiqth-wedgekmstogr-gaussmode"></a>
**Definition 429** (`gaussMode`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L25)</small>

The Gaussian wave-packet reference profile `g₀(θ) = C·exp(−θ²/2 − iθ)`.

$$
\mathrm{gaussMode}\,\hbar\,\theta \;:=\; (\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc}{\mathrm{gaussC}}\,\hbar) \cdot \exp\,((-{\theta}^{2} / 2) - \theta \cdot i)
$$

<small>Used by [`gaussMode'`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode), [`gaussMode_normSq`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-normsq), [`gaussMode_conj_mul`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-conj-mul), [`gaussMode_integrable`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-integrable), [`gaussMode_calibration`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-calibration), [`gaussMode_norm`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm), [`gaussMode_continuous`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-continuous), [`gaussMode_hasDerivAt`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-hasderivat), and 7 more.</small>

<a id="d-qiqth-wedgekmstogr-gaussmode"></a>
**Definition 430** (`gaussMode'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L29)</small>

Its derivative profile `g₀'(θ) = g₀(θ)·(−θ − i)`.

$$
\mathrm{gaussMode}^{\prime}\,\hbar\,\theta \;:=\; \href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar\,\theta \cdot (-\theta - i)
$$

<small>Used by [`gaussMode_conj_mul`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-conj-mul), [`gaussMode_integrable`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-integrable), [`gaussMode_calibration`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-calibration), [`gaussMode_hasDerivAt`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-hasderivat), [`gaussMode'_continuous`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-continuous), [`gaussMode'_norm_le`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm-le), [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian).</small>

<a id="d-qiqth-wedgekmstogr-gaussc-sq-mul-sqrt"></a>
**Lemma 431** (`gaussC_sq_mul_sqrt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L33)</small>

`C²·√π = 1/ℏ` for `ℏ > 0` — the calibration arithmetic.

$$
0 < \hbar \to {\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc}{\mathrm{gaussC}}\,\hbar}^{2} \cdot \sqrt \pi = 1 / \hbar
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gaussMode_calibration`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-calibration).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-normsq"></a>
**Lemma 432** (`gaussMode_normSq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L42)</small>

`normSq(g₀ θ) = C²·e^{−θ²}` — the Gaussian envelope.

$$
\mathrm{normSq}\,(\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar\,\theta) = {\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc}{\mathrm{gaussC}}\,\hbar}^{2} \cdot \exp\,(-{\theta}^{2})
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gaussMode_conj_mul`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-conj-mul), [`gaussMode_norm`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm), [`gaussMode_sq_integrable`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-sq-integrable).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-conj-mul"></a>
**Lemma 433** (`gaussMode_conj_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L56)</small>

The pointwise boost-charge density: `conj(g₀ θ)·g₀'(θ) = ↑(C²·e^{−θ²})·(−θ − i)`.

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar\,\theta) \cdot \href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}^{\prime}}\,\hbar\,\theta = ({\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc}{\mathrm{gaussC}}\,\hbar}^{2} \cdot \exp\,(-{\theta}^{2})) \cdot (-\theta - i)
$$

*Proof.* By [`gaussMode_normSq`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-normsq). $\square$

<small>Used by [`gaussMode_integrable`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-integrable), [`gaussMode_calibration`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-calibration).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-integrable"></a>
**Lemma 434** (`gaussMode_integrable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L64)</small>

The boost-charge integrand is integrable (Gaussian × polynomial).

$$
\mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar\,\theta) \cdot \href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}^{\prime}}\,\hbar\,\theta)\,\mathrm{volume}
$$

*Proof.* By [`gaussC`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc), [`gaussMode_conj_mul`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-conj-mul). $\square$

<small>Used by [`gaussMode_calibration`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-calibration).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-calibration"></a>
**Lemma 435** (`gaussMode_calibration`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L86)</small>

**The Gaussian profile satisfies the calibration** `(−2π ∫ conj(g₀)·g₀').im = 2π/ℏ`.  Combined with `localized_mode_hTkk`, the per-generator `hTkk` is fully discharged for the canonical Gaussian localization.

$$
0 < \hbar \to (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar\,\theta) \cdot \href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}^{\prime}}\,\hbar\,\theta)).\mathrm{im} = 2 \cdot \pi / \hbar
$$

*Proof.* By [`gaussC`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc), [`gaussC_sq_mul_sqrt`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc-sq-mul-sqrt), [`gaussMode_conj_mul`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-conj-mul), [`gaussMode_integrable`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-integrable). $\square$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian).</small>

<a id="d-qiqth-wedgekmstogr-gaussc-pos"></a>
**Lemma 436** (`gaussC_pos`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L120)</small>

$$
0 < \hbar \to 0 < \href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc}{\mathrm{gaussC}}\,\hbar
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gaussMode_norm`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm), [`gaussMode'_norm_le`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm-le).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-norm"></a>
**Lemma 437** (`gaussMode_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L123)</small>

`‖g₀(θ)‖ = C·e^{−θ²/2}` (from `normSq = C²e^{−θ²}`).

$$
0 < \hbar \to \forall (\theta : \mathbb{R}), \|\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar\,\theta\| = \href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc}{\mathrm{gaussC}}\,\hbar \cdot \exp\,(-{\theta}^{2} / 2)
$$

*Proof.* By [`gaussMode_normSq`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-normsq), [`gaussC_pos`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc-pos). $\square$

<small>Used by [`gaussMode'_norm_le`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm-le), [`gaussMode_integrable_fn`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-integrable-fn).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-continuous"></a>
**Lemma 438** (`gaussMode_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L131)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar)
$$

*Proof.* By [`gaussC`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc). $\square$

<small>Used by [`gaussMode'_continuous`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-continuous), [`gaussMode_memLp`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-memlp), [`gaussMode_integrable_fn`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-integrable-fn).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-hasderivat"></a>
**Lemma 439** (`gaussMode_hasDerivAt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L134)</small>

$$
({\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar})'({\theta})={\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}^{\prime}}\,\hbar\,\theta}
$$

*Proof.* By [`gaussC`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc). $\square$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-continuous"></a>
**Lemma 440** (`gaussMode'_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L155)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}^{\prime}}\,\hbar)
$$

*Proof.* By [`gaussMode`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode), [`gaussMode_continuous`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-continuous). $\square$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-norm-le"></a>
**Lemma 441** (`gaussMode'_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L158)</small>

`‖g₀'(θ)‖ ≤ C`, via `1 + θ² ≤ e^{θ²}` so `e^{−θ²/2}√(θ²+1) ≤ 1`.

$$
0 < \hbar \to \forall (\theta : \mathbb{R}), \|\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}^{\prime}}\,\hbar\,\theta\| \le \href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc}{\mathrm{gaussC}}\,\hbar
$$

*Proof.* By [`gaussMode`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode), [`gaussC_pos`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc-pos), [`gaussMode_norm`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm). $\square$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-sq-integrable"></a>
**Lemma 442** (`gaussMode_sq_integrable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L182)</small>

$$
\mathrm{Integrable}\,(\lambda \theta \mapsto {\|\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar\,\theta\|}^{2})\,\mathrm{volume}
$$

*Proof.* By [`gaussC`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc), [`gaussMode_normSq`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-normsq). $\square$

<small>Used by [`gaussMode_memLp`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-memlp).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-memlp"></a>
**Lemma 443** (`gaussMode_memLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L192)</small>

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar)\,2\,\mathrm{volume}
$$

*Proof.* By [`gaussMode_continuous`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-continuous), [`gaussMode_sq_integrable`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-sq-integrable). $\square$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian).</small>

<a id="d-qiqth-wedgekmstogr-gaussmode-integrable-fn"></a>
**Lemma 444** (`gaussMode_integrable_fn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/GaussianMode.lean#L196)</small>

$$
0 < \hbar \to \mathrm{Integrable}\,(\href{/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode}{\mathrm{gaussMode}}\,\hbar)\,\mathrm{volume}
$$

*Proof.* By [`gaussC`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussc), [`gaussMode_norm`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-norm), [`gaussMode_continuous`](/browser/qiqth-gaussianmode#d-qiqth-wedgekmstogr-gaussmode-continuous). $\square$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian).</small>

---
<small>[← all sections](/browser) · [← WienerL2](/browser/qiqth-fock-wienerl2) · [HregExplicitKG →](/browser/qiqth-hregexplicitkg) </small>