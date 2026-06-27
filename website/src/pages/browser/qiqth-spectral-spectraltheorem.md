---
layout: ../../layouts/Deep.astro
title: QIQTH.Spectral.SpectralTheorem
eyebrow: Spectral · section of the QIQT-H book
description: QIQTH.Spectral.SpectralTheorem — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← PVM](/browser/qiqth-spectral-pvm) · [StandardSubspaceModular →](/browser/qiqth-standardsubspacemodular) </small>

<small>Spectral · entries 670–752 of 1000</small>

<a id="d-qiqth-spectraltheorem-qform-congr-simp"></a>
**Lemma 670** (`congr_simp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean)</small>

$$
s = \mathrm{s\_1} \to \forall (z \mathrm{z\_1} : H), z = \mathrm{z\_1} \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,z = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,\mathrm{s\_1}\,\mathrm{z\_1}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qForm_neg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-neg), [`bForm_zero_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-zero-right).</small>

<a id="d-qiqth-spectraltheorem-bform-congr-simp"></a>
**Lemma 671** (`congr_simp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean)</small>

$$
s = \mathrm{s\_1} \to \forall (u \mathrm{u\_1} : H), u = \mathrm{u\_1} \to \forall (v \mathrm{v\_1} : H), v = \mathrm{v\_1} \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,\mathrm{s\_1}\,\mathrm{u\_1}\,\mathrm{v\_1}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`bForm_neg_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-neg-right).</small>

<a id="d-qiqth-spectraltheorem-specproj-congr-simp"></a>
**Lemma 672** (`congr_simp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean)</small>

$$
s = \mathrm{s\_1} \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,\mathrm{s\_1}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`specProj_finset_sum`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-finset-sum).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-congr-simp"></a>
**Lemma 673** (`congr_simp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean)</small>

$$
x = \mathrm{x\_1} \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,\mathrm{x\_1}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`specMeasure_zero`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-zero).</small>

<a id="d-qiqth-spectraltheorem-specfunctional"></a>
**Definition 674** (`specFunctional`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L84)</small>

The scalar spectral functional as an ℝ-linear map on compactly-supported continuous functions on the spectrum: `f ↦ re ⟪x, f(T) x⟫`, where `f(T) := cfcHom ha f`.

$$
\mathrm{specFunctional}\,H\,T\,x \;:=\; \{\mathrm{toFun} :=\lambda f \mapsto \mathrm{re}\,(\langle {x},{((\mathrm{cfcHom}\,\mathrm{ha})\,f.\mathrm{toContinuousMap})\,x}\rangle) , \mathrm{map\_add}^{\prime} :=\cdots , \mathrm{map\_smul}^{\prime} :=\cdots \}
$$

<small>Used by [`specPLM`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specplm).</small>

<a id="d-qiqth-spectraltheorem-specplm"></a>
**Definition 675** (`specPLM`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L100)</small>

The scalar spectral functional bundled as a **positive** linear functional `Λ_x : C_c(spectrum ℝ T, ℝ) →ₚ[ℝ] ℝ`.


<small>Used by [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`integral_specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure).</small>

<a id="d-qiqth-spectraltheorem-specmeasure"></a>
**Definition 676** (`specMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L111)</small>

The **scalar spectral measure** `μ_x` of a self-adjoint `T` at a vector `x`: the Riesz–Markov measure of the positive functional `Λ_x = specPLM`.

$$
\mu_{\mathrm{sp}}\,H\,T\,x \;:=\; \mathrm{rieszMeasure}\,(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specplm}{\mathrm{specPLM}}\,T\,\mathrm{ha}\,x)
$$

<small>Used by [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-congr-simp), [`integral_specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`specMeasure_real_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-univ), [`specMeasure_real_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-le), [`specMeasure_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-smul), [`specMeasure_parallelogram`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-parallelogram), [`specMeasure_add`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-add), and 22 more.</small>

<a id="d-qiqth-spectraltheorem-integral-specmeasure"></a>
**Lemma 677** (`integral_specMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L118)</small>

**Defining property of the scalar spectral measure** (Riesz–Markov representation): `∫ f dμ_x = re ⟪x, f(T) x⟫` for every `f ∈ C_c(spectrum ℝ T, ℝ)`.

$$
\int (s : (\mathrm{sp}\,\mathbb{R}\,T)), f\,s \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x = \mathrm{re}\,(\langle {x},{((\mathrm{cfcHom}\,\mathrm{ha})\,f.\mathrm{toContinuousMap})\,x}\rangle)
$$

*Proof.* By [`specPLM`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specplm). $\square$

<small>Used by [`specMeasure_real_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-univ), [`specMeasure_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-smul), [`specMeasure_parallelogram`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-parallelogram), [`specMeasure_add`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-add), [`integral_specMeasure_cont`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure-cont), [`re_inner_T_eq_integral`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-re-inner-t-eq-integral).</small>

<a id="d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure"></a>
**Lemma 678** (`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L124)</small>

`μ_x` is a finite measure (the spectrum is compact).

$$
\mathrm{IsFiniteMeasure}\,(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x)
$$

*Proof.* By [`specPLM`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specplm). $\square$

<small>Used by [`specMeasure_real_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-le), [`specMeasure_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-smul), [`specMeasure_parallelogram`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-parallelogram), [`specMeasure_add`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-add), [`qForm_parallelogram`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-parallelogram), [`qForm_add`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-add), [`qForm_union`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-union), [`specProj_hasSum`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-hassum), and 6 more.</small>

<a id="d-qiqth-spectraltheorem-specmeasure-real-univ"></a>
**Lemma 679** (`specMeasure_real_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L130)</small>

**Total mass of the scalar spectral measure** — the scalar-level `E(univ) = 1`: `μ_x(univ) = ‖x‖²` (as a real number), since `1(T) = 1` and `re ⟪x, x⟫ = ‖x‖²`.

$$
(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x).\mathrm{real} = {\|x\|}^{2}
$$

*Proof.* By [`integral_specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure). $\square$

<small>Used by [`specMeasure_real_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-le), [`qForm_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-univ).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-real-le"></a>
**Lemma 680** (`specMeasure_real_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L175)</small>

**Per-set bound** for the scalar spectral measure: `μ_z(B) ≤ ‖z‖²` for every set `B` (monotonicity against the total mass `μ_z(univ) = ‖z‖²`).  This feeds the operator-norm bound on the spectral projections `E(B)`.

$$
(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z).\mathrm{real}\,B \le {\|z\|}^{2}
$$

*Proof.* By [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`specMeasure_real_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-univ). $\square$

<small>Used by [`bForm_abs_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-abs-le), [`specProj_le_one`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-le-one).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-smul"></a>
**Lemma 681** (`specMeasure_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L193)</small>

**Scaling law** of the scalar spectral measure: `μ_{c•x} = ‖c‖² · μ_x`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(c \cdot x) = {\|c\|_{+}}^{2} \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x
$$

*Proof.* By [`integral_specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure). $\square$

<small>Used by [`specMeasure_zero`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-zero), [`qForm_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-smul).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-parallelogram"></a>
**Lemma 682** (`specMeasure_parallelogram`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L206)</small>

**Parallelogram law** of the scalar spectral measure: `μ_{x+y} + μ_{x−y} = 2·μ_x + 2·μ_y` (the cross terms of the quadratic form cancel). Holds for any operator; the engine for sesquilinearity of the polarized form.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + y) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - y) = 2 \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x + 2 \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,y
$$

*Proof.* By [`integral_specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure). $\square$

<small>Used by [`qForm_parallelogram`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-parallelogram).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-add"></a>
**Lemma 683** (`specMeasure_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L227)</small>

**Additivity engine** (measure level): the second-difference identity `μ_{x+a+b} + μ_{x−a} + μ_{x−b} = μ_{x−a−b} + μ_{x+a} + μ_{x+b}` (both sides expand to `3q(x)+2q(a)+2q(b)+g(a,b)` for the quadratic form `q` and its symmetric bilinear part `g`). Applied with `(a,b)=(y₁,y₂)` and `(a,b)=(I·y₁, I·y₂)` it yields additivity of the polarized spectral form in `y`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + a + b) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - a) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - b) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - a - b) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + a) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + b)
$$

*Proof.* By [`integral_specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure). $\square$

<small>Used by [`qForm_add`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-add).</small>

<a id="d-qiqth-spectraltheorem-qform"></a>
**Definition 684** (`qForm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L256)</small>

The diagonal quadratic form `q_s(z) = μ_z(s)` (real, nonnegative).

$$
q\,H\,T\,s\,z \;:=\; (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z).\mathrm{real}\,s
$$

<small>Used by [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-congr-simp), [`qForm_nonneg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-nonneg), [`qForm_zero`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-zero), [`qForm_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-smul), [`qForm_neg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-neg), [`qForm_parallelogram`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-parallelogram), [`qForm_add`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-add), [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), and 23 more.</small>

<a id="d-qiqth-spectraltheorem-qform-nonneg"></a>
**Lemma 685** (`qForm_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L260)</small>

$$
0 \le \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,z
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure). $\square$

<small>Used by [`bForm_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sq-le), [`bForm_abs_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-abs-le), [`specProj_isPositive`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-ispositive).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-zero"></a>
**Lemma 686** (`specMeasure_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L263)</small>

`μ_0 = 0` (the zero vector gives the zero measure).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,0 = 0
$$

*Proof.* By [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-congr-simp), [`specMeasure_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-smul). $\square$

<small>Used by [`qForm_zero`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-zero).</small>

<a id="d-qiqth-spectraltheorem-qform-zero"></a>
**Lemma 687** (`qForm_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L268)</small>

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,0 = 0
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`specMeasure_zero`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-zero). $\square$

<small>Used by [`bForm_self`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-self).</small>

<a id="d-qiqth-spectraltheorem-qform-smul"></a>
**Lemma 688** (`qForm_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L272)</small>

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(c \cdot z) = {\|c\|}^{2} \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,z
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`specMeasure_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-smul). $\square$

<small>Used by [`qForm_neg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-neg), [`bForm_self`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-self), [`qForm_real_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-real-smul), [`bForm_I_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-i-smul).</small>

<a id="d-qiqth-spectraltheorem-qform-neg"></a>
**Lemma 689** (`qForm_neg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L277)</small>

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(-z) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,z
$$

*Proof.* By [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-congr-simp), [`qForm_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-smul). $\square$

<small>Used by [`bForm_comm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-comm).</small>

<a id="d-qiqth-spectraltheorem-qform-parallelogram"></a>
**Lemma 690** (`qForm_parallelogram`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L282)</small>

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(x + y) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(x - y) = 2 \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,x + 2 \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,y
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`specMeasure_parallelogram`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-parallelogram). $\square$

<small>Used by [`qForm_add_expand`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-add-expand).</small>

<a id="d-qiqth-spectraltheorem-qform-add"></a>
**Lemma 691** (`qForm_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L294)</small>

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(x + a + b) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(x - a) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(x - b) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(x - a - b) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(x + a) + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(x + b)
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`specMeasure_add`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-add). $\square$

<small>Used by [`bForm_add_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-add-right).</small>

<a id="d-qiqth-spectraltheorem-bform"></a>
**Definition 692** (`bForm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L301)</small>

The polarized bilinear form `b_s(u,v) = ¼(q_s(u+v) − q_s(u−v))`.

$$
b\,H\,T\,s\,u\,v \;:=\; (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(u + v) - \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(u - v)) / 4
$$

<small>Used by [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-congr-simp), [`qForm_add_expand`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-add-expand), [`bForm_self`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-self), [`bForm_comm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-comm), [`bForm_add_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-add-right), [`bForm_zero_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-zero-right), [`bFormRight`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bformright), [`bForm_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sq-le), and 22 more.</small>

<a id="d-qiqth-spectraltheorem-qform-add-expand"></a>
**Lemma 693** (`qForm_add_expand`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L305)</small>

Expansion identity: `q_s(p+q) = q_s(p) + q_s(q) + 2 b_s(p,q)` (from the parallelogram law).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(p + q) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,p + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,q + 2 \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,p\,q
$$

*Proof.* By [`qForm_parallelogram`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-parallelogram). $\square$

<small>Used by [`bForm_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sq-le).</small>

<a id="d-qiqth-spectraltheorem-bform-self"></a>
**Lemma 694** (`bForm_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L312)</small>

`b_s(u,u) = q_s(u)`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,u = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,u
$$

*Proof.* By [`qForm_zero`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-zero), [`qForm_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-smul). $\square$

<small>Used by [`reApplyInnerSelf_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-reapplyinnerself-specproj).</small>

<a id="d-qiqth-spectraltheorem-bform-comm"></a>
**Lemma 695** (`bForm_comm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L320)</small>

`b_s` is symmetric.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,v\,u
$$

*Proof.* By [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`qForm_neg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-neg). $\square$

<small>Used by [`cForm_hermitian`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-hermitian), [`bForm_sub_left`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sub-left).</small>

<a id="d-qiqth-spectraltheorem-bform-add-right"></a>
**Lemma 696** (`bForm_add_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L326)</small>

`b_s` is additive in its right argument.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,(v + w) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,w
$$

*Proof.* By [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`qForm_add`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-add). $\square$

<small>Used by [`bFormRight`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bformright), [`bForm_sub_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sub-right), [`cForm_add_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-add-right).</small>

<a id="d-qiqth-spectraltheorem-qform-real-smul"></a>
**Lemma 697** (`qForm_real_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L339)</small>

Real-scalar version of the scaling law: `q_s(r•z) = r²·q_s(z)`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,(r \cdot z) = {r}^{2} \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,z
$$

*Proof.* By [`qForm_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-smul). $\square$

<small>Used by [`bForm_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sq-le).</small>

<a id="d-qiqth-spectraltheorem-bform-zero-right"></a>
**Lemma 698** (`bForm_zero_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L344)</small>

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,0 = 0
$$

*Proof.* By [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-congr-simp), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform). $\square$

<small>Used by [`bFormRight`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bformright).</small>

<a id="d-qiqth-spectraltheorem-bformright"></a>
**Definition 699** (`bFormRight`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L348)</small>

`b_s(u, ·)` bundled as an additive homomorphism (used for ℚ-homogeneity in Cauchy–Schwarz).

$$
\mathrm{bFormRight}\,H\,T\,s\,u \;:=\; \{\mathrm{toFun} :=\lambda w \mapsto \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,w , \mathrm{map\_zero}^{\prime} :=\cdots , \mathrm{map\_add}^{\prime} :=\cdots \}
$$

<small>Used by [`bForm_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sq-le), [`bForm_real_smul_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-real-smul-right).</small>

<a id="d-qiqth-spectraltheorem-bform-sq-le"></a>
**Lemma 700** (`bForm_sq_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L354)</small>

**Cauchy–Schwarz** for the spectral form: `b_s(u,v)² ≤ q_s(u)·q_s(v)`. Because `q_s ≥ 0`, the quadratic `t ↦ q_s(u + t•v) = q_s(v)·t² + 2 b_s(u,v)·t + q_s(u)` is nonnegative on `ℚ` (hence on `ℝ` by density), so its discriminant is `≤ 0`.

$$
{\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v}^{2} \le \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,u \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,v
$$

*Proof.* By [`qForm_nonneg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-nonneg), [`qForm_add_expand`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-add-expand), [`qForm_real_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-real-smul), [`bFormRight`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bformright). $\square$

<small>Used by [`bForm_abs_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-abs-le).</small>

<a id="d-qiqth-spectraltheorem-bform-sub-right"></a>
**Lemma 701** (`bForm_sub_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L386)</small>

`b_s` is subtractive in its right argument.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,(v - w) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v - \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,w
$$

*Proof.* By [`bForm_add_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-add-right). $\square$

<small>Used by [`bForm_continuous_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-continuous-right), [`bForm_sub_left`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sub-left).</small>

<a id="d-qiqth-spectraltheorem-bform-abs-le"></a>
**Lemma 702** (`bForm_abs_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L393)</small>

**Boundedness** of the spectral form: `|b_s(u,v)| ≤ ‖u‖·‖v‖` (from Cauchy–Schwarz and `q_s(z) ≤ ‖z‖²`).

$$
|\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v| \le \|u\| \cdot \|v\|
$$

*Proof.* By [`specMeasure_real_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-le), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`qForm_nonneg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-nonneg), [`bForm_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sq-le). $\square$

<small>Used by [`bForm_continuous_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-continuous-right), [`cForm_norm_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-norm-le).</small>

<a id="d-qiqth-spectraltheorem-bform-continuous-right"></a>
**Lemma 703** (`bForm_continuous_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L407)</small>

`b_s(u, ·)` is continuous (Lipschitz with constant `‖u‖`).

$$
\mathrm{Continuous}\,\lambda v \mapsto \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v
$$

*Proof.* By [`bForm_sub_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sub-right), [`bForm_abs_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-abs-le). $\square$

<small>Used by [`bForm_real_smul_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-real-smul-right).</small>

<a id="d-qiqth-spectraltheorem-bform-real-smul-right"></a>
**Lemma 704** (`bForm_real_smul_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L415)</small>

**ℝ-homogeneity** of `b_s(u, ·)` (continuity + `map_real_smul`).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,(r \cdot v) = r \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v
$$

*Proof.* By [`bFormRight`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bformright), [`bForm_continuous_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-continuous-right). $\square$

<small>Used by [`bForm_neg_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-neg-right).</small>

<a id="d-qiqth-spectraltheorem-bform-neg-right"></a>
**Lemma 705** (`bForm_neg_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L421)</small>

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,(-v) = -\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v
$$

*Proof.* By [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-congr-simp), [`bForm_real_smul_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-real-smul-right). $\square$

<small>Used by [`bForm_I_comm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-i-comm).</small>

<a id="d-qiqth-spectraltheorem-bform-i-smul"></a>
**Lemma 706** (`bForm_I_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L426)</small>

`b_s` is invariant under simultaneous multiplication by `i`: `b_s(I•u, I•v) = b_s(u,v)` (from the `i`-invariance `q_s(I•z) = q_s(z)`).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,(i \cdot u)\,(i \cdot v) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v
$$

*Proof.* By [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`qForm_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-smul). $\square$

<small>Used by [`bForm_I_comm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-i-comm).</small>

<a id="d-qiqth-spectraltheorem-bform-i-comm"></a>
**Lemma 707** (`bForm_I_comm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L434)</small>

The `i`-twist: `b_s(I•x, y) = − b_s(x, I•y)`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,(i \cdot x)\,y = -\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,x\,(i \cdot y)
$$

*Proof.* By [`bForm_neg_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-neg-right), [`bForm_I_smul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-i-smul). $\square$

<small>Used by [`cForm_hermitian`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-hermitian).</small>

<a id="d-qiqth-spectraltheorem-cform"></a>
**Definition 708** (`cForm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L443)</small>

The complex spectral form `c_s(x,y) = b_s(x,y) − i·b_s(x, I•y)`; its Riesz representation will be the spectral projection `E(s)`, with `⟪E(s) x, y⟫ = c_s(x,y)`.

$$
c\,H\,T\,s\,x\,y \;:=\; (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,x\,y) - i \cdot (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,x\,(i \cdot y))
$$

<small>Used by [`cForm_add_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-add-right), [`cForm_norm_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-norm-le), [`cFormCLM`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm), [`cFormCLM_norm_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm-norm-le), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj), [`cForm_empty`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-empty), [`specProj_empty`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-empty), [`cForm_hermitian`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-hermitian), and 8 more.</small>

<a id="d-qiqth-spectraltheorem-cform-add-right"></a>
**Lemma 709** (`cForm_add_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L448)</small>

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,x\,(y + z) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,x\,y + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,x\,z
$$

*Proof.* By [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`bForm_add_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-add-right). $\square$

<small>Used by [`cFormCLM`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm), [`cFormCLM_norm_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm-norm-le).</small>

<a id="d-qiqth-spectraltheorem-cform-norm-le"></a>
**Lemma 710** (`cForm_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L530)</small>

**Norm bound**: `‖c_s(x,y)‖ ≤ 2·‖x‖·‖y‖`.

$$
\|\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,x\,y\| \le 2 \cdot \|x\| \cdot \|y\|
$$

*Proof.* By [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`bForm_abs_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-abs-le). $\square$

<small>Used by [`cFormCLM`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm), [`cFormCLM_norm_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm-norm-le).</small>

<a id="d-qiqth-spectraltheorem-cformclm"></a>
**Definition 711** (`cFormCLM`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L546)</small>

`c_s(x, ·)` bundled as a continuous ℂ-linear functional `H →L[ℂ] ℂ`.

$$
\mathrm{cFormCLM}\,H\,T\,s\,x \;:=\; \{\mathrm{toFun} :=\lambda y \mapsto \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,x\,y , \mathrm{map\_add}^{\prime} :=\cdots , \mathrm{map\_smul}^{\prime} :=\cdots \}.\mathrm{mkContinuous}\,(2 \cdot \|x\|)\,\cdots
$$

<small>Used by [`cFormCLM_norm_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm-norm-le), [`specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj).</small>

<a id="d-qiqth-spectraltheorem-cformclm-norm-le"></a>
**Lemma 712** (`cFormCLM_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L558)</small>

$$
\|\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm}{\mathrm{cFormCLM}}\,T\,\mathrm{ha}\,s\,x\| \le 2 \cdot \|x\|
$$

*Proof.* By [`cForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform), [`cForm_add_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-add-right), [`cForm_norm_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-norm-le). $\square$

<small>Used by [`specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj).</small>

<a id="d-qiqth-spectraltheorem-specproj"></a>
**Definition 713** (`specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L563)</small>

The **spectral projection** `E(s) : H →L[ℂ] H`, obtained by Riesz-representing the bounded sesquilinear form `c_s` (`⟪E(s) x, y⟫ = c_s(x,y)`).

$$
E\,H\,T\,s \;:=\; \mathrm{continuousLinearMapOfBilin}\,(\{\mathrm{toFun} :=\lambda x \mapsto \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm}{\mathrm{cFormCLM}}\,T\,\mathrm{ha}\,s\,x , \mathrm{map\_add}^{\prime} :=\cdots , \mathrm{map\_smul}^{\prime} :=\cdots \}.\mathrm{mkContinuous}\,2\,\cdots )
$$

<small>Used by [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-congr-simp), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj), [`specProj_empty`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-empty), [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint), [`specProj_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-univ), [`reApplyInnerSelf_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [`specProj_isPositive`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-ispositive), [`specProj_union_disjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-union-disjoint), and 10 more.</small>

<a id="d-qiqth-spectraltheorem-inner-specproj"></a>
**Lemma 714** (`inner_specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L580)</small>

**Defining identity of the spectral projection**: `⟪E(s) x, y⟫ = c_s(x,y)`.

$$
\langle {(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,x},{y}\rangle = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,x\,y
$$

*Proof.* By [`cFormCLM`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm), [`cFormCLM_norm_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cformclm-norm-le). $\square$

<small>Used by [`specProj_empty`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-empty), [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint), [`specProj_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-univ), [`reApplyInnerSelf_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [`specProj_union_disjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-union-disjoint), [`re_inner_cfcHom_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [`specProj_inter`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-inter).</small>

<a id="d-qiqth-spectraltheorem-cform-empty"></a>
**Lemma 715** (`cForm_empty`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L586)</small>

`c_∅ = 0`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,\emptyset \,x\,y = 0
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform). $\square$

<small>Used by [`specProj_empty`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-empty).</small>

<a id="d-qiqth-spectraltheorem-specproj-empty"></a>
**Lemma 716** (`specProj_empty`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L591)</small>

`E(∅) = 0`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,\emptyset = 0
$$

*Proof.* By [`cForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj), [`cForm_empty`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-empty). $\square$

<small>Used by [`specProj_finset_sum`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-finset-sum), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectraltheorem-cform-hermitian"></a>
**Lemma 717** (`cForm_hermitian`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L596)</small>

**Hermitian symmetry** of the form: `conj(c_s(y,x)) = c_s(x,y)`.

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,y\,x) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,x\,y
$$

*Proof.* By [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`bForm_comm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-comm), [`bForm_I_comm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-i-comm). $\square$

<small>Used by [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint).</small>

<a id="d-qiqth-spectraltheorem-specproj-isselfadjoint"></a>
**Lemma 718** (`specProj_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L605)</small>

`E(s)` is self-adjoint.

$$
\mathrm{IsSelfAdjoint}\,(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)
$$

*Proof.* By [`cForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj), [`cForm_hermitian`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-hermitian). $\square$

<small>Used by [`specProj_isPositive`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-ispositive), [`specProj_le_one`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-le-one), [`norm_specProj_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-norm-specproj-sq-le), [`re_inner_cfcHom_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [`specProj_inter`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-inter), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`scalarMeasure_eq_specMeasure`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-qform-univ"></a>
**Lemma 719** (`qForm_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L613)</small>

`q_univ(z) = ‖z‖²`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,z = {\|z\|}^{2}
$$

*Proof.* By [`specMeasure_real_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-univ). $\square$

<small>Used by [`bForm_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-univ).</small>

<a id="d-qiqth-spectraltheorem-bform-univ"></a>
**Lemma 720** (`bForm_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L617)</small>

`b_univ(x,y) = re ⟪x,y⟫` (polarization of the norm).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,x\,y = \mathrm{re}\,(\langle {x},{y}\rangle)
$$

*Proof.* By [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`qForm_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-univ). $\square$

<small>Used by [`cForm_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-univ).</small>

<a id="d-qiqth-spectraltheorem-cform-univ"></a>
**Lemma 721** (`cForm_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L624)</small>

`c_univ(x,y) = ⟪x,y⟫`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,x\,y = \langle {x},{y}\rangle
$$

*Proof.* By [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`bForm_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-univ). $\square$

<small>Used by [`specProj_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-univ).</small>

<a id="d-qiqth-spectraltheorem-specproj-univ"></a>
**Lemma 722** (`specProj_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L637)</small>

`E(univ) = 1`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha} = 1
$$

*Proof.* By [`cForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj), [`cForm_univ`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-univ). $\square$

<small>Used by [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectraltheorem-reapplyinnerself-specproj"></a>
**Lemma 723** (`reApplyInnerSelf_specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L643)</small>

The diagonal of the spectral form is the (real, nonnegative) quadratic form: `re ⟪E(s) x, x⟫ = q_s(x)`.

$$
(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s).\mathrm{reApplyInnerSelf}\,x = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,x
$$

*Proof.* By [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`bForm_self`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-self), [`cForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj). $\square$

<small>Used by [`specProj_isPositive`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-ispositive), [`specProj_le_one`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-le-one), [`norm_specProj_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-norm-specproj-sq-le), [`scalarMeasure_eq_specMeasure`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-specproj-ispositive"></a>
**Lemma 724** (`specProj_isPositive`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L654)</small>

`E(s)` is a positive operator.

$$
(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s).\mathrm{IsPositive}
$$

*Proof.* By [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`qForm_nonneg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-nonneg), [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint), [`reApplyInnerSelf_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-reapplyinnerself-specproj). $\square$

<small>Used by [`norm_specProj_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-norm-specproj-sq-le).</small>

<a id="d-qiqth-spectraltheorem-qform-union"></a>
**Lemma 725** (`qForm_union`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L661)</small>

Finite additivity of the diagonal form on disjoint sets.

$$
\mathrm{Disjoint}\,s\,t \to \mathrm{MeasurableSet}\,t \to \forall (z : H), \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,(s \cup t)\,z = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,z + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,t\,z
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure). $\square$

<small>Used by [`cForm_union_disjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-union-disjoint).</small>

<a id="d-qiqth-spectraltheorem-cform-union-disjoint"></a>
**Lemma 726** (`cForm_union_disjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L667)</small>

Finite additivity of the complex form on disjoint sets.

$$
\mathrm{Disjoint}\,s\,t \to \mathrm{MeasurableSet}\,t \to \forall (x y : H), \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,(s \cup t)\,x\,y = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,s\,x\,y + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform}{c}\,T\,\mathrm{ha}\,t\,x\,y
$$

*Proof.* By [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`qForm_union`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform-union). $\square$

<small>Used by [`specProj_union_disjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-union-disjoint).</small>

<a id="d-qiqth-spectraltheorem-specproj-union-disjoint"></a>
**Lemma 727** (`specProj_union_disjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L677)</small>

**Finite additivity** of the spectral projection on disjoint measurable sets: `E(s ∪ t) = E(s) + E(t)`.

$$
\mathrm{Disjoint}\,s\,t \to \mathrm{MeasurableSet}\,t \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(s \cup t) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,t
$$

*Proof.* By [`cForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj), [`cForm_union_disjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform-union-disjoint). $\square$

<small>Used by [`specProj_finset_sum`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-finset-sum), [`specProj_hasSum`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-hassum).</small>

<a id="d-qiqth-spectraltheorem-specproj-le-one"></a>
**Lemma 728** (`specProj_le_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L687)</small>

`E(s) ≤ 1` (the spectral projection is a contraction in the Loewner order): `1 − E(s)` is positive since `re ⟪(1−E(s)) x, x⟫ = ‖x‖² − q_s(x) ≥ 0`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s \le 1
$$

*Proof.* By [`specMeasure_real_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-real-le), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint), [`reApplyInnerSelf_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-reapplyinnerself-specproj). $\square$

<small>Used by [`norm_specProj_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-norm-specproj-sq-le).</small>

<a id="d-qiqth-spectraltheorem-norm-specproj-sq-le"></a>
**Lemma 729** (`norm_specProj_sq_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L703)</small>

**Effect estimate**: for the positive contraction `E(s)`, `‖E(s) x‖² ≤ q_s(x)`. (From `E(s)² ≤ E(s)`, i.e. `E(s)·(1−E(s)) ≥ 0` for commuting positives.)

$$
{\|(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,x\|}^{2} \le \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform}{q}\,T\,\mathrm{ha}\,s\,x
$$

*Proof.* By [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint), [`reApplyInnerSelf_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [`specProj_isPositive`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-ispositive), [`specProj_le_one`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-le-one). $\square$

<small>Used by [`specProj_hasSum`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-hassum).</small>

<a id="d-qiqth-spectraltheorem-specproj-finset-sum"></a>
**Lemma 730** (`specProj_finset_sum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L726)</small>

Finite (`Finset`) additivity of the spectral projection over pairwise-disjoint measurable sets: `∑ n ∈ F, E(A n) = E(⋃ n ∈ F, A n)`.

$$
(\forall (n : \mathbb{N}), \mathrm{MeasurableSet}\,(A\,n)) \to (\mathrm{Pairwise}\,\lambda m n \mapsto \mathrm{Disjoint}\,(A\,m)\,(A\,n)) \to \forall (F : \mathrm{Finset}\,\mathbb{N}), \sum_{n F} \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(A\,n) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(\bigcup n\in F, A\,n)
$$

*Proof.* By [`congr_simp`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-congr-simp), [`specProj_empty`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-empty), [`specProj_union_disjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-union-disjoint). $\square$

<small>Used by [`specProj_hasSum`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-hassum).</small>

<a id="d-qiqth-spectraltheorem-specproj-hassum"></a>
**Lemma 731** (`specProj_hasSum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L743)</small>

**σ-additivity** of the spectral projection (strong/SOT): for pairwise-disjoint measurable `A`, `HasSum (fun n => E(A n) x) (E(⋃ n, A n) x)`.  Proved by a norm-tail estimate: `‖∑_{n∈s} E(A n) x − E(⋃A) x‖² ≤ q_{(⋃A)∖(⋃_s)}(x) = q_{⋃A}(x) − ∑_{n∈s} q_{A n}(x) → 0` (effect estimate + scalar measure σ-additivity).

$$
(\forall (n : \mathbb{N}), \mathrm{MeasurableSet}\,(A\,n)) \to (\mathrm{Pairwise}\,\lambda m n \mapsto \mathrm{Disjoint}\,(A\,m)\,(A\,n)) \to \forall (x : H), \mathrm{HasSum}\,(\lambda n \mapsto (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(A\,n))\,x)\,((\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(\bigcup n, A\,n))\,x)
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`specProj_union_disjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-union-disjoint), [`norm_specProj_sq_le`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-norm-specproj-sq-le), [`specProj_finset_sum`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-finset-sum). $\square$

<small>Used by [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectraltheorem-inner-cfchom-mul"></a>
**Lemma 732** (`inner_cfcHom_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L822)</small>

**`cfcHom`-multiplicativity in the inner product**: `⟪g(T)x, h(T)y⟫ = ⟪x, (g·h)(T)y⟫` (self-adjointness of `g(T)` + `cfcHom` is an algebra hom).  This is the clean engine for the off-diagonal measure identity `ν_{g(T)x,y} = g·ν_{x,y}` that yields `E_inter` directly.

$$
\langle {((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x},{((\mathrm{cfcHom}\,\mathrm{ha})\,h)\,y}\rangle = \langle {x},{((\mathrm{cfcHom}\,\mathrm{ha})\,(g \cdot h))\,y}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`specMeasure_engine`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-engine).</small>

<a id="d-qiqth-spectraltheorem-integral-specmeasure-cont"></a>
**Lemma 733** (`integral_specMeasure_cont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L834)</small>

Bridge: the scalar-measure integral of a *continuous* `h` is `re ⟪z, h(T) z⟫` (the `C_c` version `integral_specMeasure` specialised via `HasCompactSupport.of_compactSpace`).

$$
\int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), h\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z = \mathrm{re}\,(\langle {z},{((\mathrm{cfcHom}\,\mathrm{ha})\,h)\,z}\rangle)
$$

*Proof.* By [`integral_specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure). $\square$

<small>Used by [`specMeasure_engine`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-engine), [`integral_specMeasure_polarization`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure-polarization).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-engine"></a>
**Lemma 734** (`specMeasure_engine`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L842)</small>

**Off-diagonal engine** (integral form): for continuous `g, h` and any vectors `x, v`, `(∫h dμ_{g(T)x+v} − ∫h dμ_{g(T)x−v}) = (∫(h·g) dμ_{x+v} − ∫(h·g) dμ_{x−v})`. Both sides equal `4·re⟪x, (h·g)(T) v⟫` (polarization + `inner_cfcHom_mul`).

$$
\int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), h\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x + v) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), h\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x - v) = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), (h \cdot g)\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), (h \cdot g)\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)
$$

*Proof.* By [`inner_cfcHom_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-cfchom-mul), [`integral_specMeasure_cont`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure-cont). $\square$

<small>Used by [`specMeasure_engine_measure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-engine-measure).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-engine-measure"></a>
**Lemma 735** (`specMeasure_engine_measure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L862)</small>

**Engine, measure form** (`g ≥ 0`): `μ_{g(T)x+v} + (μ_{x−v}·g) = μ_{g(T)x−v} + (μ_{x+v}·g)`, where `·g` is `withDensity (ENNReal.ofReal ∘ g)`.  Lifts `specMeasure_engine` to a measure identity by Riesz–Markov uniqueness.

$$
(\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), 0 \le g\,\omega) \to \forall (x v : H), (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x + v) + (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)).\mathrm{wd}\,\lambda \omega \mapsto {{g\,\omega}}) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x - v) + (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v)).\mathrm{wd}\,\lambda \omega \mapsto {{g\,\omega}}
$$

*Proof.* By [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`specMeasure_engine`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-engine). $\square$

<small>Used by [`specMeasure_setEngine_nonneg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-setengine-nonneg).</small>

<a id="d-qiqth-spectraltheorem-withdensity-real-setintegral"></a>
**Lemma 736** (`withDensity_real_setIntegral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L905)</small>

`withDensity`-to-`setIntegral` bridge: `((μ_z)·g).real s = ∫_s g dμ_z` for `g ≥ 0`.

$$
(\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), 0 \le g\,\omega) \to \forall (z : H) \{s : \mathrm{Set}\,(\mathrm{sp}\,\mathbb{R}\,T)\}, \mathrm{MeasurableSet}\,s \to ((\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z).\mathrm{wd}\,\lambda \omega \mapsto {{g\,\omega}}).\mathrm{real}\,s = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`specMeasure_setEngine_nonneg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-setengine-nonneg).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-setengine-nonneg"></a>
**Lemma 737** (`specMeasure_setEngine_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L915)</small>

**Set-level engine** for `g ≥ 0`: `q_s(g(T)x+v) − q_s(g(T)x−v) = ∫_s g dμ_{x+v} − ∫_s g dμ_{x−v}` (the `.real`-at-`s` evaluation of `specMeasure_engine_measure`).

$$
(\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), 0 \le g\,\omega) \to \forall (x v : H) \{s : \mathrm{Set}\,(\mathrm{sp}\,\mathbb{R}\,T)\}, \mathrm{MeasurableSet}\,s \to (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x + v)).\mathrm{real}\,s - (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x - v)).\mathrm{real}\,s = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)
$$

*Proof.* By [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`specMeasure_engine_measure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-engine-measure), [`withDensity_real_setIntegral`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-withdensity-real-setintegral). $\square$

<small>Used by [`specMeasure_setEngine`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-setengine).</small>

<a id="d-qiqth-spectraltheorem-bform-sub-left"></a>
**Lemma 738** (`bForm_sub_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L938)</small>

`b_s` is subtractive in its left argument.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,(u - w)\,v = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,u\,v - \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,w\,v
$$

*Proof.* By [`bForm_comm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-comm), [`bForm_sub_right`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sub-right). $\square$

<small>Used by [`specMeasure_setEngine`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-setengine).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-setengine"></a>
**Lemma 739** (`specMeasure_setEngine`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L944)</small>

**Set-level engine** (general continuous `g`): `q_s(g(T)x+v) − q_s(g(T)x−v) = ∫_s g dμ_{x+v} − ∫_s g dμ_{x−v}`.  Both sides are linear in `g`; extend the `g≥0` case by `g = (g+‖g‖) − ‖g‖`.

$$
\mathrm{MeasurableSet}\,s \to (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x + v)).\mathrm{real}\,s - (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x - v)).\mathrm{real}\,s = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)
$$

*Proof.* By [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`specMeasure_setEngine_nonneg`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-setengine-nonneg), [`bForm_sub_left`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-sub-left). $\square$

<small>Used by [`specProj_engine_measure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-engine-measure).</small>

<a id="d-qiqth-spectraltheorem-re-inner-cfchom-specproj"></a>
**Lemma 740** (`re_inner_cfcHom_specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L987)</small>

**Diagonal–`E(s)` identity**: `re ⟪x, h(T)(E(s)v)⟫ = b_s(h(T)x, v)` for continuous `h`. (Move `h(T)` and `E(s)` across by self-adjointness; the imaginary part of `c_s` drops under `re`.)

$$
\mathrm{re}\,(\langle {x},{((\mathrm{cfcHom}\,\mathrm{ha})\,h)\,((\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,v)}\rangle) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,s\,(((\mathrm{cfcHom}\,\mathrm{ha})\,h)\,x)\,v
$$

*Proof.* By [`cForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj), [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint). $\square$

<small>Used by [`specProj_engine_measure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-engine-measure).</small>

<a id="d-qiqth-spectraltheorem-integral-specmeasure-polarization"></a>
**Lemma 741** (`integral_specMeasure_polarization`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1005)</small>

Polarization at the scalar-measure level: `∫f dμ_{w+u} − ∫f dμ_{w−u} = 4·re⟪w, f(T)u⟫`.

$$
\int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), f\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(w + u) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), f\,\omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(w - u) = 4 \cdot \mathrm{re}\,(\langle {w},{((\mathrm{cfcHom}\,\mathrm{ha})\,f)\,u}\rangle)
$$

*Proof.* By [`integral_specMeasure_cont`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure-cont). $\square$

<small>Used by [`specProj_engine_measure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-engine-measure).</small>

<a id="d-qiqth-spectraltheorem-specproj-engine-measure"></a>
**Lemma 742** (`specProj_engine_measure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1019)</small>

**Final measure identity**: `μ_{x+E(s)v} + (μ_{x−v})↾s = μ_{x−E(s)v} + (μ_{x+v})↾s`. Proved by Riesz–Markov uniqueness: the test against continuous `f` reduces, via the polarization + `re_inner_cfcHom_specProj` + `specMeasure_setEngine`, to an identity that holds.

$$
\mathrm{MeasurableSet}\,s \to \forall (x v : H), \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,v) + (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)).\mathrm{restr}\,s = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,v) + (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v)).\mathrm{restr}\,s
$$

*Proof.* By [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`specMeasure_setEngine`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure-setengine), [`re_inner_cfcHom_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [`integral_specMeasure_polarization`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure-polarization). $\square$

<small>Used by [`bForm_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-specproj).</small>

<a id="d-qiqth-spectraltheorem-bform-specproj"></a>
**Lemma 743** (`bForm_specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1045)</small>

**The intersection identity at the form level**: `b_t(x, E(s)v) = b_{s∩t}(x, v)` (evaluate `specProj_engine_measure` at `t` via `.real`).

$$
\mathrm{MeasurableSet}\,s \to \mathrm{MeasurableSet}\,t \to \forall (x v : H), \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,t\,x\,((\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,v) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform}{b}\,T\,\mathrm{ha}\,(s \cap t)\,x\,v
$$

*Proof.* By [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`specProj_engine_measure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-engine-measure). $\square$

<small>Used by [`specProj_inter`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-inter).</small>

<a id="d-qiqth-spectraltheorem-specproj-inter"></a>
**Lemma 744** (`specProj_inter`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1057)</small>

**`E_inter`**: `E(s∩t) = E(s)·E(t)` — the projection / multiplicativity property, the final `ProjectionValuedMeasure` field.  `E(s)·E(t)` tested against `⟪·x,y⟫` is `c_t(x,E(s)y)`, which equals `c_{s∩t}(x,y)` by `bForm_specProj` (using `E(s)` ℂ-linear for the imaginary part).

$$
\mathrm{MeasurableSet}\,s \to \mathrm{MeasurableSet}\,t \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(s \cap t) = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,t
$$

*Proof.* By [`bForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform), [`cForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-cform), [`inner_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-specproj), [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint), [`bForm_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-bform-specproj). $\square$

<small>Used by [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`scalarMeasure_eq_specMeasure`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-pvm-of-selfadjoint"></a>
**Definition 745** (`PVM_of_selfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1073)</small>

**The bounded spectral theorem (PVM form)**: every bounded self-adjoint `T : H →L[ℂ] H` induces a projection-valued measure on `spectrum ℝ T`, with `E(s) = specProj`.  All structure fields are the lemmas proved above; `isIdem` is `E_inter` at `s = t`.

$$
\mathrm{PVM\_of\_selfAdjoint}\,H\,T \;:=\; \{E :=\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha} , \mathrm{isSA} :=\cdots , \mathrm{isIdem} :=\cdots , \mathrm{E\_empty} :=\cdots , \mathrm{E\_univ} :=\cdots , \mathrm{E\_inter} :=\cdots , \mathrm{hasSum\_iUnion} :=\cdots \}
$$

<small>Used by [`rvdSpecMeasure`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure), [`deviceOpC_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-norm-le), [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), [`rvdSpec_borelFC_diag`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspec-borelfc-diag), [`rvdSpecMeasure_zero_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-zero-levelset), [`rvdSpecMeasure_two_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-two-levelset), [`tendsto_integral_devChar_remainder_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-remainder-sq), [`tendsto_integral_devChar_diff_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-diff-sq), and 17 more.</small>

<a id="d-qiqth-spectraltheorem-re-inner-t-eq-integral"></a>
**Lemma 746** (`re_inner_T_eq_integral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1090)</small>

**Spectral representation of `T` (diagonal form)**: `∫_{σ(T)} λ dμ_x(λ) = re ⟪x, T x⟫`. Since `μ_x` is the scalar spectral measure of the `PVM_of_selfAdjoint` (`μ_x(s) = ⟪E(s)x,x⟫`), this is the statement `T = ∫ λ dE(λ)` tested on the diagonal — `T` recovered from its PVM.

$$
\int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), \omega \partial \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x = \mathrm{re}\,(\langle {x},{T\,x}\rangle)
$$

*Proof.* By [`integral_specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-integral-specmeasure). $\square$

<small>Used by [`diagInt_specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-diagint-speccoord).</small>

<a id="d-qiqth-spectraltheorem-borelfc"></a>
**Definition 747** (`borelFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1110)</small>

The **bounded Borel functional calculus** of a bounded self-adjoint `T`: `f(T)` for bounded measurable `f : σ(T) → ℂ`.

$$
\Phi_{B}\,H\,T\,f\,C \;:=\; (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,T\,\mathrm{ha}).\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}
$$

<small>Used by [`borelFC_congr_ae`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`deviceOpReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal), [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), [`deviceOpC_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-norm-le), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), and 36 more.</small>

<a id="d-qiqth-spectraltheorem-inner-borelfc"></a>
**Lemma 748** (`inner_borelFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1116)</small>

Defining property: `⟪x, f(T) y⟫ = B_f(x,y)` (the polarized scalar-measure form).

$$
\langle {x},{(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC})\,y}\rangle = (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,T\,\mathrm{ha}).\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc). $\square$

<small>Used by [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), [`rvdSpec_borelFC_diag`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspec-borelfc-diag), [`borelFC_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-adjoint), [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc).</small>

<a id="d-qiqth-spectraltheorem-borelfc-mul"></a>
**Lemma 749** (`borelFC_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1122)</small>

**Multiplicativity** of the bounded Borel FC: `(f·g)(T) = f(T)·g(T)`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hfp}\,\mathrm{hC0p}\,\mathrm{hCp} = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf} \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg}
$$

*Proof.* By [`boundedFC_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Used by [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`modUnitary_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-add), [`borelFC_comm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-comm), [`cfcCont_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-mul), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h), [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-spectraltheorem-borelfc-one"></a>
**Lemma 750** (`borelFC_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1130)</small>

The bounded Borel FC is **unital**: `(fun _ => 1)(T) = 1`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = 1
$$

*Proof.* By [`boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [`boundedFC_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Used by [`modUnitary_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-zero), [`cfcCont_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-one).</small>

<a id="d-qiqth-spectraltheorem-borelfc-const"></a>
**Lemma 751** (`borelFC_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1137)</small>

**Constant rule** `(fun _ => c)(T) = c·1` — the QIQTH-layer wrapper of `boundedFC_const`.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = c \cdot 1
$$

*Proof.* By [`boundedFC_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Used by [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-spectraltheorem-borelfc-indicator"></a>
**Lemma 752** (`borelFC_indicator`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1143)</small>

**Indicator rule** `𝟙_s(T) = E s` — the QIQTH-layer wrapper of `boundedFC_indicator`: the bounded Borel FC of a level-set indicator is the corresponding spectral projection of the PVM.

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,T\,\mathrm{ha}).E\,s
$$

*Proof.* By [`boundedFC_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator). $\square$

<small>Used by [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

---
<small>[← all sections](/browser) · [← PVM](/browser/qiqth-spectral-pvm) · [StandardSubspaceModular →](/browser/qiqth-standardsubspacemodular) </small>