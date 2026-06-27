---
layout: ../../layouts/Deep.astro
title: QIQTH.EinsteinEquationOfState
eyebrow: EinsteinEquationOfState · section of the QIQT-H book
description: QIQTH.EinsteinEquationOfState — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← EffectGleason](/browser/qiqth-effectgleason) · [EinsteinFieldEquation →](/browser/qiqth-einsteinfieldequation) </small>

<small>EinsteinEquationOfState · entries 77–82 of 1000</small>

<a id="d-qiqth-einsteineos-gm"></a>
**Definition 77** (`gm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L29)</small>

Minkowski metric `(−,+,+,+)` on `Fin 4`, as a function of two indices.

$$
\href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-gm}{\eta_{{i}{j}}} \;:=\; \text{if }i = j\text{ then }\text{if }i = 0\text{ then }-1\text{ else }1\text{ else }0
$$

<small>Used by [`symmTensor_eq_smul_metric_of_null`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null), [`symmTensor_eq_smul_metric_of_null_general`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general), [`crux_of_pernull`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-crux-of-pernull), [`jacobson_einstein_equation_of_state`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-jacobson-einstein-equation-of-state), [`ppFrame_cong`](/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppframe-cong), [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_complete_covCong`](/browser/qiqth-qiqtgrcovcong#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete-covcong), [`qiqt_gr_explicit_kg`](/browser/qiqth-qiqtgrexplicitkg#d-qiqth-wedgekmstogr-qiqt-gr-explicit-kg), and 10 more.</small>

<a id="d-qiqth-einsteineos-qf"></a>
**Definition 78** (`QF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L32)</small>

The quadratic form of a *symmetric* tensor `C` evaluated on a 4-vector `(x0,x1,x2,x3)` — i.e. `∑_{μν} C_{μν} x^μ x^ν`, written out using `C i j = C j i`.


<small>Used by [`symmTensor_eq_smul_metric_of_null`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null), [`QF_eq_BL`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-qf-eq-bl), [`symmTensor_eq_smul_metric_of_null_general`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general).</small>

<a id="d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null"></a>
**Lemma 79** (`symmTensor_eq_smul_metric_of_null`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L39)</small>

**The algebraic crux of Jacobson's derivation.** A symmetric tensor `C` whose quadratic form vanishes on the *entire null cone* of Minkowski space (every `(x0,x1,x2,x3)` with `−x0²+x1²+x2²+x3² = 0`) is a scalar multiple of the metric: `C = c • g`. This is the step that turns the per-null-direction Clausius relation into a genuine tensor field equation.

$$
(\forall (i j : \mathrm{Fin}\,4), C\,i\,j = C\,j\,i) \to (\forall (x_{0} x_{1} x_{2} x_{3} : \mathbb{R}), -{x_{0}}^{2} + {x_{1}}^{2} + {x_{2}}^{2} + {x_{3}}^{2} = 0 \to \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-qf}{\mathrm{QF}}\,C\,x_{0}\,x_{1}\,x_{2}\,x_{3} = 0) \to \exists c, \forall (i j : \mathrm{Fin}\,4), C\,i\,j = c \cdot \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-gm}{\eta_{{i}{j}}}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`symmTensor_eq_smul_metric_of_null_general`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general).</small>

<a id="d-qiqth-einsteineos-bl"></a>
**Definition 80** (`BL`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L104)</small>

The bilinear form `∑_{ij} C_{ij} v^i v^j` of a tensor on a vector — the coordinate-free shape of `QF`.

$$
\href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({C})({v},{v})} \;:=\; \sum_{i} \sum_{j} C\,i\,j \cdot v\,i \cdot v\,j
$$

<small>Used by [`BL_smul_sub`](/browser/qiqth-clausiustopernull#d-qiqth-curvature-bl-smul-sub), [`QF_eq_BL`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-qf-eq-bl), [`symmTensor_eq_smul_metric_of_null_general`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general), [`crux_of_pernull`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-crux-of-pernull), [`jacobson_einstein_equation_of_state`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-jacobson-einstein-equation-of-state), [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_complete_covCong`](/browser/qiqth-qiqtgrcovcong#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete-covcong), [`qiqt_gr_explicit_kg`](/browser/qiqth-qiqtgrexplicitkg#d-qiqth-wedgekmstogr-qiqt-gr-explicit-kg), and 19 more.</small>

<a id="d-qiqth-einsteineos-qf-eq-bl"></a>
**Lemma 81** (`QF_eq_BL`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L107)</small>

`QF` is the bilinear form on the explicit 4-vector (for a symmetric tensor).

$$
(\forall (i j : \mathrm{Fin}\,4), C\,i\,j = C\,j\,i) \to \forall (x_{0} x_{1} x_{2} x_{3} : \mathbb{R}), \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-qf}{\mathrm{QF}}\,C\,x_{0}\,x_{1}\,x_{2}\,x_{3} = \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({C})({![x_{0} , x_{1} , x_{2} , x_{3}]},{![x_{0} , x_{1} , x_{2} , x_{3}]})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`symmTensor_eq_smul_metric_of_null_general`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general).</small>

<a id="d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general"></a>
**Lemma 82** (`symmTensor_eq_smul_metric_of_null_general`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L114)</small>

**The algebraic crux for a GENERAL Lorentzian metric** (Phase 3 — the framework bridge). A symmetric tensor `C` whose bilinear form vanishes on the *entire null cone* of an arbitrary Lorentzian metric `g` is a scalar multiple of `g`. The Lorentzian hypothesis enters as Sylvester's law of inertia: `g` is congruent to Minkowski, `g = Pᵀ·η·P` for an invertible `P` (`hcong` with `P`, `Pinv` a two-sided inverse). The proof is a **congruence reduction** to the proven Minkowski case `symmTensor_eq_smul_metric_of_null`: transform `C` by `Pinv`, apply the Minkowski lemma, transform back. This is exactly what upgrades Jacobson's per-null Clausius relation (stated in each point's local inertial frame) into the tensor field equation.

$$
(\forall (i j : \mathrm{Fin}\,4), C\,i\,j = C\,j\,i) \to \forall (P \mathrm{Pinv} : \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (i j : \mathrm{Fin}\,4), \sum_{k} P\,i\,k \cdot \mathrm{Pinv}\,k\,j = \delta_{ij}) \to (\forall (i j : \mathrm{Fin}\,4), \sum_{k} \mathrm{Pinv}\,i\,k \cdot P\,k\,j = \delta_{ij}) \to (\forall (i j : \mathrm{Fin}\,4), g\,i\,j = \sum_{k} \sum_{l} P\,k\,i \cdot \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P\,l\,j) \to (\forall (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g})({v},{v})} = 0 \to \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({C})({v},{v})} = 0) \to \exists c, \forall (i j : \mathrm{Fin}\,4), C\,i\,j = c \cdot g\,i\,j
$$

*Proof.* By [`QF`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-qf), [`symmTensor_eq_smul_metric_of_null`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null), [`QF_eq_BL`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-qf-eq-bl). $\square$

<small>Used by [`crux_of_pernull`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-crux-of-pernull).</small>

---
<small>[← all sections](/browser) · [← EffectGleason](/browser/qiqth-effectgleason) · [EinsteinFieldEquation →](/browser/qiqth-einsteinfieldequation) </small>