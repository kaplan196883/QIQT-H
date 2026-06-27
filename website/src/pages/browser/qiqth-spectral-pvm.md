---
layout: ../../layouts/Deep.astro
title: QIQTH.Spectral.PVM
eyebrow: Spectral · section of the QIQT-H book
description: QIQTH.Spectral.PVM — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← RicciSymm](/browser/qiqth-riccisymm) · [SpectralTheorem →](/browser/qiqth-spectral-spectraltheorem) </small>

<small>Spectral · entries 586–669 of 1000</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure"></a>
**Lemma 586** (`ProjectionValuedMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L325)</small>

A **projection-valued measure** on a measurable space `Ω` acting on `H`: laws on *measurable* sets, with **strong-operator** countable additivity. This is the corrected primitive (cf. `PVContent`): on it the scalar measures `μ_x` are genuine finite measures and the Phase-1 analytic targets are sound.

`hasSum_iUnion` states σ-additivity vectorwise/strongly — `HasSum` in `H`, not in `H →L[ℂ] H` (operator-norm σ-additivity is false).

$$
(\Omega : Type\mathrm{u\_3}) \to (H : Type\mathrm{u\_4}) \to [\mathrm{MeasurableSpace}\,\Omega] \to [\mathrm{inst} : \mathrm{NormedAddCommGroup}\,H] \to [\mathrm{InnerProductSpace}\,\mathbb{C}\,H] \to [\mathrm{CompleteSpace}\,H] \to Type(max\mathrm{u\_3} \mathrm{u\_4})
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`mk`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-mk), [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`isSA`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-issa), [`isIdem`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-isidem), [`E_univ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-univ), [`E_inter`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-inter), [`adjoint_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq), [`E_apply_idem`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem), and 70 more.</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-mk"></a>
**Lemma 587** (`mk`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L332)</small>

$$
\{\Omega : Type\mathrm{u\_3}\} \to \{H : Type\mathrm{u\_4}\} \to [\mathrm{inst} : \mathrm{MeasurableSpace}\,\Omega] \to [\mathrm{inst\_1} : \mathrm{NormedAddCommGroup}\,H] \to [\mathrm{inst\_2} : \mathrm{InnerProductSpace}\,\mathbb{C}\,H] \to [\mathrm{inst\_3} : \mathrm{CompleteSpace}\,H] \to (E : \mathrm{Set}\,\Omega \to H \to L[\mathbb{C}] H) \to (\forall s : \mathrm{Set}\,\Omega, \mathrm{MeasurableSet}\,s \to \mathrm{IsSelfAdjoint}\,(E\,s)) \to (\forall s : \mathrm{Set}\,\Omega, \mathrm{MeasurableSet}\,s \to \mathrm{IsIdempotentElem}\,(E\,s)) \to E\,\emptyset = 0 \to E = 1 \to (\forall s t : \mathrm{Set}\,\Omega, \mathrm{MeasurableSet}\,s \to \mathrm{MeasurableSet}\,t \to E\,(s \cap t) = E\,s \cdot E\,t) \to (\forall \{A : \mathbb{N} \to \mathrm{Set}\,\Omega\}, (\forall (n : \mathbb{N}), \mathrm{MeasurableSet}\,(A\,n)) \to (\mathrm{Pairwise}\,\lambda m n \mapsto \mathrm{Disjoint}\,(A\,m)\,(A\,n)) \to \forall (x : H), \mathrm{HasSum}\,(\lambda n \mapsto (E\,(A\,n))\,x)\,((E\,(\bigcup n, A\,n))\,x)) \to \href{/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure}{\mathrm{ProjectionValuedMeasure}}\,\Omega\,H
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-e"></a>
**Definition 588** (`E`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L334)</small>

$$
E\,\Omega\,H\,\mathrm{self} \;:=\; \mathrm{self}.1
$$

<small>Used by [`rvdSpecMeasure_zero_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-zero-levelset), [`rvdSpecMeasure_two_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-two-levelset), [`isSA`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-issa), [`isIdem`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-isidem), [`E_univ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-univ), [`E_inter`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-inter), [`adjoint_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq), [`E_apply_idem`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem), and 21 more.</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-issa"></a>
**Lemma 589** (`isSA`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L335)</small>

$$
\mathrm{MeasurableSet}\,s \to \mathrm{IsSelfAdjoint}\,(\mathrm{self}.E\,s)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`adjoint_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-isidem"></a>
**Lemma 590** (`isIdem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L336)</small>

$$
\mathrm{MeasurableSet}\,s \to \mathrm{IsIdempotentElem}\,(\mathrm{self}.E\,s)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`E_apply_idem`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-e-univ"></a>
**Lemma 591** (`E_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L338)</small>

$$
\mathrm{self}.E = 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`scalarMeasure_univ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-e-inter"></a>
**Lemma 592** (`E_inter`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L339)</small>

$$
\mathrm{MeasurableSet}\,s \to \mathrm{MeasurableSet}\,t \to \mathrm{self}.E\,(s \cap t) = \mathrm{self}.E\,s \cdot \mathrm{self}.E\,t
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`integralSimple_mul_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq"></a>
**Lemma 593** (`adjoint_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L349)</small>

$$
\mathrm{MeasurableSet}\,s \to {{P.E\,s}}^{\dagger} = P.E\,s
$$

*Proof.* By [`isSA`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-issa). $\square$

<small>Used by [`inner_E_self`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-e-self).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem"></a>
**Lemma 594** (`E_apply_idem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L353)</small>

$$
\mathrm{MeasurableSet}\,s \to \forall (x : H), (P.E\,s)\,((P.E\,s)\,x) = (P.E\,s)\,x
$$

*Proof.* By [`isIdem`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-isidem). $\square$

<small>Used by [`inner_E_self`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-e-self).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-inner-e-self"></a>
**Lemma 595** (`inner_E_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L364)</small>

`⟪x, E s x⟫ = ‖E s x‖²` for measurable `s`.

$$
\mathrm{MeasurableSet}\,s \to \forall (x : H), \langle {x},{(P.E\,s)\,x}\rangle = {\|(P.E\,s)\,x\|}^{2}
$$

*Proof.* By [`adjoint_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq), [`E_apply_idem`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem). $\square$

<small>Used by [`diagInt_indicator_eq_inner`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure"></a>
**Definition 596** (`scalarMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L378)</small>

**The scalar spectral measure** `μ_x` — now a genuine `MeasureTheory.Measure Ω` (this is Phase-1 target T1, PROVED): the strong- operator σ-additivity of `E` (`hasSum_iUnion`) pushed through the bounded linear functional `⟪x,·⟫` gives σ-additivity of `s ↦ ‖E s x‖²`.


<small>Used by [`rvdSpecMeasure`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure), [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), [`rvdSpec_borelFC_diag`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspec-borelfc-diag), [`rvdSpecMeasure_zero_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-zero-levelset), [`rvdSpecMeasure_two_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-two-levelset), [`tendsto_integral_devChar_remainder_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-remainder-sq), [`tendsto_integral_devChar_diff_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-diff-sq), [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), and 23 more.</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply"></a>
**Lemma 597** (`scalarMeasure_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L406)</small>

Value of the scalar spectral measure on a measurable set.

$$
\mathrm{MeasurableSet}\,s \to (P.\mu\,x)\,s = {{{\|(P.E\,s)\,x\|}^{2}}}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdSpecMeasure_zero_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-zero-levelset), [`rvdSpecMeasure_two_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-two-levelset), [`scalarMeasure_univ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ), [`scalarMeasure_toReal`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal), [`scalarMeasure_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul), [`scalarMeasure_parallelogram_measure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure), [`scalarMeasure_odd_measure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure), [`scalarMeasure_eq_specMeasure`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ"></a>
**Lemma 598** (`scalarMeasure_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L411)</small>

**Total mass `‖x‖²`** — `μ_x` is a finite measure summing the resolution of identity.

$$
(P.\mu\,x) = {{{\|x\|}^{2}}}
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`E_univ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-univ), [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Used by [`instIsFiniteMeasure_scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [`diagInt_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [`diagInt_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-const).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-integralsimple"></a>
**Definition 599** (`integralSimple`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L420)</small>

**Spectral integral of a simple function** on the genuine PVM: `∫(∑ᵢ cᵢ 𝟙_{sᵢ}) dE = ∑ᵢ cᵢ E sᵢ`.

$$
\textstyle\int\,\Omega\,H\,P\,\iota\,t\,c\,\mathrm{sets} \;:=\; \sum_{i t} c\,i \cdot P.E\,(\mathrm{sets}\,i)
$$

<small>Used by [`inner_integralSimple_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-integralsimple-left), [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [`integralSimple_mul_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq), [`integralSimple_product_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq), [`boundedFC_simple_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [`boundedFC_simpleFunc`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [`boundedFC_simpleFunc_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-inner-integralsimple-left"></a>
**Lemma 600** (`inner_integralSimple_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L426)</small>

**Sesquilinear form of the simple integral** (pure linearity, no measurability needed): `⟪x, (∫f dE) y⟫ = ∑ᵢ cᵢ ⟪x, E sᵢ y⟫`.  This is the bilinear datum whose diagonal is `∫ f dμ_x` and whose polarization gives the complex measures `μ_{x,y}`.

$$
\langle {x},{(P.\textstyle\int\,t\,c\,\mathrm{sets})\,y}\rangle = \sum_{i t} c\,i \cdot \langle {x},{(P.E\,(\mathrm{sets}\,i))\,y}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal"></a>
**Lemma 601** (`scalarMeasure_toReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L484)</small>

The real value of `μ_x` on a measurable set: `(μ_x s).toReal = ‖E s x‖²`.

$$
\mathrm{MeasurableSet}\,s \to ((P.\mu\,x)\,s).\mathrm{toReal} = {\|(P.E\,s)\,x\|}^{2}
$$

*Proof.* By [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Used by [`diagInt_indicator_eq_inner`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure"></a>
**Lemma 602** (`instIsFiniteMeasure_scalarMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L539)</small>

`μ_x` is a **finite** measure (total mass `‖x‖²`) — so every bounded measurable function is Bochner-integrable against it.  Prerequisite for the integral functional `f ↦ ∫ f dμ_x` of the bounded-Borel FC.

$$
\mathrm{IsFiniteMeasure}\,(P.\mu\,x)
$$

*Proof.* By [`scalarMeasure_univ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ). $\square$

<small>Used by [`tendsto_integral_devChar_remainder_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-remainder-sq), [`tendsto_integral_devChar_diff_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-diff-sq), [`integrable_boundedMeasurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable), [`diagInt_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [`tendsto_diagInt_of_dominated`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul"></a>
**Lemma 603** (`scalarMeasure_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L561)</small>

**Scaling at the measure level:** `μ_{c·x} = ‖c‖² · μ_x`.  (`E s (c•x) = c•E s x` so `‖E s (c•x)‖² = ‖c‖²‖E s x‖²`.)

$$
P.\mu\,(c \cdot x) = {{{\|c\|}^{2}}} \cdot P.\mu\,x
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Used by [`diagInt_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure"></a>
**Lemma 604** (`scalarMeasure_parallelogram_measure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L570)</small>

**Parallelogram at the measure level:** `μ_{x+y} + μ_{x−y} = 2·μ_x + 2·μ_y`.

$$
P.\mu\,(x + y) + P.\mu\,(x - y) = 2 \cdot P.\mu\,x + 2 \cdot P.\mu\,y
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Used by [`diagInt_parallelogram`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable"></a>
**Lemma 605** (`integrable_boundedMeasurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L588)</small>

A bounded measurable function is **Bochner-integrable** against the finite measure `μ_x`.

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x : H), \mathrm{Integrable}\,f\,(P.\mu\,x)
$$

*Proof.* By [`instIsFiniteMeasure_scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure). $\square$

<small>Used by [`diagInt_parallelogram`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram), [`diagInt_odd`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd), [`diagInt_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [`diagInt_add`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-add), [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint"></a>
**Definition 606** (`diagInt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L596)</small>

**The diagonal functional** `D_f(x) := ∫ f dμ_x` (E2a of the bounded-Borel FC sub-plan).  Its homogeneity `D_f(c·x) = ‖c‖² D_f(x)` and parallelogram law are what make the polarized form `B_f(x,y)` sesquilinear.

$$
\textstyle\int\,\Omega\,H\,P\,f\,x \;:=\; \int (\omega : \Omega), f\,\omega \partial P.\mu\,x
$$

<small>Used by [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), [`rvdSpec_borelFC_diag`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspec-borelfc-diag), [`diagInt_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul), [`diagInt_parallelogram`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram), [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`bilinDiag_add_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [`diagInt_unit_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul), [`diagInt_neg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg), and 26 more.</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-smul"></a>
**Lemma 607** (`diagInt_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L602)</small>

**Homogeneity** of the diagonal functional: `D_f(c·x) = ‖c‖² D_f(x)`.

$$
P.\textstyle\int\,f\,(c \cdot x) = ({\|c\|}^{2}) \cdot P.\textstyle\int\,f\,x
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`scalarMeasure_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul). $\square$

<small>Used by [`diagInt_unit_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram"></a>
**Lemma 608** (`diagInt_parallelogram`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L609)</small>

**Parallelogram law** for the diagonal functional: `D_f(x+y) + D_f(x−y) = 2 D_f(x) + 2 D_f(y)`.

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H), P.\textstyle\int\,f\,(x + y) + P.\textstyle\int\,f\,(x - y) = 2 \cdot P.\textstyle\int\,f\,x + 2 \cdot P.\textstyle\int\,f\,y
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`scalarMeasure_parallelogram_measure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure), [`integrable_boundedMeasurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable). $\square$

<small>Used by [`bilinDiag_add_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag"></a>
**Definition 609** (`bilinDiag`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L625)</small>

**E2b — the polarized sesquilinear form** `B_f(x,y)`, mirroring Mathlib's Fréchet–von Neumann–Jordan `inner_` but with the quadratic functional `D_f = diagInt f` in place of `‖·‖²`.  Its diagonal is `D_f` and (once shown sesquilinear + bounded) it represents `∫ f dE` via `continuousLinearMapOfBilin`.

$$
\mathrm{bd}\,\Omega\,H\,P\,f\,x\,y \;:=\; {4}^{-1} \cdot (P.\textstyle\int\,f\,(x + y) - P.\textstyle\int\,f\,(x - y) + i \cdot P.\textstyle\int\,f\,(i \cdot x + y) - i \cdot P.\textstyle\int\,f\,(i \cdot x - y))
$$

<small>Used by [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), [`rvdSpec_borelFC_diag`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspec-borelfc-diag), [`bilinDiag_add_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [`bilinDiag_conj_symm`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [`bilinDiag_add_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right), [`bilinDiag_I_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left), [`bilinDiag_real_smul_left_nonneg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg), [`bilinDiag_zero_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left), and 28 more.</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left"></a>
**Lemma 610** (`bilinDiag_add_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L634)</small>

**Additivity in the first slot** of `B_f` — the Jordan–von Neumann core, ported from `InnerProductSpace.OfNorm.add_left` (no `algebraMap` casting needed since `D_f` is already ℂ-valued), using `diagInt_parallelogram`.

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y z : H), P.\mathrm{bd}\,f\,(x + y)\,z = P.\mathrm{bd}\,f\,x\,z + P.\mathrm{bd}\,f\,y\,z
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_parallelogram`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram). $\square$

<small>Used by [`bilinDiag_add_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right), [`bilinDiag_neg_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left), [`bilinDiag_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left), [`bilinDiagₗ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul"></a>
**Lemma 611** (`diagInt_unit_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L653)</small>

`D_f` is invariant under **unit-modulus scaling**: `D_f(c·x) = D_f(x)` when `‖c‖ = 1` (special case of `diagInt_smul`).

$$
\|c\| = 1 \to \forall (x : H), P.\textstyle\int\,f\,(c \cdot x) = P.\textstyle\int\,f\,x
$$

*Proof.* By [`diagInt_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul). $\square$

<small>Used by [`diagInt_neg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg), [`diagInt_I_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left), [`diagInt_I_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-right).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-neg"></a>
**Lemma 612** (`diagInt_neg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L659)</small>

`D_f` is **even**: `D_f(-x) = D_f(x)`.

$$
P.\textstyle\int\,f\,(-x) = P.\textstyle\int\,f\,x
$$

*Proof.* By [`diagInt_unit_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul). $\square$

<small>Used by [`diagInt_I_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left), [`bilinDiag_conj_symm`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [`bilinDiag_I_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left), [`bilinDiag_zero_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-conj"></a>
**Lemma 613** (`diagInt_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L663)</small>

**Conjugation** passes through `D_f`: `conj (D_f x) = D_{f̄}(x)` (the scalar measure `μ_x` is real, so `conj ∫ f = ∫ conj f`).

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(P.\textstyle\int\,f\,x) = P.\textstyle\int\,(\lambda \omega \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\omega))\,x
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure). $\square$

<small>Used by [`bilinDiag_conj_symm`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left"></a>
**Lemma 614** (`diagInt_I_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L669)</small>

`D_f(i·y + x) = D_f(i·x − y)` (unit-scaling invariance + evenness; used to establish the conjugate-symmetry of `B_f`).

$$
P.\textstyle\int\,f\,(i \cdot y + x) = P.\textstyle\int\,f\,(i \cdot x - y)
$$

*Proof.* By [`diagInt_unit_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul), [`diagInt_neg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg). $\square$

<small>Used by [`bilinDiag_conj_symm`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-i-right"></a>
**Lemma 615** (`diagInt_I_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L680)</small>

`D_f(i·y − x) = D_f(i·x + y)` (companion of `diagInt_I_left`).

$$
P.\textstyle\int\,f\,(i \cdot y - x) = P.\textstyle\int\,f\,(i \cdot x + y)
$$

*Proof.* By [`diagInt_unit_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul). $\square$

<small>Used by [`bilinDiag_conj_symm`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm"></a>
**Lemma 616** (`bilinDiag_conj_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L690)</small>

**Conjugate-symmetry of the polarized form** for complex `f`: `conj (B_f(y,x)) = B_{f̄}(x,y)` where `f̄ = conj ∘ f`.  (For real `f` this is the usual `⟪x,y⟫ = conj⟪y,x⟫`.)  This transfers slot-1 additivity to slot 2.

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(P.\mathrm{bd}\,f\,y\,x) = P.\mathrm{bd}\,(\lambda \omega \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\omega))\,x\,y
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_neg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg), [`diagInt_conj`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-conj), [`diagInt_I_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left), [`diagInt_I_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-right). $\square$

<small>Used by [`bilinDiag_add_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right), [`bilinDiag_smul_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right), [`borelFC_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-adjoint).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right"></a>
**Lemma 617** (`bilinDiag_add_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L703)</small>

**Additivity in the second slot** of `B_f`, from slot-1 additivity (of `f̄`) through `bilinDiag_conj_symm`.

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y z : H), P.\mathrm{bd}\,f\,x\,(y + z) = P.\mathrm{bd}\,f\,x\,y + P.\mathrm{bd}\,f\,x\,z
$$

*Proof.* By [`bilinDiag_add_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [`bilinDiag_conj_symm`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm). $\square$

<small>Used by [`bilinDiagₗ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left"></a>
**Lemma 618** (`bilinDiag_I_smul_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L719)</small>

**`i`-scaling in the first slot** (the `I_prop` of Jordan–von Neumann, pure algebra via `i² = −1` and evenness of `D_f`): `B_f(i·x, y) = conj(i)·B_f(x,y)`.

$$
P.\mathrm{bd}\,f\,(i \cdot x)\,y = (\mathrm{starRingEnd}\,\mathbb{C})\,i \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_neg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg). $\square$

<small>Used by [`bilinDiag_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure"></a>
**Lemma 619** (`scalarMeasure_odd_measure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L730)</small>

**Odd measure identity** (the continuity-free key to real homogeneity): for `r ≥ 0`, `μ_{r·x+y} + r·μ_{x−y} = μ_{r·x−y} + r·μ_{x+y}` (both sides equal `r²‖Ex‖² + ‖Ey‖² + r‖Ex‖² + r‖Ey‖²` at each set; all positive measures, no signed-measure machinery).

$$
0 \le r \to P.\mu\,(r \cdot x + y) + {{r}} \cdot P.\mu\,(x - y) = P.\mu\,(r \cdot x - y) + {{r}} \cdot P.\mu\,(x + y)
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Used by [`diagInt_odd`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-odd"></a>
**Lemma 620** (`diagInt_odd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L757)</small>

**Odd functional identity:** `D_f(r·x+y) − D_f(r·x−y) = r(D_f(x+y) − D_f(x−y))` (here as `D_f(r·x+y) + r·D_f(x−y) = D_f(r·x−y) + r·D_f(x+y)`), `r ≥ 0`. Integrates `scalarMeasure_odd_measure`; the seed of real homogeneity of `B_f`.

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H) \{r : \mathbb{R}\}, 0 \le r \to P.\textstyle\int\,f\,(r \cdot x + y) + r \cdot P.\textstyle\int\,f\,(x - y) = P.\textstyle\int\,f\,(r \cdot x - y) + r \cdot P.\textstyle\int\,f\,(x + y)
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`integrable_boundedMeasurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable), [`scalarMeasure_odd_measure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure). $\square$

<small>Used by [`bilinDiag_real_smul_left_nonneg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg"></a>
**Lemma 621** (`bilinDiag_real_smul_left_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L775)</small>

**Real homogeneity in the first slot, `r ≥ 0`:** `B_f(r·x, y) = r·B_f(x,y)`. Both the `x` and the `i·x` odd identities feed in; no continuity used.

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H) \{r : \mathbb{R}\}, 0 \le r \to P.\mathrm{bd}\,f\,(r \cdot x)\,y = r \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_odd`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd). $\square$

<small>Used by [`bilinDiag_real_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left"></a>
**Lemma 622** (`bilinDiag_zero_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L786)</small>

`B_f(0, y) = 0`.

$$
P.\mathrm{bd}\,f\,0\,y = 0
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_neg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg). $\square$

<small>Used by [`bilinDiag_neg_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left), [`bilinDiag_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left"></a>
**Lemma 623** (`bilinDiag_neg_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L791)</small>

`B_f(-x, y) = -B_f(x, y)` (from additivity in the first slot).

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H), P.\mathrm{bd}\,f\,(-x)\,y = -P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`bilinDiag_add_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [`bilinDiag_zero_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left). $\square$

<small>Used by [`bilinDiag_real_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left"></a>
**Lemma 624** (`bilinDiag_real_smul_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L799)</small>

**Real homogeneity in the first slot (all `r : ℝ`):** `B_f(r·x,y) = r·B_f(x,y)`.

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H) (r : \mathbb{R}), P.\mathrm{bd}\,f\,(r \cdot x)\,y = r \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`bilinDiag_real_smul_left_nonneg`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg), [`bilinDiag_neg_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left). $\square$

<small>Used by [`bilinDiag_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left"></a>
**Lemma 625** (`bilinDiag_smul_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L811)</small>

**Conjugate-linearity in the first slot (full `ℂ`):** `B_f(c·x, y) = conj(c)·B_f(x,y)` — combines real homogeneity, `i`-scaling and additivity via `c = c.re + c.im·i`.  This is the sesquilinear half (with `bilinDiag_conj_symm` giving linearity in the second slot).

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (c : \mathbb{C}) (x y : H), P.\mathrm{bd}\,f\,(c \cdot x)\,y = (\mathrm{starRingEnd}\,\mathbb{C})\,c \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`bilinDiag_add_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [`bilinDiag_I_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left), [`bilinDiag_real_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left). $\square$

<small>Used by [`bilinDiag_smul_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right), [`bilinDiag_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le"></a>
**Lemma 626** (`diagInt_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L826)</small>

**Diagonal bound** `‖D_f x‖ ≤ C‖x‖²` from `‖f‖ ≤ C` and `μ_x(univ) = ‖x‖²`.

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, 0 \le C \to (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x : H), \|P.\textstyle\int\,f\,x\| \le C \cdot {\|x\|}^{2}
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`scalarMeasure_univ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ), [`instIsFiniteMeasure_scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [`integrable_boundedMeasurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable). $\square$

<small>Used by [`bilinDiag_norm_le_add`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right"></a>
**Lemma 627** (`bilinDiag_smul_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L840)</small>

**Linearity in the second slot:** `B_f(x, c·y) = c·B_f(x,y)` (from conjugate-symmetry + first-slot conjugate-linearity of `f̄`).

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (c : \mathbb{C}) (x y : H), P.\mathrm{bd}\,f\,x\,(c \cdot y) = c \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`bilinDiag_conj_symm`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [`bilinDiag_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left). $\square$

<small>Used by [`bilinDiag_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-right"></a>
**Lemma 628** (`bilinDiag_zero_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L853)</small>

`B_f(x, 0) = 0`.

$$
P.\mathrm{bd}\,f\,x\,0 = 0
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint). $\square$

<small>Used by [`bilinDiag_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add"></a>
**Lemma 629** (`bilinDiag_norm_le_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L857)</small>

**Quadratic bound** `‖B_f(x,y)‖ ≤ C(‖x‖²+‖y‖²)` (polarization + diagonal bound + two parallelogram laws).

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, 0 \le C \to (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H), \|P.\mathrm{bd}\,f\,x\,y\| \le C \cdot ({\|x\|}^{2} + {\|y\|}^{2})
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le). $\square$

<small>Used by [`bilinDiag_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le"></a>
**Lemma 630** (`bilinDiag_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L889)</small>

**Product (bilinear) bound** `‖B_f(x,y)‖ ≤ 2C·‖x‖·‖y‖` — the bound feeding `LinearMap.mkContinuous₂`.  Proof: normalize to unit vectors and apply the quadratic bound (giving `‖u‖²+‖v‖² = 2`).

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, 0 \le C \to (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H), \|P.\mathrm{bd}\,f\,x\,y\| \le 2 \cdot C \cdot \|x\| \cdot \|y\|
$$

*Proof.* By [`bilinDiag_zero_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left), [`bilinDiag_smul_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left), [`bilinDiag_smul_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right), [`bilinDiag_zero_right`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-right), [`bilinDiag_norm_le_add`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add). $\square$

<small>Used by [`intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-intborel), [`inner_intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel), [`intBorel_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag"></a>
**Definition 631** (`bilinDiagₗ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L924)</small>

The polarized form as a **bundled sesquilinear `LinearMap`** `H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ` (conjugate-linear in the first slot, linear in the second), mirroring `innerₛₗ`.

$$
\mathrm{bilinDiagₗ}\,\Omega\,H\,P\,f\,C \;:=\; \mathrm{mk'}\,(\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{id}\,\mathbb{C})\,(\lambda x y \mapsto P.\mathrm{bd}\,f\,x\,y)\,\cdots \,\cdots \,\cdots \,\cdots
$$

<small>Used by [`intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-intborel), [`inner_intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-intborel"></a>
**Definition 632** (`intBorel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L934)</small>

**The bounded-Borel functional calculus `∫ f dE`** (E2c), defined via the Riesz representation `continuousLinearMapOfBilin` of the bounded sesquilinear form `B_f`.  Requires `0 ≤ C` and `‖f‖ ≤ C`.

$$
\textstyle\int\,\Omega\,H\,P\,f\,C \;:=\; \mathrm{continuousLinearMapOfBilin}\,((P.\mathrm{bd}_{l}\,\mathrm{hf}\,\mathrm{hC}).\mathrm{mkContinuous}_{2}\,(2 \cdot C)\,\cdots )
$$

<small>Used by [`inner_intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel), [`intBorel_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le), [`boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [`boundedFC_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-inner-intborel"></a>
**Lemma 633** (`inner_intBorel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L943)</small>

**Defining property of `∫ f dE`:** `⟪(∫f dE) x, y⟫ = B_f(x,y)` — the sesquilinear form `B_f(x,y) = ∫ f dμ_{x,y}` is realized by the operator.

$$
\langle {(P.\textstyle\int\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC})\,x},{y}\rangle = P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`bilinDiag_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le), [`bilinDiagₗ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag). $\square$

<small>Used by [`intBorel_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le"></a>
**Lemma 634** (`intBorel_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L952)</small>

**Operator norm bound:** `‖∫f dE‖ ≤ 2C`.  From `‖T x‖² = Re B_f(x, T x) ≤ ‖B_f(x, T x)‖ ≤ 2C‖x‖‖T x‖`.

$$
\|P.\textstyle\int\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}\| \le 2 \cdot C
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`bilinDiag_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le), [`inner_intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel). $\square$

<small>Used by [`boundedFC_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-const"></a>
**Lemma 635** (`diagInt_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L971)</small>

`D_f` of a CONSTANT function: `∫ c dμ_z = ‖z‖²·c`.

$$
P.\textstyle\int\,(\lambda x \mapsto c)\,z = {\|z\|}^{2} \cdot c
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`scalarMeasure_univ`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ). $\square$

<small>Used by [`bilinDiag_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const"></a>
**Lemma 636** (`bilinDiag_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L978)</small>

`B_f` of a CONSTANT function is `c·⟪x,y⟫` (polarization of `‖·‖²` = `⟪x,y⟫`). Note this is conjugate-linear in `x` — confirming that the Riesz operator `intBorel` is the *conjugated* calculus (see `intBorel_const`).

$$
P.\mathrm{bd}\,(\lambda x \mapsto c)\,x\,y = c \cdot \langle {x},{y}\rangle
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-const). $\square$

<small>Used by [`boundedFC_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc"></a>
**Definition 637** (`boundedFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1007)</small>

**The correctly-oriented bounded-Borel functional calculus** `Φ(f) := (∫f dE)*` (the adjoint of the Riesz operator), so that `⟪x, Φ(f) y⟫ = B_f(x,y) = ∫ f dμ_{x,y}` with the operator on the SECOND slot — the standard convention.

$$
\Phi\,\Omega\,H\,P\,f\,C \;:=\; {{P.\textstyle\int\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}}}^{\dagger}
$$

<small>Used by [`deviceOpC_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-norm-le), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [`boundedFC_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [`boundedFC_add`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add), [`boundedFC_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [`boundedFC_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le), [`boundedFC_congr`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [`boundedFC_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), and 9 more.</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc"></a>
**Lemma 638** (`inner_boundedFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1014)</small>

Defining property of the oriented FC: `⟪x, Φ(f) y⟫ = B_f(x,y)`.

$$
\langle {x},{(P.\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC})\,y}\rangle = P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-intborel), [`inner_intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel). $\square$

<small>Used by [`boundedFC_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [`boundedFC_add`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add), [`boundedFC_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [`boundedFC_congr`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [`boundedFC_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [`boundedFC_mul_simpleFunc_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [`boundedFC_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul), and 1 more.</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const"></a>
**Lemma 639** (`boundedFC_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1020)</small>

**Unitality / constant rule:** `Φ(const c) = c·1`.  In particular `Φ(1) = 1`, so the oriented calculus is unital (a genuine functional calculus).

$$
P.\Phi\,\cdots \,\cdots \,\cdots = c \cdot 1
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`bilinDiag_const`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc). $\square$

<small>Used by [`borelFC_one`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-one), [`borelFC_const`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-const).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-add"></a>
**Lemma 640** (`diagInt_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1030)</small>

Additivity of the diagonal functional in `f`: `D_{f+g} = D_f + D_g`.

$$
\mathrm{Measurable}\,f \to \mathrm{Measurable}\,g \to \forall \{\mathrm{Cf} \mathrm{Cg} : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le \mathrm{Cf}) \to (\forall (\omega : \Omega), \|g\,\omega\| \le \mathrm{Cg}) \to \forall (z : H), P.\textstyle\int\,(\lambda \omega \mapsto f\,\omega + g\,\omega)\,z = P.\textstyle\int\,f\,z + P.\textstyle\int\,g\,z
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`integrable_boundedMeasurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable). $\square$

<small>Used by [`bilinDiag_add_f`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-finsetsum"></a>
**Lemma 641** (`diagInt_finsetSum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1038)</small>

Linearity of the diagonal functional over finite sums: `D_{∑ᵢ Fᵢ} = ∑ᵢ D_{Fᵢ}` (each `Fᵢ` integrable against `μ_z`).  Bound-free.

$$
(\forall i\in t, \mathrm{Integrable}\,(F\,i)\,(P.\mu\,z)) \to P.\textstyle\int\,(\lambda \omega \mapsto \sum_{i t} F\,i\,\omega)\,z = \sum_{i t} P.\textstyle\int\,(F\,i)\,z
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`bilinDiag_finsetSum`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f"></a>
**Lemma 642** (`bilinDiag_add_f`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1046)</small>

Additivity of the polarized sesquilinear form in `f`: `B_{f+g} = B_f + B_g`.

$$
\mathrm{Measurable}\,f \to \mathrm{Measurable}\,g \to \forall \{\mathrm{Cf} \mathrm{Cg} : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le \mathrm{Cf}) \to (\forall (\omega : \Omega), \|g\,\omega\| \le \mathrm{Cg}) \to \forall (x y : H), P.\mathrm{bd}\,(\lambda \omega \mapsto f\,\omega + g\,\omega)\,x\,y = P.\mathrm{bd}\,f\,x\,y + P.\mathrm{bd}\,g\,x\,y
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_add`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-add). $\square$

<small>Used by [`boundedFC_add`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum"></a>
**Lemma 643** (`bilinDiag_finsetSum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1055)</small>

Linearity of the polarized form over finite sums: `B_{∑ᵢ Fᵢ} = ∑ᵢ B_{Fᵢ}`.

$$
(\forall (z : H), \forall i\in t, \mathrm{Integrable}\,(F\,i)\,(P.\mu\,z)) \to \forall (x y : H), P.\mathrm{bd}\,(\lambda \omega \mapsto \sum_{i t} F\,i\,\omega)\,x\,y = \sum_{i t} P.\mathrm{bd}\,(F\,i)\,x\,y
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_finsetSum`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-finsetsum). $\square$

<small>Used by [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add"></a>
**Lemma 644** (`boundedFC_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1065)</small>

**Additivity of the bounded-Borel FC in `f`:** `Φ(f+g) = Φ(f) + Φ(g)`.

$$
P.\Phi\,\cdots \,\cdots \,\cdots = P.\Phi\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} + P.\Phi\,\mathrm{hg}\,\mathrm{hCg0}\,\mathrm{hCg}
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [`bilinDiag_add_f`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f). $\square$

<small>Used by [`borelFC_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-add).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-smul-f"></a>
**Lemma 645** (`diagInt_smul_f`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1078)</small>

Scalar-homogeneity of the diagonal functional in `f`: `D_{c·f} = c·D_f`.

$$
P.\textstyle\int\,(\lambda \omega \mapsto c \cdot f\,\omega)\,z = c \cdot P.\textstyle\int\,f\,z
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure). $\square$

<small>Used by [`bilinDiag_smul_f`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f"></a>
**Lemma 646** (`bilinDiag_smul_f`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1084)</small>

Scalar-homogeneity of the polarized form in `f`: `B_{c·f} = c·B_f`.

$$
P.\mathrm{bd}\,(\lambda \omega \mapsto c \cdot f\,\omega)\,x\,y = c \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_smul_f`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul-f). $\square$

<small>Used by [`boundedFC_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul"></a>
**Lemma 647** (`boundedFC_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1091)</small>

**ℂ-homogeneity of the bounded-Borel FC in `f`:** `Φ(c·f) = c·Φ(f)`.

$$
P.\Phi\,\cdots \,\cdots \,\cdots = c \cdot P.\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [`bilinDiag_smul_f`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f). $\square$

<small>Used by [`borelFC_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-smul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le"></a>
**Lemma 648** (`boundedFC_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1102)</small>

**Operator-norm bound for the bounded-Borel FC:** `‖Φ(f)‖ ≤ 2C` for `‖f‖∞ ≤ C`. (`Φ(f)` is the adjoint of the Riesz operator `intBorel f`, and the adjoint is a linear isometry.)  This is the estimate that makes the simple→bounded-Borel extension converge in OPERATOR NORM — the route to multiplicativity `Φ(fg)=Φ(f)Φ(g)` that weak-operator convergence cannot deliver.

$$
\|P.\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}\| \le 2 \cdot C
$$

*Proof.* By [`intBorel`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-intborel), [`intBorel_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le). $\square$

<small>Used by [`deviceOpC_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-norm-le), [`cfcCont_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr"></a>
**Lemma 649** (`boundedFC_congr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1112)</small>

**`Φ(f)` depends only on `f`, not on the bound:** equal functions give equal operators (the value is `⟪x,Φ(f)y⟫ = B_f(x,y)`, independent of the bound proof). Lets us rewrite `f` to any pointwise-equal form (e.g. reindex a product).

$$
f = f^{\prime} \to P.\Phi\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} = P.\Phi\,\mathrm{hf}^{\prime}\,\mathrm{hCf0}^{\prime}\,\mathrm{hCf}^{\prime}
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc). $\square$

<small>Used by [`boundedFC_simple_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [`boundedFC_simpleFunc`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [`boundedFC_simpleFunc_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-norm-indicatorone-le"></a>
**Lemma 650** (`norm_indicatorOne_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1125)</small>

The complex indicator `𝟙_s` is bounded by `1`.

$$
\|s.\mathbf{1}\,(\lambda x \mapsto 1)\,\omega\| \le 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boundedFC_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [`boundedFC_simple_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [`boundedFC_simpleFunc`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [`boundedFC_simpleFunc_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul), [`borelFC_indicator`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-indicator), [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator"></a>
**Lemma 651** (`diagInt_indicator`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1132)</small>

`D_{𝟙_s}(z) = μ_z(s)` — the diagonal functional of an indicator is the scalar spectral mass.

$$
\mathrm{MeasurableSet}\,s \to \forall (z : H), P.\textstyle\int\,(s.\mathbf{1}\,\lambda x \mapsto 1)\,z = ((P.\mu\,z)\,s).\mathrm{toReal}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`diagInt_indicator_eq_inner`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner"></a>
**Lemma 652** (`diagInt_indicator_eq_inner`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1139)</small>

`D_{𝟙_s}(z) = ⟪z, E s z⟫` — the diagonal of the indicator's form is the projection's quadratic form.

$$
\mathrm{MeasurableSet}\,s \to \forall (z : H), P.\textstyle\int\,(s.\mathbf{1}\,\lambda x \mapsto 1)\,z = \langle {z},{(P.E\,s)\,z}\rangle
$$

*Proof.* By [`inner_E_self`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-e-self), [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`scalarMeasure_toReal`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal), [`diagInt_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator). $\square$

<small>Used by [`bilinDiag_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator"></a>
**Lemma 653** (`bilinDiag_indicator`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1146)</small>

**Indicator bridge (polarized):** the bounded-Borel sesquilinear form of an indicator is the spectral projection's form, `B_{𝟙_s}(x,y) = ⟪x, E s y⟫`. Proved by reducing the four polarization points to `⟪z, E s z⟫` and expanding by sesquilinearity (the same Jordan–von Neumann computation as `inner_E_polarization`, with the `I•x ± y` convention of `bilinDiag`).

$$
\mathrm{MeasurableSet}\,s \to \forall (x y : H), P.\mathrm{bd}\,(s.\mathbf{1}\,\lambda x \mapsto 1)\,x\,y = \langle {x},{(P.E\,s)\,y}\rangle
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`diagInt_indicator_eq_inner`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner). $\square$

<small>Used by [`boundedFC_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator"></a>
**Lemma 654** (`boundedFC_indicator`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1161)</small>

**The bounded-Borel FC of an indicator is the spectral projection:** `Φ(𝟙_s) = E s`. This anchors the abstract Borel functional calculus to the PVM it came from.

$$
P.\Phi\,\cdots \,\cdots \,\cdots = P.E\,s
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [`bilinDiag_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator). $\square$

<small>Used by [`borelFC_indicator`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-indicator).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple"></a>
**Lemma 655** (`boundedFC_eq_integralSimple`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1183)</small>

**The bounded-Borel FC of a simple function is its spectral integral:** `Φ(∑ᵢ cᵢ 𝟙_{sᵢ}) = ∑ᵢ cᵢ E sᵢ = integralSimple`.  Proved at the sesquilinear-form level: `B_{∑cᵢ𝟙_{sᵢ}} = ∑ cᵢ B_{𝟙_{sᵢ}} = ∑ cᵢ ⟪x, E sᵢ y⟫` (finset linearity + smul-in-`f` + the indicator bridge).

$$
P.\Phi\,\cdots \,\cdots \,\cdots = P.\textstyle\int\,t\,c\,\mathrm{sets}
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`inner_integralSimple_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-integralsimple-left), [`integrable_boundedMeasurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable), [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [`bilinDiag_finsetSum`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum), [`bilinDiag_smul_f`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f), [`bilinDiag_indicator`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator). $\square$

<small>Used by [`boundedFC_simple_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [`boundedFC_simpleFunc`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq"></a>
**Lemma 656** (`integralSimple_mul_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1213)</small>

**Operator product of two simple integrals** (the algebraic core of multiplicativity `Φ(fg)=Φ(f)Φ(g)` for simple `f,g`): cross terms collapse by `E Aᵢ · E Bⱼ = E(Aᵢ ∩ Bⱼ)`.

$$
(\forall i\in t, \mathrm{MeasurableSet}\,(A\,i)) \to (\forall j\in s, \mathrm{MeasurableSet}\,(B\,j)) \to P.\textstyle\int\,t\,a\,A \cdot P.\textstyle\int\,s\,b\,B = \sum_{i t} \sum_{j s} (a\,i \cdot b\,j) \cdot P.E\,(A\,i \cap B\,j)
$$

*Proof.* By [`E_inter`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e-inter). $\square$

<small>Used by [`integralSimple_product_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq"></a>
**Lemma 657** (`integralSimple_product_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1227)</small>

The simple integral over the **product index** `t ×ˢ s` (weights `aᵢbⱼ`, sets `Aᵢ ∩ Bⱼ`) equals the product of the two simple integrals.  Pure operator algebra (`integralSimple_mul_eq` + `Finset.sum_product`).

$$
(\forall i\in t, \mathrm{MeasurableSet}\,(A\,i)) \to (\forall j\in s, \mathrm{MeasurableSet}\,(B\,j)) \to (P.\textstyle\int\,(t \times s)\,(\lambda p \mapsto a\,p.1 \cdot b\,p.2)\,\lambda p \mapsto A\,p.1 \cap B\,p.2) = P.\textstyle\int\,t\,a\,A \cdot P.\textstyle\int\,s\,b\,B
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`integralSimple_mul_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq). $\square$

<small>Used by [`boundedFC_simple_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul"></a>
**Lemma 658** (`boundedFC_simple_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1237)</small>

**Multiplicativity on simple functions:** `Φ(f·g) = Φ(f)·Φ(g)` for simple `f = ∑ᵢ aᵢ 𝟙_{Aᵢ}`, `g = ∑ⱼ bⱼ 𝟙_{Bⱼ}`.  Stated with `Φ(f), Φ(g)` as the simple integrals (`= Φ(f), Φ(g)` by `boundedFC_eq_integralSimple`).  Proof: the product `f·g` reindexes pointwise to the `t ×ˢ s` simple function (`boundedFC_congr` + `Finset.sum_mul_sum` + the indicator product `𝟙_A·𝟙_B = 𝟙_{A∩B}`), whose FC is `integralSimple (t ×ˢ s) = (integralSimple t)·(integralSimple s)`.

$$
P.\Phi\,\cdots \,\cdots \,\cdots = P.\textstyle\int\,t\,a\,A \cdot P.\textstyle\int\,s\,b\,B
$$

*Proof.* By [`boundedFC_congr`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [`integralSimple_product_eq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq). $\square$

<small>Used by [`boundedFC_simpleFunc_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-simplefunc-eq-sum"></a>
**Lemma 659** (`simpleFunc_eq_sum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1284)</small>

**`SimpleFunc` as a sum of scaled indicators** (the bridge from Mathlib's `SimpleFunc`, produced by `approxOn`, to the `∑ cᵢ 𝟙_{sᵢ}` form of our FC lemmas): `φ a = ∑_{y ∈ φ.range} y · 𝟙_{φ⁻¹{y}}(a)`.  Exactly one range term is nonzero.

$$
\varphi\,a = \sum_{y \varphi \mathrm{range}} y \cdot (\varphi ^{-1}{}' \{y\}).\mathbf{1}\,(\lambda x \mapsto 1)\,a
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boundedFC_simpleFunc`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [`boundedFC_simpleFunc_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc"></a>
**Lemma 660** (`boundedFC_simpleFunc`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1298)</small>

**The FC of a `SimpleFunc`** equals the spectral integral over its range: `Φ(⇑φ) = ∑_{y ∈ φ.range} y · E(φ⁻¹{y})`.

$$
P.\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC} = P.\textstyle\int\,\varphi.\mathrm{range}\,\mathrm{id}\,\lambda y \mapsto \varphi ^{-1}{}' \{y\}
$$

*Proof.* By [`boundedFC_congr`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [`norm_indicatorOne_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-norm-indicatorone-le), [`boundedFC_eq_integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [`simpleFunc_eq_sum`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-simplefunc-eq-sum). $\square$

<small>Used by [`boundedFC_simpleFunc_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul"></a>
**Lemma 661** (`boundedFC_simpleFunc_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1307)</small>

**Multiplicativity on `SimpleFunc`s:** `Φ(⇑φ · ⇑ψ) = Φ(⇑φ)·Φ(⇑ψ)`.  Reduces to `boundedFC_simple_mul` over the ranges of `φ, ψ` via `simpleFunc_eq_sum`.

$$
P.\Phi\,\mathrm{hfp}\,\mathrm{hC0p}\,\mathrm{hCp} = P.\Phi\,\mathrm{hf}\varphi\,\mathrm{hC0}\varphi\,\mathrm{hC}\varphi \cdot P.\Phi\,\mathrm{hf}\psi\,\mathrm{hC0}\psi\,\mathrm{hC}\psi
$$

*Proof.* By [`integralSimple`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-integralsimple), [`boundedFC_congr`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [`norm_indicatorOne_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-norm-indicatorone-le), [`boundedFC_simple_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [`simpleFunc_eq_sum`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-simplefunc-eq-sum), [`boundedFC_simpleFunc`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc). $\square$

<small>Used by [`boundedFC_mul_simpleFunc_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated"></a>
**Lemma 662** (`tendsto_diagInt_of_dominated`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1325)</small>

**Dominated/bounded convergence for the diagonal functional:** if `fₙ → f` pointwise with a common bound `C`, then `D_{fₙ}(z) → D_f(z)`.  (DCT against the finite measure `μ_z`.)  The engine for extending FC identities from simple to all bounded Borel functions.

$$
(\forall (n : \mathbb{N}), \mathrm{Measurable}\,(f\,n)) \to (\forall (n : \mathbb{N}) (\omega : \Omega), \|f\,n\,\omega\| \le C) \to (\forall (\omega : \Omega), \mathrm{Tendsto}\,(\lambda n \mapsto f\,n\,\omega)\,\mathrm{atTop}\,(\mathcal{N}\,(g\,\omega))) \to \forall (z : H), \mathrm{Tendsto}\,(\lambda n \mapsto P.\textstyle\int\,(f\,n)\,z)\,\mathrm{atTop}\,(\mathcal{N}\,(P.\textstyle\int\,g\,z))
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`instIsFiniteMeasure_scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure). $\square$

<small>Used by [`tendsto_bilinDiag_of_dominated`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated"></a>
**Lemma 663** (`tendsto_bilinDiag_of_dominated`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1359)</small>

Bound-free form of the normality engine: `B_{fₙ}(x,y) → B_f(x,y)` under bounded pointwise convergence (the limit `f` needs no bound — `bilinDiag` carries none). This is the workhorse for the simple→bounded-Borel multiplicativity extension.

$$
(\forall (n : \mathbb{N}), \mathrm{Measurable}\,(f\,n)) \to (\forall (n : \mathbb{N}) (\omega : \Omega), \|f\,n\,\omega\| \le C) \to (\forall (\omega : \Omega), \mathrm{Tendsto}\,(\lambda n \mapsto f\,n\,\omega)\,\mathrm{atTop}\,(\mathcal{N}\,(g\,\omega))) \to \forall (x y : H), \mathrm{Tendsto}\,(\lambda n \mapsto P.\mathrm{bd}\,(f\,n)\,x\,y)\,\mathrm{atTop}\,(\mathcal{N}\,(P.\mathrm{bd}\,g\,x\,y))
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`tendsto_diagInt_of_dominated`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated). $\square$

<small>Used by [`boundedFC_mul_simpleFunc_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [`boundedFC_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-approxseq"></a>
**Definition 664** (`approxSeq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1376)</small>

The `approxOn` simple-function sequence for a bounded measurable `f` (base point `0`, set `univ`): `approxSeq f hf n` is a `SimpleFunc`, `→ f` pointwise, with `‖approxSeq f hf n ω‖ ≤ 2‖f ω‖`.

$$
\mathrm{aseq}\,\Omega\,f\,n \;:=\; \mathrm{approxOn}\,f\,\mathrm{hf}\,0\,\mathrm{\_proof\_2}\,n
$$

<small>Used by [`approxSeq_tendsto`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-tendsto), [`approxSeq_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-norm-le), [`approxSeq_measurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-measurable), [`boundedFC_mul_simpleFunc_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [`boundedFC_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-approxseq-tendsto"></a>
**Lemma 665** (`approxSeq_tendsto`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1383)</small>

$$
\mathrm{Tendsto}\,(\lambda n \mapsto (\href{/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq}{\mathrm{aseq}}\,f\,\mathrm{hf}\,n)\,\omega)\,\mathrm{atTop}\,(\mathcal{N}\,(f\,\omega))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boundedFC_mul_simpleFunc_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [`boundedFC_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-approxseq-norm-le"></a>
**Lemma 666** (`approxSeq_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1388)</small>

$$
\|(\href{/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq}{\mathrm{aseq}}\,f\,\mathrm{hf}\,n)\,\omega\| \le \|f\,\omega\| + \|f\,\omega\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boundedFC_mul_simpleFunc_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [`boundedFC_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-approxseq-measurable"></a>
**Lemma 667** (`approxSeq_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1392)</small>

$$
\mathrm{Measurable}\,(\href{/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq}{\mathrm{aseq}}\,f\,\mathrm{hf}\,n)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boundedFC_mul_simpleFunc_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [`boundedFC_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left"></a>
**Lemma 668** (`boundedFC_mul_simpleFunc_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1398)</small>

**Stage 1 (left simple):** `Φ(⇑φ · g) = Φ(⇑φ)·Φ(g)` for a `SimpleFunc φ` and a bounded measurable `g`.  Approximate `g` by `SimpleFunc`s `gₘ → g` and pass to the weak limit: `⟪x, Φ(φ·gₘ)y⟫ = ⟪Φ(φ)†x, Φ(gₘ)y⟫` (by `boundedFC_simpleFunc_mul`), both sides converge (`tendsto_bilinDiag`), so the limits agree.

$$
P.\Phi\,\mathrm{hfp}\,\mathrm{hC0p}\,\mathrm{hCp} = P.\Phi\,\mathrm{hf}\varphi\,\mathrm{hC0}\varphi\,\mathrm{hC}\varphi \cdot P.\Phi\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg}
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [`boundedFC_simpleFunc_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul), [`tendsto_bilinDiag_of_dominated`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated), [`approxSeq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq), [`approxSeq_tendsto`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-tendsto), [`approxSeq_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-norm-le), [`approxSeq_measurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-measurable). $\square$

<small>Used by [`boundedFC_mul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul"></a>
**Lemma 669** (`boundedFC_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1440)</small>

**MULTIPLICATIVITY OF THE BOUNDED-BOREL FUNCTIONAL CALCULUS** (the keystone): `Φ(f·g) = Φ(f)·Φ(g)` for all bounded measurable `f, g`.  Approximate `f` by `SimpleFunc`s `fₙ → f` and pass to the weak limit, using Stage 1 (left-simple multiplicativity) for each `fₙ`: `⟪x, Φ(fₙ·g)y⟫ = ⟪x, Φ(fₙ)(Φ(g)y)⟫`, both sides converge (`tendsto_bilinDiag`), so the limits agree.  Together with `boundedFC_add`, `boundedFC_smul` and `boundedFC_const`, the FC `Φ : Bᵇ(Ω) → (H →L[ℂ] H)` is a unital `*`-algebra homomorphism.

$$
P.\Phi\,\mathrm{hfp}\,\mathrm{hC0p}\,\mathrm{hCp} = P.\Phi\,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf} \cdot P.\Phi\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg}
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`inner_boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [`tendsto_bilinDiag_of_dominated`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated), [`approxSeq`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq), [`approxSeq_tendsto`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-tendsto), [`approxSeq_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-norm-le), [`approxSeq_measurable`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-approxseq-measurable), [`boundedFC_mul_simpleFunc_left`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left). $\square$

<small>Used by [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul).</small>

---
<small>[← all sections](/browser) · [← RicciSymm](/browser/qiqth-riccisymm) · [SpectralTheorem →](/browser/qiqth-spectral-spectraltheorem) </small>