---
layout: ../../layouts/Deep.astro
title: QIQTH.StandardSubspaceModularFlow
eyebrow: StandardSubspaceModularFlow · section of the QIQT-H book
description: QIQTH.StandardSubspaceModularFlow — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← StandardSubspaceModular](/browser/qiqth-standardsubspacemodular) · [StripUniqueness →](/browser/qiqth-stripuniqueness) </small>

<small>StandardSubspaceModularFlow · entries 808–978 of 1000</small>

<a id="d-qiqth-standardsubspacemodular-modchar"></a>
**Definition 808** (`modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L39)</small>

The RvD modular character `u_t(r)`, a globally bounded Borel function on `ℝ`: on `(0,2)` it is `exp(i·t·log((2−r)/r))`, and `1` outside (the endpoint convention makes the group law hold pointwise).

$$
\chi_{\mathrm{mod}}\,t \;:=\; (\mathrm{Ioo}\,0\,2).\mathrm{piecewise}\,(\lambda r \mapsto \exp\,(i \cdot t \cdot (\log\,((2 - r) / r))))\,\lambda x \mapsto 1
$$

<small>Used by [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`modChar_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-measurable), [`modChar_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-norm), [`modChar_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-zero), [`modChar_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-add), [`modChar_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-conj), [`modSpecFun`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun), and 7 more.</small>

<a id="d-qiqth-standardsubspacemodular-modchar-measurable"></a>
**Lemma 809** (`modChar_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L47)</small>

$$
\mathrm{Measurable}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-norm"></a>
**Lemma 810** (`modChar_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L54)</small>

$$
\|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r\| = 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-zero"></a>
**Lemma 811** (`modChar_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L63)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,0\,r = 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modUnitary_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-zero).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-add"></a>
**Lemma 812** (`modChar_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L70)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,(s + t)\,r = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,s\,r \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modUnitary_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-add).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-conj"></a>
**Lemma 813** (`modChar_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L81)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,(-t)\,r
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modUnitary_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-adjoint).</small>

<a id="d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure"></a>
**Lemma 814** (`scalarMeasure_eq_specMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L94)</small>

**`scalarMeasure(PVM_of_selfAdjoint) = specMeasure`.**  The PVM's scalar measure `μ_x(s) = ‖E(s)x‖²` (with `E = specProj` a projection, so `‖E(s)x‖² = re⟪E(s)x,x⟫ = qForm = μ_x^{spec}(s)`) agrees with the Riesz–Markov spectral measure.  This connects the bounded-Borel-FC layer (`diagInt`/`bilinDiag`, on `scalarMeasure`) to the integral spectral theorem `re_inner_T_eq_integral` (on `specMeasure`).

$$
(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,T\,\mathrm{ha}).\mu\,x = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x
$$

*Proof.* By [`E`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-e), [`scalarMeasure_apply`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [`qForm`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-qform), [`specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj), [`specProj_isSelfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-isselfadjoint), [`reApplyInnerSelf_specProj`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [`specProj_inter`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specproj-inter). $\square$

<small>Used by [`diagInt_specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-diagint-speccoord).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-congr"></a>
**Lemma 815** (`borelFC_congr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L127)</small>

`borelFC` depends only on the function (not the bound proofs).

$$
f = f^{\prime} \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}^{\prime}\,\mathrm{hCf0}^{\prime}\,\mathrm{hCf}^{\prime}
$$

*Proof.* By [`boundedFC_congr`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Used by [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`modUnitary_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-zero), [`modUnitary_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-add), [`modUnitary_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-adjoint), [`borelFC_comm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-comm), [`borelFC_neg`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-neg), and 9 more.</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-adjoint"></a>
**Lemma 816** (`borelFC_adjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L134)</small>

**Adjoint of the bounded Borel FC:** `f(T)⋆ = (conj f)(T)`.  From the hermitian symmetry of the polarized bilinear form (`bilinDiag_conj_symm`).

$$
{{\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}}}^{\dagger} = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hcf}\,\mathrm{hC0}^{\prime}\,\mathrm{hcfb}
$$

*Proof.* By [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`bilinDiag_conj_symm`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`inner_borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-borelfc). $\square$

<small>Used by [`borelFC_inner_self`](/browser/qiqth-modularrelativeentropy#d-qiqth-borelfc-inner-self), [`modUnitary_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-adjoint), [`cfcCont_star`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-star).</small>

<a id="d-qiqth-standardsubspacemodular-modspecfun"></a>
**Definition 817** (`modSpecFun`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L147)</small>

`u_t` restricted to the spectrum of `R` — the function fed to the bounded Borel FC.

$$
f_{\mathrm{mod}}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,t\,\omega \;:=\; \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,\omega
$$

<small>Used by [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable), [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [`modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary), [`modUnitary_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-zero), [`modUnitary_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-add), [`modUnitary_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-adjoint), and 2 more.</small>

<a id="d-qiqth-standardsubspacemodular-modspecfun-measurable"></a>
**Lemma 818** (`modSpecFun_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L151)</small>

$$
\mathrm{Measurable}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun}{f_{\mathrm{mod}}}\,S\,t)
$$

*Proof.* By [`modChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar), [`modChar_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-measurable). $\square$

<small>Used by [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary), [`modUnitary_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-zero), [`modUnitary_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-add), [`modUnitary_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-adjoint), [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-modspecfun-norm-le"></a>
**Lemma 819** (`modSpecFun_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L154)</small>

$$
\|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun}{f_{\mathrm{mod}}}\,S\,t\,\omega\| \le 1
$$

*Proof.* By [`modChar_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-norm). $\square$

<small>Used by [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary), [`modUnitary_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-zero), [`modUnitary_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-add), [`modUnitary_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-adjoint), [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint"></a>
**Lemma 820** (`rvdRC_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L157)</small>

`R = rvdRC S` is self-adjoint (it is positive).

$$
\mathrm{IsSelfAdjoint}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)
$$

*Proof.* By [`rvdRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-nonneg). $\square$

<small>Used by [`borelFC_congr_ae`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`rvdSpecMeasure`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure), [`deviceOpReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal), [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), [`deviceOpC_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-norm-le), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq), and 34 more.</small>

<a id="d-qiqth-standardsubspacemodular-modunitary"></a>
**Definition 821** (`modUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L161)</small>

**The continuum modular unitary `U_t = Δ^{it} = u_t(R)`** via the bounded Borel FC of `R`.

$$
\Delta\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,t \;:=\; \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\cdots \,\cdots \,\cdots
$$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`oneParticleBW_niceWedge_of_standard`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [`oneParticleBW_niceWedge_reehSchlieder`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [`oneParticleBW_niceWedge_unconditional`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [`hasDerivAt_modularEnergy_of_boost_pos`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-hasderivat-modularenergy-of-boost-pos), [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux), [`freeField_component_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-component-hflux), and 53 more.</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-zero"></a>
**Lemma 822** (`modUnitary_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L166)</small>

**`U_0 = 1`.**

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,0 = 1
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_one`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-one), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`modChar_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-zero), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`modSpecFun`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun), [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable), [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`deviceVecF_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf-zero).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-add"></a>
**Lemma 823** (`modUnitary_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L174)</small>

**Group law `U_{s+t} = U_s · U_t`** — from `borelFC_mul` and the pointwise law `u_{s+t}=u_s·u_t`.

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,(s + t) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,s \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`modChar_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-add), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`modSpecFun`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun), [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable), [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-adjoint"></a>
**Lemma 824** (`modUnitary_adjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L190)</small>

**`U_t⋆ = U_{-t}`** — from the adjoint relation `Φ(f)⋆ = Φ(conj f)` and `conj u_t = u_{-t}`.

$$
{{\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t}}^{\dagger} = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,(-t)
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`modChar_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-conj), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`borelFC_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-adjoint), [`modSpecFun`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun), [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable), [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq"></a>
**Lemma 825** (`rvdR_add_rvdPmQ_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L317)</small>

**`R + D = 2·P`** (RvD `P = ½(R+D)`): `(P+Q) + (P−Q) = 2P`.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S + \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S = 2 \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S
$$

*Proof.* By [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik). $\square$

<small>Used by [`modUnitary_commute_projK_of`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-projk-of), [`commute_projK_of_commute_R_D`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-commute-projk-of-commute-r-d).</small>

<a id="d-qiqth-standardsubspacemodular-mem-k-iff-projk"></a>
**Lemma 826** (`mem_K_iff_projK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L323)</small>

`𝒦`-membership via its projection: `ξ ∈ 𝒦 ↔ P ξ = ξ`.

$$
\xi \in S.\mathrm{cl} \leftrightarrow (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi = \xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete), [`modUnitary_eq_of_orbit_compare`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare), [`gFunction_top_edge_real`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-top-edge-real), [`modUnitary_mapsTo_K_of_commute`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute), [`rvdSqrtR_range_dense_in_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k), and 1 more.</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-projk-of"></a>
**Lemma 827** (`modUnitary_commute_projK_of`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L328)</small>

**Reduction of `[U_t, P] = 0` to `[U_t, R] = 0 ∧ [U_t, D] = 0`** via `P = ½(R+D)`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi) \to (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi) \to (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)
$$

*Proof.* By [`rvdR_add_rvdPmQ_eq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq). $\square$

<small>Used by [`modUnitary_mapsTo_K_of_commute`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute"></a>
**Lemma 828** (`modUnitary_mapsTo_K_of_commute`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L340)</small>

**Conditional standard-subspace invariance:** if `U_t` commutes with `R` and `D` (pointwise), then `U_t 𝒦 ⊆ 𝒦`.  With unitarity this gives `U_t 𝒦 = 𝒦` — the property certifying `Δ^{it}` is the modular flow OF `𝒦`.  The hypotheses are the two commutators isolated above.

$$
(\forall (\xi : H), (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)) \to (\forall (\xi : H), (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)) \to \forall \xi\in S.\mathrm{cl}, (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi \in S.\mathrm{cl}
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`modUnitary_commute_projK_of`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-projk-of). $\square$

<small>Used by [`modUnitary_mapsTo_K_of_commute_D`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-comm"></a>
**Lemma 829** (`borelFC_comm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L379)</small>

Two values of the bounded Borel FC commute (multiplicative + scalar functions commute).

$$
(\mathrm{Measurable}\,\lambda \omega \mapsto f\,\omega \cdot g\,\omega) \to 0 \le \mathrm{Cfg} \to (\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), \|f\,\omega \cdot g\,\omega\| \le \mathrm{Cfg}) \to (\mathrm{Measurable}\,\lambda \omega \mapsto g\,\omega \cdot f\,\omega) \to 0 \le \mathrm{Cgf} \to (\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), \|g\,\omega \cdot f\,\omega\| \le \mathrm{Cgf}) \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf} \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg} = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg} \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf}
$$

*Proof.* By [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr). $\square$

<small>Used by [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc).</small>

<a id="d-qiqth-standardsubspacemodular-speccoord"></a>
**Definition 830** (`specCoord`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L392)</small>

The coordinate function `λ ↦ λ` on `σ(R)` — the integrand of `R = ∫λ dE`.

$$
\mathrm{sc}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,\omega \;:=\; \omega
$$

<small>Used by [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`specCoord_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-measurable), [`specCoord_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-norm-le), [`diagInt_specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-diagint-speccoord), [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [`cfcCont_coord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-coord), and 2 more.</small>

<a id="d-qiqth-standardsubspacemodular-speccoord-measurable"></a>
**Lemma 831** (`specCoord_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L396)</small>

$$
\mathrm{Measurable}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord}{\mathrm{sc}}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [`cfcCont_coord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-coord), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-speccoord-norm-le"></a>
**Lemma 832** (`specCoord_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L399)</small>

$$
\|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord}{\mathrm{sc}}\,S\,\omega\| \le \|\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S\| \cdot \|1\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [`cfcCont_coord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-coord), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc"></a>
**Lemma 833** (`rvdRC_spectrum_mem_Icc`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L404)</small>

**The spectrum of `R = P + Q` lies in `[0, 2]`** (the TIGHT bound, from the RvD order relations `0 ≤ R` and `0 ≤ 2 − R`, not the loose norm margin `spectrum_subset_covΩ`).  Lower: `0 ≤ R` (`rvdRC_nonneg`) gives `0 ≤ ω` via `StarOrderedRing.nonneg_iff_spectrum_nonneg`.  Upper: for `ω ∈ σ(R)`, `2 − ω ∈ {2} − σ(R) = σ(2·1 − R) = σ(2 − R)` (`spectrum.singleton_sub_eq`), and `0 ≤ 2 − R` (`rvdTwoSubRC_nonneg`) gives `0 ≤ 2 − ω`, i.e. `ω ≤ 2`.  This is the spectral location the `borelFC` construction of the operator device vector `(2−R)^{iz}R^{−iz+1/2}ζ = d_z(R)ζ` consumes (`devChar_norm_le_Icc` bounds `d_z` exactly on `[0,2]`).

$$
\omega \in \mathrm{Icc}\,0\,2
$$

*Proof.* By [`rvdRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-nonneg), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdTwoSubRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive), [`rvdTwoSubRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`devSpecReal_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-norm-le), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`devCharDeriv_norm_le_slab`](/browser/qiqth-modularrelativeentropy#d-qiqth-devcharderiv-norm-le-slab), [`devChar_slope_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devchar-slope-norm-le), [`tendsto_devChar_slope`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-devchar-slope), and 4 more.</small>

<a id="d-qiqth-standardsubspacemodular-diagint-speccoord"></a>
**Lemma 834** (`diagInt_specCoord`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L425)</small>

`diagInt(coord) z = ⟪z, R z⟫` (the `scalarMeasure=specMeasure` bridge + `re_inner_T_eq_integral` + self-adjoint realness).

$$
(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).\textstyle\int\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord}{\mathrm{sc}}\,S)\,z = \langle {z},{(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,z}\rangle
$$

*Proof.* By [`scalarMeasure`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [`specMeasure`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-specmeasure), [`re_inner_T_eq_integral`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-re-inner-t-eq-integral), [`rvdRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-issymmetric), [`scalarMeasure_eq_specMeasure`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure). $\square$

<small>Used by [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc"></a>
**Lemma 835** (`rvdRC_eq_borelFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L441)</small>

**`R = borelFC(coord) = ∫λ dE`** — the operator spectral theorem for `R`, via polarization.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\cdots \,\cdots \,\cdots
$$

*Proof.* By [`diagInt`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-diagint), [`bilinDiag`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`inner_borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-inner-borelfc), [`diagInt_specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-diagint-speccoord). $\square$

<small>Used by [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [`cfcCont_coord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-coord), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc"></a>
**Lemma 836** (`modUnitary_commute_rvdRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L463)</small>

** `[U_t, R] = 0`** (operator form): the modular flow commutes with `R`.

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`modSpecFun`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun), [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable), [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`borelFC_comm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-comm), [`specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord), [`specCoord_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-measurable), [`specCoord_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-norm-le), [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc). $\square$

<small>Used by [`modUnitary_commute_rvdR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdr), [`modUnitary_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdr"></a>
**Lemma 837** (`modUnitary_commute_rvdR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L482)</small>

**`[U_t, R] = 0`** (pointwise on `rvdR`): `U_t(R ξ) = R(U_t ξ)`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc). $\square$

<small>Used by [`modUnitary_mapsTo_K_of_commute_D`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d"></a>
**Lemma 838** (`modUnitary_mapsTo_K_of_commute_D`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L489)</small>

**Standard-subspace invariance modulo the covariance:** with `[U_t,R]=0` discharged, `U_t 𝒦 ⊆ 𝒦` follows from the SINGLE remaining obligation `[U_t, D] = 0` (the covariance).

$$
(\forall (\xi : H), (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)) \to \forall \xi\in S.\mathrm{cl}, (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi \in S.\mathrm{cl}
$$

*Proof.* By [`modUnitary_mapsTo_K_of_commute`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute), [`modUnitary_commute_rvdR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdr). $\square$

<small>Used by [`modUnitary_mapsTo_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k).</small>

<a id="d-qiqth-standardsubspacemodular-restrictscalars-star"></a>
**Lemma 839** (`restrictScalars_star`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L503)</small>

ℂ-adjoint restricted to ℝ equals the ℝ-adjoint (no direct Mathlib lemma).

$$
\mathrm{res}\,\mathbb{R}\,({{Y}}^{*}) = {{\mathrm{res}\,\mathbb{R}\,Y}}^{*}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`rvdRC_mul_rvdTwoSubRC_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange).</small>

<a id="d-qiqth-standardsubspacemodular-realcommutant"></a>
**Definition 840** (`realCommutant`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L512)</small>

The **real commutant** of a self-adjoint `D : H →L[ℝ] H`, as a real `*`-subalgebra of `H →L[ℂ] H` (over `ℝ` only, since `D` is antilinear).

$$
\mathcal{M}'\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,D\,\mathrm{hD} \;:=\; \{\mathrm{carrier} :=\{Y|D \cdot \mathrm{res}\,\mathbb{R}\,Y = \mathrm{res}\,\mathbb{R}\,Y \cdot D\} , \mathrm{mul\_mem}^{\prime} :=\cdots , \mathrm{one\_mem}^{\prime} :=\cdots , \mathrm{add\_mem}^{\prime} :=\cdots , \mathrm{zero\_mem}^{\prime} :=\cdots , \mathrm{algebraMap\_mem}^{\prime} :=\cdots , \mathrm{star\_mem}^{\prime} :=\cdots \}
$$

<small>Used by [`realCommutant_isClosed`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-realcommutant-isclosed), [`commute_of_mem_elemental`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-commute-of-mem-elemental).</small>

<a id="d-qiqth-standardsubspacemodular-realcommutant-isclosed"></a>
**Lemma 841** (`realCommutant_isClosed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L540)</small>

$$
\mathrm{IsClosed}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-realcommutant}{\mathcal{M}{}'}\,D\,\mathrm{hD})
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`commute_of_mem_elemental`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-commute-of-mem-elemental).</small>

<a id="d-qiqth-standardsubspacemodular-commute-of-mem-elemental"></a>
**Lemma 842** (`commute_of_mem_elemental`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L557)</small>

**Antilinear-CFC commutation:** `D` (self-adjoint, ℝ-linear) commuting with `B` commutes with everything in `elemental ℝ B`.

$$
\mathrm{IsSelfAdjoint}\,D \to D \cdot \mathrm{res}\,\mathbb{R}\,B = \mathrm{res}\,\mathbb{R}\,B \cdot D \to \forall \{Y : H \to L[\mathbb{C}] H\}, Y \in \mathrm{elem}\,\mathbb{R}\,B \to D \cdot \mathrm{res}\,\mathbb{R}\,Y = \mathrm{res}\,\mathbb{R}\,Y \cdot D
$$

*Proof.* By [`realCommutant`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-realcommutant), [`realCommutant_isClosed`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-realcommutant-isclosed). $\square$

<small>Used by [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-sqrt-mem-elemental"></a>
**Lemma 843** (`sqrt_mem_elemental`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L565)</small>

`CFC.sqrt B ∈ elemental ℝ B` for `0 ≤ B` (via `CFC.sqrt = cfcₙ Real.sqrt = cfc Real.sqrt`).

$$
0 \le B \to \mathrm{sqrt}\,B \in \mathrm{elem}\,\mathbb{R}\,B
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt"></a>
**Lemma 844** (`rvdPmQ_commute_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L571)</small>

** `D·T = T·D`** (operator form): the antilinear modular conjugation `D` commutes with the positive modulus `T = √(R(2−R))`.  Whence `J = D·T⁻¹` is self-adjoint and `J² = 1`.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S) = \mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S) \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-nonneg), [`rvdPmQ_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [`rvdTwoSubRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg), [`rvdRC_commute_rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc), [`rvdT_sq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-sq), [`rvdT_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-nonneg), [`rvdPmQ_commute_A`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [`commute_of_mem_elemental`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-commute-of-mem-elemental), [`sqrt_mem_elemental`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-sqrt-mem-elemental). $\square$

<small>Used by [`rvdPmQ_commute_rvdT_apply`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply"></a>
**Lemma 845** (`rvdPmQ_commute_rvdT_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L589)</small>

** `D·T = T·D`** (pointwise): `D(T ξ) = T(D ξ)`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi)
$$

*Proof.* By [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt). $\square$

<small>Used by [`modConj_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-isselfadjoint).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange"></a>
**Lemma 846** (`rvdT_restrictScalars_denseRange`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L601)</small>

`range T` is dense (`T` injective self-adjoint ⟹ `(range T)ᗮ = ker T = ⊥`).

$$
\mathrm{DenseRange}\,(\mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S))
$$

*Proof.* By [`rvdT_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint), [`rvdT_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-injective), [`restrictScalars_star`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-restrictscalars-star). $\square$

<small>Used by [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt), [`modConj_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-norm), [`modConj_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [`modConj_smul_I`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-smul-i), [`modConj_rvdRC_reflect`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [`rvdSqrtR_range_dense_in_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k), [`modConj_commute_modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modconj"></a>
**Definition 847** (`modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L624)</small>

**The modular conjugation `J`** — the ℝ-linear extension of `T ξ ↦ D ξ`.

$$
J\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S \;:=\; ((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)).\mathrm{extendOfNorm}\,(\mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S))
$$

<small>Used by [`GConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy), [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire), [`gConstancy_entire_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [`gConstancy_of_entireVec_limit`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit), [`gConstancy_real_smul`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-real-smul), [`gConstancy_eta_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [`gConstancy_of_tendsto_xi`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-of-tendsto-xi), and 41 more.</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdt"></a>
**Lemma 848** (`modConj_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L628)</small>

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi
$$

*Proof.* By [`rvdT_norm_eq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange). $\square$

<small>Used by [`modConj_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-norm), [`modConj_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [`modConj_smul_I`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-smul-i), [`modConj_rvdRC_reflect`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [`rvdT_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-modconj), [`modConj_rvdPmQ_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj), [`modConj_rvdT_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt-of-mem-k), [`commute_rvdPmQ_of_commute_modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-commute-rvdpmq-of-commute-modconj-rvdt), and 1 more.</small>

<a id="d-qiqth-standardsubspacemodular-modconj-norm"></a>
**Lemma 849** (`modConj_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L634)</small>

`J` is an isometry (`‖J η‖ = ‖η‖`), by density from `‖J(Tξ)‖ = ‖Dξ‖ = ‖Tξ‖`.

$$
\|(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta\| = \|\eta\|
$$

*Proof.* By [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`rvdT_norm_eq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt). $\square$

<small>Used by [`gFunction_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-norm-le), [`modConj_inner_map`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-inner-map).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-inner-map"></a>
**Lemma 850** (`modConj_inner_map`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L643)</small>

**`J` preserves the real inner product** (it is an isometry): `⟪J η, J ζ⟫ = ⟪η, ζ⟫`.

$$
\langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta}\rangle = \langle {\eta},{\zeta}\rangle
$$

*Proof.* By [`modConj_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-norm). $\square$

<small>Used by [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_inner_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-inner-conj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-real-inner-symm"></a>
**Lemma 851** (`rvdT_real_inner_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L648)</small>

`T` is real-symmetric — via ℂ-self-adjointness (fast: primary ℂ instance, no scoped-ℝ adjoint).

$$
\langle {(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,x},{y}\rangle = \langle {x},{(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,y}\rangle
$$

*Proof.* By [`rvdT_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint). $\square$

<small>Used by [`modConj_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-isselfadjoint).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-real-inner-symm"></a>
**Lemma 852** (`rvdPmQ_real_inner_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L659)</small>

`D = P − Q` is real-symmetric — via the projection symmetry (fast, no adjoint).

$$
\langle {(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,x},{y}\rangle = \langle {x},{(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,y}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modConj_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-isselfadjoint).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-isselfadjoint"></a>
**Lemma 853** (`modConj_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L665)</small>

`J` is self-adjoint (`⟪J η, ζ⟫ = ⟪η, J ζ⟫`), by density from `D·T=T·D` (using the fast symmetry lemmas above — avoids the scoped-ℝ adjoint that times out).

$$
\langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta},{\zeta}\rangle = \langle {\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta}\rangle
$$

*Proof.* By [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`rvdPmQ_commute_rvdT_apply`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt), [`rvdT_real_inner_symm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-real-inner-symm), [`rvdPmQ_real_inner_symm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-real-inner-symm). $\square$

<small>Used by [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_inner_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-inner-conj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-sq"></a>
**Lemma 854** (`modConj_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L688)</small>

** `J² = 1`** — the modular conjugation is an involution (`⟪ζ, J²η⟫ = ⟪Jζ, Jη⟫ = ⟪ζ, η⟫`).

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta) = \eta
$$

*Proof.* By [`modConj_inner_map`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-inner-map), [`modConj_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-isselfadjoint). $\square$

<small>Used by [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`modConj_deviceOpC_neg_half`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [`modConj_inner_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-inner-conj), [`modConj_rvdRC_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [`modConjSqrtR_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjsqrtr-sq), [`modConj_rvdSqrtR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj), [`modConj_rvdSqrtTwoSubR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [`modConj_rvdSqrtR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr), and 6 more.</small>

<a id="d-qiqth-standardsubspacemodular-modconj-smul-i"></a>
**Lemma 855** (`modConj_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L693)</small>

**The modular conjugation `J` is antilinear**: `J(i·η) = −i·(J η)`.  On the dense range of `T` (which is ℂ-linear), `J(i·T x) = J(T(i·x)) = D(i·x) = (P−Q)(i·x) = i·(Q−P)x = −i·D x = −i·J(T x)` (`projK_smul_I`/`projIK_smul_I`), and continuity extends to all `η`.  This is the antilinearity RvD use to place `J𝒦` in `(i𝒦)^⊥` (Prop 2.2(5)), the source of the `w ⊥ i𝒦` vectors of Theorem 3.8.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(i \cdot \eta) = -i \cdot (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`projIK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-smul-i), [`projK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk-smul-i), [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt). $\square$

<small>Used by [`modConj_smul_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-smul-conj), [`modConj_inner_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-inner-conj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-smul-conj"></a>
**Lemma 856** (`modConj_smul_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L730)</small>

**`J` is conjugate-linear**: `J(c·η) = conj(c)·(J η)`.  Extends the antilinearity `modConj_smul_I` (`c = i`) to all complex scalars via the real decomposition `c = Re c + i·Im c` and `J`'s ℝ-linearity. This is the clean statement that bundles `J R^{1/2} J` (and similar `J`-sandwiches) as ℂ-linear.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(c \cdot \eta) = (\mathrm{starRingEnd}\,\mathbb{C})\,c \cdot (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta
$$

*Proof.* By [`modConj_smul_I`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-smul-i). $\square$

<small>Used by [`modConj_rvdSqrtR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconjbilin"></a>
**Definition 857** (`modConjBilin`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L748)</small>

**The J-twisted bilinear form** `B(v,w) = ⟪J v, w⟫` as a continuous ℂ-BILINEAR map `H →L[ℂ] H →L[ℂ] ℂ`. ℂ-linear in `v` by the J-cancellation (`inner_modConj_smul_left`: `J` antilinear ∘ inner conj-linear = ℂ-linear), ℂ-linear in `w` (inner second slot), bounded by `‖v‖·‖w‖` (`modConj_norm` isometry + Cauchy–Schwarz).  This is the bilinear form whose composition with two HOLOMORPHIC curves `g(z) = B(d_z(R)ζ, V_z η)` is holomorphic — the device-vector RvD g-function.

$$
J\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S \;:=\; (\mathrm{mk}\,\mathbb{C}\,(\lambda v w \mapsto \langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,v},{w}\rangle)\,\cdots \,\cdots \,\cdots \,\cdots ).\mathrm{mkContinuous}_{2}\,1\,\cdots
$$

<small>Used by [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire), [`gFunction_top_edge_real_all`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [`gConstancy_entire_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), and 11 more.</small>

<a id="d-qiqth-standardsubspacemodular-modconjbilin-apply"></a>
**Lemma 858** (`modConjBilin_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L766)</small>

`modConjBilin` applied: `B(v, w) = ⟪J v, w⟫`.

$$
((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,v)\,w = \langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,v},{w}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gFunction_bottom_eq_of_mem_K`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [`gFunction_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-zero), [`gFunction_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-real-eq), [`gFunction_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-inner-conj"></a>
**Lemma 859** (`modConj_inner_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L777)</small>

**The modular conjugation `J` is antiunitary**: `⟪J η, J ζ⟫ = conj⟪η, ζ⟫`.  The real part is `modConj_inner_map` (`J` is a real isometry); the imaginary part flips sign because `J` is antilinear (`modConj_smul_I`): `Im⟪Jη, Jζ⟫ = ⟪i·Jη, Jζ⟫_ℝ = −⟪J(i·η), Jζ⟫_ℝ = −⟪i·η, ζ⟫_ℝ = −Im⟪η, ζ⟫`.  This is the full Tomita reality of `J`, the engine behind `J𝒦 = (i𝒦)^⊥` (RvD Prop 2.2(5)).

$$
\langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta}\rangle = (\mathrm{starRingEnd}\,\mathbb{C})\,(\langle {\eta},{\zeta}\rangle)
$$

*Proof.* By [`modConj_inner_map`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-inner-map), [`modConj_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_smul_I`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-smul-i). $\square$

<small>Used by [`modConj_rvdSqrtR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt"></a>
**Lemma 860** (`rvdRC_commute_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L797)</small>

`T` commutes with `R` (both are continuous functions of `R`).

$$
\mathrm{Commute}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)
$$

*Proof.* By [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdSqrtR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr), [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`rvdRC_commute_rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc). $\square$

<small>Used by [`modConj_rvdRC_reflect`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [`rvdSqrtR_range_dense_in_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-rvdrc"></a>
**Lemma 861** (`rvdPmQ_rvdRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L806)</small>

`D R = (2 − R) D` pointwise — from the anticommutation `D(R−1) = −(R−1)D`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi)
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdPmQ_anticommute_rvdR_sub_one`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-anticommute-rvdr-sub-one). $\square$

<small>Used by [`modConj_rvdRC_reflect`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect"></a>
**Lemma 862** (`modConj_rvdRC_reflect`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L820)</small>

`J R = (2 − R) J` pointwise (the reflection intertwiner), by density from `range T`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)
$$

*Proof.* By [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt), [`rvdRC_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [`rvdPmQ_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-rvdrc). $\square$

<small>Used by [`modConj_rvdRC_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj"></a>
**Lemma 863** (`modConj_rvdRC_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L832)</small>

** `J R J = 2 − R`** — the modular conjugation reflects `R` (the bounded shadow of `J Δ J = Δ⁻¹`). One of the canonical Tomita–Takesaki relations, and a prerequisite for the CGP spectral balance.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi
$$

*Proof.* By [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_rvdRC_reflect`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect). $\square$

<small>Used by [`modConjSqrtR_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjsqrtr-sq), [`modConj_projIK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [`modConj_projK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projk-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconjsqrtr-sq"></a>
**Lemma 864** (`modConjSqrtR_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L838)</small>

**The square of `B = J R^{1/2} J` is `2 − R`**: `B(B ξ) = (2−R) ξ`, where `B ξ = J(R^{1/2}(J ξ))`. The inner `J² = 1` (`modConj_sq`) collapses `B² ξ = J R^{1/2} (J J) R^{1/2} J ξ = J R^{1/2} R^{1/2} J ξ = J R J ξ = (2−R) ξ` (`rvdSqrtR_mul_self` + `modConj_rvdRC_modConj`).  This is the `b·b = a` input to `CFC.sqrt_unique`: once `B` is bundled as a ℂ-linear positive operator (it commutes with `i·` by `modConj_smul_I` applied twice), square-root uniqueness yields `J R^{1/2} J = (2−R)^{1/2}` — the sqrt-reflection underlying `J𝒦 = (i𝒦)^⊥`, reachable WITHOUT general antilinear CFC.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi))))) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdSqrtR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self), [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_rvdRC_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj). $\square$

<small>Used by [`modConj_rvdSqrtR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj"></a>
**Lemma 865** (`modConj_rvdSqrtR_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L848)</small>

** The sqrt-reflection `J R^{1/2} J = (2−R)^{1/2}`** (RvD Prop 2.2(5) engine), reached via square-root UNIQUENESS — NOT general antilinear CFC.  Bundle `B ξ = J(R^{1/2}(J ξ))` as a ℂ-linear operator (ℂ-linear by `modConj_smul_conj` applied twice), self-adjoint and positive (the antiunitary `modConj_inner_conj` reduces `⟨B x, y⟩` to `conj⟨R^{1/2}(J x), J y⟩`, and `R^{1/2} ≥ 0`), with `B·B = 2−R` (`modConjSqrtR_sq`). `CFC.sqrt_unique` then identifies `B` with `(2−R)^{1/2} = rvdSqrtTwoSubR`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)\,\xi
$$

*Proof.* By [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdSqrtR_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-nonneg), [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_smul_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-smul-conj), [`modConj_inner_conj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-inner-conj), [`modConjSqrtR_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjsqrtr-sq). $\square$

<small>Used by [`modConj_rvdSqrtTwoSubR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [`modConj_rvdSqrtR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj"></a>
**Lemma 866** (`modConj_rvdSqrtTwoSubR_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L891)</small>

**The symmetric sqrt-reflection `J (2−R)^{1/2} J = R^{1/2}`** — immediate from `J R^{1/2} J = (2−R)^{1/2}` (`modConj_rvdSqrtR_modConj`) by sandwiching with `J` and using `J² = 1` (`modConj_sq`).

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\xi
$$

*Proof.* By [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_rvdSqrtR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj). $\square$

<small>Used by [`modConj_deviceOpC_neg_half`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [`modConj_rvdT_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [`modConj_rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdsqrtr"></a>
**Lemma 867** (`modConj_rvdSqrtR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L899)</small>

**The "moved" sqrt-reflection** `J R^{1/2} = (2−R)^{1/2} J`: `J(R^{1/2} y) = (2−R)^{1/2}(J y)`. (`modConj_rvdSqrtR_modConj` at `J y` + `J² = 1`.)

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,y) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,y)
$$

*Proof.* By [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_rvdSqrtR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj). $\square$

<small>Used by [`modConj_rvdT_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [`rvdSqrtR_modConj_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-modconj-of-mem-k), [`modConj_fixed_of_sqrtR_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdt-modconj"></a>
**Lemma 868** (`modConj_rvdT_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L915)</small>

**`J T J = T`** — the modular conjugation commutes with the polar radius `T = R^{1/2}(2−R)^{1/2}`. `J T J = (J R^{1/2} J)(J (2−R)^{1/2} J) = (2−R)^{1/2} R^{1/2} = R^{1/2}(2−R)^{1/2} = T`, using both sqrt-reflections and that the square roots commute (`rvdSqrtR_commute_rvdSqrtTwoSubR`).  Hence `[J, T] = 0`, the keystone giving `J D J = D` and thence `J P J = 1 − Q` (`J𝒦 = (i𝒦)^⊥`).

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi
$$

*Proof.* By [`rvdSqrtR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr), [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`rvdSqrtR_commute_rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [`modConj_rvdSqrtTwoSubR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [`modConj_rvdSqrtR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr). $\square$

<small>Used by [`rvdT_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-modconj), [`rvdSqrtR_range_dense_in_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-modconj"></a>
**Lemma 869** (`rvdT_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L926)</small>

**`T J = D`** — combining `[J, T] = 0` (`J T J = T`) with `J T = D` (`modConj_rvdT`). `T(J η) = J(T η) = D η`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\eta
$$

*Proof.* By [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt), [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_rvdT_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj). $\square$

<small>Used by [`modConj_rvdPmQ_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj"></a>
**Lemma 870** (`modConj_rvdPmQ_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L935)</small>

**`J D J = D`** — the modular conjugation commutes with `D = P − Q`.  From `T J = D` (`rvdT_modConj`): `J(D(J ξ)) = J(T(J(J ξ))) = J(T ξ) = D ξ`.  With `J R J = 2 − R` this gives `J P J = 1 − Q`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi
$$

*Proof.* By [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt), [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`rvdT_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-modconj). $\square$

<small>Used by [`modConj_projIK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [`modConj_projK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projk-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-projik-modconj"></a>
**Lemma 871** (`modConj_projIK_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L941)</small>

**`J Q J = 1 − P`** — the modular conjugation reflects the projection `Q = projIK` onto `1 − P`. `J Q J = (J R J − J D J)/2 = ((2−R) − D)/2 = 1 − P` (`J R J = 2−R`, `J D J = D`).  Concretely `J(Q(J ξ)) = ξ − P ξ`.  This is RvD Prop 2.2(5): `J` carries `i𝒦` onto `𝒦^⊥` and `𝒦` onto `(i𝒦)^⊥`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = \xi - (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdR_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-apply), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-apply), [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [`modConj_rvdRC_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [`modConj_rvdPmQ_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj). $\square$

<small>Used by [`projIK_modConj_eq_zero_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k"></a>
**Lemma 872** (`projIK_modConj_eq_zero_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L956)</small>

**`J 𝒦 ⊆ (i𝒦)^⊥`** (RvD Prop 2.2(5)): for `ξ ∈ 𝒦` (`P ξ = ξ`), `J ξ ⊥ i𝒦` (`projIK (J ξ) = 0`). From `J Q J = 1 − P` (`modConj_projIK_modConj`): `J(Q(J ξ)) = ξ − P ξ = 0`, and `J` is injective (`J² = 1`), so `Q(J ξ) = 0`.  This places the modular-conjugated standard-subspace vectors — the `J`-twisted `w`-vectors of RvD Theorem 3.8's `g`-function — in `(i𝒦)^⊥`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi = \xi \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi) = 0
$$

*Proof.* By [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_projIK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projik-modconj). $\square$

<small>Used by [`gFunction_top_edge_real`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-top-edge-real).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-projk-modconj"></a>
**Lemma 873** (`modConj_projK_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L967)</small>

**`J P J = 1 − Q`** — the symmetric reflection: `J(P(J ξ)) = ξ − Q ξ`.  `J P J = (J R J + J D J)/2 = ((2−R) + D)/2 = 1 − Q` (`J R J = 2−R`, `J D J = D`).  With `J Q J = 1 − P` this is the full RvD Prop 2.2(5): `J` swaps `(𝒦, i𝒦)` with `((i𝒦)^⊥, 𝒦^⊥)`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = \xi - (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,\xi
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdR_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-apply), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-apply), [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [`modConj_rvdRC_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [`modConj_rvdPmQ_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj). $\square$

<small>Used by [`projK_modConj_eq_self_of_perp_IK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik"></a>
**Lemma 874** (`projK_modConj_eq_self_of_perp_IK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L982)</small>

**`(i𝒦)^⊥ ⊆ J𝒦`** — the reverse inclusion, giving the equality `J𝒦 = (i𝒦)^⊥`.  For `w ⊥ i𝒦` (`projIK w = 0`), `J P J` at `w` gives `J(P(J w)) = w − Q w = w`, and `J²=1` injectivity yields `P(J w) = J w`, i.e. `J w ∈ 𝒦`; hence `w = J(J w) ∈ J𝒦`.  So the `(i𝒦)^⊥` `w`-supply of the orbit-identity framework is *exactly* the `J`-images of `𝒦`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,w = 0 \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,w) = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,w
$$

*Proof.* By [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_projK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projk-modconj). $\square$

<small>Used by [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-eq-of-mem-k"></a>
**Lemma 875** (`rvdPmQ_eq_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1002)</small>

**Bounded Tomita fixedness:** for `ξ ∈ 𝒦` (`P ξ = ξ`), `D ξ = (2 − R) ξ`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi = \xi \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi
$$

*Proof.* By [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc). $\square$

<small>Used by [`modConj_rvdT_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdt-of-mem-k"></a>
**Lemma 876** (`modConj_rvdT_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1012)</small>

For `ξ ∈ 𝒦`, `J(T ξ) = (2 − R) ξ` — the modular form of the bounded Tomita fixedness, equating the two bounded objects whose `R`-spectral measures drive the CGP balance.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi = \xi \to (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi
$$

*Proof.* By [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt), [`rvdPmQ_eq_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-eq-of-mem-k). $\square$

<small>Used by [`rvdSqrtR_modConj_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-modconj-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-commute-projk-of-commute-r-d"></a>
**Lemma 877** (`commute_projK_of_commute_R_D`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1026)</small>

**Generic `projK`-commutation:** a continuous ℂ-linear `A` commuting with `rvdR` (`= R`) and `rvdPmQ` (`= D`) pointwise commutes with `projK = (R + D)/2`.  The operator-generic form of `modUnitary_commute_projK_of`.

$$
(\forall (\xi : H), A\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,(A\,\xi)) \to (\forall (\xi : H), A\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,(A\,\xi)) \to \forall (\xi : H), A\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,(A\,\xi)
$$

*Proof.* By [`rvdR_add_rvdPmQ_eq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq). $\square$

<small>Used by [`rvdSqrtR_range_dense_in_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k).</small>

<a id="d-qiqth-standardsubspacemodular-commute-rvdpmq-of-commute-modconj-rvdt"></a>
**Lemma 878** (`commute_rvdPmQ_of_commute_modConj_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1047)</small>

**`[A, D] = 0` from `[A, J] = [A, T] = 0`:** since `D = J·T` (`modConj_rvdT`: `J(Tξ) = Dξ`), an operator commuting with the modular conjugation `J` and the polar radius `T` commutes with `D = rvdPmQ`.  For a real *symmetric* `f`, `cfcCont f` commutes with both (`J` via `modConj_cfcΩ`/`twΩ`, `T` as a function of `R`), so it commutes with `D` — the `[·, D] = 0` "frontier" step, available for symmetric symbols.

$$
(\forall (\xi : H), A\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(A\,\xi)) \to (\forall (\xi : H), A\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,(A\,\xi)) \to \forall (\xi : H), A\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,(A\,\xi)
$$

*Proof.* By [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt). $\square$

<small>Used by [`rvdSqrtR_range_dense_in_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k).</small>

<a id="d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik"></a>
**Lemma 879** (`inner_real_of_mem_K_perp_IK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1056)</small>

**RvD Proposition 2.3 — reality across `𝒦` and `(i𝒦)^⊥`.**  If `x ∈ 𝒦` (`projK x = x`) and `y ⊥ i𝒦` (`projIK y = 0`), then `⟨x, y⟩_ℂ` is *real*.  Reason: `Im⟨x, y⟩ = ⟨i·x, y⟩_ℝ`, and `i·x ∈ i𝒦` while `y ⊥ i𝒦`, so this real inner product vanishes.  This is the reality used in RvD Theorem 3.8 to show the correlation `g(t) = ⟨U_t η, J(2−R)^{1/2}R^{−1/2}ζ⟩` is real on the real axis (and, after the KMS flip, on the lower edge), the input to "real on both edges ⟹ constant".

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,x = x \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,y = 0 \to (\langle {x},{y}\rangle).\mathrm{im} = 0
$$

*Proof.* By [`projIK_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-isselfadjoint), [`projIK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-smul-i). $\square$

<small>Used by [`gFunction_top_edge_real`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-top-edge-real).</small>

<a id="d-qiqth-standardsubspacemodular-eq-of-mem-k-of-inner-perp-ik"></a>
**Lemma 880** (`eq_of_mem_K_of_inner_perp_IK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1073)</small>

**Totality of `(i𝒦)^⊥` against `𝒦`** (RvD Theorem 3.8 closeout): two vectors of `𝒦` with equal inner products against *every* `w ⊥ i𝒦` (`projIK w = 0`) are equal.  Their difference `d ∈ 𝒦` is orthogonal to all of `(i𝒦)^⊥`: taking `w = d − Q d ∈ (i𝒦)^⊥` gives `‖d − Q d‖² = Re⟨w, d⟩ = 0`, so `d = Q d ∈ i𝒦`; then `d ∈ 𝒦 ⊓ i𝒦 = {0}` (`IsSeparating`).  This is the totality step: combined with `orbit_inner_eq_of_entire` for `V` and `Δ^{it}` (both giving `⟨w, ·_t η⟩ = ⟨w, η⟩`) it yields `V_t η = Δ^{it} η` on `𝒦`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,a = a \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,b = b \to (\forall (w : H), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,w = 0 \to \langle {w},{a}\rangle = \langle {w},{b}\rangle) \to a = b
$$

*Proof.* By [`projIK_idem`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-idem). $\square$

<small>Used by [`modUnitary_eq_of_orbit_compare`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-add"></a>
**Lemma 881** (`borelFC_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1110)</small>

`borelFC` is additive in `f` (lift of `boundedFC_add`).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} + \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hCg0}\,\mathrm{hCg}
$$

*Proof.* By [`boundedFC_add`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Used by [`borelFC_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-sub), [`cfcCont_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-add).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-smul"></a>
**Lemma 882** (`borelFC_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1119)</small>

`borelFC` is ℂ-homogeneous in `f` (lift of `boundedFC_smul`).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = c \cdot \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}
$$

*Proof.* By [`boundedFC_smul`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Used by [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq), [`borelFC_neg`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-neg), [`cfcCont_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-smul).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-neg"></a>
**Lemma 883** (`borelFC_neg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1127)</small>

`borelFC` is additive-inverse compatible: `(-f)(T) = -f(T)` (from `borelFC_smul (-1)`).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\mathrm{hC0}\,\cdots = -\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}
$$

*Proof.* By [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`borelFC_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-smul). $\square$

<small>Used by [`borelFC_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-sub).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-sub"></a>
**Lemma 884** (`borelFC_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1137)</small>

`borelFC` is subtractive: `(f − g)(T) = f(T) − g(T)` (lift of additivity + `borelFC_neg`).

$$
\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} - \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hCg0}\,\mathrm{hCg}
$$

*Proof.* By [`borelFC_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-add), [`borelFC_neg`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-neg). $\square$

<small>Used by [`deviceOpC_sub`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-sub), [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont"></a>
**Definition 885** (`cfcCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1151)</small>

The bounded Borel FC of `R = rvdRC S` on a continuous function, with the automatic compact-sup bound `‖f ω‖ ≤ ‖f‖`.

$$
\Phi_{c}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,f \;:=\; \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\cdots \,\cdots \,\cdots
$$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`cfcCont_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-norm-le), [`cfcCont_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-one), [`cfcCont_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-mul), [`cfcCont_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-add), [`cfcCont_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-smul), and 12 more.</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-norm-le"></a>
**Lemma 886** (`cfcCont_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1164)</small>

$$
\|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f\| \le 2 \cdot \|f\|
$$

*Proof.* By [`boundedFC`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [`boundedFC_norm_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le), [`PVM_of_selfAdjoint`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`cfcCont_continuous`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-continuous).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-one"></a>
**Lemma 887** (`cfcCont_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1168)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,1 = 1
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_one`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-one), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`cfcΩ_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-one).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-mul"></a>
**Lemma 888** (`cfcCont_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1174)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,(f \cdot g) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,g
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`cfcΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-mul).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-add"></a>
**Lemma 889** (`cfcCont_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1191)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,(f + g) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f + \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,g
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`borelFC_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-add). $\square$

<small>Used by [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`cfcContₗ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`cfcΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-add).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-smul"></a>
**Lemma 890** (`cfcCont_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1205)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,(c \cdot f) = c \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`borelFC_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-smul). $\square$

<small>Used by [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`cfcΩ_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-smul).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-star"></a>
**Lemma 891** (`cfcCont_star`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1217)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,({{f}}^{*}) = {{\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f}}^{*}
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`borelFC_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-adjoint), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-coord"></a>
**Lemma 892** (`cfcCont_coord`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1226)</small>

`cfcCont` sends the coordinate function to `R`.

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,\{\mathrm{toFun} :=\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord}{\mathrm{sc}}\,S , \mathrm{continuous\_toFun} :=\cdots \} = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`specCoord_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-measurable), [`specCoord_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-norm-le), [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc). $\square$

<small>Used by [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont"></a>
**Definition 893** (`cfcContₗ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1233)</small>

`cfcCont` as a ℂ-linear map (for the continuity bound).

$$
\mathrm{cfcContₗ}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S \;:=\; \{\mathrm{toFun} :=\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S , \mathrm{map\_add}^{\prime} :=\cdots , \mathrm{map\_smul}^{\prime} :=\cdots \}
$$

<small>Used by [`cfcCont_continuous`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-continuous).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-continuous"></a>
**Lemma 894** (`cfcCont_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1239)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S)
$$

*Proof.* By [`cfcCont_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-norm-le), [`cfcContₗ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont). $\square$

<small>Used by [`cfcΩ_continuous`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-continuous).</small>

<a id="d-qiqth-standardsubspacemodular-covm"></a>
**Definition 895** (`covM`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1249)</small>

The radius `M = ‖R‖·‖1‖` bounding the spectrum.

$$
\mathrm{covM}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S \;:=\; \|\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S\| \cdot \|1\|
$$

<small>Used by [`spectrum_subset_covΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-spectrum-subset-cov), [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl), [`tauΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tau), [`cfcΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc), [`cfcΩ_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-one), [`cfcΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-mul), [`cfcΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-add), [`cfcΩ_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-smul), and 14 more.</small>

<a id="d-qiqth-standardsubspacemodular-spectrum-subset-cov"></a>
**Lemma 896** (`spectrum_subset_covΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1254)</small>

$$
\mathrm{sp}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S) \subseteq \mathrm{Icc}\,(-\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-covm}{\mathrm{covM}}\,S)\,(2 + \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-covm}{\mathrm{covM}}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl).</small>

<a id="d-qiqth-standardsubspacemodular-incl"></a>
**Definition 897** (`inclΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1262)</small>

The inclusion `σℝ R ↪ Ω` as a continuous map.

$$
\mathrm{inclΩ}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S \;:=\; \{\mathrm{toFun} :=\mathrm{inclusion}\,\cdots , \mathrm{continuous\_toFun} :=\cdots \}
$$

<small>Used by [`cfcΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc), [`cfcΩ_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-one), [`cfcΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-mul), [`cfcΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-add), [`cfcΩ_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-smul), [`cfcΩ_continuous`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-continuous), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-tau"></a>
**Definition 898** (`tauΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1267)</small>

The involution `τ(r) = 2 − r` on the symmetric `Ω`.

$$
\mathrm{tauΩ}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S \;:=\; \{\mathrm{toFun} :=\lambda x \mapsto \langle 2 - x , \cdots \rangle , \mathrm{continuous\_toFun} :=\cdots \}
$$

<small>Used by [`twΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw), [`twΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-add), [`twΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-mul), [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-cfc"></a>
**Definition 899** (`cfcΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1273)</small>

`cfcΩ f = f(R)` for `f` continuous on the symmetric domain `Ω`.

$$
\mathrm{cfcΩ}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,f \;:=\; \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,(f.\mathrm{comp}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl}{\mathrm{incl}}\,S))
$$

<small>Used by [`cfcΩ_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-one), [`cfcΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-mul), [`cfcΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-add), [`cfcΩ_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-smul), [`cfcΩ_continuous`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-continuous), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`cfcΩ_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-sub), [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord), and 3 more.</small>

<a id="d-qiqth-standardsubspacemodular-cfc-one"></a>
**Lemma 900** (`cfcΩ_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1277)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,1 = 1
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`cfcCont_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-one), [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Used by [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord), [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-mul"></a>
**Lemma 901** (`cfcΩ_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1280)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(f \cdot g) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,g
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`cfcCont_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-mul), [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Used by [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-add"></a>
**Lemma 902** (`cfcΩ_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1284)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(f + g) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f + \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,g
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`cfcCont_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-add), [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Used by [`cfcΩ_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-sub), [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-smul"></a>
**Lemma 903** (`cfcΩ_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1288)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(c \cdot f) = c \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`cfcCont_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-smul), [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Used by [`cfcΩ_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-sub), [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord), [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-continuous"></a>
**Lemma 904** (`cfcΩ_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1297)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S)
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`cfcCont_continuous`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont-continuous), [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Used by [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-coord"></a>
**Definition 905** (`coordΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1302)</small>

The coordinate function `x ↦ x.1` on `Ω` (real-valued ⟹ self-adjoint, the SW generator).

$$
\mathrm{coordΩ}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S \;:=\; \{\mathrm{toFun} :=\lambda x \mapsto x , \mathrm{continuous\_toFun} :=\cdots \}
$$

<small>Used by [`coordΩ_star`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-coord-star), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord), [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-coord-star"></a>
**Lemma 906** (`coordΩ_star`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1307)</small>

$$
{{\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-coord}{\mathrm{coord}}\,S}}^{*} = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-coord}{\mathrm{coord}}\,S
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-tw"></a>
**Definition 907** (`twΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1310)</small>

The twist `(twΩ f)(r) = conj(f(2−r))`.

$$
\mathrm{twΩ}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,f \;:=\; {{f.\mathrm{comp}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tau}{\mathrm{tau}}\,S)}}^{*}
$$

<small>Used by [`twΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-add), [`twΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-mul), [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord), [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine), [`twΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-h), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h), [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-tw-add"></a>
**Lemma 908** (`twΩ_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1314)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,(f + g) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,f + \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,g
$$

*Proof.* By [`tauΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tau). $\square$

<small>Used by [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-tw-mul"></a>
**Lemma 909** (`twΩ_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1318)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,(f \cdot g) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,f \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,g
$$

*Proof.* By [`tauΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tau). $\square$

<small>Used by [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-coord"></a>
**Lemma 910** (`cfcΩ_coordΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1322)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-coord}{\mathrm{coord}}\,S) = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord), [`specCoord_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-measurable), [`specCoord_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-norm-le), [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`covM`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-covm), [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Used by [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord), [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-sub"></a>
**Lemma 911** (`cfcΩ_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1327)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(f - g) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f - \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,g
$$

*Proof.* By [`cfcΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-add), [`cfcΩ_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-smul). $\square$

<small>Used by [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-tw-coord"></a>
**Lemma 912** (`cfcΩ_twΩ_coordΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1331)</small>

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-coord}{\mathrm{coord}}\,S)) = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`covM`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-covm), [`cfcΩ_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-one), [`cfcΩ_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-smul), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`cfcΩ_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-sub). $\square$

<small>Used by [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs"></a>
**Lemma 913** (`rvdPmQ_mul_rvdRC_rs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1338)</small>

The base case of the intertwiner: `D·R = (2−R)·D` in `restrictScalars` form.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S) = \mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S) \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [`rvdPmQ_mul_rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr). $\square$

<small>Used by [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-intertwine"></a>
**Lemma 914** (`cfcΩ_intertwine`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1348)</small>

** The continuous intertwiner `D·f(R) = conj(f(2−·))(R)·D`** for every CONTINUOUS `f` on the symmetric domain `Ω`.  Proved by complex Stone–Weierstrass: both sides are continuous in `f`, the `coordΩ`-generated subalgebra is dense, and they agree there (base case `D·R=(2−R)·D` + the algebra structure).  `D` is antilinear, so the relation is conjugate-linear — hence the "good set" is a plain `Subalgebra` (not a `*`-subalgebra), but `coordΩ` is self-adjoint so the generated subalgebra still has dense closure.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f) = \mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,f)) \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdPmQ_smul_conj`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-smul-conj), [`tauΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tau), [`cfcΩ_one`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-one), [`cfcΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-mul), [`cfcΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-add), [`cfcΩ_smul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-smul), [`cfcΩ_continuous`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-continuous), [`coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-coord), [`coordΩ_star`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-coord-star), [`twΩ_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-add), [`twΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-mul), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord), [`rvdPmQ_mul_rvdRC_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs). $\square$

<small>Used by [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k"></a>
**Lemma 915** (`rvdSqrtR_range_dense_in_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1540)</small>

** The `√R`-range density in `𝒦` (`hdense`)** — RvD's `ξ = R^{1/2}ζ` reconciliation, the LAST analytic input of the device g-function discharge.  Every `ξ ∈ 𝒦` is a limit of vectors `√R ζ_k ∈ 𝒦`. …

$$
\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`projK_idem`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk-idem), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj), [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`rvdRC_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [`modConj_rvdT_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [`commute_projK_of_commute_R_D`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-commute-projk-of-commute-r-d), [`commute_rvdPmQ_of_commute_modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-commute-rvdpmq-of-commute-modconj-rvdt). $\square$

<small>Used by [`oneParticleBW_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-complete).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-reflect"></a>
**Lemma 916** (`modChar_reflect`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1581)</small>

**`u_t` is θ-fixed:** `conj(u_t(2−r)) = u_t(r)`.  (`u_t(2−r)=exp(it·log(r/(2−r)))=conj(u_t(r))`.)

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,(2 - r)) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`twΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-h).</small>

<a id="d-qiqth-standardsubspacemodular-h"></a>
**Definition 917** (`hΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1597)</small>

The **damped modular function** as a continuous map on `Ω`.

$$
\mathrm{hΩ}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,t \;:=\; \{\mathrm{toFun} :=\lambda x \mapsto \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,x \cdot (x \cdot (2 - x)) , \mathrm{continuous\_toFun} :=\cdots \}
$$

<small>Used by [`twΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-h), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h), [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-tw-h"></a>
**Lemma 918** (`twΩ_hΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1602)</small>

`hΩ` is θ-fixed: `twΩ (hΩ) = hΩ` (the damped modular function is invariant under `r↦2−r` + conj).

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-h}{\mathrm{h}}\,S\,t) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-h}{\mathrm{h}}\,S\,t
$$

*Proof.* By [`modChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar), [`modChar_reflect`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar-reflect). $\square$

<small>Used by [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-h"></a>
**Lemma 919** (`cfcΩ_hΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1613)</small>

`cfcΩ(hΩ) = U_t · A` with `A = R(2−R)` — the damped FC factors as the modular unitary times the polynomial damping (`borelFC_mul`).

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-h}{\mathrm{h}}\,S\,t) = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t \cdot (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* By [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul), [`modChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`modSpecFun`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun), [`modSpecFun_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-measurable), [`modSpecFun_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`covM`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-covm), [`inclΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-incl), [`tauΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tau), [`cfcΩ_mul`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-mul), [`coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-coord), [`twΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw), [`cfcΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-coord), [`cfcΩ_twΩ_coordΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-tw-coord). $\square$

<small>Used by [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint"></a>
**Lemma 920** (`rvdRC_mul_rvdTwoSubRC_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1650)</small>

`A = R(2−R)` is self-adjoint.

$$
\mathrm{IsSelfAdjoint}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* By [`rvdRC_commute_rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Used by [`rvdRC_mul_rvdTwoSubRC_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective"></a>
**Lemma 921** (`rvdRC_mul_rvdTwoSubRC_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1660)</small>

`A = R(2−R) = D²` is injective (`D` injective).

$$
\mathrm{Injective}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* By [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdPmQ_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-injective), [`rvdRC_mul_rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply). $\square$

<small>Used by [`rvdRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-injective), [`rvdTwoSubRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdtwosubrc-injective), [`rvdRC_mul_rvdTwoSubRC_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-injective"></a>
**Lemma 922** (`rvdRC_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1667)</small>

**`R = rvdRC` is injective** (toward the `√R`-range density, the `ξ = √R ζ` reconciliation of the device g-function discharge).  From `R(2−R)` injective (`rvdRC_mul_rvdTwoSubRC_injective`): `R a = R b` gives `R(2−R)a = (2−R)(R a) = (2−R)(R b) = R(2−R)b` (commute), hence `a = b`.  As a self-adjoint operator, `R` injective ⟹ `√R` injective ⟹ `√R` has DENSE RANGE in `H` — the structural basis of the `√R`-range density that lifts GConstancy from `ξ = √R ζ` to all of `𝒦`.

$$
\mathrm{Injective}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)
$$

*Proof.* By [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdRC_commute_rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc), [`rvdRC_mul_rvdTwoSubRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective). $\square$

<small>Used by [`rvdRC_E_zero_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-injective"></a>
**Lemma 923** (`rvdTwoSubRC_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1677)</small>

**`2 − R = rvdTwoSubRC` is injective** (the companion to `rvdRC_injective`, giving `E({2}) = 0`).  From `R(2−R)` injective: `(2−R)a = (2−R)b` gives `R((2−R)a) = R((2−R)b)`, i.e. `R(2−R)a = R(2−R)b`, hence `a = b`.  So `2` is not an eigenvalue of `R` — the spectral atom at the device-character endpoint `r = 2` vanishes, the other half of `deviceOpC(−i/2) = √(2−R)` (a.e., `PVM({0,2}) = 0`).

$$
\mathrm{Injective}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdRC_mul_rvdTwoSubRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective). $\square$

<small>Used by [`rvdSqrtTwoSubR_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-injective), [`rvdRC_E_two_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr"></a>
**Lemma 924** (`modConj_rvdSqrtTwoSubR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1686)</small>

**`J √(2−R) = √R J`** — the companion of `modConj_rvdSqrtR` (`J √R = √(2−R) J`), for the bottom-edge Tomita algebra.  From `modConj_rvdSqrtTwoSubR_modConj` (`J √(2−R) J = √R`) at `J y` + `J² = 1`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)\,y) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,y)
$$

*Proof.* By [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_rvdSqrtTwoSubR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj). $\square$

<small>Used by [`rvdSqrtR_modConj_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-modconj-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrttwosubr-injective"></a>
**Lemma 925** (`rvdSqrtTwoSubR_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1693)</small>

**`√(2−R)` is injective** — companion to `rvdT_injective`: from `√(2−R)² = 2−R` and `2−R` injective (`rvdTwoSubRC_injective`).

$$
\mathrm{Injective}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)
$$

*Proof.* By [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdSqrtTwoSubR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [`rvdTwoSubRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdtwosubrc-injective). $\square$

<small>Used by [`rvdSqrtR_modConj_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-modconj-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr-modconj-of-mem-k"></a>
**Lemma 926** (`rvdSqrtR_modConj_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1705)</small>

**RvD Proposition 3.7 (bounded Tomita on `√R`):** for `ξ ∈ 𝒦`, `√R (Jξ) = √(2−R) ξ`.  This is the BOUNDED form of `Δ^{1/2}ξ = Jξ` (with `Δ^{1/2} = √(2−R)·√R⁻¹`): from `J(Tξ) = (2−R)ξ` (`modConj_rvdT_of_mem_K`, `T = √R √(2−R)`) expand `J(√R(√(2−R)ξ)) = √(2−R)(√R(Jξ))` (the two sqrt reflections), so `√(2−R)(√R(Jξ)) = (2−R)ξ = √(2−R)(√(2−R)ξ)`, and cancel one `√(2−R)`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi = \xi \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)\,\xi
$$

*Proof.* By [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdSqrtTwoSubR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`modConj_rvdSqrtR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr), [`modConj_rvdT_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt-of-mem-k), [`modConj_rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr), [`rvdSqrtTwoSubR_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-injective). $\square$

<small>Used by [`modConj_fixed_of_sqrtR_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k"></a>
**Lemma 927** (`modConj_fixed_of_sqrtR_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1718)</small>

**`√Rζ ∈ 𝒦 ⟹ Jζ = ζ`** — the bottom-edge condition reconciliation.  Resolves the gap between the `gConstancy_eta_of_bottom` hypothesis `√Rζ ∈ 𝒦` and the `J`-fixedness `Jζ = ζ` the bottom-edge g-vector simplification needs.  From `√R(J(√Rζ)) = √(2−R)(√Rζ)` (`rvdSqrtR_modConj_of_mem_K` at `ξ = √Rζ`) and `J(√Rζ) = √(2−R)(Jζ)` (`modConj_rvdSqrtR`): `√R√(2−R)(Jζ) = √(2−R)√R ζ = √R√(2−R) ζ` (commute), so `rvdT(Jζ) = rvdT ζ`, and `rvdT` injective gives `Jζ = ζ`.  (So `√Rζ ∈ 𝒦` makes `ζ` `J`-fixed: `Jξ = Δ^{1/2}ξ` on `𝒦` forces `Jζ = ζ` here.)

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta = \zeta
$$

*Proof.* By [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`rvdSqrtR_commute_rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`rvdT_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-injective), [`modConj_rvdSqrtR`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr), [`rvdSqrtR_modConj_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-modconj-of-mem-k). $\square$

<small>Used by [`modConj_deviceVecF_bottom_eq_of_mem_K`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset"></a>
**Lemma 928** (`rvdRC_mul_E_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1733)</small>

**Spectral-atom eigen-relation** `R · E({λ = c}) = c · E({λ = c})`: the bounded Borel FC sends the coordinate `λ` to multiplication, so on the level set `{λ = c}` the operator `R = ∫λ dE` acts as the scalar `c`.  Route: `R = borelFC(coord)` (`rvdRC_eq_borelFC`), `E(s) = borelFC(𝟙_s)` (`borelFC_indicator`), the pointwise identity `coord·𝟙_s = c·𝟙_s`, then `borelFC_mul` + `borelFC_const`. With `R`/`2−R` injectivity this kills the endpoint spectral atoms (`E({0}) = E({2}) = 0`).

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).E\,\{\omega|\omega = c\} = c \cdot (\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).E\,\{\omega|\omega = c\}
$$

*Proof.* By [`norm_indicatorOne_le`](/browser/qiqth-spectral-pvm#d-qiqth-spectral-projectionvaluedmeasure-norm-indicatorone-le), [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`borelFC_mul`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-mul), [`borelFC_const`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-const), [`borelFC_indicator`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc-indicator), [`borelFC_congr`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-borelfc-congr), [`specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord), [`specCoord_measurable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-measurable), [`specCoord_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-speccoord-norm-le), [`rvdRC_eq_borelFC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc). $\square$

<small>Used by [`rvdRC_E_zero_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset), [`rvdRC_E_two_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset"></a>
**Lemma 929** (`rvdRC_E_zero_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1780)</small>

**`E({λ = 0}) = 0`** — no spectral atom at `0`: from `R · E({0}) = 0` (`rvdRC_mul_E_levelSet` at `c = 0`) and `R` injective (`rvdRC_injective`).  So `0` is not an eigenvalue of `R`.

$$
(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).E\,\{\omega|\omega = 0\} = 0
$$

*Proof.* By [`rvdRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-injective), [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset). $\square$

<small>Used by [`rvdSpecMeasure_zero_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-zero-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset"></a>
**Lemma 930** (`rvdRC_E_two_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1794)</small>

**`E({λ = 2}) = 0`** — no spectral atom at `2`: from `R · E({2}) = 2 · E({2})`, so `(2 − R) · E({2}) = 0`, and `2 − R` injective (`rvdTwoSubRC_injective`).

$$
(\href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).E\,\{\omega|\omega = 2\} = 0
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [`rvdTwoSubRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdtwosubrc-injective), [`rvdRC_mul_E_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset). $\square$

<small>Used by [`rvdSpecMeasure_two_levelSet`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-two-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange"></a>
**Lemma 931** (`rvdRC_mul_rvdTwoSubRC_denseRange`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1813)</small>

`A.restrictScalars ℝ` has dense range (self-adjoint + injective).

$$
\mathrm{DenseRange}\,(\mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S))
$$

*Proof.* By [`restrictScalars_star`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-restrictscalars-star), [`rvdRC_mul_rvdTwoSubRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint), [`rvdRC_mul_rvdTwoSubRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective). $\square$

<small>Used by [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs"></a>
**Lemma 932** (`modUnitary_commute_rvdPmQ_rs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1830)</small>

** The modular covariance `[U_t, D] = 0`** (operator form): the modular flow commutes with the antilinear `D = P−Q`.  From the intertwiner applied to the θ-fixed damped function `hΩ` (`D·(U_t·A)=(U_t·A)·D`), `D·A=A·D`, and cancelling `A` by its dense range.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t) = \mathrm{res}\,\mathbb{R}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t) \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [`rvdPmQ_commute_A`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [`covM`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-covm), [`cfcΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc), [`twΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw), [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine), [`hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-h), [`twΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-tw-h), [`cfcΩ_hΩ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-h), [`rvdRC_mul_rvdTwoSubRC_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange). $\square$

<small>Used by [`modUnitary_commute_rvdPmQ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq"></a>
**Lemma 933** (`modUnitary_commute_rvdPmQ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1851)</small>

** The modular covariance `[U_t, D] = 0`** (pointwise): `U_t(D ξ) = D(U_t ξ)`.  Combined with `[U_t, R] = 0` this gives full standard-subspace invariance `U_t 𝒦 = 𝒦`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)
$$

*Proof.* By [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs). $\square$

<small>Used by [`modUnitary_mapsTo_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [`modConj_commute_modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-mapsto-k"></a>
**Lemma 934** (`modUnitary_mapsTo_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1858)</small>

** Full standard-subspace invariance `U_t 𝒦 ⊆ 𝒦`** — both obligations (`[U_t,R]=0` and the covariance `[U_t,D]=0`) now discharged.

$$
\forall \xi\in S.\mathrm{cl}, (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi \in S.\mathrm{cl}
$$

*Proof.* By [`modUnitary_mapsTo_K_of_commute_D`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d), [`modUnitary_commute_rvdPmQ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq). $\square$

<small>Used by [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`oneParticleBW_of_comparison`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`gFunction_top_edge_real`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-top-edge-real).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdt"></a>
**Lemma 935** (`modUnitary_commute_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1866)</small>

`U_t` commutes with `T = √(R(2−R))` (both functions of `R`; via `[U_t,R]=0` and `Commute.cfc_real`).

$$
\mathrm{Commute}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdSqrtR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr), [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`modUnitary_commute_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc). $\square$

<small>Used by [`modConj_commute_modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-commute-modunitary"></a>
**Lemma 936** (`modConj_commute_modUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1879)</small>

** `J Δ^{it} = Δ^{it} J`** — the modular conjugation `J` commutes with the modular flow.  Now UNBLOCKED by the covariance `[U_t,D]=0`: since `D = J·T` and `U_t` commutes with both `D` and `T`, `J` commutes with `U_t` on the dense `range T`.  (One of the canonical Tomita–Takesaki relations.)

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\eta) = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta)
$$

*Proof.* By [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt), [`modUnitary_commute_rvdPmQ`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq), [`modUnitary_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt). $\square$

<small>Used by [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`gFunction_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-real-eq), [`gFunction_top_edge_real`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-top-edge-real), [`modConj_deviceVecF_bottom`](/browser/qiqth-modularrelativeentropy#d-qiqth-modconj-devicevecf-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmear"></a>
**Definition 937** (`gaussSmear`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1907)</small>

The **Gaussian-smeared vector** `(n/π)^{1/2}∫ e^{−n t²} V_t η dt` (without the normalisation constant): the construction RvD use to produce a dense set of entire vectors inside the real subspace `K`.

$$
g\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,V\,n\,\eta \;:=\; \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot (V\,t)\,\eta
$$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [`oneParticleBW_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-complete), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete), [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire), and 14 more.</small>

<a id="d-qiqth-standardsubspacemodular-gausssmear-integrable"></a>
**Lemma 938** (`gaussSmear_integrable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1913)</small>

The smeared integrand is Bochner-integrable: dominated by `e^{−n t²}·‖η‖` (a Gaussian), since `V_t` is norm-non-increasing and the orbit is continuous.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{Integrable}\,(\lambda t \mapsto \exp\,(-n \cdot {t}^{2}) \cdot (V\,t)\,\eta)\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gaussSmear_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-mem-k), [`gaussSmear_smul_left`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-smul-left), [`entireVec_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-sub).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmear-mem-k"></a>
**Lemma 939** (`gaussSmear_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1926)</small>

** The smeared vector lands in `K`.**  Since `e^{−n t²} ≥ 0` is a real scalar and `V_t η ∈ K` (real-subspace invariance), the Bochner integral stays in the closed real subspace `K` — because the `ℝ`-linear orthogonal projection `projK` commutes with the integral and fixes the integrand (`ContinuousLinearMap.integral_comp_comm`).  First brick of the entire-vector construction.

$$
0 < n \to \forall \{\eta : H\}, (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (t : \mathbb{R}), (V\,t)\,\eta \in S.\mathrm{cl}) \to \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta \in S.\mathrm{cl}
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`gaussSmear_integrable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-integrable). $\square$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmear-smul-left"></a>
**Lemma 940** (`gaussSmear_smul_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1941)</small>

**The translation property of the smeared vector**: `V_s (gaussSmear V n η) = ∫ e^{−n t²}·V_{s+t} η dt`. Applying the unitary `V_s` (a continuous linear map) commutes with the Bochner integral (`integral_comp_comm`) and, via the group law, shifts the orbit.  After the change of variables `u = s + t` the right side is `∫ e^{−n (u−s)²}·V_u η du`, whose integrand is *entire* in the parameter `s` — this is what makes `gaussSmear V n η` an entire vector for `V` (RvD's key property toward Theorem 3.8).

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to \forall (s : \mathbb{R}), (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta) = \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot (V\,(s + t))\,\eta
$$

*Proof.* By [`gaussSmear_integrable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-integrable). $\square$

<small>Used by [`gaussSmearC_ofReal`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-ofreal).</small>

<a id="d-qiqth-standardsubspacemodular-entirevec"></a>
**Definition 941** (`entireVec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1964)</small>

The **normalised entire vector** `η_n = √(n/π)·gaussSmear V n η` — RvD's dense entire vectors in `K`.

$$
\mathrm{ev}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,V\,n\,\eta \;:=\; \sqrt (n / \pi) \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta
$$

<small>Used by [`gConstancy_of_entireVec_limit`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit), [`gConstancy_eta_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [`entireVec_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-sub), [`entireVec_sub_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-sub-norm-le), [`entireVec_tendsto`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-entirevec-sub"></a>
**Lemma 942** (`entireVec_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1976)</small>

**Mollifier form of the error** `η_n − η = √(n/π)·∫ e^{−n t²}·(V_t η − η) dt`.  Subtracting the normalised constant `η = √(n/π)·∫ e^{−n t²}·η dt` (Gaussian normalisation) from the smeared vector.  This is the setup for the density `η_n → η`: as `n → ∞` the Gaussian concentrates at `t = 0`, where `V_t η → η` by strong continuity.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta - \eta = \sqrt (n / \pi) \cdot \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot ((V\,t)\,\eta - \eta)
$$

*Proof.* By [`gaussSmear`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear), [`gaussSmear_integrable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-integrable). $\square$

<small>Used by [`entireVec_sub_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-sub-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-entirevec-sub-norm-le"></a>
**Lemma 943** (`entireVec_sub_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1998)</small>

**The density error bound** `‖η_n − η‖ ≤ √(n/π)·∫ e^{−n t²}·‖V_t η − η‖ dt`.  Reduces the vector density to a *scalar* Gaussian-mollifier limit of `t ↦ ‖V_t η − η‖`, a bounded continuous function vanishing at `t = 0` (`V_0 η = η` + strong continuity).  From `entireVec_sub` + `norm_integral_le_integral_norm`.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta - \eta\| \le \sqrt (n / \pi) \cdot \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot \|(V\,t)\,\eta - \eta\|
$$

*Proof.* By [`entireVec_sub`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-sub). $\square$

<small>Used by [`entireVec_tendsto`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-gauss-mollifier-change-of-var"></a>
**Lemma 944** (`gauss_mollifier_change_of_var`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2014)</small>

**Change of variables for the Gaussian mollifier** `u = √n·t`: `∫ e^{−u²}·f(u/√n) du = √n·∫ e^{−n t²}·f(t) dt`. The substitution that turns the *concentrating* Gaussian kernel into a *fixed* Gaussian `e^{−u²}` against the rescaled `f(u/√n)`, so the mollifier limit follows from dominated convergence (`f(u/√n) → f(0)`).

$$
0 < n \to \forall (f : \mathbb{R} \to \mathbb{R}), \int (u : \mathbb{R}), \exp\,(-{u}^{2}) \cdot f\,(u / \sqrt n) = \sqrt n \cdot \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot f\,t
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gauss_density_tendsto`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gauss-density-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-gauss-mollifier-integral-tendsto"></a>
**Lemma 945** (`gauss_mollifier_integral_tendsto`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2032)</small>

**The fixed-Gaussian mollifier limit** (dominated convergence): for bounded continuous `f`, `∫ e^{−u²}·f(u/√n) du → ∫ e^{−u²}·f(0) du` as `n → ∞`.  Since `u/√n → 0` and `f` is continuous, `f(u/√n) → f(0)` pointwise, dominated by `e^{−u²}·M`.

$$
\mathrm{Continuous}\,f \to (\forall (t : \mathbb{R}), |f\,t| \le M) \to \mathrm{Tendsto}\,(\lambda n \mapsto \int (u : \mathbb{R}), \exp\,(-{u}^{2}) \cdot f\,(u / \sqrt n))\,\mathrm{atTop}\,(\mathrm{nhds}\,(\int (u : \mathbb{R}), \exp\,(-{u}^{2}) \cdot f\,0))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gauss_density_tendsto`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gauss-density-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-gauss-density-tendsto"></a>
**Lemma 946** (`gauss_density_tendsto`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2052)</small>

**The scalar Gaussian density** `√(n/π)·∫ e^{−n t²}·f(t) dt → f(0)` as `n → ∞`, for bounded continuous `f`.  Combines the change of variables `u = √n·t` (`gauss_mollifier_change_of_var`) with the fixed-Gaussian limit (`gauss_mollifier_integral_tendsto`): `√(n/π)·∫ e^{−n t²}f = √(1/π)·∫ e^{−u²}f(u/√n) → √(1/π)·∫ e^{−u²}f(0) = f(0)`. Applied to `f(t) = ‖V_t η − η‖` (bounded by `2‖η‖`, vanishing at `0`) this lands the RvD entire-vector density `η_n → η`.

$$
\mathrm{Continuous}\,f \to (\forall (t : \mathbb{R}), |f\,t| \le M) \to \mathrm{Tendsto}\,(\lambda n \mapsto \sqrt (n / \pi) \cdot \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot f\,t)\,\mathrm{atTop}\,(\mathrm{nhds}\,(f\,0))
$$

*Proof.* By [`gauss_mollifier_change_of_var`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gauss-mollifier-change-of-var), [`gauss_mollifier_integral_tendsto`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gauss-mollifier-integral-tendsto). $\square$

<small>Used by [`entireVec_tendsto`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-entirevec-tendsto"></a>
**Lemma 947** (`entireVec_tendsto`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2082)</small>

**RvD entire-vector density** `η_n → η`: the normalised entire vectors `η_n = √(n/π)·∫ e^{−n t²}·V_t η dt` converge to `η` as `n → ∞`, for any strongly-continuous one-parameter contraction `V` with `V_0 η = η`. Squeeze: `0 ≤ ‖η_n − η‖ ≤ √(n/π)·∫ e^{−n t²}·‖V_t η − η‖ → ‖V_0 η − η‖ = 0` (`entireVec_sub_norm_le` + `gauss_density_tendsto` on the bounded continuous `t ↦ ‖V_t η − η‖`). With `entireVec_mem_K` this makes the entire vectors a *dense* subset of the real subspace `K` — the totality input for the RvD Theorem 3.8 KMS-uniqueness argument (`hUniq`).

$$
(\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (V\,0)\,\eta = \eta \to \mathrm{Tendsto}\,(\lambda n \mapsto \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta)\,\mathrm{atTop}\,(\mathrm{nhds}\,\eta)
$$

*Proof.* By [`entireVec_sub_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-sub-norm-le), [`gauss_density_tendsto`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gauss-density-tendsto). $\square$

<small>Used by [`gConstancy_of_entireVec_limit`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc"></a>
**Definition 948** (`gaussSmearC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2115)</small>

The **complex orbit** of the smeared vector: `G(z) = ∫ e^{−n(u−z)²}·V_u η du`, an `H`-valued function of complex time `z`.  On the real axis it is `V_s(gaussSmear V n η)`; it is entire in `z`.

$$
g\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,V\,n\,\eta\,z \;:=\; \int (u : \mathbb{R}), \exp\,(-n \cdot {(u - z)}^{2}) \cdot (V\,u)\,\eta
$$

<small>Used by [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire), [`gFunction_top_edge_real_all`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [`gConstancy_entire_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), and 17 more.</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc-integrable"></a>
**Lemma 949** (`gaussSmearC_integrable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2121)</small>

The complex-orbit integrand is Bochner-integrable for every fixed `z`: dominated by the shifted Gaussian `e^{n·(Im z)²}·e^{−n(u−Re z)²}·‖η‖` (since `Re(−n(u−z)²) = −n(u−Re z)² + n(Im z)²`).

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \forall (z : \mathbb{C}), \mathrm{Integrable}\,(\lambda u \mapsto \exp\,(-n \cdot {(u - z)}^{2}) \cdot (V\,u)\,\eta)\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`hasDerivAt_gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-gausssmearc), [`gaussSmearC_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc-ofreal"></a>
**Lemma 950** (`gaussSmearC_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2143)</small>

**Real-axis agreement** `gaussSmearC V n η ↑s = V_s(gaussSmear V n η)`.  On the real axis the complex orbit reduces to the genuine unitary-group orbit of the smeared vector: the complex Gaussian kernel `e^{−n(u−s)²}` collapses to its real value and, after the translation `u = s + t`, equals `∫ e^{−n t²}·V_{s+t} η dt = V_s(gaussSmear V n η)` (`gaussSmear_smul_left`).  This anchors the entire extension `gaussSmearC` to the actual flow `V`.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to \forall (s : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,s = (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)
$$

*Proof.* By [`gaussSmear_smul_left`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-smul-left). $\square$

<small>Used by [`gFunction_bottom_real_of_faithful_kms`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [`gFunction_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-real-eq).</small>

<a id="d-qiqth-standardsubspacemodular-integrable-abs-add-mul-exp-neg-mul-sq"></a>
**Lemma 951** (`integrable_abs_add_mul_exp_neg_mul_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2166)</small>

**Linear×Gaussian integrability** `Integrable (u ↦ (|u| + c)·e^{−b u²})` for `b > 0` — a degree-one polynomial against a Gaussian.  `|u|·e^{−b u²}` is integrable (norm of `u·e^{−b u²}`, `integrable_mul_exp_neg_mul_sq`) and `c·e^{−b u²}` is integrable; their sum dominates the derivative of the complex orbit (the `‖2n(u−z)·e^{−n(u−z)²}‖` bound), so this is the integrable dominating function for the holomorphy of `gaussSmearC`.

$$
0 < b \to \mathrm{Integrable}\,(\lambda u \mapsto (|u| + c) \cdot \exp\,(-b \cdot {u}^{2}))\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`hasDerivAt_gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-gausssmearc).</small>

<a id="d-qiqth-standardsubspacemodular-hasderivat-gausssmearc"></a>
**Lemma 952** (`hasDerivAt_gaussSmearC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2184)</small>

**The complex orbit is entire**: `gaussSmearC V n η` is complex-differentiable at every `z₀`, with `HasDerivAt` given by differentiation under the integral sign, `(gaussSmearC V n η)'(z₀) = ∫ (2n(u−z₀)·e^{−n(u−z₀)²})·V_u η du`.  The derivative integrand is dominated, uniformly for `z` in a unit ball around `z₀`, by the integrable linear×Gaussian `2n·C₁·‖η‖·(|u−Re z₀|+|Im z₀|+2)·e^{−(n/2)(u−Re z₀)²}` — using `Re(−n(u−z)²) = −n(u−Re z)²+n(Im z)²`, the AM-GM bound `(u−Re z)² ≥ (u−Re z₀)²/2 − 2`, and `|Im z| ≤ |Im z₀|+1`.  This entirety is what makes the KMS correlation `z ↦ ⟨gaussSmearC … z, ·⟩` holomorphic on the strip (RvD Theorem 3.8).

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \forall (z_{0} : \mathbb{C}), ({\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta})'({z_{0}})={\int (u : \mathbb{R}), (2 \cdot n \cdot (u - z_{0}) \cdot \exp\,(-n \cdot {(u - z_{0})}^{2})) \cdot (V\,u)\,\eta}
$$

*Proof.* By [`gaussSmearC_integrable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-integrable), [`integrable_abs_add_mul_exp_neg_mul_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-integrable-abs-add-mul-exp-neg-mul-sq). $\square$

<small>Used by [`differentiable_gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-differentiable-gausssmearc).</small>

<a id="d-qiqth-standardsubspacemodular-differentiable-gausssmearc"></a>
**Lemma 953** (`differentiable_gaussSmearC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2313)</small>

**The complex orbit is entire.**  `gaussSmearC V n η` is complex-differentiable on all of `ℂ` (`HasDerivAt` at every point, `hasDerivAt_gaussSmearC`).  Composed with a continuous-linear functional this gives the entire KMS correlation needed for the strip-uniqueness step of RvD Theorem 3.8.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{Differentiable}\,\mathbb{C}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta)
$$

*Proof.* By [`hasDerivAt_gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-gausssmearc). $\square$

<small>Used by [`differentiableOn_gFunction`](/browser/qiqth-modularrelativeentropy#d-qiqth-differentiableon-gfunction), [`diffContOnCl_gFunction`](/browser/qiqth-modularrelativeentropy#d-qiqth-diffcontoncl-gfunction), [`differentiable_corrC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-differentiable-corrc).</small>

<a id="d-qiqth-standardsubspacemodular-corrc"></a>
**Definition 954** (`corrC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2321)</small>

The **KMS two-point correlation** of two entire vectors, `corrC ξ V n η z = ⟨ξ, gaussSmearC V n η z⟩` — the analytic object the strip-uniqueness step compares between two candidate modular flows.

$$
\mathrm{corrC}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\xi\,V\,n\,\eta\,z \;:=\; ((\mathrm{innerSL}\,\mathbb{C})\,\xi)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)
$$

<small>Used by [`corrC_bdd_halfStrip`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-corrc-bdd-halfstrip), [`gFunction_bottom_real_of_kms_match`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [`gFunction_bottom_real_of_faithful_kms`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [`differentiable_corrC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-differentiable-corrc), [`corrC_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-corrc-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-differentiable-corrc"></a>
**Lemma 955** (`differentiable_corrC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2326)</small>

**The KMS correlation is entire**: `z ↦ ⟨ξ, gaussSmearC V n η z⟩` is complex-differentiable on all of `ℂ`, being the continuous-linear functional `innerSL ℂ ξ` composed with the entire orbit (`differentiable_gaussSmearC`).

$$
0 < n \to \forall (\eta \xi : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{Differentiable}\,\mathbb{C}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-corrc}{\mathrm{corrC}}\,\xi\,V\,n\,\eta)
$$

*Proof.* By [`gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc), [`differentiable_gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-differentiable-gausssmearc). $\square$

<small>Used by [`gFunction_bottom_real_of_kms_match`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc-zero"></a>
**Lemma 956** (`gaussSmearC_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2343)</small>

**The complex orbit at `0` is the smeared vector**: `gaussSmearC V n η 0 = gaussSmear V n η` (`h(0)=η_n`). At `z = 0` the complex Gaussian `e^{−n(u−0)²}` collapses to the real `e^{−n u²}`.  Used to evaluate the KMS correlation at the origin: `g(0) = ⟨w, η_n⟩`, the comparison point in RvD Theorem 3.8.

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,0 = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gFunction_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-zero).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc-norm-le"></a>
**Lemma 957** (`gaussSmearC_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2391)</small>

**Gaussian bound on the complex orbit**: `‖gaussSmearC V n η z‖ ≤ e^{n(Im z)²}·‖η‖·√(π/n)`. The complex Gaussian `e^{−n(u−z)²}` has modulus `e^{−n(u−Re z)²+n(Im z)²}`, so the orbit's norm is at most `e^{n(Im z)²}·‖η‖·∫ e^{−n(u−Re z)²} = e^{n(Im z)²}·‖η‖·√(π/n)`.  On the closed KMS strip `0 ≤ Im z ≤ 1` this gives a *uniform* bound `e^{n}·‖η‖·√(π/n)` — the boundedness hypothesis the strip-uniqueness step requires.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \forall (z : \mathbb{C}), \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z\| \le \exp\,(n \cdot {z.\mathrm{im}}^{2}) \cdot \|\eta\| \cdot \sqrt (\pi / n)
$$

*Proof.* By [`gaussSmearC_integrable`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-integrable). $\square$

<small>Used by [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [`corrC_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-corrc-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-corrc-norm-le"></a>
**Lemma 958** (`corrC_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2421)</small>

**Gaussian bound on the KMS correlation**: `|corrC ξ V n η z| ≤ ‖ξ‖·e^{n(Im z)²}·‖η‖·√(π/n)`. Cauchy–Schwarz (`innerSL` norm `≤ ‖ξ‖`) over `gaussSmearC_norm_le`.  On the closed strip `0 ≤ Im z ≤ 1` the correlation is uniformly bounded — the `bound` hypothesis of `StripUniqueness.eqOn_of_bdd_holomorphic_strip`.

$$
0 < n \to \forall (\eta \xi : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \forall (z : \mathbb{C}), \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-corrc}{\mathrm{corrC}}\,\xi\,V\,n\,\eta\,z\| \le \|\xi\| \cdot (\exp\,(n \cdot {z.\mathrm{im}}^{2}) \cdot \|\eta\| \cdot \sqrt (\pi / n))
$$

*Proof.* By [`gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc), [`gaussSmearC_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-norm-le). $\square$

<small>Used by [`corrC_bdd_halfStrip`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-corrc-bdd-halfstrip).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc"></a>
**Definition 959** (`modCharC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2440)</small>

The **complexified modular character** `u_z(r) = exp(i·z·log((2−r)/r))` on `(0,2)` (and `1` outside) — the analytic continuation of `modChar` to complex time `z`.

$$
\chi_{\mathrm{mod}}\,z \;:=\; (\mathrm{Ioo}\,0\,2).\mathrm{piecewise}\,(\lambda r \mapsto \exp\,(i \cdot z \cdot (\log\,((2 - r) / r))))\,\lambda x \mapsto 1
$$

<small>Used by [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`devCharDeriv_norm_le_slab`](/browser/qiqth-modularrelativeentropy#d-qiqth-devcharderiv-norm-le-slab), [`devChar_slope_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devchar-slope-norm-le), [`measurable_modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-modcharc), [`modCharC_of_mem`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-of-mem), [`modCharC_ofReal`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-ofreal), [`modCharC_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-add), [`hasDerivAt_modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-modcharc), and 12 more.</small>

<a id="d-qiqth-standardsubspacemodular-measurable-modcharc"></a>
**Lemma 960** (`measurable_modCharC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2447)</small>

The complexified character is Borel measurable (in `r`, for fixed `z`).

$$
\mathrm{Measurable}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`measurable_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-devchar).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-of-mem"></a>
**Lemma 961** (`modCharC_of_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2455)</small>

On `(0,2)` the complexified character is the bare exponential.

$$
r \in \mathrm{Ioo}\,0\,2 \to \forall (z : \mathbb{C}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r = \exp\,(i \cdot z \cdot (\log\,((2 - r) / r)))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modCharC_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-add), [`hasDerivAt_modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-modcharc), [`modCharC_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-norm), [`modCharC_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-zero), [`devChar_neg_half_I`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-neg-half-i).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-ofreal"></a>
**Lemma 962** (`modCharC_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2460)</small>

On the real axis the complexification recovers `modChar`.

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,(t)\,r = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`devChar_ofReal`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-ofreal).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-add"></a>
**Lemma 963** (`modCharC_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2463)</small>

**The complexified modular character is an exponential homomorphism in `z`**: `u_{z+w}(r) = u_z(r)·u_w(r)`. On `(0,2)` it is `exp(i(z+w)L) = exp(izL)·exp(iwL)` (`Complex.exp_add`, `L = log((2−r)/r)`); off `(0,2)` both sides are `1`.  This drives the device's `t`-translation `d_{(t:ℂ)+z}(r) = u_t(r)·d_z(r)` — e.g. the bottom-edge factorization `deviceOpC(t−i/2) = Δ^{it}·deviceOpC(−i/2)`.

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,(z + w)\,r = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,w\,r
$$

*Proof.* By [`modCharC_of_mem`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Used by [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq).</small>

<a id="d-qiqth-standardsubspacemodular-hasderivat-modcharc"></a>
**Lemma 964** (`hasDerivAt_modCharC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2506)</small>

**The complex `z`-derivative of the modular character**: `d/dz u_z(r) = i·log((2−r)/r)·u_z(r)`.  This is the pointwise derivative that, integrated against the spectral measure and dominated in the regular regime, gives holomorphy of the strip extension `z ↦ ∫ u_z dμ` under the integral sign.

$$
r \in \mathrm{Ioo}\,0\,2 \to \forall (z : \mathbb{C}), ({\lambda z \mapsto \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r})'({z})={i \cdot (\log\,((2 - r) / r)) \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r}
$$

*Proof.* By [`modCharC_of_mem`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Used by [`hasDerivAt_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-devchar).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-norm"></a>
**Lemma 965** (`modCharC_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2539)</small>

**The exact modulus of the complexified character on the strip**: `‖u_z(r)‖ = exp(−Im(z)·log((2−r)/r))`. On the real axis (`Im z = 0`) this is `1`; for `Im z ∈ (0,1]` it is the modular weight raised to `−Im z`. This is the seed of the *boundedness* of the strip extension of `⟪ξ, Δ^{it} ξ⟫` in the regular spectral regime (`σ(R) ⊆ [a, 2−a]`), where the exponent stays bounded.

$$
r \in \mathrm{Ioo}\,0\,2 \to \forall (z : \mathbb{C}), \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r\| = \exp\,(-z.\mathrm{im} \cdot \log\,((2 - r) / r))
$$

*Proof.* By [`modCharC_of_mem`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Used by [`devChar_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-le), [`devChar_norm_eq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-eq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar"></a>
**Definition 966** (`devChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2594)</small>

The **device character** `d_z(r) = ((2−r)/r)^{iz}·√r = modCharC z r · √r` (RvD Prop 3.7).

$$
\chi_{\mathrm{dev}}\,z\,r \;:=\; \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r \cdot \sqrt r
$$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`devSpecReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal), [`devSpecReal_measurable`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-measurable), [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), [`deviceOpC_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-norm-le), [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`devCharDeriv_norm_le_slab`](/browser/qiqth-modularrelativeentropy#d-qiqth-devcharderiv-norm-le-slab), and 20 more.</small>

<a id="d-qiqth-standardsubspacemodular-measurable-devchar"></a>
**Lemma 967** (`measurable_devChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2597)</small>

The device character is Borel measurable in `r` (for fixed `z`).

$$
\mathrm{Measurable}\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z)
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`measurable_modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-measurable-modcharc). $\square$

<small>Used by [`devSpecReal_measurable`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-measurable), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`tendsto_integral_devChar_remainder_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-remainder-sq), [`deviceOpC_sub`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-sub), [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq), [`deviceOpC_diff_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-diff-normsq), [`tendsto_integral_devChar_diff_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-diff-sq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-ofreal"></a>
**Lemma 968** (`devChar_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2602)</small>

On the real axis the device character is `modChar t · √r` (the `Δ^{it}·√R` part of the continuation).

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,(t)\,r = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r \cdot \sqrt r
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`modCharC_ofReal`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-ofreal). $\square$

<small>Used by [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-zero"></a>
**Lemma 969** (`modCharC_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2611)</small>

The modular character at `z = 0` is `1` (`exp(0) = 1` on `(0,2)`, `1` off it).

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,0\,r = 1
$$

*Proof.* By [`modCharC_of_mem`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Used by [`devChar_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-zero).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-zero"></a>
**Lemma 970** (`devChar_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2617)</small>

**Device character at `z = 0` is `√r`** (`= R^{1/2}` at the operator level): `d_0(r) = √r`.  The device interpolation starts at `√R` (so `deviceOpC 0 ζ = R^{1/2}ζ = ξ`, giving the g-function value `g(0) = ⟨η, Jξ⟩`).

$$
\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,0\,r = \sqrt r
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`modCharC_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-zero). $\square$

<small>Used by [`deviceOpReal_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-zero), [`deviceOpReal_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-neg-half-i"></a>
**Lemma 971** (`devChar_neg_half_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2623)</small>

**Device character at the bottom edge `z = −i/2` is `√(2−r)`** (`= (2−R)^{1/2}` at the operator level): `d_{−i/2}(r) = √(2−r)` for `r ∈ (0,2)`.  The device interpolation ends at `(2−R)^{1/2}` (so `deviceOpC (−i/2) ζ = (2−R)^{1/2}ζ = Jξ`, the half-modular-shift `Δ^{1/2} = J` on `𝒦`).  Computed from `Complex.exp(I·(−I/2)·log((2−r)/r))·√r = √((2−r)/r)·√r = √(2−r)`.

$$
r \in \mathrm{Ioo}\,0\,2 \to \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,(-(i / 2))\,r = \sqrt (2 - r)
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`modCharC_of_mem`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-norm-le"></a>
**Lemma 972** (`devChar_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2643)</small>

**The device character is bounded by `√2` on the half-strip** `{−1/2 ≤ Im z ≤ 0}`, uniformly over the spectrum `r ∈ (0,2)` — with NO regular-window assumption (RvD Lemma 3.6 / Prop 3.7).  Writing `b = −Im z ∈ [0, 1/2]`, `‖d_z(r)‖ = exp(b·log((2−r)/r))·√r`; in log form `b·log(2−r) + (1/2 − b)·log r ≤ (1/2)·log 2` since `log(2−r), log r ≤ log 2` and the coefficients `b, 1/2 − b` are nonnegative and sum to `1/2`.  The `√r` factor (the `+1/2` exponent of `R^{−iz+1/2}`) is exactly what cancels the `r^{−iz}` blow-up, so the device continuation is *bounded*-holomorphic on the half-strip for ANY standard subspace — the U-side boundedness the strip-uniqueness comparison consumes.

$$
z.\mathrm{im} \le 0 \to -(1/2) \le z.\mathrm{im} \to \forall \{r : \mathbb{R}\}, r \in \mathrm{Ioo}\,0\,2 \to \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r\| \le \sqrt 2
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`modCharC_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-norm). $\square$

<small>Used by [`devChar_norm_le_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-le-icc).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-norm-le-icc"></a>
**Lemma 973** (`devChar_norm_le_Icc`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2666)</small>

**The device character is bounded by `√2` on the CLOSED interval `[0,2]`** (the spectrum-ready strengthening of `devChar_norm_le`).  On the open interior `(0,2)` this is `devChar_norm_le`; at the endpoints `r ∈ {0,2}` the modular character collapses to `1` (`r ∉ (0,2)`), so `d_z(r) = √r` with `‖d_z(r)‖ = √r ≤ √2`.  In particular `d_z(0) = 0` (the `√r` factor kills the `r → 0` singularity outright).  Since `0 ≤ R ≤ 2`, the spectrum of `R` lies in `[0,2]`, so this is the bound the `borelFC` construction of the operator device vector `(2−R)^{iz}R^{−iz+1/2}ζ = d_z(R)ζ` consumes.

$$
z.\mathrm{im} \le 0 \to -(1/2) \le z.\mathrm{im} \to \forall \{r : \mathbb{R}\}, r \in \mathrm{Icc}\,0\,2 \to \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r\| \le \sqrt 2
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`devChar_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-le). $\square$

<small>Used by [`devSpecReal_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-norm-le), [`deviceOpC_bottomEdge_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-bottomedge-eq), [`deviceOpC_sub`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-sub), [`deviceOpC_slope_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-slope-normsq), [`deviceOpC_diff_normSq`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc-diff-normsq), [`tendsto_integral_devChar_diff_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-diff-sq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-norm-eq"></a>
**Lemma 974** (`devChar_norm_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2681)</small>

**The device-character modulus in `rpow` form**: `‖d_z(r)‖ = (2−r)^{−Im z}·r^{1/2+Im z}` on `(0,2)`. From `‖d_z(r)‖ = exp(−Im z·log((2−r)/r))·√r` (`modCharC_norm`), converting `exp(c·log x) = x^c`, `((2−r)/r)^c = (2−r)^c·r^{−c}`, and `r^{−Im z}·r^{1/2} = r^{1/2+Im z}`.  This exposes the two `rpow`-with-nonnegative-exponent factors (`−Im z ∈ (0,1/2)`, `1/2+Im z ∈ (0,1/2)` on the open half-strip) that `rpow_mul_abs_log_le` pairs against the `log((2−r)/r)` of the derivative.

$$
r \in \mathrm{Ioo}\,0\,2 \to \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r\| = {(2 - r)}^{(-z.\mathrm{im})} \cdot {r}^{(1/2 + z.\mathrm{im})}
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`modCharC_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc-norm). $\square$

<small>Used by [`devChar_deriv_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-rpow-mul-abs-log-le"></a>
**Lemma 975** (`rpow_mul_abs_log_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2698)</small>

**Uniform `x^δ·|log x|` bound** (the heart of the device-derivative domination): for `x ∈ (0,2]` and `δ ∈ (0,1]`, `x^δ·|log x| ≤ 2/δ + log 2`.  On `(0,1]` use `log x⁻¹ ≤ (x⁻¹)^{δ/2}/(δ/2)` (`Real.log_le_rpow_div`) so `x^δ·|log x| ≤ 2·x^{δ/2}/δ ≤ 2/δ`; on `[1,2]` use `log x ≤ log 2`, `x^δ ≤ 2`.  This is the polynomial-beats-log estimate that tames the `log((2−r)/r)` factor of the device `z`-derivative against the `r^{1/2±·}` factors of `‖d_z‖`, giving the integrable constant dominator.

$$
0 < x \to x \le 2 \to 0 < \delta \to \delta \le 1 \to {x}^{\delta} \cdot |\log\,x| \le 2 / \delta + \log\,2
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`devChar_deriv_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-deriv-norm-le"></a>
**Lemma 976** (`devChar_deriv_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2740)</small>

**Uniform domination of the device `z`-derivative on a half-strip slab** (the assembled dominator for holomorphy of `devCorrExt`).  For `z` with `−Im z = b ∈ [β₀, β₁] ⊂ (0, 1/2)` and `r ∈ (0,2)`, the derivative coefficient `|log((2−r)/r)|·‖d_z(r)‖` is bounded by the constant `√2·(2/β₀ + log2) + √2·(2/(1/2−β₁) + log2)`, uniformly in `r` and over the slab.  Proof: write `‖d_z(r)‖ = (2−r)^b·r^{1/2−b}` (`devChar_norm_eq`), split `|log((2−r)/r)| ≤ |log(2−r)| + |log r|`, and apply `rpow_mul_abs_log_le` to `(2−r)^b·|log(2−r)|` and `r^{1/2−b}·|log r|`, bounding the complementary `rpow` factors by `√2`.  This is the integrable constant dominator (`μ` finite) that `hasDerivAt_integral_of_dominated_loc_of_deriv_le` consumes — with NO regular-window assumption.

$$
0 < \beta_{0} \to \beta_{1} < 1/2 \to z.\mathrm{im} \le -\beta_{0} \to -\beta_{1} \le z.\mathrm{im} \to \forall \{r : \mathbb{R}\}, r \in \mathrm{Ioo}\,0\,2 \to |\log\,((2 - r) / r)| \cdot \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r\| \le \sqrt 2 \cdot (2 / \beta_{0} + \log\,2) + \sqrt 2 \cdot (2 / (1/2 - \beta_{1}) + \log\,2)
$$

*Proof.* By [`devChar_norm_eq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-norm-eq), [`rpow_mul_abs_log_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rpow-mul-abs-log-le). $\square$

<small>Used by [`devCharDeriv_norm_le_slab`](/browser/qiqth-modularrelativeentropy#d-qiqth-devcharderiv-norm-le-slab), [`devChar_slope_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devchar-slope-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-hasderivat-devchar"></a>
**Lemma 977** (`hasDerivAt_devChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2800)</small>

**The complex `z`-derivative of the device character**: `d/dz d_z(r) = i·log((2−r)/r)·d_z(r)` (same modular frequency as `modCharC`, since the `√r` factor is `z`-constant).  This is the pointwise derivative that, integrated against the spectral measure and dominated on the *open* half-strip (where `−Im z ∈ (0,1/2)`, so the `r^{1/2+Im z}` factor of `‖d_z‖` keeps `log·d_z` bounded), gives holomorphy of `devCorrExt`.

$$
r \in \mathrm{Ioo}\,0\,2 \to \forall (z : \mathbb{C}), ({\lambda z \mapsto \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r})'({z})={i \cdot (\log\,((2 - r) / r)) \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r}
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`hasDerivAt_modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-modcharc). $\square$

<small>Used by [`hasDerivAt_devChar_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc).</small>

<a id="d-qiqth-standardsubspacemodular-hasderivat-devchar-icc"></a>
**Lemma 978** (`hasDerivAt_devChar_Icc`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2811)</small>

**The device-character `z`-derivative on the CLOSED interval `[0,2]`** (covering the spectrum endpoints). On `(0,2)` this is `hasDerivAt_devChar`.  At `r ∈ {0,2}` the modular character collapses to `1`, so `d_z(r) = √r` is `z`-constant (derivative `0`), and the formula's coefficient also vanishes because `(2−r)/r = 0` there (`2/0 = 0` at `r=0`, `0/2 = 0` at `r=2`) gives `log 0 = 0`.  So the same `HasDerivAt` statement holds across `[0,2]` — the form the differentiate-under-the-spectral-integral holomorphy of `devCorrExt` needs (the spectrum `σ(R) ⊆ [0,2]` may include the endpoints).

$$
r \in \mathrm{Icc}\,0\,2 \to \forall (z : \mathbb{C}), ({\lambda z \mapsto \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r})'({z})={i \cdot (\log\,((2 - r) / r)) \cdot \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r}
$$

*Proof.* By [`modCharC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modcharc), [`hasDerivAt_devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-hasderivat-devchar). $\square$

<small>Used by [`devChar_slope_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devchar-slope-norm-le), [`tendsto_devChar_slope`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-devchar-slope), [`tendsto_integral_devChar_diff_sq`](/browser/qiqth-modularrelativeentropy#d-qiqth-tendsto-integral-devchar-diff-sq).</small>

---
<small>[← all sections](/browser) · [← StandardSubspaceModular](/browser/qiqth-standardsubspacemodular) · [StripUniqueness →](/browser/qiqth-stripuniqueness) </small>