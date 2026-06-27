---
layout: ../../layouts/Deep.astro
title: QIQTH.Curvature
eyebrow: Curvature · section of the QIQT-H book
description: QIQTH.Curvature — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← CoreNoCollapse](/browser/qiqth-corenocollapse) · [DifferentialAreaLaw →](/browser/qiqth-differentialarealaw) </small>

<small>Curvature · entries 15–70 of 1000</small>

<a id="d-qiqth-curvature-point"></a>
**Definition 15** (`Point`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L26)</small>

A point of the coordinate chart.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \;:=\; \mathrm{Fin}\,n \to \mathbb{R}
$$

<small>Used by [`contDiff_pd`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-contdiff-pd), [`christoffel_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-christoffel-contdiff), [`riemann_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-riemann-contdiff), [`ricci_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-ricci-contdiff), [`scalarCurv_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-scalarcurv-contdiff), [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), and 137 more.</small>

<a id="d-qiqth-curvature-pd"></a>
**Definition 16** (`pd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L29)</small>

Partial derivative `∂ᵢ f` of a scalar field, along the `i`-th coordinate.

$$
\mathrm{pd}\,n\,f\,i\,x \;:=\; \mathrm{D}\,(\lambda t \mapsto f\,(\mathrm{update}\,x\,i\,t))\,(x\,i)
$$

<small>Used by [`contDiff_pd`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-contdiff-pd), [`christoffel_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-christoffel-contdiff), [`riemann_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-riemann-contdiff), [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), [`pd_sub`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sub), [`pd_const_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const-mul), [`pd_const`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), and 83 more.</small>

<a id="d-qiqth-curvature-pdiffat"></a>
**Definition 17** (`PdiffAt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L33)</small>

Partial differentiability of `f` at `x` along coordinate `i` (the analytic hypothesis for the `pd` algebra below).

$$
\mathrm{PdiffAt}\,n\,f\,i\,x \;:=\; \mathrm{DifferentiableAt}\,\mathbb{R}\,(\lambda t \mapsto f\,(\mathrm{update}\,x\,i\,t))\,(x\,i)
$$

<small>Used by [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), [`pd_sub`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sub), [`pd_const_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const-mul), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`sub`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sub), [`add`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-add), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), and 40 more.</small>

<a id="d-qiqth-curvature-pd-add"></a>
**Lemma 18** (`pd_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L38)</small>

`∂ᵢ(f+g) = ∂ᵢf + ∂ᵢg`.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto f\,y + g\,y})({x})} = \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({f})({x})} + \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({g})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm), [`div02_add`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-add), [`einstein_field_equation`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation), [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved), [`pd_covDerivVec`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-pd-covderivvec).</small>

<a id="d-qiqth-curvature-pd-sub"></a>
**Lemma 19** (`pd_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L44)</small>

`∂ᵢ(f−g) = ∂ᵢf − ∂ᵢg`.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto f\,y - g\,y})({x})} = \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({f})({x})} - \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({g})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`second_bianchi_deriv_part`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-deriv-part), [`pd_riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-pd-riemannquad).</small>

<a id="d-qiqth-curvature-pd-const-mul"></a>
**Lemma 20** (`pd_const_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L50)</small>

`∂ᵢ(c·f) = c·∂ᵢf`.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto c \cdot f\,y})({x})} = c \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({f})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`covDerivRiem_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-antisymm), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci), [`einstein_field_equation`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation), [`div02_kgStress_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-eq), [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved), [`div02_const_smul`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-const-smul).</small>

<a id="d-qiqth-curvature-pd-const"></a>
**Lemma 21** (`pd_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L56)</small>

`∂ᵢ(const) = 0`.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda x \mapsto c})({x})} = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`pd_metric_inv_identity`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-metric-inv-identity), [`geodesic_divergence_leibniz`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-geodesic-divergence-leibniz), [`pd_expansion_zero_of_covConst`](/browser/qiqth-raychaudhuricongruence#d-qiqth-curvature-pd-expansion-zero-of-covconst).</small>

<a id="d-qiqth-curvature-pdiffat-of-contdiff"></a>
**Lemma 22** (`PdiffAt_of_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L60)</small>

A smooth field is partially differentiable in every direction at every point.

$$
({f})\in C^{\infty} \to \forall (i : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`pd_riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-pd-riemannquad), [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann), [`lowered_riemann_eq`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-eq), [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci), and 6 more.</small>

<a id="d-qiqth-curvature-pdiffat-mul"></a>
**Lemma 23** (`mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L67)</small>

A product of partially-differentiable fields is partially differentiable.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto f\,y \cdot g\,y)\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`pd_riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-pd-riemannquad), [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann), [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`lowered_riemann_eq`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-eq), [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem), and 11 more.</small>

<a id="d-qiqth-curvature-pdiffat-sub"></a>
**Lemma 24** (`sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L72)</small>

Difference of partially-differentiable fields.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto f\,y - g\,y)\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`pd_riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-pd-riemannquad), [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann), [`kg_conserv_of_contDiff`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv-of-contdiff).</small>

<a id="d-qiqth-curvature-pdiffat-add"></a>
**Lemma 25** (`add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L77)</small>

Sum of partially-differentiable fields.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto f\,y + g\,y)\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann), [`kg_conserv_of_contDiff`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv-of-contdiff), [`covDeriv2Vec_trace`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec-trace), [`geodesic_divergence_leibniz`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-pdiffat-sum"></a>
**Lemma 26** (`PdiffAt_sum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L82)</small>

A finite sum of partially-differentiable fields is partially differentiable.

$$
(\forall k\in s, \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(F\,k)\,i\,x) \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \sum_{k s} F\,k\,y)\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann), [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm), [`PdiffAt_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-ricci), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci), [`einstein_field_equation_real`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real), and 5 more.</small>

<a id="d-qiqth-curvature-pd-sum"></a>
**Lemma 27** (`pd_sum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L87)</small>

`∂ᵢ` commutes with finite sums: `∂ᵢ(∑ₖ fₖ) = ∑ₖ ∂ᵢfₖ`.

$$
(\forall k\in s, \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(F\,k)\,i\,x) \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto \sum_{k s} F\,k\,y})({x})} = \sum_{k s} \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({F\,k})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`pd_riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-pd-riemannquad), [`covDerivRiem_contract`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`lowered_riemann_eq`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-eq), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci), [`pd_metric_inv_identity`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-metric-inv-identity), and 4 more.</small>

<a id="d-qiqth-curvature-pd-mul"></a>
**Lemma 28** (`pd_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L94)</small>

**Leibniz rule** `∂ᵢ(f·g) = (∂ᵢf)·g + f·(∂ᵢg)`.

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto f\,y \cdot g\,y})({x})} = \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({f})({x})} \cdot g\,x + f\,x \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({g})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`pd_riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-pd-riemannquad), [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`lowered_riemann_eq`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-eq), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci), [`div02_scalar_metric`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-scalar-metric), [`covDeriv02_kgKinetic`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-covderiv02-kgkinetic), and 5 more.</small>

<a id="d-qiqth-curvature-pd-eq-fderiv"></a>
**Lemma 29** (`pd_eq_fderiv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L102)</small>

**`pd` as a directional `fderiv`**: `∂ᵢ g (x) = Dg(x)[eᵢ]` for `g` differentiable at `x`. The bridge from the coordinate partial derivative to the Fréchet derivative (chain rule through `update`).

$$
\mathrm{DifferentiableAt}\,\mathbb{R}\,g\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({g})({x})} = (\mathrm{fderiv}\,\mathbb{R}\,g\,x)\,(\mathrm{single}\,i\,1)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`contDiff_pd`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-contdiff-pd), [`pd_pd_eq`](/browser/qiqth-curvature#d-qiqth-curvature-pd-pd-eq), [`PdiffAt_pd`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-pd), [`second_bianchi_deriv_part`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-deriv-part), [`const_of_pd_zero`](/browser/qiqth-curvature#d-qiqth-curvature-const-of-pd-zero).</small>

<a id="d-qiqth-curvature-pd-pd-eq"></a>
**Lemma 30** (`pd_pd_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L112)</small>

A mixed second partial equals the second Fréchet derivative bilinear form on the basis vectors.

$$
({f})\in C^{\infty} \to \partial_{{i}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{j}}({f})({y})}})({x}) = ((\mathrm{fderiv}\,\mathbb{R}\,(\mathrm{fderiv}\,\mathbb{R}\,f)\,x)\,(\mathrm{single}\,i\,1))\,(\mathrm{single}\,j\,1)
$$

*Proof.* By [`pd_eq_fderiv`](/browser/qiqth-curvature#d-qiqth-curvature-pd-eq-fderiv). $\square$

<small>Used by [`pd_comm`](/browser/qiqth-curvature#d-qiqth-curvature-pd-comm).</small>

<a id="d-qiqth-curvature-pd-comm"></a>
**Lemma 31** (`pd_comm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L125)</small>

**Schwarz: mixed partial derivatives commute** `∂ᵢ∂ⱼ f = ∂ⱼ∂ᵢ f` for smooth `f`. The analytic keystone for the second Bianchi identity.

$$
({f})\in C^{\infty} \to \partial_{{i}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{j}}({f})({y})}})({x}) = \partial_{{j}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({f})({y})}})({x})
$$

*Proof.* By [`pd_pd_eq`](/browser/qiqth-curvature#d-qiqth-curvature-pd-pd-eq). $\square$

<small>Used by [`second_bianchi_deriv_part`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-deriv-part), [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm), [`hessGrad_partial_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hessgrad-partial-eq), [`ricci_identity`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-ricci-identity).</small>

<a id="d-qiqth-curvature-pdiffat-pd"></a>
**Lemma 32** (`PdiffAt_pd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L132)</small>

The partial derivative `∂_d f` of a smooth field is itself partially differentiable in any direction (`f ∈ C^∞` ⇒ `∂_d f ∈ C^∞` ⇒ differentiable).

$$
({f})\in C^{\infty} \to \forall (d e : \mathrm{Fin}\,n) (z : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{d}}({f})({y})})\,e\,z
$$

*Proof.* By [`pd_eq_fderiv`](/browser/qiqth-curvature#d-qiqth-curvature-pd-eq-fderiv). $\square$

<small>Used by [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann), [`kg_conserv_of_contDiff`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv-of-contdiff), [`pd_covDerivVec`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-pd-covderivvec), [`covDeriv2Vec_trace`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec-trace), [`geodesic_divergence_leibniz`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-christoffel"></a>
**Definition 33** (`christoffel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L147)</small>

**Christoffel symbols** `Γ^μ_{νρ} = ½ g^{μα}(∂_ν g_{αρ} + ∂_ρ g_{αν} − ∂_α g_{νρ})`.


<small>Used by [`christoffel_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-christoffel-contdiff), [`riemann_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-riemann-contdiff), [`christoffel_symm`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel-symm), [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann), [`riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-riemann-antisymm), [`covDerivVec`](/browser/qiqth-curvature#d-qiqth-curvature-covderivvec), [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`covDeriv20`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv20), and 53 more.</small>

<a id="d-qiqth-curvature-christoffel-symm"></a>
**Lemma 34** (`christoffel_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L153)</small>

**Christoffel symbols are symmetric in their lower indices** (torsion-freeness), for a symmetric metric. Immediate from the definition — no analytic input.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (\mu \nu \rho : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\mu}}_{{\nu}{\rho}}({x})} = \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\mu}}_{{\rho}{\nu}}({x})}
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd). $\square$

<small>Used by [`riemann_first_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-riemann-first-bianchi), [`bianchi_extra_terms`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-extra-terms), [`hHessGrad_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hhessgrad-eq), [`ricci_identity`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-ricci-identity).</small>

<a id="d-qiqth-curvature-riemann"></a>
**Definition 35** (`riemann`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L197)</small>

**Riemann curvature tensor** (type (1,3)), `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Σ_λ (Γ^ρ_{μλ} Γ^λ_{νσ} − Γ^ρ_{νλ} Γ^λ_{μσ})`.


<small>Used by [`riemann_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-riemann-contdiff), [`ricci_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-ricci-contdiff), [`riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-riemann-antisymm), [`ricci`](/browser/qiqth-curvature#d-qiqth-curvature-ricci), [`riemann_first_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-riemann-first-bianchi), [`bianchi_extra_terms`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-extra-terms), [`covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem), [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), and 14 more.</small>

<a id="d-qiqth-curvature-riemann-antisymm"></a>
**Lemma 36** (`riemann_antisymm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L205)</small>

**Riemann is antisymmetric in its last two indices**: `R^ρ_{σμν} = −R^ρ_{σνμ}`. Immediate from the definition (the derivative pair and the quadratic sum each negate under `μ ↔ ν`).

$$
\href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,x = -\href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\mu\,x
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel). $\square$

<small>Used by [`bianchi_extra_terms`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-extra-terms), [`covDerivRiem_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-antisymm), [`lowered_riemann_pair_symm`](/browser/qiqth-riccisymm#d-qiqth-curvature-lowered-riemann-pair-symm).</small>

<a id="d-qiqth-curvature-ricci"></a>
**Definition 37** (`ricci`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L227)</small>

**Ricci tensor** `R_{σν} = R^μ_{σμν}` (contraction on the first and third indices).

$$
\mathrm{ricci}\,n\,g\,\mathrm{gi}\,\sigma\,\nu\,x \;:=\; \sum_{\mu} \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\mu\,\sigma\,\mu\,\nu\,x
$$

<small>Used by [`ricci_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-ricci-contdiff), [`scalarCurv_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-scalarcurv-contdiff), [`scalarCurv`](/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv), [`einsteinTensor`](/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor), [`covDerivRiem_contract`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`covDerivRiem_contract'`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`second_bianchi_contracted`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-contracted), [`lowered_riemann_gi_trace`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-gi-trace), and 24 more.</small>

<a id="d-qiqth-curvature-scalarcurv"></a>
**Definition 38** (`scalarCurv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L231)</small>

**Scalar curvature** `R = g^{σν} R_{σν}`.

$$
\mathrm{scalarCurv}\,n\,g\,\mathrm{gi}\,x \;:=\; \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})}
$$

<small>Used by [`scalarCurv_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-scalarcurv-contdiff), [`einsteinTensor`](/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`twice_contracted_bianchi`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-twice-contracted-bianchi), [`einstein_field_equation_real`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real), [`einstein_field_equation_real_global`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real-global), [`jacobson_einstein_equation_of_state`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-jacobson-einstein-equation-of-state), [`hreg_kg`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-hreg-kg), and 5 more.</small>

<a id="d-qiqth-curvature-einsteintensor"></a>
**Definition 39** (`einsteinTensor`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L235)</small>

**Einstein tensor** `G_{σν} = R_{σν} − ½ R g_{σν}`.

$$
\mathrm{einsteinTensor}\,n\,g\,\mathrm{gi}\,\sigma\,\nu\,x \;:=\; \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} - 1/2 \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({x})} \cdot g_{{\sigma}{\nu}}({x})
$$

<small>Used by [`einstein_field_equation_real`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real), [`einstein_field_equation_real_global`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real-global), [`jacobson_einstein_equation_of_state`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-jacobson-einstein-equation-of-state), [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_complete_covCong`](/browser/qiqth-qiqtgrcovcong#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete-covcong), [`qiqt_gr_explicit_kg`](/browser/qiqth-qiqtgrexplicitkg#d-qiqth-wedgekmstogr-qiqt-gr-explicit-kg), [`qiqt_gr_freefield`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [`qiqt_gr_freefield_localized`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), and 10 more.</small>

<a id="d-qiqth-curvature-covderivvec"></a>
**Definition 40** (`covDerivVec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L242)</small>

**Covariant derivative of a vector field** `V^μ`: `∇_ν V^μ = ∂_ν V^μ + Γ^μ_{νσ} V^σ`.

$$
\mathrm{covDerivVec}\,n\,g\,\mathrm{gi}\,V\,\nu\,\mu\,x \;:=\; \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto V\,y\,\mu})({x})} + \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\mu}}_{{\nu}{\sigma}}({x})} \cdot V\,x\,\sigma
$$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_complete_covCong`](/browser/qiqth-qiqtgrcovcong#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete-covcong), [`qiqt_gr_freefield_localized'`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [`qiqt_gr_freefield_nullEnergy`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [`qiqt_gr_freefield_geom`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian), [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave), [`qiqt_gr_ppwave_showcase`](/browser/qiqth-qiqtgrshowcase#d-qiqth-wedgekmstogr-qiqt-gr-ppwave-showcase), and 15 more.</small>

<a id="d-qiqth-curvature-covderiv02"></a>
**Definition 41** (`covDeriv02`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L252)</small>

**Covariant derivative of a (0,2) tensor** `T_{μρ}`: `∇_ν T_{μρ} = ∂_ν T_{μρ} − Γ^σ_{νμ} T_{σρ} − Γ^σ_{νρ} T_{μσ}`.


<small>Used by [`metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-metric-compat), [`covDerivRiem_contract`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`covDerivRiem_contract'`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`second_bianchi_contracted`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-contracted), [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`lowered_riemann_eq`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-eq), [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), and 9 more.</small>

<a id="d-qiqth-curvature-covderiv20"></a>
**Definition 42** (`covDeriv20`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L260)</small>

**Covariant derivative of a (2,0) tensor** `T^{μρ}`: `∇_ν T^{μρ} = ∂_ν T^{μρ} + Γ^μ_{νκ} T^{κρ} + Γ^ρ_{νκ} T^{μκ}`.


<small>Used by [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci).</small>

<a id="d-qiqth-curvature-inv-contract"></a>
**Lemma 43** (`inv_contract`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L286)</small>

**Inverse-metric contraction.** For `gi` a right-inverse of the (symmetric) metric `g` at `x`, lowering an upper index then contracting returns the original: `∑σ g_{σν} (∑α g^{σα} w_α) = w_ν`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), (\forall (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({x}) \cdot g^{{\sigma}{b}}({x}) = \delta_{ab}) \to \forall (\nu : \mathrm{Fin}\,n) (w : \mathrm{Fin}\,n \to \mathbb{R}), \sum_{\sigma} g_{{\sigma}{\nu}}({x}) \cdot \sum_{\alpha} g^{{\sigma}{\alpha}}({x}) \cdot w\,\alpha = w\,\nu
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`christoffel_lower`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel-lower).</small>

<a id="d-qiqth-curvature-christoffel-lower"></a>
**Lemma 44** (`christoffel_lower`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L310)</small>

**Lowered Christoffel symbol** `Γ_{νλμ} = ∑σ g_{σν} Γ^σ_{λμ} = ½(∂_λ g_{νμ} + ∂_μ g_{νλ} − ∂_ν g_{λμ})` — the inverse metric in Γ is cancelled by the lowering, via `inv_contract`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), (\forall (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({x}) \cdot g^{{\sigma}{b}}({x}) = \delta_{ab}) \to \forall (\nu \lambda \mathrm{mu} : \mathrm{Fin}\,n), \sum_{\sigma} g_{{\sigma}{\nu}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\sigma}}_{{\lambda}{\mathrm{mu}}}({x})} = 1/2 \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\lambda}}({\lambda y \mapsto g_{{\nu}{\mathrm{mu}}}({y})})({x})} + \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mathrm{mu}}}({\lambda y \mapsto g_{{\nu}{\lambda}}({y})})({x})} - \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto g_{{\lambda}{\mathrm{mu}}}({y})})({x})})
$$

*Proof.* By [`inv_contract`](/browser/qiqth-curvature#d-qiqth-curvature-inv-contract). $\square$

<small>Used by [`metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-metric-compat).</small>

<a id="d-qiqth-curvature-metric-compat"></a>
**Lemma 45** (`metric_compat`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L330)</small>

**Metric compatibility `∇_λ g_{μν} = 0`** — the defining property of the Levi-Civita connection, now a THEOREM from the Christoffel definition (via `christoffel_lower`) + metric symmetry. (Needs only that `gi` is the inverse and `g` is symmetric — no smoothness, since `∇g` is algebraic in the `∂g`.)

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), (\forall (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({x}) \cdot g^{{\sigma}{b}}({x}) = \delta_{ab}) \to \forall (\lambda \mathrm{mu} \nu : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,g\,\lambda\,\mathrm{mu}\,\nu\,x = 0
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel), [`christoffel_lower`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel-lower). $\square$

<small>Used by [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`lowered_riemann_eq`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-eq), [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm), [`div02_scalar_metric`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-scalar-metric), [`pd_g_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-g-eq).</small>

<a id="d-qiqth-curvature-riemann-first-bianchi"></a>
**Lemma 46** (`riemann_first_bianchi`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L354)</small>

**First Bianchi identity** (the algebraic/cyclic one): `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0`, for the torsion-free (Levi-Civita) connection. Purely algebraic — the derivative terms cancel pairwise by Christoffel lower-symmetry (no Schwarz / mixed partials needed), and the quadratic ΓΓ sums cancel termwise.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (\rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,x + \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\mu\,\nu\,\sigma\,x + \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\nu\,\sigma\,\mu\,x = 0
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel), [`christoffel_symm`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel-symm). $\square$

<small>Used by [`lowered_riemann_pair_symm`](/browser/qiqth-riccisymm#d-qiqth-curvature-lowered-riemann-pair-symm).</small>

<a id="d-qiqth-curvature-riemannlin"></a>
**Definition 47** (`riemannLin`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L383)</small>

**The derivative ("principal") part of the Riemann tensor** — `∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ}`, the part of `R^ρ_{σμν}` linear in `∂Γ` (the ΓΓ part dropped).

$$
\mathrm{Riem}\,n\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,x \;:=\; \partial_{{\mu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\sigma}}({y})}})({x}) - \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mu}{\sigma}}({y})}})({x})
$$

<small>Used by [`second_bianchi_deriv_part`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-deriv-part), [`bianchi_dGamma`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-dgamma), [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-second-bianchi-deriv-part"></a>
**Lemma 48** (`second_bianchi_deriv_part`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L389)</small>

**The derivative part of the second Bianchi cyclic sum vanishes** — `∂_λ Rlin^ρ_{σμν} + ∂_μ Rlin^ρ_{σνλ} + ∂_ν Rlin^ρ_{σλμ} = 0` for smooth Christoffel symbols. This is the part of the second Bianchi identity that the SCHWARZ keystone (`pd_comm`) handles: the six second-derivative `∂∂Γ` terms cancel in pairs once mixed partials commute. (The full second Bianchi additionally needs the ΓΓ / Γ·R terms to cancel via the first Bianchi + Christoffel symmetry — the long general-coordinate remainder; see note 51.)

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \partial_{{\lambda}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{mu}\,\nu\,y})({x}) + \partial_{{\mathrm{mu}}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\lambda\,y})({x}) + \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\lambda\,\mathrm{mu}\,y})({x}) = 0
$$

*Proof.* By [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`pd_sub`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sub), [`pd_eq_fderiv`](/browser/qiqth-curvature#d-qiqth-curvature-pd-eq-fderiv), [`pd_comm`](/browser/qiqth-curvature#d-qiqth-curvature-pd-comm). $\square$

<small>Used by [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-bianchi-extra-terms"></a>
**Lemma 49** (`bianchi_extra_terms`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L460)</small>

**The "extra" lower-index connection terms cancel under the cyclic sum.** `∇R` (as a (1,3) tensor) has four `Γ·R` terms; the curvature-2-form `DF=0` proof needs only the two acting on the `ρ,σ` matrix indices. The other two (acting on the antisymmetric form indices `μ,ν`) cancel cyclically, by Christoffel symmetry + Riemann antisymmetry — reducing the second Bianchi to the clean matrix-form `DF=0`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (\rho \sigma \lambda \mathrm{mu} \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\lambda}{\mathrm{mu}}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\kappa\,\nu\,x + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\lambda}{\nu}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{mu}\,\kappa\,x + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{mu}}{\nu}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\kappa\,\lambda\,x + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{mu}}{\lambda}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\kappa\,x + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\lambda}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\kappa\,\mathrm{mu}\,x + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\mathrm{mu}}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\lambda\,\kappa\,x = 0
$$

*Proof.* By [`christoffel_symm`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel-symm), [`riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-riemann-antisymm). $\square$

<small>Used by [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-riemannquad"></a>
**Definition 50** (`riemannQuad`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L481)</small>

The quadratic (`ΓΓ`) part of the Riemann tensor: `R^ρ_{σμν}|_quad = ∑_l (Γ^ρ_{μl}Γ^l_{νσ} − Γ^ρ_{νl}Γ^l_{μσ})`. As a matrix in the `(ρ,σ)` indices this is the commutator `[Γ_μ, Γ_ν]`.


<small>Used by [`bianchi_GGG`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-ggg), [`pd_riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-pd-riemannquad), [`bianchi_dGamma`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-dgamma), [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-bianchi-ggg"></a>
**Lemma 51** (`bianchi_GGG`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L488)</small>

**The ΓΓΓ part of the second Bianchi cyclic sum vanishes — the Jacobi identity.** In the matrix-form `DF=0`, the cubic part is `∑_cyclic [Γ_λ, [Γ_μ, Γ_ν]] = 0` (Jacobi). In components every matrix triple-product appears once with each sign, matched pairwise by a single `κ ↔ e` swap of the two contracted indices (`Finset.sum_comm`) — no Christoffel symmetry needed.

$$
\sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\lambda}{\kappa}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\mathrm{mu}\,\nu\,x - \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\lambda}{\sigma}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\mathrm{mu}\,\nu\,x + (\sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mathrm{mu}}{\kappa}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\nu\,\lambda\,x - \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{mu}}{\sigma}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\nu\,\lambda\,x) + (\sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\kappa}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\lambda\,\mathrm{mu}\,x - \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\sigma}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\lambda\,\mathrm{mu}\,x) = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-pd-riemannquad"></a>
**Lemma 52** (`pd_riemannQuad`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L554)</small>

**Expansion of `∂_λ (R_quad)^ρ_{σμν}`** via `pd_sum` + Leibniz: the `∑_l (∂Γ·Γ + Γ·∂Γ)` terms.

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\lambda \rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \partial_{{\lambda}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,y})({x}) = \sum_{l} (\partial_{{\lambda}}({\lambda w \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mu}{l}}({w})}})({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{l}}_{{\nu}{\sigma}}({x})} + \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mu}{l}}({x})} \cdot \partial_{{\lambda}}({\lambda w \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{l}}_{{\nu}{\sigma}}({w})}})({x}) - \partial_{{\lambda}}({\lambda w \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{l}}({w})}})({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{l}}_{{\mu}{\sigma}}({x})} - \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{l}}({x})} \cdot \partial_{{\lambda}}({\lambda w \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{l}}_{{\mu}{\sigma}}({w})}})({x}))
$$

*Proof.* By [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`pd_sub`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sub), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`sub`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sub), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul). $\square$

<small>Used by [`bianchi_dGamma`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-dgamma).</small>

<a id="d-qiqth-curvature-bianchi-dgamma"></a>
**Lemma 53** (`bianchi_dGamma`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L578)</small>

**The ∂Γ·Γ part of the second Bianchi cyclic sum vanishes.** The first-derivative-of-`Γ` terms come from two places — the Leibniz derivative of `R_quad` (`pd_riemannQuad`) and the linear part of the `Γ·R` terms (`Γ·R_lin`). Under the cyclic sum they cancel as *identical sums up to renaming the contracted index* (no Christoffel symmetry, no index swap) — closed by `ring`.

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \lambda \mathrm{mu} \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \partial_{{\lambda}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{mu}\,\nu\,y})({x}) + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\lambda}{\kappa}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\mathrm{mu}\,\nu\,x - \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\lambda}{\sigma}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\mathrm{mu}\,\nu\,x + (\partial_{{\mathrm{mu}}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\lambda\,y})({x}) + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mathrm{mu}}{\kappa}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\nu\,\lambda\,x - \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{mu}}{\sigma}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\nu\,\lambda\,x) + (\partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\lambda\,\mathrm{mu}\,y})({x}) + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\kappa}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\lambda\,\mathrm{mu}\,x - \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\sigma}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\lambda\,\mathrm{mu}\,x) = 0
$$

*Proof.* By [`pd_riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-pd-riemannquad). $\square$

<small>Used by [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-covderivriem"></a>
**Definition 54** (`covDerivRiem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L601)</small>

**Covariant derivative of the (1,3) Riemann tensor** `∇_λ R^ρ_{σμν} = ∂_λ R^ρ_{σμν} + Γ^ρ_{λκ}R^κ_{σμν} − Γ^κ_{λσ}R^ρ_{κμν} − Γ^κ_{λμ}R^ρ_{σκν} − Γ^κ_{λν}R^ρ_{σμκ}`.


<small>Used by [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), [`covDerivRiem_contract`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`covDerivRiem_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-antisymm), [`covDerivRiem_contract'`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`second_bianchi_contracted`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-contracted), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci), [`divRiemann_trace_eq`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-divriemann-trace-eq), and 1 more.</small>

<a id="d-qiqth-curvature-second-bianchi"></a>
**Lemma 55** (`second_bianchi`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L611)</small>

**The second Bianchi identity** (differential Bianchi): for the Levi-Civita connection of a smooth metric, the cyclic sum of covariant derivatives of the Riemann tensor vanishes, `∇_λ R^ρ_{σμν} + ∇_μ R^ρ_{σνλ} + ∇_ν R^ρ_{σλμ} = 0`. Proved by decomposing each `∇R` into four pieces — `∂∂Γ` (cancels via Schwarz, `second_bianchi_deriv_part`), `∂Γ·Γ` (`bianchi_dGamma`), the cubic `ΓΓΓ`/Jacobi part (`bianchi_GGG`), and the lower-index "extra" terms (`bianchi_extra_terms`) — each of whose cyclic sum is zero. This is the conservation identity behind `∇^μ G_{μν}=0` (Jacobson's contracted-Bianchi step). Established mathematics, here machine-checked component-level and axiom-free.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \lambda \mathrm{mu} \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\lambda\,\rho\,\sigma\,\mathrm{mu}\,\nu\,x + \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\mathrm{mu}\,\rho\,\sigma\,\nu\,\lambda\,x + \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\nu\,\rho\,\sigma\,\lambda\,\mathrm{mu}\,x = 0
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`sub`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sub), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`PdiffAt_pd`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-pd), [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann), [`riemannLin`](/browser/qiqth-curvature#d-qiqth-curvature-riemannlin), [`second_bianchi_deriv_part`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-deriv-part), [`bianchi_extra_terms`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-extra-terms), [`riemannQuad`](/browser/qiqth-curvature#d-qiqth-curvature-riemannquad), [`bianchi_GGG`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-ggg), [`bianchi_dGamma`](/browser/qiqth-curvature#d-qiqth-curvature-bianchi-dgamma). $\square$

<small>Used by [`second_bianchi_contracted`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-contracted).</small>

<a id="d-qiqth-curvature-pdiffat-riemann"></a>
**Lemma 56** (`PdiffAt_riemann`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L668)</small>

`R^ρ_{σμν}` is partially differentiable in any direction (Γ smooth).

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \mu \nu \lambda : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,y)\,\lambda\,x
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`sub`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sub), [`add`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-add), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`PdiffAt_pd`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-pd). $\square$

<small>Used by [`covDerivRiem_contract`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`covDerivRiem_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-antisymm), [`PdiffAt_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem).</small>

<a id="d-qiqth-curvature-covderivriem-contract"></a>
**Lemma 57** (`covDerivRiem_contract`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L678)</small>

**The covariant derivative commutes with contraction** (the `(ρ,μ)`-trace giving Ricci): `∑_ρ ∇_λ R^ρ_{σρν} = ∇_λ R_{σν}`. The connection corrections for the contracted index pair cancel (`Finset.sum_comm`), and the remaining two assemble into the `(0,2)` covariant derivative of `Ric`. The key step that turns the second Bianchi into the contracted Bianchi `∇^μ G_{μν}=0`.

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\lambda \sigma \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\rho} \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\lambda\,\rho\,\sigma\,\rho\,\nu\,x = \href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\lambda\,\sigma\,\nu\,x
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann). $\square$

<small>Used by [`covDerivRiem_contract'`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`second_bianchi_contracted`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-contracted).</small>

<a id="d-qiqth-curvature-covderivriem-antisymm"></a>
**Lemma 58** (`covDerivRiem_antisymm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L703)</small>

**`∇R` inherits Riemann's antisymmetry in the last two indices**: `∇_λ R^ρ_{σμν} + ∇_λ R^ρ_{σνμ} = 0`. Each of the five constituent terms pairs off via `riemann_antisymm` (the `∂∂` term via `pd_const_mul`).

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\lambda \rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\lambda\,\rho\,\sigma\,\mu\,\nu\,x + \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\lambda\,\rho\,\sigma\,\nu\,\mu\,x = 0
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`pd_const_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const-mul), [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann), [`riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-riemann-antisymm), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann). $\square$

<small>Used by [`covDerivRiem_contract'`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract).</small>

<a id="d-qiqth-curvature-covderivriem-contract"></a>
**Lemma 59** (`covDerivRiem_contract'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L734)</small>

The Ricci trace via the *other* contraction (antisymmetry): `∑_ρ R^ρ_{σμρ} = −R_{σμ}`. Helper not needed standalone — folded into the `(ρ,ν)`-slot contraction below.

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{dir} \sigma \mu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\rho} \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\mathrm{dir}\,\rho\,\sigma\,\mu\,\rho\,x = -\href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\mathrm{dir}\,\sigma\,\mu\,x
$$

*Proof.* By [`covDerivRiem_contract`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`covDerivRiem_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-antisymm). $\square$

<small>Used by [`second_bianchi_contracted`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-contracted).</small>

<a id="d-qiqth-curvature-second-bianchi-contracted"></a>
**Lemma 60** (`second_bianchi_contracted`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L747)</small>

**The once-contracted (second) Bianchi identity** `∇_λ R_{σν} − ∇_ν R_{σλ} + ∇_ρ R^ρ_{σνλ} = 0`, obtained by tracing the second Bianchi over `(ρ,μ)` (`covDerivRiem_contract`/`'`). The remaining divergence term `∑_ρ ∇_ρ R^ρ_{σνλ}` is the Riemann divergence; contracting once more with `g^{μν}` yields `∇^μ G_{μν}=0`. Established mathematics, machine-checked component-level and axiom-free.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\lambda \sigma \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\lambda\,\sigma\,\nu\,x - \href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\nu\,\sigma\,\lambda\,x + \sum_{\rho} \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\rho\,\sigma\,\nu\,\lambda\,x = 0
$$

*Proof.* By [`second_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi), [`covDerivRiem_contract`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract), [`covDerivRiem_contract'`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem-contract). $\square$

<small>Used by [`twice_contracted_bianchi`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-twice-contracted-bianchi).</small>

<a id="d-qiqth-curvature-inv-metric-compat"></a>
**Lemma 61** (`inv_metric_compat`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L765)</small>

**Inverse-metric covariant constancy `∇_λ g^{μρ} = 0`** — the raised-index companion of `metric_compat`. Derived by differentiating the inverse relation `∑_σ g_{aσ}g^{σb}=δ` (so `∑_σ g_{aσ}∂_λ g^{σρ} = −∑_σ (∂_λ g_{aσ})g^{σρ}`), substituting `∂g` from `metric_compat`, and cancelling the connection terms; the contraction with `g` is then removed by invertibility. The tool that lets the metric pass through `∇` in the `g^{μν}`-contractions of `∇^μ G_{μν}=0`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to \forall (\lambda : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), (\forall (a b : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\lambda\,x) \to (\forall (a b : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g^{{a}{b}}({y}))\,\lambda\,x) \to \forall (\mu \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv20}{\nabla^{2}}\,g\,\mathrm{gi}\,\mathrm{gi}\,\lambda\,\mu\,\rho\,x = 0
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`pd_const`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel), [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-metric-compat). $\square$

<small>Used by [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci).</small>

<a id="d-qiqth-curvature-lowered-riemann-eq"></a>
**Lemma 62** (`lowered_riemann_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L865)</small>

**Riemann in terms of the metric** (lowered first index): `g_{ρα} R^α_{σμν}` equals `∂_μ Γ_{ρνσ} − ∂_ν Γ_{ρμσ} − Γ^κ_{μρ}Γ_{κνσ} + Γ^κ_{νρ}Γ_{κμσ}`, where `Γ_{ρνσ}=∑_α g_{ρα}Γ^α_{νσ}` is the lowered Christoffel (written here as the contraction `g_{ακ}` for the connection terms). The `g·ΓΓ` terms produced by differentiating `g` (`metric_compat`) cancel the Riemann `ΓΓ` terms.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\alpha} g_{{\rho}{\alpha}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,\sigma\,\mu\,\nu\,x = \partial_{{\mu}}({\lambda y \mapsto \sum_{\alpha} g_{{\rho}{\alpha}}({y}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\alpha}}_{{\nu}{\sigma}}({y})}})({x}) - \partial_{{\nu}}({\lambda y \mapsto \sum_{\alpha} g_{{\rho}{\alpha}}({y}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\alpha}}_{{\mu}{\sigma}}({y})}})({x}) - \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mu}{\rho}}({x})} \cdot \sum_{\alpha} g_{{\alpha}{\kappa}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\alpha}}_{{\nu}{\sigma}}({x})} + \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\rho}}({x})} \cdot \sum_{\alpha} g_{{\alpha}{\kappa}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\alpha}}_{{\mu}{\sigma}}({x})}
$$

*Proof.* By [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-metric-compat). $\square$

<small>Used by [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm).</small>

<a id="d-qiqth-curvature-lowered-riemann-antisymm"></a>
**Lemma 63** (`lowered_riemann_antisymm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L937)</small>

**First-pair antisymmetry of the lowered Riemann tensor**: `g_{ρα}R^α_{σμν} + g_{σα}R^α_{ρμν} = 0`, i.e. `R_{ρσμν}=−R_{σρμν}`. From `lowered_riemann_eq`: the `∂Γ_lower` pairs combine (via `metric_compat` as a *function* identity) into `∂∂g_{ρσ}` and cancel by **Schwarz** (`pd_comm`); the `ΓΓ` pairs cancel by the symmetry of `⟨ab,cd⟩=∑_{κα}g_{ακ}Γ^κ_{ab}Γ^α_{cd}` under `(ab)↔(cd)`. The crux of the metric-raising tower (piece B) — required for `g^{σν}R^ρ_{σνλ}` in `∇^μ G_{μν}=0`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\alpha} g_{{\rho}{\alpha}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,\sigma\,\mu\,\nu\,x + \sum_{\alpha} g_{{\sigma}{\alpha}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,\rho\,\mu\,\nu\,x = 0
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`pd_comm`](/browser/qiqth-curvature#d-qiqth-curvature-pd-comm), [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-metric-compat), [`lowered_riemann_eq`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-eq). $\square$

<small>Used by [`lowered_riemann_gi_trace`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-gi-trace), [`lowered_riemann_pair_symm`](/browser/qiqth-riccisymm#d-qiqth-curvature-lowered-riemann-pair-symm).</small>

<a id="d-qiqth-curvature-lowered-riemann-gi-trace"></a>
**Lemma 64** (`lowered_riemann_gi_trace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L988)</small>

**Metric trace of the lowered Riemann tensor → Ricci**: `∑_{σν} g^{σν}(g_{βρ}R^ρ_{σνλ}) = −R_{βλ}`. The contraction over the *first two* lower slots, via first-pair antisymmetry (`lowered_riemann_antisymm`) turns into the contraction over the (1,3)-Ricci slots, and the `g^{σν}g_{σρ}=δ` collapse reproduces `ricci β λ = ∑_ν R^ν_{βνλ}`. The core of metric-raising tower piece C (the contraction identity behind `g^{σν}R^ρ_{σνλ}` in `∇^μ G_{μν}=0`).

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\beta \lambda : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \sum_{\rho} g_{{\beta}{\rho}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\lambda\,x = -\href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\beta}{\lambda}}({x})}
$$

*Proof.* By [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm). $\square$

<small>Used by [`ricci_gi_raise`](/browser/qiqth-curvature#d-qiqth-curvature-ricci-gi-raise).</small>

<a id="d-qiqth-curvature-ricci-gi-raise"></a>
**Lemma 65** (`ricci_gi_raise`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1030)</small>

**Raised metric trace of Riemann → raised Ricci** (metric-raising tower, piece C raised): `∑_{σν} g^{σν} R^ρ_{σνλ} = −∑_β g^{ρβ} Ric_{βλ}`. Raises `lowered_riemann_gi_trace` through the `g⁻¹·g = δ` inversion.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \lambda : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\lambda\,x = -\sum_{\beta} g^{{\rho}{\beta}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\beta}{\lambda}}({x})}
$$

*Proof.* By [`lowered_riemann_gi_trace`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-gi-trace). $\square$

<small>Used by [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci).</small>

<a id="d-qiqth-curvature-pdiffat-ricci"></a>
**Lemma 66** (`PdiffAt_ricci`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1078)</small>

`Ric_{σν}` is partially differentiable in any direction (Γ smooth).

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\sigma \nu \lambda : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({y})})\,\lambda\,x
$$

*Proof.* By [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann). $\square$

<small>Used by [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci), [`einstein_field_equation_real`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real).</small>

<a id="d-qiqth-curvature-gi-trace-covderiv-ricci"></a>
**Lemma 67** (`gi_trace_covDeriv_ricci`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1084)</small>

**T1 of the twice-contracted Bianchi — the scalar-curvature derivative**: `∑_{σν} g^{σν} ∇_λ Ric_{σν} = ∂_λ R`. Product rule on `R = ∑g^{σν}Ric_{σν}` (`pd_sum`+`pd_mul`) plus `inv_metric_compat` (`∂g^{σν} = −Γg−Γg`) cancels the connection terms by index swaps.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\lambda : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\lambda\,\sigma\,\nu\,x = \partial_{{\lambda}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({y})}})({x})
$$

*Proof.* By [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`covDeriv20`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv20), [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`PdiffAt_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-ricci). $\square$

<small>Used by [`twice_contracted_bianchi`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-twice-contracted-bianchi).</small>

<a id="d-qiqth-curvature-gi-trace-covderivriem"></a>
**Lemma 68** (`gi_trace_covDerivRiem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1151)</small>

**T3 core — contraction commutes with the Riemann divergence**: for fixed `ρ`, `∑_{σν} g^{σν} ∇_ρ R^ρ_{σνλ}` equals `∂_ρ S^ρ_λ + Γ^ρ_{ρκ}S^κ_λ − Γ^κ_{ρλ}S^ρ_κ`, the `(1,1)` covariant divergence of `S^a_b := ∑_{σν} g^{σν} R^a_{σνb}` — the `σ,ν` connection corrections of `covDerivRiem` cancel `∂g^{σν}` (`inv_metric_compat`) by the same swaps as T1.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \lambda : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\rho\,\sigma\,\nu\,\lambda\,x = \partial_{{\rho}}({\lambda y \mapsto \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({y}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\lambda\,y})({x}) + \sum_{\sigma} \sum_{\nu} \sum_{\kappa} g^{{\sigma}{\nu}}({x}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\rho}{\kappa}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\nu\,\lambda\,x) - \sum_{\sigma} \sum_{\nu} \sum_{\kappa} g^{{\sigma}{\nu}}({x}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\rho}{\lambda}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\kappa\,x)
$$

*Proof.* By [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`covDeriv20`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv20), [`PdiffAt_riemann`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-riemann), [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat). $\square$

<small>Used by [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci).</small>

<a id="d-qiqth-curvature-gi-trace-covderivriem-ricci"></a>
**Lemma 69** (`gi_trace_covDerivRiem_ricci`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1217)</small>

**T3 core with `S` substituted to `−`(raised Ricci)** (via `ricci_gi_raise`): for fixed `ρ`, `∑_{σν} g^{σν} ∇_ρ R^ρ_{σνλ} = −∑_β g^{ρβ}∂_ρ Ric_{βλ} + ∑_{βκ} Γ^β_{ρκ}g^{ρκ}Ric_{βλ} + ∑_{βκ} Γ^κ_{ρλ}g^{ρβ}Ric_{βκ}`. The `Γ^ρ_{ρκ}` terms from `∂g` cancel the `∑Γ^ρ_{ρκ}S^κ` spectator.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \lambda : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\rho\,\sigma\,\nu\,\lambda\,x = -\sum_{\beta} g^{{\rho}{\beta}}({x}) \cdot \partial_{{\rho}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\beta}{\lambda}}({y})}})({x}) + \sum_{\beta} \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\beta}}_{{\rho}{\kappa}}({x})} \cdot g^{{\rho}{\kappa}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\beta}{\lambda}}({x})} + \sum_{\beta} \sum_{\kappa} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\rho}{\lambda}}({x})} \cdot g^{{\rho}{\beta}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\beta}{\kappa}}({x})}
$$

*Proof.* By [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`pd_const_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const-mul), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann), [`covDeriv20`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv20), [`inv_metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-inv-metric-compat), [`ricci_gi_raise`](/browser/qiqth-curvature#d-qiqth-curvature-ricci-gi-raise), [`PdiffAt_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-ricci), [`gi_trace_covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem). $\square$

<small>Used by [`divRiemann_trace_eq`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-divriemann-trace-eq).</small>

<a id="d-qiqth-curvature-const-of-pd-zero"></a>
**Lemma 70** (`const_of_pd_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1295)</small>

**A field with vanishing partial derivatives everywhere is constant** (on `Point n = Fin n → ℝ`, which is connected). All `∂ᵢ F = 0` ⇒ `fderiv F = 0` (the partials span the differential) ⇒ `F` is constant by `is_const_of_fderiv_eq_zero`. Upgrades "covariantly constant at a point" to a genuine constant — e.g. the cosmological constant `Λ`.

$$
\mathrm{Differentiable}\,\mathbb{R}\,F \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\nu : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({F})({x})} = 0) \to \forall (x y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), F\,x = F\,y
$$

*Proof.* By [`pd_eq_fderiv`](/browser/qiqth-curvature#d-qiqth-curvature-pd-eq-fderiv). $\square$

<small>Used by [`einstein_field_equation_real_global`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real-global).</small>

---
<small>[← all sections](/browser) · [← CoreNoCollapse](/browser/qiqth-corenocollapse) · [DifferentialAreaLaw →](/browser/qiqth-differentialarealaw) </small>