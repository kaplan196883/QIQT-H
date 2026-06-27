---
layout: ../../layouts/Deep.astro
title: QIQTH.KGStressConservation
eyebrow: KGStressConservation · section of the QIQT-H book
description: QIQTH.KGStressConservation — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← HregExplicitKG](/browser/qiqth-hregexplicitkg) · [KMSCorrelation →](/browser/qiqth-kmscorrelation) </small>

<small>KGStressConservation · entries 448–468 of 1000</small>

<a id="d-qiqth-curvature-kgkinetic"></a>
**Definition 448** (`kgKinetic`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L22)</small>

The KG **kinetic** `(0,2)` tensor `K_{ab} = ∂_a φ · ∂_b φ`.

$$
\mathrm{kgKinetic}\,n\,\varphi\,y\,a\,b \;:=\; \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{a}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({y})}
$$

<small>Used by [`div02_kgStress_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-eq), [`covDeriv02_kgKinetic`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-covderiv02-kgkinetic), [`div02_kgKinetic_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgkinetic-eq), [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved), [`div02_kgStress_conserved_of_KG`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved-of-kg), [`kg_conserv`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv), [`kg_conserv_of_contDiff`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv-of-contdiff).</small>

<a id="d-qiqth-curvature-kglagr"></a>
**Definition 449** (`kgLagr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L26)</small>

The KG **Lagrangian scalar** `L = g^{αβ} ∂_α φ ∂_β φ + m² φ²` (the combination appearing inside the trace term of the stress tensor; the sign makes `∇^μ T_{μν} = 0` close against the equation of motion `□φ = m²φ`).

$$
\mathrm{kgLagr}\,n\,m\,\varphi\,\mathrm{gi}\,y \;:=\; \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({y}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})}) + {m}^{2} \cdot {\varphi\,y}^{2}
$$

<small>Used by [`kgLagr_contDiff`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-kglagr-contdiff), [`kgStress_contDiff`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-kgstress-contdiff), [`kgStress`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress), [`div02_kgStress_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-eq), [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved), [`div02_kgStress_conserved_of_KG`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved-of-kg), [`kg_conserv`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv), [`kg_conserv_of_contDiff`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv-of-contdiff), and 3 more.</small>

<a id="d-qiqth-curvature-kgstress"></a>
**Definition 450** (`kgStress`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L32)</small>

The **Klein–Gordon stress tensor** `T_{ab} = ∂_a φ ∂_b φ − ½ g_{ab} L`.

$$
\mathrm{kgStress}\,n\,m\,\varphi\,g\,\mathrm{gi}\,y\,a\,b \;:=\; \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{a}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({y})} - 1/2 \cdot g_{{a}{b}}({y}) \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr}{\mathrm{kgLagr}}\,m\,\varphi\,\mathrm{gi}\,y
$$

<small>Used by [`kgStress_contDiff`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-kgstress-contdiff), [`hreg_kg`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-hreg-kg), [`div02_kgStress_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-eq), [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved), [`div02_kgStress_conserved_of_KG`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved-of-kg), [`kg_conserv`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv), [`kg_conserv_of_contDiff`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv-of-contdiff), [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), and 12 more.</small>

<a id="d-qiqth-curvature-div02-kgstress-eq"></a>
**Lemma 451** (`div02_kgStress_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L37)</small>

**Conservation SPLIT.**  The covariant divergence of the KG stress tensor reduces to the kinetic divergence minus half the Lagrangian gradient: `∇^μ T_{μν} = ∇^μ K_{μν} − ½ ∂_ν L`. The scalar/metric term `½ g_{μν} L` is handled by metric compatibility (`div02_scalar_metric`, the same mechanism that makes `Λ·g` covariantly constant); what remains — the kinetic identity `∇^μ K_{μν} = ½ ∂_ν L` — is the Klein–Gordon equation of motion in disguise (the next brick).  This is the first step of discharging the `conserv` input of the free-field QIQT→GR surface.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgkinetic}{\mathrm{kgKinetic}}\,\varphi\,y\,a\,b)\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr}{\mathrm{kgLagr}}\,m\,\varphi\,\mathrm{gi})\,\rho\,x) \to (\nabla\!\cdot {\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{\mathrm{kgStress}}\,m\,\varphi\,g\,\mathrm{gi}})_{{\nu}}({x}) = (\nabla\!\cdot {\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgkinetic}{\mathrm{kgKinetic}}\,\varphi})_{{\nu}}({x}) - 1/2 \cdot \partial_{{\nu}}({\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr}{\mathrm{kgLagr}}\,m\,\varphi\,\mathrm{gi}})({x})
$$

*Proof.* By [`pd_const_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const-mul), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`div02_add`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-add), [`div02_scalar_metric`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-scalar-metric). $\square$

<small>Used by [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved).</small>

<a id="d-qiqth-curvature-kghess"></a>
**Definition 452** (`kgHess`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L69)</small>

The **covariant Hessian** of the scalar `φ`: `(∇∇φ)_{ρμ} = ∂_ρ ∂_μ φ − Γ^σ_{ρμ} ∂_σ φ` (the covariant derivative of the gradient covector `∂φ`).  It is symmetric in `ρ μ` (torsion-free connection), which the kinetic identity will use.

$$
\mathrm{kgHess}\,n\,\varphi\,g\,\mathrm{gi}\,\rho\,\mu\,x \;:=\; \partial_{{\rho}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mu}}({\varphi})({y})}})({x}) - \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\sigma}}_{{\rho}{\mu}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\sigma}}({\varphi})({x})}
$$

<small>Used by [`covDeriv02_kgKinetic`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-covderiv02-kgkinetic), [`boxField`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield), [`div02_kgKinetic_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgkinetic-eq), [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved), [`hHessGrad_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hhessgrad-eq).</small>

<a id="d-qiqth-curvature-covderiv02-kgkinetic"></a>
**Lemma 453** (`covDeriv02_kgKinetic`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L76)</small>

**Leibniz/product rule for the kinetic tensor.**  The covariant derivative of `K_{μν} = ∂_μφ ∂_νφ` factors through the covariant Hessian: `(∇_ρ K)_{μν} = (∇∇φ)_{ρμ} ∂_νφ + ∂_μφ (∇∇φ)_{ρν}`. Each Christoffel term in `covDeriv02` regroups (by `Finset.sum_mul`/`Finset.mul_sum`) into exactly one of the two Hessians, leaving the partial-derivative Leibniz term (`pd_mul`).  This is the second brick of the `conserv` discharge: contracting it with `g^{μρ}` and using `□φ = m²φ` + Hessian symmetry will give `∇^μ K_{μν} = ½ ∂_ν L`, closing conservation via `div02_kgStress_eq`.

$$
(\forall (i j : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\varphi})({y})})\,j\,x) \to \href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgkinetic}{\mathrm{kgKinetic}}\,\varphi)\,\rho\,\mu\,\nu\,x = \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kghess}{\mathrm{kgHess}}\,\varphi\,g\,\mathrm{gi}\,\rho\,\mu\,x \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\varphi})({x})} + \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mu}}({\varphi})({x})} \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kghess}{\mathrm{kgHess}}\,\varphi\,g\,\mathrm{gi}\,\rho\,\nu\,x
$$

*Proof.* By [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel). $\square$

<small>Used by [`div02_kgKinetic_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgkinetic-eq).</small>

<a id="d-qiqth-curvature-boxfield"></a>
**Definition 454** (`boxField`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L98)</small>

The **d'Alembertian** `□φ = g^{μρ} (∇∇φ)_{ρμ}` (the covariant Laplace–Beltrami of the scalar `φ`).

$$
\mathrm{boxField}\,n\,\varphi\,g\,\mathrm{gi}\,x \;:=\; \sum_{\mu} \sum_{\rho} g^{{\mu}{\rho}}({x}) \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kghess}{\mathrm{kgHess}}\,\varphi\,g\,\mathrm{gi}\,\rho\,\mu\,x
$$

<small>Used by [`div02_kgKinetic_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgkinetic-eq), [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved), [`div02_kgStress_conserved_of_KG`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved-of-kg), [`kg_conserv`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv), [`kg_conserv_of_contDiff`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv-of-contdiff), [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_complete_covCong`](/browser/qiqth-qiqtgrcovcong#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete-covcong), [`qiqt_gr_explicit_kg`](/browser/qiqth-qiqtgrexplicitkg#d-qiqth-wedgekmstogr-qiqt-gr-explicit-kg), and 9 more.</small>

<a id="d-qiqth-curvature-div02-kgkinetic-eq"></a>
**Lemma 455** (`div02_kgKinetic_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L102)</small>

**Kinetic divergence in Hessian form.**  Contracting the Leibniz rule (`covDeriv02_kgKinetic`) with the inverse metric splits the kinetic divergence into the `□φ` piece and a Hessian-gradient piece: `∇^μ K_{μν} = (□φ) ∂_νφ + g^{μρ} ∂_μφ (∇∇φ)_{ρν}`. The first piece is exactly where the Klein–Gordon equation `□φ = m²φ` enters; the second is `½ ∂_ν` of the kinetic part of `L` (by Hessian symmetry + metric compatibility) — the two facts that, with `div02_kgStress_eq`, close `∇^μ T_{μν} = 0`.  This is the third brick of the `conserv` discharge.

$$
(\forall (i j : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\varphi})({y})})\,j\,x) \to (\nabla\!\cdot {\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgkinetic}{\mathrm{kgKinetic}}\,\varphi})_{{\nu}}({x}) = \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\varphi})({x})} + \sum_{\mu} \sum_{\rho} g^{{\mu}{\rho}}({x}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mu}}({\varphi})({x})} \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kghess}{\mathrm{kgHess}}\,\varphi\,g\,\mathrm{gi}\,\rho\,\nu\,x)
$$

*Proof.* By [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`covDeriv02_kgKinetic`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-covderiv02-kgkinetic). $\square$

<small>Used by [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved).</small>

<a id="d-qiqth-curvature-div02-kgstress-conserved"></a>
**Lemma 456** (`div02_kgStress_conserved`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L136)</small>

**KG STRESS-TENSOR CONSERVATION (final assembly), conditional on the two physical/geometric facts.** For the explicit Klein–Gordon field, `∇^μ T_{μν} = 0` follows from exactly: * `hKG`  — the equation of motion `□φ = m²φ` (`boxField φ = m²·φ`); and * `hHessGrad` — the Hessian-gradient identity `g^{μρ} ∂_μφ (∇∇φ)_{ρν} = ½ ∂_ν(g^{αβ}∂_αφ ∂_βφ)`, the one place metric compatibility (`metric_compat`, `∇g = 0`) + Hessian symmetry (`kgHess_symm`) enter. Given these, the split (`div02_kgStress_eq`) + contraction (`div02_kgKinetic_eq`) collapse algebraically: `∇^μ T_{μν} = (□φ − m²φ) ∂_νφ = 0`. …

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgkinetic}{\mathrm{kgKinetic}}\,\varphi\,y\,a\,b)\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr}{\mathrm{kgLagr}}\,m\,\varphi\,\mathrm{gi})\,\rho\,x) \to (\forall (i j : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\varphi})({y})})\,j\,x) \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,\varphi\,\nu\,x \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({y}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})}))\,\nu\,x \to \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x \to \sum_{\mu} \sum_{\rho} g^{{\mu}{\rho}}({x}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mu}}({\varphi})({x})} \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kghess}{\mathrm{kgHess}}\,\varphi\,g\,\mathrm{gi}\,\rho\,\nu\,x) = 1/2 \cdot \partial_{{\nu}}({\lambda y \mapsto \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({y}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})})})({x}) \to (\nabla\!\cdot {\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{\mathrm{kgStress}}\,m\,\varphi\,g\,\mathrm{gi}})_{{\nu}}({x}) = 0
$$

*Proof.* By [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), [`pd_const_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const-mul), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`div02_kgStress_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-eq), [`div02_kgKinetic_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgkinetic-eq). $\square$

<small>Used by [`div02_kgStress_conserved_of_KG`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved-of-kg).</small>

<a id="d-qiqth-curvature-pd-metric-inv-identity"></a>
**Lemma 457** (`pd_metric_inv_identity`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L180)</small>

**Differentiated inverse relation** (`∂(g·gi = δ)`): for a pointwise inverse metric, differentiating the identity `∑_α g_{μα} gi^{αβ} = δ_μ^β` gives `∑_α ∂_ν(g_{μα}) gi^{αβ} + ∑_α g_{μα} ∂_ν(gi^{αβ}) = 0`.  This is the first step toward inverse-metric compatibility `∇gi = 0` (which then follows by contracting with `gi^{λμ}` and substituting `metric_compat` for `∂g`), the one geometric fact still needed for `hHessGrad`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g^{{a}{b}}({y}))\,\rho\,x) \to \sum_{\alpha} \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto g_{{\mu}{\alpha}}({y})})({x})} \cdot g^{{\alpha}{\beta}}({x}) + \sum_{\alpha} g_{{\mu}{\alpha}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto g^{{\alpha}{\beta}}({y})})({x})} = 0
$$

*Proof.* By [`pd_const`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul). $\square$

<small>Used by [`pd_gi_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-gi-eq).</small>

<a id="d-qiqth-curvature-gi-g-delta"></a>
**Lemma 458** (`gi_g_delta`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L203)</small>

**The inverse metric is a left inverse too** `∑_μ gi^{aμ} g_{μb} = δ^a_b` (from the right-inverse `hinv` plus symmetry of `g` and `gi`).  The δ used to extract `∂gi` in the inverse-metric compatibility.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({x}) \cdot g^{{\sigma}{b}}({x}) = \delta_{ab}) \to \forall (a b : \mathrm{Fin}\,n), \sum_{\mu} g^{{a}{\mu}}({x}) \cdot g_{{\mu}{b}}({x}) = \delta_{ab}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`pd_gi_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-gi-eq).</small>

<a id="d-qiqth-curvature-pd-g-eq"></a>
**Lemma 459** (`pd_g_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L217)</small>

**`∂g` in terms of the connection** `∂_ν g_{μα} = ∑σ Γ^σ_{νμ} g_{σα} + ∑σ Γ^σ_{να} g_{μσ}` — the explicit content of metric compatibility `∇g = 0` (`metric_compat`), unpacked from the `covDeriv02` definition.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({x}) \cdot g^{{\sigma}{b}}({x}) = \delta_{ab}) \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto g_{{\mu}{\alpha}}({y})})({x})} = \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\sigma}}_{{\nu}{\mu}}({x})} \cdot g_{{\sigma}{\alpha}}({x}) + \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\sigma}}_{{\nu}{\alpha}}({x})} \cdot g_{{\mu}{\sigma}}({x})
$$

*Proof.* By [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-metric-compat). $\square$

<small>Used by [`pd_gi_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-gi-eq).</small>

<a id="d-qiqth-curvature-pd-gi-eq"></a>
**Lemma 460** (`pd_gi_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L228)</small>

**INVERSE-METRIC COMPATIBILITY `∇gi = 0`** (upper-index companion of `metric_compat`): `∂_ν gi^{λβ} = −∑σ Γ^λ_{νσ} gi^{σβ} − ∑σ Γ^β_{νσ} gi^{σλ}`. Contract the differentiated inverse relation (`pd_metric_inv_identity`) with `gi^{λμ}`, extract `∂gi^{λβ}` via the δ-identity `gi_g_delta`, substitute `pd_g_eq` for `∂g`, and collapse the two double sums by the δ-contractions `∑α g_{σα}gi^{αβ} = δ_σ^β` (`hinv`) and `∑μ gi^{λμ}g_{μσ} = δ^λ_σ` (`gi_g_delta`).  The last purely-geometric fact needed for `hHessGrad`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g^{{a}{b}}({y}))\,\rho\,x) \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto g^{{\mathrm{lam}}{\beta}}({y})})({x})} = -\sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\mathrm{lam}}}_{{\nu}{\sigma}}({x})} \cdot g^{{\sigma}{\beta}}({x}) - \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\beta}}_{{\nu}{\sigma}}({x})} \cdot g^{{\sigma}{\mathrm{lam}}}({x})
$$

*Proof.* By [`pd_metric_inv_identity`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-metric-inv-identity), [`gi_g_delta`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-gi-g-delta), [`pd_g_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-g-eq). $\square$

<small>Used by [`hHessGrad_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hhessgrad-eq).</small>

<a id="d-qiqth-curvature-pd-gradsq-eq"></a>
**Lemma 461** (`pd_gradSq_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L324)</small>

**Product-rule expansion of the kinetic-scalar gradient** `∂_ν(g^{αβ}∂_αφ∂_βφ)`.  Differentiating term by term (`pd_sum` twice, `pd_mul` for the triple product) splits it into the `∂gi` term plus the two `∂(∂φ)` terms: `∂_ν(∑_{αβ} gi^{αβ}∂_αφ∂_βφ) = ∑_{αβ} ∂_ν(gi^{αβ})∂_αφ∂_βφ + ∑_{αβ} gi^{αβ}(∂_ν∂_αφ)∂_βφ + ∑_{αβ} gi^{αβ}∂_αφ(∂_ν∂_βφ)`. The first term meets `pd_gi_eq` (inverse-metric compatibility) and the last two meet the Hessian partials (`pd_comm`) in the final `hHessGrad` assembly.

$$
(\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g^{{a}{b}}({y}))\,\rho\,x) \to (\forall (i j : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\varphi})({y})})\,j\,x) \to \partial_{{\nu}}({\lambda y \mapsto \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({y}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})})})({x}) = \sum_{\alpha} \sum_{\beta} \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto g^{{\alpha}{\beta}}({y})})({x})} \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({x})}) + (\sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({x}) \cdot (\partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})}})({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({x})}) + \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({x}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({x})} \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})}})({x})))
$$

*Proof.* By [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul). $\square$

<small>Used by [`hHessGrad_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hhessgrad-eq).</small>

<a id="d-qiqth-curvature-gradsq-cross-symm"></a>
**Lemma 462** (`gradSq_cross_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L357)</small>

**The two cross gradient terms are equal** `R2 = R3`: `∑_{αβ} gi^{αβ}(∂_ν∂_αφ)∂_βφ = ∑_{αβ} gi^{αβ}∂_αφ(∂_ν∂_βφ)` (swap `α ↔ β`, `gi`-symmetry).  Used to fold the two `∂(∂φ)` terms of `pd_gradSq_eq` into one in `hHessGrad`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({x}) \cdot (\partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})}})({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({x})}) = \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({x}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({x})} \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})}})({x}))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`hHessGrad_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hhessgrad-eq).</small>

<a id="d-qiqth-curvature-hessgrad-partial-eq"></a>
**Lemma 463** (`hessGrad_partial_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L368)</small>

**The Hessian-partial term equals `R2`** `T1 = R2`: `∑_{μρ} gi^{μρ}∂_μφ ∂_ρ∂_νφ = ∑_{αβ} gi^{αβ}(∂_ν∂_αφ)∂_βφ` (commute the second derivative by `pd_comm`, then relabel `μ↔β, ρ↔α` via `gi`-symmetry).  This is the partial-derivative half of the Hessian-gradient identity.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to ({\varphi})\in C^{\infty} \to \sum_{\mu} \sum_{\rho} g^{{\mu}{\rho}}({x}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mu}}({\varphi})({x})} \cdot \partial_{{\rho}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\varphi})({y})}})({x})) = \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({x}) \cdot (\partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})}})({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({x})})
$$

*Proof.* By [`pd_comm`](/browser/qiqth-curvature#d-qiqth-curvature-pd-comm). $\square$

<small>Used by [`hHessGrad_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hhessgrad-eq).</small>

<a id="d-qiqth-curvature-hhessgrad-eq"></a>
**Lemma 464** (`hHessGrad_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L379)</small>

**THE HESSIAN-GRADIENT IDENTITY `hHessGrad`** — the last brick of the `conserv` discharge: `g^{μρ}∂_μφ(∇∇φ)_{ρν} = ½ ∂_ν(g^{αβ}∂_αφ∂_βφ)`. Decompose the LHS `= T1 − T2` (Hessian partials minus the Christoffel term) and the RHS `= ½(R1+R2+R3)` (`pd_gradSq_eq`).  Then `T1 = R2` (`hessGrad_partial_eq`), `R2 = R3` (`gradSq_cross_symm`), and `T2 = −½R1` (the Christoffel term: substitute `pd_gi_eq` into `R1`, giving `R1 = −P − Q`; `Q = P` by α↔β; `P = T2` by a triple-sum reindex with `christoffel_symm` + gi-symmetry).  Algebra then closes `LHS = R2 − T2 = ½R1 + R2 = ½(R1+R2+R3) = RHS`.  Feeding this to `div02_kgStress_conserved` makes KG conservation `∇^μ T_{μν} = 0` unconditional (modulo only the matter equation of motion `□φ = m²φ`).

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g^{{a}{b}}({y}))\,\rho\,x) \to (\forall (i j : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\varphi})({y})})\,j\,x) \to ({\varphi})\in C^{\infty} \to \sum_{\mu} \sum_{\rho} g^{{\mu}{\rho}}({x}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mu}}({\varphi})({x})} \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kghess}{\mathrm{kgHess}}\,\varphi\,g\,\mathrm{gi}\,\rho\,\nu\,x) = 1/2 \cdot \partial_{{\nu}}({\lambda y \mapsto \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({y}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})})})({x})
$$

*Proof.* By [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel), [`christoffel_symm`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel-symm), [`pd_gi_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-gi-eq), [`pd_gradSq_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-pd-gradsq-eq), [`gradSq_cross_symm`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-gradsq-cross-symm), [`hessGrad_partial_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hessgrad-partial-eq). $\square$

<small>Used by [`div02_kgStress_conserved_of_KG`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved-of-kg).</small>

<a id="d-qiqth-curvature-div02-kgstress-conserved-of-kg"></a>
**Lemma 465** (`div02_kgStress_conserved_of_KG`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L448)</small>

**KLEIN–GORDON STRESS-TENSOR CONSERVATION, DISCHARGED — `∇^μ T_{μν} = 0` for the explicit free KG field, axiom-free, modulo ONLY the equation of motion.**  The Hessian-gradient identity (`hHessGrad`) is now supplied internally by `hHessGrad_eq` (built from inverse-metric compatibility `pd_gi_eq` + the gradient expansion + the symmetry lemmas), so the only remaining hypothesis is `hKG : □φ = m²φ` — the matter equation of motion, genuine physics.  Everything geometric is machine-checked.  This DISCHARGES the `conserv` input of the free-field QIQT→GR surface for the explicit Klein–Gordon stress tensor: `conserv = a · (this) = 0`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgkinetic}{\mathrm{kgKinetic}}\,\varphi\,y\,a\,b)\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g^{{a}{b}}({y}))\,\rho\,x) \to (\forall (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr}{\mathrm{kgLagr}}\,m\,\varphi\,\mathrm{gi})\,\rho\,x) \to (\forall (i j : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\varphi})({y})})\,j\,x) \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,\varphi\,\nu\,x \to ({\varphi})\in C^{\infty} \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({y}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})}))\,\nu\,x \to \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x \to (\nabla\!\cdot {\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{\mathrm{kgStress}}\,m\,\varphi\,g\,\mathrm{gi}})_{{\nu}}({x}) = 0
$$

*Proof.* By [`div02_kgStress_conserved`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved), [`hHessGrad_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-hhessgrad-eq). $\square$

<small>Used by [`kg_conserv`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv).</small>

<a id="d-qiqth-curvature-div02-const-smul"></a>
**Lemma 466** (`div02_const_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L469)</small>

**The raised divergence scales out a constant** `∇^μ(a·X)_{μν} = a·∇^μ X_{μν}` (the connection and metric are linear, `a` is constant — `pd_const_mul` + `Finset.mul_sum`).  This is what carries the Einstein coupling `a` through the conservation law `∇·(a·T) = a·∇·T`.

$$
(\forall (b c \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto X\,y\,b\,c)\,\rho\,x) \to \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y b c \mapsto a \cdot X\,y\,b\,c})_{{\nu}}({x})} = a \cdot \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {X})_{{\nu}}({x})}
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`pd_const_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const-mul), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel), [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02). $\square$

<small>Used by [`kg_conserv`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv).</small>

<a id="d-qiqth-curvature-kg-conserv"></a>
**Lemma 467** (`kg_conserv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L495)</small>

**THE `conserv` INPUT OF THE QIQT→GR DERIVATION, IN ITS EXACT FORM, DISCHARGED for the explicit KG field.**  `∇·(a·T) = 0` with `T = kgStress` (the free Klein–Gordon stress tensor): the Einstein-coupling constant `a` scales out (`div02_const_smul`) and the bare divergence vanishes (`div02_kgStress_conserved_of_KG`).  This is exactly the `conserv : ∀ x ν, div02 g gi (fun y a' b => a · T y a' b) ν x = 0` hypothesis consumed by `WedgeKMSToGR`/`qiqt_gr_from_wedge_kms_complete` — so the matter-conservation input is now a THEOREM for the explicit free scalar, modulo only the equation of motion `□φ = m²φ`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgkinetic}{\mathrm{kgKinetic}}\,\varphi\,y\,a\,b)\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g^{{a}{b}}({y}))\,\rho\,x) \to (\forall (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr}{\mathrm{kgLagr}}\,m\,\varphi\,\mathrm{gi})\,\rho\,x) \to (\forall (i j : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({\varphi})({y})})\,j\,x) \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,\varphi\,\nu\,x \to ({\varphi})\in C^{\infty} \to \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \sum_{\alpha} \sum_{\beta} g^{{\alpha}{\beta}}({y}) \cdot (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\alpha}}({\varphi})({y})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\beta}}({\varphi})({y})}))\,\nu\,x \to (\forall (b c \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({y})\,b\,c})\,\rho\,x) \to \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x \to (\nabla\!\cdot {\lambda y b c \mapsto a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({y})\,b\,c}})_{{\nu}}({x}) = 0
$$

*Proof.* By [`div02_kgStress_conserved_of_KG`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-conserved-of-kg), [`div02_const_smul`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-const-smul). $\square$

<small>Used by [`kg_conserv_of_contDiff`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv-of-contdiff).</small>

<a id="d-qiqth-curvature-kg-conserv-of-contdiff"></a>
**Lemma 468** (`kg_conserv_of_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L518)</small>

**`conserv` FROM SMOOTHNESS ALONE — the clean drop-in.**  The same matter-conservation input `∇·(a·T) = 0` (`T = kgStress`), but with all the pointwise differentiability hypotheses *derived* from a single `ContDiff` assumption on the field `φ` and the metric components `g, gi`.  This is the form actually convenient to plug into `WedgeKMSToGR`/`qiqt_gr_from_wedge_kms_complete`: given a smooth free scalar on a smooth (symmetric, invertible) metric satisfying the Klein–Gordon equation `□φ = m²φ`, the explicit stress tensor is covariantly conserved.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to ({\varphi})\in C^{\infty} \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x \to (\nabla\!\cdot {\lambda y b c \mapsto a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({y})\,b\,c}})_{{\nu}}({x}) = 0
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`sub`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sub), [`add`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-add), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`PdiffAt_pd`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-pd), [`kgKinetic`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgkinetic), [`kgLagr`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kglagr), [`kg_conserv`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-kg-conserv). $\square$

<small>Used by [`qiqt_gr_explicit_kg`](/browser/qiqth-qiqtgrexplicitkg#d-qiqth-wedgekmstogr-qiqt-gr-explicit-kg), [`qiqt_gr_freefield`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

---
<small>[← all sections](/browser) · [← HregExplicitKG](/browser/qiqth-hregexplicitkg) · [KMSCorrelation →](/browser/qiqth-kmscorrelation) </small>