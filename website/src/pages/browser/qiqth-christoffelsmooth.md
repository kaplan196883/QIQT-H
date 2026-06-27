---
layout: ../../layouts/Deep.astro
title: QIQTH.ChristoffelSmooth
eyebrow: ChristoffelSmooth · section of the QIQT-H book
description: QIQTH.ChristoffelSmooth — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← BranchLedger](/browser/qiqth-branchledger) · [ClausiusFiniteWitness →](/browser/qiqth-clausiusfinitewitness) </small>

<small>ChristoffelSmooth · entries 6–10 of 1000</small>

<a id="d-qiqth-curvature-contdiff-pd"></a>
**Lemma 6** (`contDiff_pd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L20)</small>

**The partial derivative of a `C^∞` scalar is `C^∞`.**  `pd f i = (fun y => fderiv ℝ f y (Pi.single i 1))` (`pd_eq_fderiv`, valid everywhere since `f` is differentiable), and `y ↦ fderiv ℝ f y` is `C^∞` (`ContDiff.fderiv_right`), so applying it to the constant basis covector `e_i` (`ContDiff.clm_apply`) is `C^∞`.

$$
({f})\in C^{\infty} \to \forall (i : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{i}}({f})({y})}})\in C^{\infty}
$$

*Proof.* By [`pd_eq_fderiv`](/browser/qiqth-curvature#d-qiqth-curvature-pd-eq-fderiv). $\square$

<small>Used by [`christoffel_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-christoffel-contdiff), [`riemann_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-riemann-contdiff), [`kgLagr_contDiff`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-kglagr-contdiff), [`kgStress_contDiff`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-kgstress-contdiff).</small>

<a id="d-qiqth-curvature-christoffel-contdiff"></a>
**Lemma 7** (`christoffel_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L31)</small>

** Christoffel symbols are `C^∞`** — discharges `hC`.  `christoffel g gi μ ν ρ = ½·∑α gi_{μα}(∂_ν g_{αρ} + ∂_ρ g_{αν} − ∂_α g_{νρ})` is a finite sum of products of `gi` (`C^∞` by `hCgi`) and partial derivatives of `g` (`C^∞` by `contDiff_pd` + `hCg`).

$$
(\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\mu \nu \rho : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\mu}}_{{\nu}{\rho}}({y})}})\in C^{\infty}
$$

*Proof.* By [`contDiff_pd`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-contdiff-pd), [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd). $\square$

<small>Used by [`riemann_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-riemann-contdiff), [`qiqt_gr_freefield_localized'`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [`qiqt_bekenstein_gives_gr`](/browser/qiqth-qiqttogr#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr).</small>

<a id="d-qiqth-curvature-riemann-contdiff"></a>
**Lemma 8** (`riemann_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L45)</small>

**The Riemann tensor is `C^∞`** — `R^ρ_{σμν} = ∂_μΓ^ρ_{νσ} − ∂_νΓ^ρ_{μσ} + Σ_l(Γ^ρ_{μl}Γ^l_{νσ} − Γ^ρ_{νl}Γ^l_{μσ})` is a finite combination of `∂Γ` (`contDiff_pd` ∘ `christoffel_contDiff`) and `ΓΓ`.

$$
(\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\rho \sigma \mu \nu : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,y})\in C^{\infty}
$$

*Proof.* By [`contDiff_pd`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-contdiff-pd), [`christoffel_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-christoffel-contdiff), [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel). $\square$

<small>Used by [`ricci_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-ricci-contdiff).</small>

<a id="d-qiqth-curvature-ricci-contdiff"></a>
**Lemma 9** (`ricci_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L59)</small>

**The Ricci tensor is `C^∞`** — `R_{σν} = ∑μ R^μ_{σμν}` (sum of `C^∞` Riemann components).

$$
(\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\sigma \nu : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({y})}})\in C^{\infty}
$$

*Proof.* By [`riemann_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-riemann-contdiff), [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann). $\square$

<small>Used by [`scalarCurv_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-scalarcurv-contdiff).</small>

<a id="d-qiqth-curvature-scalarcurv-contdiff"></a>
**Lemma 10** (`scalarCurv_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L68)</small>

**The scalar curvature is `C^∞`** — `R = ∑_{σν} g^{σν} R_{σν}` (a finite combination of `C^∞` `gi` and `C^∞` Ricci).  Feeds the `hreg` regularity input of the QIQT→GR capstone (Tier A4).

$$
(\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({y})}})\in C^{\infty}
$$

*Proof.* By [`ricci_contDiff`](/browser/qiqth-christoffelsmooth#d-qiqth-curvature-ricci-contdiff), [`ricci`](/browser/qiqth-curvature#d-qiqth-curvature-ricci). $\square$

<small>Used by [`hreg_kg`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-hreg-kg).</small>

---
<small>[← all sections](/browser) · [← BranchLedger](/browser/qiqth-branchledger) · [ClausiusFiniteWitness →](/browser/qiqth-clausiusfinitewitness) </small>