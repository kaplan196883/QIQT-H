---
layout: ../layouts/Deep.astro
title: The development as a book
eyebrow: Definitions · theorems · lemmas · proofs
description: The QIQT-H Lean development presented as a hyperlinked math book — definitions, theorems and lemmas in printed math, each proof citing the lemmas it uses, all linked down to the Lean source.
---

The Lean development, presented as a **hyperlinked math book**. It is organized into sections (one
per Lean module, in dependency order); each entry is a numbered **Definition**, **Theorem** or
**Lemma**, typeset in printed math (free variables are implicitly universally quantified). Every
**Proof** cites the lemmas it rests on — click a citation to jump to that result, read it, and
follow *its* proof deeper; symbols inside the formulas link to their definitions; and a *source ↗*
link on each entry opens the exact Lean line. Regenerate with `scripts/gen_browser_page.py`.

## Contents

- [QIQTH.BranchLedger](#sec-qiqth-branchledger)
- [QIQTH.ChristoffelSmooth](#sec-qiqth-christoffelsmooth)
- [QIQTH.ClausiusFiniteWitness](#sec-qiqth-clausiusfinitewitness)
- [QIQTH.ClausiusToPernull](#sec-qiqth-clausiustopernull)
- [QIQTH.Curvature](#sec-qiqth-curvature)
- [QIQTH.DifferentialAreaLaw](#sec-qiqth-differentialarealaw)
- [QIQTH.EinsteinEquationOfState](#sec-qiqth-einsteinequationofstate)
- [QIQTH.EinsteinFieldEquation](#sec-qiqth-einsteinfieldequation)
- [QIQTH.Fock.BoostKMS](#sec-qiqth-fock-boostkms)
- [QIQTH.Fock.CyclicWitness](#sec-qiqth-fock-cyclicwitness)
- [QIQTH.Fock.FreeFieldHFlux](#sec-qiqth-fock-freefieldhflux)
- [QIQTH.Fock.Localization](#sec-qiqth-fock-localization)
- [QIQTH.Fock.OneParticle](#sec-qiqth-fock-oneparticle)
- [QIQTH.Fock.OneParticleBW](#sec-qiqth-fock-oneparticlebw)
- [QIQTH.Fock.SchwartzDecay](#sec-qiqth-fock-schwartzdecay)
- [QIQTH.Fock.WedgeAnalyticity](#sec-qiqth-fock-wedgeanalyticity)
- [QIQTH.Fock.WienerL2](#sec-qiqth-fock-wienerl2)
- [QIQTH.HregExplicitKG](#sec-qiqth-hregexplicitkg)
- [QIQTH.KGStressConservation](#sec-qiqth-kgstressconservation)
- [QIQTH.KMSCorrelation](#sec-qiqth-kmscorrelation)
- [QIQTH.ModularRelativeEntropy](#sec-qiqth-modularrelativeentropy)
- [QIQTH.QiqtGrComplete](#sec-qiqth-qiqtgrcomplete)
- [QIQTH.QiqtGrFreeField](#sec-qiqth-qiqtgrfreefield)
- [QIQTH.QiqtGrThermo](#sec-qiqth-qiqtgrthermo)
- [QIQTH.QiqtToGR](#sec-qiqth-qiqttogr)
- [QIQTH.Raychaudhuri](#sec-qiqth-raychaudhuri)
- [QIQTH.RecordContract](#sec-qiqth-recordcontract)
- [QIQTH.RelEntPositivity](#sec-qiqth-relentpositivity)
- [QIQTH.RicciSymm](#sec-qiqth-riccisymm)
- [QIQTH.Spectral.PVM](#sec-qiqth-spectral-pvm)
- [QIQTH.Spectral.SpectralTheorem](#sec-qiqth-spectral-spectraltheorem)
- [QIQTH.StandardSubspaceModular](#sec-qiqth-standardsubspacemodular)
- [QIQTH.StandardSubspaceModularFlow](#sec-qiqth-standardsubspacemodularflow)
- [QIQTH.StripUniqueness](#sec-qiqth-stripuniqueness)
- [QIQTH.WedgeKMSToGR](#sec-qiqth-wedgekmstogr)

<a id="sec-qiqth-branchledger"></a>
## QIQTH.BranchLedger

<a id="d-qiqth-branchledger-shannon"></a>
**Definition 1** (`Shannon`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/BranchLedger.lean#L39)</small>

A definition — see source for the body.

<small>Referenced in [Lem 7](#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model), [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Lem 498](#d-qiqth-recordcontract-shannon-eq-sum-negmullog), [Lem 499](#d-qiqth-recordcontract-shannon-le-log-card), [Lem 500](#d-qiqth-recordcontract-shannon-uniform-eq-log-card).</small>

<a id="sec-qiqth-christoffelsmooth"></a>
## QIQTH.ChristoffelSmooth

<a id="d-qiqth-curvature-contdiff-pd"></a>
**Lemma 2** (`contDiff_pd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L20)</small>

$$
({f})\in C^{\infty} \to \forall (i : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-pd}{\partial_{{i}}({f})({y})}})\in C^{\infty}
$$

*Proof.* By [Lem 23](#d-qiqth-curvature-pd-eq-fderiv). $\square$

<small>Referenced in [Lem 3](#d-qiqth-curvature-christoffel-contdiff), [Lem 4](#d-qiqth-curvature-riemann-contdiff), [Lem 404](#d-qiqth-curvature-kglagr-contdiff), [Lem 405](#d-qiqth-curvature-kgstress-contdiff).</small>

<a id="d-qiqth-curvature-christoffel-contdiff"></a>
**Lemma 3** (`christoffel_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L31)</small>

$$
(\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\mu \nu \rho : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\mu}}_{{\nu}{\rho}}({y})}})\in C^{\infty}
$$

*Proof.* By [Lem 2](#d-qiqth-curvature-contdiff-pd), [Def 10](#d-qiqth-curvature-pd). $\square$

<small>Referenced in [Lem 4](#d-qiqth-curvature-riemann-contdiff), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr).</small>

<a id="d-qiqth-curvature-riemann-contdiff"></a>
**Lemma 4** (`riemann_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L45)</small>

$$
(\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\rho \sigma \mu \nu : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,y})\in C^{\infty}
$$

*Proof.* By [Lem 2](#d-qiqth-curvature-contdiff-pd), [Lem 3](#d-qiqth-curvature-christoffel-contdiff), [Def 10](#d-qiqth-curvature-pd), [Def 27](#d-qiqth-curvature-christoffel). $\square$

<small>Referenced in [Lem 5](#d-qiqth-curvature-ricci-contdiff).</small>

<a id="d-qiqth-curvature-ricci-contdiff"></a>
**Lemma 5** (`ricci_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L59)</small>

$$
(\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\sigma \nu : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({y})}})\in C^{\infty}
$$

*Proof.* By [Lem 4](#d-qiqth-curvature-riemann-contdiff), [Def 29](#d-qiqth-curvature-riemann). $\square$

<small>Referenced in [Lem 6](#d-qiqth-curvature-scalarcurv-contdiff).</small>

<a id="d-qiqth-curvature-scalarcurv-contdiff"></a>
**Lemma 6** (`scalarCurv_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ChristoffelSmooth.lean#L68)</small>

$$
(\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to ({\lambda y \mapsto \href{#d-qiqth-curvature-scalarcurv}{R({y})}})\in C^{\infty}
$$

*Proof.* By [Lem 5](#d-qiqth-curvature-ricci-contdiff), [Def 31](#d-qiqth-curvature-ricci). $\square$

<small>Referenced in [Lem 406](#d-qiqth-curvature-hreg-kg).</small>

<a id="sec-qiqth-clausiusfinitewitness"></a>
## QIQTH.ClausiusFiniteWitness

<a id="d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model"></a>
**Lemma 7** (`clausius_package_from_finite_model`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ClausiusFiniteWitness.lean#L29)</small>

$$
(\forall (t : \mathbb{R}) (r : R), 0 \le p\,t\,r) \to (\forall (t : \mathbb{R}), \sum_{r} p\,t\,r = 1) \to (p\,0 = \lambda x \mapsto {((\#\,R))}^{-1}) \to \eta \cdot \mathrm{Acap} = \log\,(\#\,R) \to (\text{for }t\text{ near }0,\; \href{#d-qiqth-branchledger-shannon}{S({p\,t})} \le \eta \cdot \mathrm{Acap}) \wedge \href{#d-qiqth-branchledger-shannon}{S({p\,0})} = \eta \cdot \mathrm{Acap} \wedge (\forall (t : \mathbb{R}), 0 \le \href{#d-qiqth-branchledger-shannon}{S({p\,t})} + \href{#d-qiqth-relentpositivity-kl}{D_{\mathrm{KL}}({p\,t}\,\|\,{p\,0})} - \href{#d-qiqth-branchledger-shannon}{S({p\,t})}) \wedge \href{#d-qiqth-branchledger-shannon}{S({p\,0})} + \href{#d-qiqth-relentpositivity-kl}{D_{\mathrm{KL}}({p\,0}\,\|\,{p\,0})} - \href{#d-qiqth-branchledger-shannon}{S({p\,0})} = 0
$$

*Proof.* By [Lem 499](#d-qiqth-recordcontract-shannon-le-log-card), [Lem 500](#d-qiqth-recordcontract-shannon-uniform-eq-log-card), [Lem 502](#d-qiqth-relentpositivity-kl-classical-nonneg). $\square$

<small>Referenced in [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo).</small>

<a id="sec-qiqth-clausiustopernull"></a>
## QIQTH.ClausiusToPernull

<a id="d-qiqth-curvature-bl-smul-sub"></a>
**Lemma 8** (`BL_smul_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ClausiusToPernull.lean#L35)</small>

$$
\href{#d-qiqth-einsteineos-bl}{({\lambda i j \mapsto a \cdot T\,i\,j - R\,i\,j})({v},{v})} = a \cdot \href{#d-qiqth-einsteineos-bl}{({T})({v},{v})} - \href{#d-qiqth-einsteineos-bl}{({R})({v},{v})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 484](#d-qiqth-qiqttogr-bl-pernull-of-modular).</small>

<a id="sec-qiqth-curvature"></a>
## QIQTH.Curvature

<a id="d-qiqth-curvature-point"></a>
**Definition 9** (`Point`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L26)</small>

A definition — see source for the body.

<small>Referenced in [Lem 2](#d-qiqth-curvature-contdiff-pd), [Lem 3](#d-qiqth-curvature-christoffel-contdiff), [Lem 4](#d-qiqth-curvature-riemann-contdiff), [Lem 5](#d-qiqth-curvature-ricci-contdiff), [Lem 6](#d-qiqth-curvature-scalarcurv-contdiff), [Def 10](#d-qiqth-curvature-pd), [Def 11](#d-qiqth-curvature-pdiffat), [Lem 12](#d-qiqth-curvature-pd-add), [Lem 13](#d-qiqth-curvature-pd-sub), [Lem 14](#d-qiqth-curvature-pd-const-mul), [Lem 15](#d-qiqth-curvature-pd-const), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 18](#d-qiqth-curvature-pdiffat-sub), [Lem 19](#d-qiqth-curvature-pdiffat-add), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Lem 23](#d-qiqth-curvature-pd-eq-fderiv), [Lem 24](#d-qiqth-curvature-pd-pd-eq), [Lem 25](#d-qiqth-curvature-pd-comm), [Lem 26](#d-qiqth-curvature-pdiffat-pd), [Def 27](#d-qiqth-curvature-christoffel), [Lem 28](#d-qiqth-curvature-christoffel-symm), [Def 29](#d-qiqth-curvature-riemann), [Lem 30](#d-qiqth-curvature-riemann-antisymm), [Def 31](#d-qiqth-curvature-ricci), [Def 32](#d-qiqth-curvature-scalarcurv), [Def 33](#d-qiqth-curvature-einsteintensor), [Def 34](#d-qiqth-curvature-covderivvec), [Def 35](#d-qiqth-curvature-covderiv02), [Def 36](#d-qiqth-curvature-covderiv20), [Lem 37](#d-qiqth-curvature-inv-contract), [Lem 38](#d-qiqth-curvature-christoffel-lower), [Lem 39](#d-qiqth-curvature-metric-compat), [Lem 40](#d-qiqth-curvature-riemann-first-bianchi), [Def 41](#d-qiqth-curvature-riemannlin), [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 43](#d-qiqth-curvature-bianchi-extra-terms), [Def 44](#d-qiqth-curvature-riemannquad), [Lem 45](#d-qiqth-curvature-bianchi-ggg), [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 47](#d-qiqth-curvature-bianchi-dgamma), [Def 48](#d-qiqth-curvature-covderivriem), [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 52](#d-qiqth-curvature-covderivriem-antisymm), [Lem 53](#d-qiqth-curvature-covderivriem-contract), [Lem 54](#d-qiqth-curvature-second-bianchi-contracted), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 58](#d-qiqth-curvature-lowered-riemann-gi-trace), [Lem 59](#d-qiqth-curvature-ricci-gi-raise), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 64](#d-qiqth-curvature-const-of-pd-zero), [Def 74](#d-qiqth-curvature-div02), [Lem 75](#d-qiqth-curvature-div02-add), [Lem 76](#d-qiqth-curvature-div02-scalar-metric), [Lem 77](#d-qiqth-curvature-divriemann-trace-eq), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi), [Lem 79](#d-qiqth-curvature-metric-contraction-trace), [Lem 80](#d-qiqth-curvature-einstein-field-equation), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 83](#d-qiqth-curvature-crux-of-pernull), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Lem 404](#d-qiqth-curvature-kglagr-contdiff), [Lem 405](#d-qiqth-curvature-kgstress-contdiff), [Lem 406](#d-qiqth-curvature-hreg-kg), [Def 407](#d-qiqth-curvature-kglagr), [Def 408](#d-qiqth-curvature-kgstress), [Def 409](#d-qiqth-curvature-kghess), [Def 410](#d-qiqth-curvature-boxfield), [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Lem 475](#d-qiqth-wedgekmstogr-bl-kgstress-null), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Def 487](#d-qiqth-curvature-covderiv2vec), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 489](#d-qiqth-curvature-ricci-identity), [Lem 490](#d-qiqth-curvature-ricci-identity-contracted), [Def 491](#d-qiqth-curvature-expansion), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz), [Lem 495](#d-qiqth-curvature-geodesic-leibniz), [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic), [Lem 497](#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium), [Lem 503](#d-qiqth-curvature-lowered-riemann-pair-symm), [Lem 504](#d-qiqth-curvature-ricci-symm), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="d-qiqth-curvature-pd"></a>
**Definition 10** (`pd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L29)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 2](#d-qiqth-curvature-contdiff-pd), [Lem 3](#d-qiqth-curvature-christoffel-contdiff), [Lem 4](#d-qiqth-curvature-riemann-contdiff), [Lem 12](#d-qiqth-curvature-pd-add), [Lem 13](#d-qiqth-curvature-pd-sub), [Lem 14](#d-qiqth-curvature-pd-const-mul), [Lem 15](#d-qiqth-curvature-pd-const), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Lem 23](#d-qiqth-curvature-pd-eq-fderiv), [Lem 24](#d-qiqth-curvature-pd-pd-eq), [Lem 25](#d-qiqth-curvature-pd-comm), [Lem 26](#d-qiqth-curvature-pdiffat-pd), [Def 27](#d-qiqth-curvature-christoffel), [Lem 28](#d-qiqth-curvature-christoffel-symm), [Def 29](#d-qiqth-curvature-riemann), [Lem 30](#d-qiqth-curvature-riemann-antisymm), [Def 34](#d-qiqth-curvature-covderivvec), [Def 35](#d-qiqth-curvature-covderiv02), [Def 36](#d-qiqth-curvature-covderiv20), [Lem 38](#d-qiqth-curvature-christoffel-lower), [Lem 39](#d-qiqth-curvature-metric-compat), [Lem 40](#d-qiqth-curvature-riemann-first-bianchi), [Def 41](#d-qiqth-curvature-riemannlin), [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 47](#d-qiqth-curvature-bianchi-dgamma), [Def 48](#d-qiqth-curvature-covderivriem), [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 52](#d-qiqth-curvature-covderivriem-antisymm), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 64](#d-qiqth-curvature-const-of-pd-zero), [Lem 75](#d-qiqth-curvature-div02-add), [Lem 76](#d-qiqth-curvature-div02-scalar-metric), [Lem 77](#d-qiqth-curvature-divriemann-trace-eq), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi), [Lem 80](#d-qiqth-curvature-einstein-field-equation), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 404](#d-qiqth-curvature-kglagr-contdiff), [Lem 405](#d-qiqth-curvature-kgstress-contdiff), [Def 407](#d-qiqth-curvature-kglagr), [Def 408](#d-qiqth-curvature-kgstress), [Def 409](#d-qiqth-curvature-kghess), [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Lem 475](#d-qiqth-wedgekmstogr-bl-kgstress-null), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri), [Def 487](#d-qiqth-curvature-covderiv2vec), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 489](#d-qiqth-curvature-ricci-identity), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz), [Lem 495](#d-qiqth-curvature-geodesic-leibniz), [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic), [Lem 497](#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium).</small>

<a id="d-qiqth-curvature-pdiffat"></a>
**Definition 11** (`PdiffAt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L33)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 12](#d-qiqth-curvature-pd-add), [Lem 13](#d-qiqth-curvature-pd-sub), [Lem 14](#d-qiqth-curvature-pd-const-mul), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 18](#d-qiqth-curvature-pdiffat-sub), [Lem 19](#d-qiqth-curvature-pdiffat-add), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Lem 26](#d-qiqth-curvature-pdiffat-pd), [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 75](#d-qiqth-curvature-div02-add), [Lem 76](#d-qiqth-curvature-div02-scalar-metric), [Lem 80](#d-qiqth-curvature-einstein-field-equation), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Lem 406](#d-qiqth-curvature-hreg-kg), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="d-qiqth-curvature-pd-add"></a>
**Lemma 12** (`pd_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L38)</small>

$$
\href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto f\,y + g\,y})({x})} = \href{#d-qiqth-curvature-pd}{\partial_{{i}}({f})({x})} + \href{#d-qiqth-curvature-pd}{\partial_{{i}}({g})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 75](#d-qiqth-curvature-div02-add), [Lem 80](#d-qiqth-curvature-einstein-field-equation), [Lem 488](#d-qiqth-curvature-pd-covderivvec).</small>

<a id="d-qiqth-curvature-pd-sub"></a>
**Lemma 13** (`pd_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L44)</small>

$$
\href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto f\,y - g\,y})({x})} = \href{#d-qiqth-curvature-pd}{\partial_{{i}}({f})({x})} - \href{#d-qiqth-curvature-pd}{\partial_{{i}}({g})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 46](#d-qiqth-curvature-pd-riemannquad).</small>

<a id="d-qiqth-curvature-pd-const-mul"></a>
**Lemma 14** (`pd_const_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L50)</small>

$$
\href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto c \cdot f\,y})({x})} = c \cdot \href{#d-qiqth-curvature-pd}{\partial_{{i}}({f})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 52](#d-qiqth-curvature-covderivriem-antisymm), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 80](#d-qiqth-curvature-einstein-field-equation).</small>

<a id="d-qiqth-curvature-pd-const"></a>
**Lemma 15** (`pd_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L56)</small>

$$
\href{#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda x \mapsto c})({x})} = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-pdiffat-of-contdiff"></a>
**Lemma 16** (`PdiffAt_of_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L60)</small>

$$
({f})\in C^{\infty} \to \forall (i : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 406](#d-qiqth-curvature-hreg-kg), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-pdiffat-mul"></a>
**Lemma 17** (`mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L67)</small>

$$
\href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto f\,y \cdot g\,y)\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 80](#d-qiqth-curvature-einstein-field-equation), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-pdiffat-sub"></a>
**Lemma 18** (`sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L72)</small>

$$
\href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto f\,y - g\,y)\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann).</small>

<a id="d-qiqth-curvature-pdiffat-add"></a>
**Lemma 19** (`add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L77)</small>

$$
\href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto f\,y + g\,y)\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-pdiffat-sum"></a>
**Lemma 20** (`PdiffAt_sum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L82)</small>

$$
(\forall k\in s, \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(F\,k)\,i\,x) \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \sum_{k s} F\,k\,y)\,i\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-pd-sum"></a>
**Lemma 21** (`pd_sum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L87)</small>

$$
(\forall k\in s, \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(F\,k)\,i\,x) \to \href{#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto \sum_{k s} F\,k\,y})({x})} = \sum_{k s} \href{#d-qiqth-curvature-pd}{\partial_{{i}}({F\,k})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-pd-mul"></a>
**Lemma 22** (`pd_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L94)</small>

$$
\href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,i\,x \to \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,g\,i\,x \to \href{#d-qiqth-curvature-pd}{\partial_{{i}}({\lambda y \mapsto f\,y \cdot g\,y})({x})} = \href{#d-qiqth-curvature-pd}{\partial_{{i}}({f})({x})} \cdot g\,x + f\,x \cdot \href{#d-qiqth-curvature-pd}{\partial_{{i}}({g})({x})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 76](#d-qiqth-curvature-div02-scalar-metric), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-pd-eq-fderiv"></a>
**Lemma 23** (`pd_eq_fderiv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L102)</small>

$$
\mathrm{DifferentiableAt}\,\mathbb{R}\,g\,x \to \href{#d-qiqth-curvature-pd}{\partial_{{i}}({g})({x})} = (\mathrm{fderiv}\,\mathbb{R}\,g\,x)\,(\mathrm{single}\,i\,1)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 2](#d-qiqth-curvature-contdiff-pd), [Lem 24](#d-qiqth-curvature-pd-pd-eq), [Lem 26](#d-qiqth-curvature-pdiffat-pd), [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 64](#d-qiqth-curvature-const-of-pd-zero).</small>

<a id="d-qiqth-curvature-pd-pd-eq"></a>
**Lemma 24** (`pd_pd_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L112)</small>

$$
({f})\in C^{\infty} \to \partial_{{i}}({\lambda y \mapsto \href{#d-qiqth-curvature-pd}{\partial_{{j}}({f})({y})}})({x}) = ((\mathrm{fderiv}\,\mathbb{R}\,(\mathrm{fderiv}\,\mathbb{R}\,f)\,x)\,(\mathrm{single}\,i\,1))\,(\mathrm{single}\,j\,1)
$$

*Proof.* By [Lem 23](#d-qiqth-curvature-pd-eq-fderiv). $\square$

<small>Referenced in [Lem 25](#d-qiqth-curvature-pd-comm).</small>

<a id="d-qiqth-curvature-pd-comm"></a>
**Lemma 25** (`pd_comm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L125)</small>

$$
({f})\in C^{\infty} \to \partial_{{i}}({\lambda y \mapsto \href{#d-qiqth-curvature-pd}{\partial_{{j}}({f})({y})}})({x}) = \partial_{{j}}({\lambda y \mapsto \href{#d-qiqth-curvature-pd}{\partial_{{i}}({f})({y})}})({x})
$$

*Proof.* By [Lem 24](#d-qiqth-curvature-pd-pd-eq). $\square$

<small>Referenced in [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 489](#d-qiqth-curvature-ricci-identity).</small>

<a id="d-qiqth-curvature-pdiffat-pd"></a>
**Lemma 26** (`PdiffAt_pd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L132)</small>

$$
({f})\in C^{\infty} \to \forall (d e : \mathrm{Fin}\,n) (z : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{#d-qiqth-curvature-pd}{\partial_{{d}}({f})({y})})\,e\,z
$$

*Proof.* By [Lem 23](#d-qiqth-curvature-pd-eq-fderiv). $\square$

<small>Referenced in [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz).</small>

<a id="d-qiqth-curvature-christoffel"></a>
**Definition 27** (`christoffel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L147)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 3](#d-qiqth-curvature-christoffel-contdiff), [Lem 4](#d-qiqth-curvature-riemann-contdiff), [Lem 28](#d-qiqth-curvature-christoffel-symm), [Def 29](#d-qiqth-curvature-riemann), [Lem 30](#d-qiqth-curvature-riemann-antisymm), [Def 34](#d-qiqth-curvature-covderivvec), [Def 35](#d-qiqth-curvature-covderiv02), [Def 36](#d-qiqth-curvature-covderiv20), [Lem 38](#d-qiqth-curvature-christoffel-lower), [Lem 39](#d-qiqth-curvature-metric-compat), [Lem 40](#d-qiqth-curvature-riemann-first-bianchi), [Def 41](#d-qiqth-curvature-riemannlin), [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 43](#d-qiqth-curvature-bianchi-extra-terms), [Def 44](#d-qiqth-curvature-riemannquad), [Lem 45](#d-qiqth-curvature-bianchi-ggg), [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 47](#d-qiqth-curvature-bianchi-dgamma), [Def 48](#d-qiqth-curvature-covderivriem), [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 52](#d-qiqth-curvature-covderivriem-antisymm), [Lem 53](#d-qiqth-curvature-covderivriem-contract), [Lem 54](#d-qiqth-curvature-second-bianchi-contracted), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 58](#d-qiqth-curvature-lowered-riemann-gi-trace), [Lem 59](#d-qiqth-curvature-ricci-gi-raise), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 75](#d-qiqth-curvature-div02-add), [Lem 76](#d-qiqth-curvature-div02-scalar-metric), [Lem 77](#d-qiqth-curvature-divriemann-trace-eq), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Def 409](#d-qiqth-curvature-kghess), [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Def 487](#d-qiqth-curvature-covderiv2vec), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 489](#d-qiqth-curvature-ricci-identity), [Lem 490](#d-qiqth-curvature-ricci-identity-contracted), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz), [Lem 495](#d-qiqth-curvature-geodesic-leibniz), [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic), [Lem 497](#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium), [Lem 503](#d-qiqth-curvature-lowered-riemann-pair-symm), [Lem 504](#d-qiqth-curvature-ricci-symm).</small>

<a id="d-qiqth-curvature-christoffel-symm"></a>
**Lemma 28** (`christoffel_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L153)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (\mu \nu \rho : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\mu}}_{{\nu}{\rho}}({x})} = \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\mu}}_{{\rho}{\nu}}({x})}
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd). $\square$

<small>Referenced in [Lem 40](#d-qiqth-curvature-riemann-first-bianchi), [Lem 43](#d-qiqth-curvature-bianchi-extra-terms), [Lem 489](#d-qiqth-curvature-ricci-identity).</small>

<a id="d-qiqth-curvature-riemann"></a>
**Definition 29** (`riemann`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L197)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 4](#d-qiqth-curvature-riemann-contdiff), [Lem 5](#d-qiqth-curvature-ricci-contdiff), [Lem 30](#d-qiqth-curvature-riemann-antisymm), [Def 31](#d-qiqth-curvature-ricci), [Lem 40](#d-qiqth-curvature-riemann-first-bianchi), [Lem 43](#d-qiqth-curvature-bianchi-extra-terms), [Def 48](#d-qiqth-curvature-covderivriem), [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 52](#d-qiqth-curvature-covderivriem-antisymm), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 58](#d-qiqth-curvature-lowered-riemann-gi-trace), [Lem 59](#d-qiqth-curvature-ricci-gi-raise), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 489](#d-qiqth-curvature-ricci-identity), [Lem 490](#d-qiqth-curvature-ricci-identity-contracted), [Lem 503](#d-qiqth-curvature-lowered-riemann-pair-symm), [Lem 504](#d-qiqth-curvature-ricci-symm).</small>

<a id="d-qiqth-curvature-riemann-antisymm"></a>
**Lemma 30** (`riemann_antisymm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L205)</small>

$$
\href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,x = -\href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\mu\,x
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Def 27](#d-qiqth-curvature-christoffel). $\square$

<small>Referenced in [Lem 43](#d-qiqth-curvature-bianchi-extra-terms), [Lem 52](#d-qiqth-curvature-covderivriem-antisymm), [Lem 503](#d-qiqth-curvature-lowered-riemann-pair-symm).</small>

<a id="d-qiqth-curvature-ricci"></a>
**Definition 31** (`ricci`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L227)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 5](#d-qiqth-curvature-ricci-contdiff), [Lem 6](#d-qiqth-curvature-scalarcurv-contdiff), [Def 32](#d-qiqth-curvature-scalarcurv), [Def 33](#d-qiqth-curvature-einsteintensor), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 53](#d-qiqth-curvature-covderivriem-contract), [Lem 54](#d-qiqth-curvature-second-bianchi-contracted), [Lem 58](#d-qiqth-curvature-lowered-riemann-gi-trace), [Lem 59](#d-qiqth-curvature-ricci-gi-raise), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 77](#d-qiqth-curvature-divriemann-trace-eq), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 83](#d-qiqth-curvature-crux-of-pernull), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Lem 406](#d-qiqth-curvature-hreg-kg), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Lem 490](#d-qiqth-curvature-ricci-identity-contracted), [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing), [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic), [Lem 497](#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium), [Lem 504](#d-qiqth-curvature-ricci-symm), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="d-qiqth-curvature-scalarcurv"></a>
**Definition 32** (`scalarCurv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L231)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 6](#d-qiqth-curvature-scalarcurv-contdiff), [Def 33](#d-qiqth-curvature-einsteintensor), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Lem 406](#d-qiqth-curvature-hreg-kg), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="d-qiqth-curvature-einsteintensor"></a>
**Definition 33** (`einsteinTensor`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L235)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="d-qiqth-curvature-covderivvec"></a>
**Definition 34** (`covDerivVec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L242)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri), [Def 487](#d-qiqth-curvature-covderiv2vec), [Lem 488](#d-qiqth-curvature-pd-covderivvec), [Lem 489](#d-qiqth-curvature-ricci-identity), [Def 491](#d-qiqth-curvature-expansion), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz), [Lem 495](#d-qiqth-curvature-geodesic-leibniz), [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic), [Lem 497](#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium).</small>

<a id="d-qiqth-curvature-covderiv02"></a>
**Definition 35** (`covDeriv02`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L252)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 39](#d-qiqth-curvature-metric-compat), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 53](#d-qiqth-curvature-covderivriem-contract), [Lem 54](#d-qiqth-curvature-second-bianchi-contracted), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Def 74](#d-qiqth-curvature-div02), [Lem 75](#d-qiqth-curvature-div02-add), [Lem 76](#d-qiqth-curvature-div02-scalar-metric), [Lem 77](#d-qiqth-curvature-divriemann-trace-eq), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi).</small>

<a id="d-qiqth-curvature-covderiv20"></a>
**Definition 36** (`covDeriv20`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L260)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci).</small>

<a id="d-qiqth-curvature-inv-contract"></a>
**Lemma 37** (`inv_contract`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L286)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), (\forall (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({x}) \cdot g^{{\sigma}{b}}({x}) = \delta_{ab}) \to \forall (\nu : \mathrm{Fin}\,n) (w : \mathrm{Fin}\,n \to \mathbb{R}), \sum_{\sigma} g_{{\sigma}{\nu}}({x}) \cdot \sum_{\alpha} g^{{\sigma}{\alpha}}({x}) \cdot w\,\alpha = w\,\nu
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 38](#d-qiqth-curvature-christoffel-lower).</small>

<a id="d-qiqth-curvature-christoffel-lower"></a>
**Lemma 38** (`christoffel_lower`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L310)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), (\forall (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({x}) \cdot g^{{\sigma}{b}}({x}) = \delta_{ab}) \to \forall (\nu \mathrm{lam} \mathrm{mu} : \mathrm{Fin}\,n), \sum_{\sigma} g_{{\sigma}{\nu}}({x}) \cdot \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\sigma}}_{{\mathrm{lam}}{\mathrm{mu}}}({x})} = 1/2 \cdot (\href{#d-qiqth-curvature-pd}{\partial_{{\mathrm{lam}}}({\lambda y \mapsto g_{{\nu}{\mathrm{mu}}}({y})})({x})} + \href{#d-qiqth-curvature-pd}{\partial_{{\mathrm{mu}}}({\lambda y \mapsto g_{{\nu}{\mathrm{lam}}}({y})})({x})} - \href{#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto g_{{\mathrm{lam}}{\mathrm{mu}}}({y})})({x})})
$$

*Proof.* By [Lem 37](#d-qiqth-curvature-inv-contract). $\square$

<small>Referenced in [Lem 39](#d-qiqth-curvature-metric-compat).</small>

<a id="d-qiqth-curvature-metric-compat"></a>
**Lemma 39** (`metric_compat`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L330)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), (\forall (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({x}) \cdot g^{{\sigma}{b}}({x}) = \delta_{ab}) \to \forall (\mathrm{lam} \mathrm{mu} \nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,g\,\mathrm{lam}\,\mathrm{mu}\,\nu\,x = 0
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Def 27](#d-qiqth-curvature-christoffel), [Lem 38](#d-qiqth-curvature-christoffel-lower). $\square$

<small>Referenced in [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm), [Lem 76](#d-qiqth-curvature-div02-scalar-metric).</small>

<a id="d-qiqth-curvature-riemann-first-bianchi"></a>
**Lemma 40** (`riemann_first_bianchi`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L354)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (\rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,x + \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\mu\,\nu\,\sigma\,x + \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\nu\,\sigma\,\mu\,x = 0
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Def 27](#d-qiqth-curvature-christoffel), [Lem 28](#d-qiqth-curvature-christoffel-symm). $\square$

<small>Referenced in [Lem 503](#d-qiqth-curvature-lowered-riemann-pair-symm).</small>

<a id="d-qiqth-curvature-riemannlin"></a>
**Definition 41** (`riemannLin`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L383)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 47](#d-qiqth-curvature-bianchi-dgamma), [Lem 49](#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-second-bianchi-deriv-part"></a>
**Lemma 42** (`second_bianchi_deriv_part`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L389)</small>

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \partial_{{\mathrm{lam}}}({\lambda y \mapsto \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{mu}\,\nu\,y})({x}) + \partial_{{\mathrm{mu}}}({\lambda y \mapsto \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\mathrm{lam}\,y})({x}) + \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{lam}\,\mathrm{mu}\,y})({x}) = 0
$$

*Proof.* By [Def 11](#d-qiqth-curvature-pdiffat), [Lem 13](#d-qiqth-curvature-pd-sub), [Lem 23](#d-qiqth-curvature-pd-eq-fderiv), [Lem 25](#d-qiqth-curvature-pd-comm). $\square$

<small>Referenced in [Lem 49](#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-bianchi-extra-terms"></a>
**Lemma 43** (`bianchi_extra_terms`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L460)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (\rho \sigma \mathrm{lam} \mathrm{mu} \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{lam}}{\mathrm{mu}}}({x})} \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\kappa\,\nu\,x + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{lam}}{\nu}}({x})} \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{mu}\,\kappa\,x + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{mu}}{\nu}}({x})} \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\kappa\,\mathrm{lam}\,x + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{mu}}{\mathrm{lam}}}({x})} \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\kappa\,x + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\mathrm{lam}}}({x})} \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\kappa\,\mathrm{mu}\,x + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\mathrm{mu}}}({x})} \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{lam}\,\kappa\,x = 0
$$

*Proof.* By [Lem 28](#d-qiqth-curvature-christoffel-symm), [Lem 30](#d-qiqth-curvature-riemann-antisymm). $\square$

<small>Referenced in [Lem 49](#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-riemannquad"></a>
**Definition 44** (`riemannQuad`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L481)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 45](#d-qiqth-curvature-bianchi-ggg), [Lem 46](#d-qiqth-curvature-pd-riemannquad), [Lem 47](#d-qiqth-curvature-bianchi-dgamma), [Lem 49](#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-bianchi-ggg"></a>
**Lemma 45** (`bianchi_GGG`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L488)</small>

$$
\sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mathrm{lam}}{\kappa}}({x})} \cdot \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\mathrm{mu}\,\nu\,x - \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{lam}}{\sigma}}({x})} \cdot \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\mathrm{mu}\,\nu\,x + (\sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mathrm{mu}}{\kappa}}({x})} \cdot \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\nu\,\mathrm{lam}\,x - \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{mu}}{\sigma}}({x})} \cdot \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\nu\,\mathrm{lam}\,x) + (\sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\kappa}}({x})} \cdot \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\mathrm{lam}\,\mathrm{mu}\,x - \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\sigma}}({x})} \cdot \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\mathrm{lam}\,\mathrm{mu}\,x) = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 49](#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-pd-riemannquad"></a>
**Lemma 46** (`pd_riemannQuad`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L554)</small>

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} \rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \partial_{{\mathrm{lam}}}({\lambda y \mapsto \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,y})({x}) = \sum_{l} (\partial_{{\mathrm{lam}}}({\lambda w \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mu}{l}}({w})}})({x}) \cdot \href{#d-qiqth-curvature-christoffel}{\Gamma^{{l}}_{{\nu}{\sigma}}({x})} + \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mu}{l}}({x})} \cdot \partial_{{\mathrm{lam}}}({\lambda w \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{l}}_{{\nu}{\sigma}}({w})}})({x}) - \partial_{{\mathrm{lam}}}({\lambda w \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{l}}({w})}})({x}) \cdot \href{#d-qiqth-curvature-christoffel}{\Gamma^{{l}}_{{\mu}{\sigma}}({x})} - \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{l}}({x})} \cdot \partial_{{\mathrm{lam}}}({\lambda w \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{l}}_{{\mu}{\sigma}}({w})}})({x}))
$$

*Proof.* By [Def 11](#d-qiqth-curvature-pdiffat), [Lem 13](#d-qiqth-curvature-pd-sub), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 18](#d-qiqth-curvature-pdiffat-sub), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul). $\square$

<small>Referenced in [Lem 47](#d-qiqth-curvature-bianchi-dgamma).</small>

<a id="d-qiqth-curvature-bianchi-dgamma"></a>
**Lemma 47** (`bianchi_dGamma`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L578)</small>

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \mathrm{lam} \mathrm{mu} \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \partial_{{\mathrm{lam}}}({\lambda y \mapsto \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{mu}\,\nu\,y})({x}) + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mathrm{lam}}{\kappa}}({x})} \cdot \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\mathrm{mu}\,\nu\,x - \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{lam}}{\sigma}}({x})} \cdot \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\mathrm{mu}\,\nu\,x + (\partial_{{\mathrm{mu}}}({\lambda y \mapsto \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\mathrm{lam}\,y})({x}) + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\mathrm{mu}}{\kappa}}({x})} \cdot \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\nu\,\mathrm{lam}\,x - \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mathrm{mu}}{\sigma}}({x})} \cdot \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\nu\,\mathrm{lam}\,x) + (\partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-riemannquad}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mathrm{lam}\,\mathrm{mu}\,y})({x}) + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\kappa}}({x})} \cdot \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\mathrm{lam}\,\mathrm{mu}\,x - \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\sigma}}({x})} \cdot \href{#d-qiqth-curvature-riemannlin}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\kappa\,\mathrm{lam}\,\mathrm{mu}\,x) = 0
$$

*Proof.* By [Lem 46](#d-qiqth-curvature-pd-riemannquad). $\square$

<small>Referenced in [Lem 49](#d-qiqth-curvature-second-bianchi).</small>

<a id="d-qiqth-curvature-covderivriem"></a>
**Definition 48** (`covDerivRiem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L601)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 52](#d-qiqth-curvature-covderivriem-antisymm), [Lem 53](#d-qiqth-curvature-covderivriem-contract), [Lem 54](#d-qiqth-curvature-second-bianchi-contracted), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 77](#d-qiqth-curvature-divriemann-trace-eq), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi).</small>

<a id="d-qiqth-curvature-second-bianchi"></a>
**Lemma 49** (`second_bianchi`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L611)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \mathrm{lam} \mathrm{mu} \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\mathrm{lam}\,\rho\,\sigma\,\mathrm{mu}\,\nu\,x + \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\mathrm{mu}\,\rho\,\sigma\,\nu\,\mathrm{lam}\,x + \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\nu\,\rho\,\sigma\,\mathrm{lam}\,\mathrm{mu}\,x = 0
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Def 11](#d-qiqth-curvature-pdiffat), [Lem 12](#d-qiqth-curvature-pd-add), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 18](#d-qiqth-curvature-pdiffat-sub), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 26](#d-qiqth-curvature-pdiffat-pd), [Def 29](#d-qiqth-curvature-riemann), [Def 41](#d-qiqth-curvature-riemannlin), [Lem 42](#d-qiqth-curvature-second-bianchi-deriv-part), [Lem 43](#d-qiqth-curvature-bianchi-extra-terms), [Def 44](#d-qiqth-curvature-riemannquad), [Lem 45](#d-qiqth-curvature-bianchi-ggg), [Lem 47](#d-qiqth-curvature-bianchi-dgamma). $\square$

<small>Referenced in [Lem 54](#d-qiqth-curvature-second-bianchi-contracted).</small>

<a id="d-qiqth-curvature-pdiffat-riemann"></a>
**Lemma 50** (`PdiffAt_riemann`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L668)</small>

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \mu \nu \mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,y)\,\mathrm{lam}\,x
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 18](#d-qiqth-curvature-pdiffat-sub), [Lem 19](#d-qiqth-curvature-pdiffat-add), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 26](#d-qiqth-curvature-pdiffat-pd). $\square$

<small>Referenced in [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 52](#d-qiqth-curvature-covderivriem-antisymm), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem).</small>

<a id="d-qiqth-curvature-covderivriem-contract"></a>
**Lemma 51** (`covDerivRiem_contract`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L678)</small>

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} \sigma \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\rho} \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\mathrm{lam}\,\rho\,\sigma\,\rho\,\nu\,x = \href{#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\mathrm{lam}\,\sigma\,\nu\,x
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Lem 21](#d-qiqth-curvature-pd-sum), [Def 29](#d-qiqth-curvature-riemann), [Lem 50](#d-qiqth-curvature-pdiffat-riemann). $\square$

<small>Referenced in [Lem 53](#d-qiqth-curvature-covderivriem-contract), [Lem 54](#d-qiqth-curvature-second-bianchi-contracted).</small>

<a id="d-qiqth-curvature-covderivriem-antisymm"></a>
**Lemma 52** (`covDerivRiem_antisymm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L703)</small>

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} \rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\mathrm{lam}\,\rho\,\sigma\,\mu\,\nu\,x + \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\mathrm{lam}\,\rho\,\sigma\,\nu\,\mu\,x = 0
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Lem 14](#d-qiqth-curvature-pd-const-mul), [Def 29](#d-qiqth-curvature-riemann), [Lem 30](#d-qiqth-curvature-riemann-antisymm), [Lem 50](#d-qiqth-curvature-pdiffat-riemann). $\square$

<small>Referenced in [Lem 53](#d-qiqth-curvature-covderivriem-contract).</small>

<a id="d-qiqth-curvature-covderivriem-contract"></a>
**Lemma 53** (`covDerivRiem_contract'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L734)</small>

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{dir} \sigma \mu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\rho} \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\mathrm{dir}\,\rho\,\sigma\,\mu\,\rho\,x = -\href{#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\mathrm{dir}\,\sigma\,\mu\,x
$$

*Proof.* By [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 52](#d-qiqth-curvature-covderivriem-antisymm). $\square$

<small>Referenced in [Lem 54](#d-qiqth-curvature-second-bianchi-contracted).</small>

<a id="d-qiqth-curvature-second-bianchi-contracted"></a>
**Lemma 54** (`second_bianchi_contracted`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L747)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} \sigma \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\mathrm{lam}\,\sigma\,\nu\,x - \href{#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\nu\,\sigma\,\mathrm{lam}\,x + \sum_{\rho} \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\rho\,\sigma\,\nu\,\mathrm{lam}\,x = 0
$$

*Proof.* By [Lem 49](#d-qiqth-curvature-second-bianchi), [Lem 51](#d-qiqth-curvature-covderivriem-contract), [Lem 53](#d-qiqth-curvature-covderivriem-contract). $\square$

<small>Referenced in [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi).</small>

<a id="d-qiqth-curvature-inv-metric-compat"></a>
**Lemma 55** (`inv_metric_compat`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L765)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to \forall (\mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), (\forall (a b : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\mathrm{lam}\,x) \to (\forall (a b : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g^{{a}{b}}({y}))\,\mathrm{lam}\,x) \to \forall (\mu \rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-covderiv20}{\nabla^{2}}\,g\,\mathrm{gi}\,\mathrm{gi}\,\mathrm{lam}\,\mu\,\rho\,x = 0
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Lem 15](#d-qiqth-curvature-pd-const), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Def 27](#d-qiqth-curvature-christoffel), [Def 35](#d-qiqth-curvature-covderiv02), [Lem 39](#d-qiqth-curvature-metric-compat). $\square$

<small>Referenced in [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci).</small>

<a id="d-qiqth-curvature-lowered-riemann-eq"></a>
**Lemma 56** (`lowered_riemann_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L865)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\alpha} g_{{\rho}{\alpha}}({x}) \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,\sigma\,\mu\,\nu\,x = \partial_{{\mu}}({\lambda y \mapsto \sum_{\alpha} g_{{\rho}{\alpha}}({y}) \cdot \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\alpha}}_{{\nu}{\sigma}}({y})}})({x}) - \partial_{{\nu}}({\lambda y \mapsto \sum_{\alpha} g_{{\rho}{\alpha}}({y}) \cdot \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\alpha}}_{{\mu}{\sigma}}({y})}})({x}) - \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\mu}{\rho}}({x})} \cdot \sum_{\alpha} g_{{\alpha}{\kappa}}({x}) \cdot \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\alpha}}_{{\nu}{\sigma}}({x})} + \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\nu}{\rho}}({x})} \cdot \sum_{\alpha} g_{{\alpha}{\kappa}}({x}) \cdot \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\alpha}}_{{\mu}{\sigma}}({x})}
$$

*Proof.* By [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Def 35](#d-qiqth-curvature-covderiv02), [Lem 39](#d-qiqth-curvature-metric-compat). $\square$

<small>Referenced in [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm).</small>

<a id="d-qiqth-curvature-lowered-riemann-antisymm"></a>
**Lemma 57** (`lowered_riemann_antisymm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L937)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \sigma \mu \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\alpha} g_{{\rho}{\alpha}}({x}) \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,\sigma\,\mu\,\nu\,x + \sum_{\alpha} g_{{\sigma}{\alpha}}({x}) \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,\rho\,\mu\,\nu\,x = 0
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Def 11](#d-qiqth-curvature-pdiffat), [Lem 12](#d-qiqth-curvature-pd-add), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 25](#d-qiqth-curvature-pd-comm), [Def 35](#d-qiqth-curvature-covderiv02), [Lem 39](#d-qiqth-curvature-metric-compat), [Lem 56](#d-qiqth-curvature-lowered-riemann-eq). $\square$

<small>Referenced in [Lem 58](#d-qiqth-curvature-lowered-riemann-gi-trace), [Lem 503](#d-qiqth-curvature-lowered-riemann-pair-symm).</small>

<a id="d-qiqth-curvature-lowered-riemann-gi-trace"></a>
**Lemma 58** (`lowered_riemann_gi_trace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L988)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\beta \mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \sum_{\rho} g_{{\beta}{\rho}}({x}) \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\mathrm{lam}\,x = -\href{#d-qiqth-curvature-ricci}{R_{{\beta}{\mathrm{lam}}}({x})}
$$

*Proof.* By [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm). $\square$

<small>Referenced in [Lem 59](#d-qiqth-curvature-ricci-gi-raise).</small>

<a id="d-qiqth-curvature-ricci-gi-raise"></a>
**Lemma 59** (`ricci_gi_raise`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1030)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\mathrm{lam}\,x = -\sum_{\beta} g^{{\rho}{\beta}}({x}) \cdot \href{#d-qiqth-curvature-ricci}{R_{{\beta}{\mathrm{lam}}}({x})}
$$

*Proof.* By [Lem 58](#d-qiqth-curvature-lowered-riemann-gi-trace). $\square$

<small>Referenced in [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci).</small>

<a id="d-qiqth-curvature-pdiffat-ricci"></a>
**Lemma 60** (`PdiffAt_ricci`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1078)</small>

$$
(\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\sigma \nu \mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \href{#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({y})})\,\mathrm{lam}\,x
$$

*Proof.* By [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Def 29](#d-qiqth-curvature-riemann), [Lem 50](#d-qiqth-curvature-pdiffat-riemann). $\square$

<small>Referenced in [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real).</small>

<a id="d-qiqth-curvature-gi-trace-covderiv-ricci"></a>
**Lemma 61** (`gi_trace_covDeriv_ricci`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1084)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,(\lambda y a b \mapsto \href{#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})})\,\mathrm{lam}\,\sigma\,\nu\,x = \partial_{{\mathrm{lam}}}({\lambda y \mapsto \href{#d-qiqth-curvature-scalarcurv}{R({y})}})({x})
$$

*Proof.* By [Def 11](#d-qiqth-curvature-pdiffat), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Def 36](#d-qiqth-curvature-covderiv20), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 60](#d-qiqth-curvature-pdiffat-ricci). $\square$

<small>Referenced in [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi).</small>

<a id="d-qiqth-curvature-gi-trace-covderivriem"></a>
**Lemma 62** (`gi_trace_covDerivRiem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1151)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\rho\,\sigma\,\nu\,\mathrm{lam}\,x = \partial_{{\rho}}({\lambda y \mapsto \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({y}) \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\mathrm{lam}\,y})({x}) + \sum_{\sigma} \sum_{\nu} \sum_{\kappa} g^{{\sigma}{\nu}}({x}) \cdot (\href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\rho}{\kappa}}({x})} \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\kappa\,\sigma\,\nu\,\mathrm{lam}\,x) - \sum_{\sigma} \sum_{\nu} \sum_{\kappa} g^{{\sigma}{\nu}}({x}) \cdot (\href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\rho}{\mathrm{lam}}}({x})} \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\nu\,\kappa\,x)
$$

*Proof.* By [Def 11](#d-qiqth-curvature-pdiffat), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Def 36](#d-qiqth-curvature-covderiv20), [Lem 50](#d-qiqth-curvature-pdiffat-riemann), [Lem 55](#d-qiqth-curvature-inv-metric-compat). $\square$

<small>Referenced in [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci).</small>

<a id="d-qiqth-curvature-gi-trace-covderivriem-ricci"></a>
**Lemma 63** (`gi_trace_covDerivRiem_ricci`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1217)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\rho \mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\rho\,\sigma\,\nu\,\mathrm{lam}\,x = -\sum_{\beta} g^{{\rho}{\beta}}({x}) \cdot \partial_{{\rho}}({\lambda y \mapsto \href{#d-qiqth-curvature-ricci}{R_{{\beta}{\mathrm{lam}}}({y})}})({x}) + \sum_{\beta} \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\beta}}_{{\rho}{\kappa}}({x})} \cdot g^{{\rho}{\kappa}}({x}) \cdot \href{#d-qiqth-curvature-ricci}{R_{{\beta}{\mathrm{lam}}}({x})} + \sum_{\beta} \sum_{\kappa} \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\kappa}}_{{\rho}{\mathrm{lam}}}({x})} \cdot g^{{\rho}{\beta}}({x}) \cdot \href{#d-qiqth-curvature-ricci}{R_{{\beta}{\kappa}}({x})}
$$

*Proof.* By [Def 11](#d-qiqth-curvature-pdiffat), [Lem 14](#d-qiqth-curvature-pd-const-mul), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Def 29](#d-qiqth-curvature-riemann), [Def 36](#d-qiqth-curvature-covderiv20), [Lem 55](#d-qiqth-curvature-inv-metric-compat), [Lem 59](#d-qiqth-curvature-ricci-gi-raise), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 62](#d-qiqth-curvature-gi-trace-covderivriem). $\square$

<small>Referenced in [Lem 77](#d-qiqth-curvature-divriemann-trace-eq).</small>

<a id="d-qiqth-curvature-const-of-pd-zero"></a>
**Lemma 64** (`const_of_pd_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Curvature.lean#L1295)</small>

$$
\mathrm{Differentiable}\,\mathbb{R}\,F \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}) (\nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pd}{\partial_{{\nu}}({F})({x})} = 0) \to \forall (x y : \href{#d-qiqth-curvature-point}{M^{{n}}}), F\,x = F\,y
$$

*Proof.* By [Lem 23](#d-qiqth-curvature-pd-eq-fderiv). $\square$

<small>Referenced in [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global).</small>

<a id="sec-qiqth-differentialarealaw"></a>
## QIQTH.DifferentialAreaLaw

<a id="d-qiqth-differentialarealaw-deriv-eq-of-le-of-eq"></a>
**Lemma 65** (`deriv_eq_of_le_of_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/DifferentialAreaLaw.lean#L36)</small>

$$
({f})'({0})={f^{\prime}} \to ({g})'({0})={g^{\prime}} \to (\text{for }t\text{ near }0,\; f\,t \le g\,t) \to f\,0 = g\,0 \to f^{\prime} = g^{\prime}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 66](#d-qiqth-differentialarealaw-differential-area-law).</small>

<a id="d-qiqth-differentialarealaw-differential-area-law"></a>
**Lemma 66** (`differential_area_law`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/DifferentialAreaLaw.lean#L53)</small>

$$
({S})'({0})={s^{\prime}} \to ({\mathrm{KE}})'({0})={k^{\prime}} \to ({A})'({0})={a^{\prime}} \to (\text{for }t\text{ near }0,\; S\,t \le \eta \cdot A\,t) \to S\,0 = \eta \cdot A\,0 \to \mathrm{IsLocalMin}\,(\lambda t \mapsto \mathrm{KE}\,t - S\,t)\,0 \to s^{\prime} = \eta \cdot a^{\prime} \wedge k^{\prime} = \eta \cdot a^{\prime}
$$

*Proof.* By [Lem 65](#d-qiqth-differentialarealaw-deriv-eq-of-le-of-eq). $\square$

<small>Referenced in [Lem 67](#d-qiqth-differentialarealaw-differential-area-law-of-relentropy).</small>

<a id="d-qiqth-differentialarealaw-differential-area-law-of-relentropy"></a>
**Lemma 67** (`differential_area_law_of_relEntropy`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/DifferentialAreaLaw.lean#L75)</small>

$$
({S})'({0})={s^{\prime}} \to ({\mathrm{KE}})'({0})={k^{\prime}} \to ({A})'({0})={a^{\prime}} \to (\text{for }t\text{ near }0,\; S\,t \le \eta \cdot A\,t) \to S\,0 = \eta \cdot A\,0 \to (\forall (t : \mathbb{R}), 0 \le \mathrm{KE}\,t - S\,t) \to \mathrm{KE}\,0 - S\,0 = 0 \to s^{\prime} = \eta \cdot a^{\prime} \wedge k^{\prime} = \eta \cdot a^{\prime}
$$

*Proof.* By [Lem 66](#d-qiqth-differentialarealaw-differential-area-law). $\square$

<small>Referenced in [Lem 485](#d-qiqth-qiqttogr-bl-pernull-of-qiqt).</small>

<a id="sec-qiqth-einsteinequationofstate"></a>
## QIQTH.EinsteinEquationOfState

<a id="d-qiqth-einsteineos-gm"></a>
**Definition 68** (`gm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L29)</small>

A definition — see source for the body.

<small>Referenced in [Lem 70](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null), [Lem 73](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general), [Lem 83](#d-qiqth-curvature-crux-of-pernull), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="d-qiqth-einsteineos-qf"></a>
**Definition 69** (`QF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L32)</small>

A definition — see source for the body.

<small>Referenced in [Lem 70](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null), [Lem 72](#d-qiqth-einsteineos-qf-eq-bl), [Lem 73](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general).</small>

<a id="d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null"></a>
**Lemma 70** (`symmTensor_eq_smul_metric_of_null`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L39)</small>

$$
(\forall (i j : \mathrm{Fin}\,4), C\,i\,j = C\,j\,i) \to (\forall (x_{0} x_{1} x_{2} x_{3} : \mathbb{R}), -{x_{0}}^{2} + {x_{1}}^{2} + {x_{2}}^{2} + {x_{3}}^{2} = 0 \to \href{#d-qiqth-einsteineos-qf}{\mathrm{QF}}\,C\,x_{0}\,x_{1}\,x_{2}\,x_{3} = 0) \to \exists c, \forall (i j : \mathrm{Fin}\,4), C\,i\,j = c \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{i}{j}}}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 73](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general).</small>

<a id="d-qiqth-einsteineos-bl"></a>
**Definition 71** (`BL`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L104)</small>

A definition — see source for the body.

<small>Referenced in [Lem 8](#d-qiqth-curvature-bl-smul-sub), [Lem 72](#d-qiqth-einsteineos-qf-eq-bl), [Lem 73](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general), [Lem 83](#d-qiqth-curvature-crux-of-pernull), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Lem 475](#d-qiqth-wedgekmstogr-bl-kgstress-null), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri), [Lem 484](#d-qiqth-qiqttogr-bl-pernull-of-modular), [Lem 485](#d-qiqth-qiqttogr-bl-pernull-of-qiqt), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="d-qiqth-einsteineos-qf-eq-bl"></a>
**Lemma 72** (`QF_eq_BL`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L107)</small>

$$
(\forall (i j : \mathrm{Fin}\,4), C\,i\,j = C\,j\,i) \to \forall (x_{0} x_{1} x_{2} x_{3} : \mathbb{R}), \href{#d-qiqth-einsteineos-qf}{\mathrm{QF}}\,C\,x_{0}\,x_{1}\,x_{2}\,x_{3} = \href{#d-qiqth-einsteineos-bl}{({C})({![x_{0} , x_{1} , x_{2} , x_{3}]},{![x_{0} , x_{1} , x_{2} , x_{3}]})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 73](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general).</small>

<a id="d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general"></a>
**Lemma 73** (`symmTensor_eq_smul_metric_of_null_general`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinEquationOfState.lean#L114)</small>

$$
(\forall (i j : \mathrm{Fin}\,4), C\,i\,j = C\,j\,i) \to \forall (P \mathrm{Pinv} : \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (i j : \mathrm{Fin}\,4), \sum_{k} P\,i\,k \cdot \mathrm{Pinv}\,k\,j = \delta_{ij}) \to (\forall (i j : \mathrm{Fin}\,4), \sum_{k} \mathrm{Pinv}\,i\,k \cdot P\,k\,j = \delta_{ij}) \to (\forall (i j : \mathrm{Fin}\,4), g\,i\,j = \sum_{k} \sum_{l} P\,k\,i \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P\,l\,j) \to (\forall (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g})({v},{v})} = 0 \to \href{#d-qiqth-einsteineos-bl}{({C})({v},{v})} = 0) \to \exists c, \forall (i j : \mathrm{Fin}\,4), C\,i\,j = c \cdot g\,i\,j
$$

*Proof.* By [Def 69](#d-qiqth-einsteineos-qf), [Lem 70](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null), [Lem 72](#d-qiqth-einsteineos-qf-eq-bl). $\square$

<small>Referenced in [Lem 83](#d-qiqth-curvature-crux-of-pernull).</small>

<a id="sec-qiqth-einsteinfieldequation"></a>
## QIQTH.EinsteinFieldEquation

<a id="d-qiqth-curvature-div02"></a>
**Definition 74** (`div02`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L30)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 75](#d-qiqth-curvature-div02-add), [Lem 76](#d-qiqth-curvature-div02-scalar-metric), [Lem 77](#d-qiqth-curvature-divriemann-trace-eq), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi), [Lem 80](#d-qiqth-curvature-einstein-field-equation), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real), [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="d-qiqth-curvature-div02-add"></a>
**Lemma 75** (`div02_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L35)</small>

$$
(\forall (a b \rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto X\,y\,a\,b)\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto Y\,y\,a\,b)\,\rho\,x) \to \forall (\nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a b \mapsto X\,y\,a\,b + Y\,y\,a\,b})_{{\nu}}({x})} = \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {X})_{{\nu}}({x})} + \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {Y})_{{\nu}}({x})}
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Lem 12](#d-qiqth-curvature-pd-add), [Def 27](#d-qiqth-curvature-christoffel), [Def 35](#d-qiqth-curvature-covderiv02). $\square$

<small>Referenced in [Lem 80](#d-qiqth-curvature-einstein-field-equation).</small>

<a id="d-qiqth-curvature-div02-scalar-metric"></a>
**Lemma 76** (`div02_scalar_metric`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L53)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to \forall (f : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathbb{R}) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), (\forall (\rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to \forall (\nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a b \mapsto f\,y \cdot g_{{a}{b}}({y})})_{{\nu}}({x})} = \href{#d-qiqth-curvature-pd}{\partial_{{\nu}}({f})({x})}
$$

*Proof.* By [Lem 22](#d-qiqth-curvature-pd-mul), [Def 27](#d-qiqth-curvature-christoffel), [Def 35](#d-qiqth-curvature-covderiv02), [Lem 39](#d-qiqth-curvature-metric-compat). $\square$

<small>Referenced in [Lem 80](#d-qiqth-curvature-einstein-field-equation).</small>

<a id="d-qiqth-curvature-divriemann-trace-eq"></a>
**Lemma 77** (`divRiemann_trace_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L93)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\rho} \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\rho\,\sigma\,\nu\,\mathrm{lam}\,x = -(\nabla\!\cdot {\lambda y a b \mapsto \href{#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})}})_{{\mathrm{lam}}}({x})
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Def 35](#d-qiqth-curvature-covderiv02), [Lem 63](#d-qiqth-curvature-gi-trace-covderivriem-ricci). $\square$

<small>Referenced in [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi).</small>

<a id="d-qiqth-curvature-twice-contracted-bianchi"></a>
**Lemma 78** (`twice_contracted_bianchi`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L130)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), (\nabla\!\cdot {\lambda y a b \mapsto \href{#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})}})_{{\mathrm{lam}}}({x}) = 1/2 \cdot \partial_{{\mathrm{lam}}}({\lambda y \mapsto \href{#d-qiqth-curvature-scalarcurv}{R({y})}})({x})
$$

*Proof.* By [Def 35](#d-qiqth-curvature-covderiv02), [Def 48](#d-qiqth-curvature-covderivriem), [Lem 54](#d-qiqth-curvature-second-bianchi-contracted), [Lem 61](#d-qiqth-curvature-gi-trace-covderiv-ricci), [Lem 77](#d-qiqth-curvature-divriemann-trace-eq). $\square$

<small>Referenced in [Lem 81](#d-qiqth-curvature-einstein-field-equation-real).</small>

<a id="d-qiqth-curvature-metric-contraction-trace"></a>
**Lemma 79** (`metric_contraction_trace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L194)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\mu} \sum_{\nu} g^{{\mu}{\nu}}({x}) \cdot g_{{\mu}{\nu}}({x}) = n
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 406](#d-qiqth-curvature-hreg-kg).</small>

<a id="d-qiqth-curvature-einstein-field-equation"></a>
**Lemma 80** (`einstein_field_equation`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L234)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to \forall (T \mathrm{Ric} : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathrm{Fin}\,n \to \mathbb{R}) (f \mathrm{tr} : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathbb{R}) (a : \mathbb{R}) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), (\forall (\rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \to (\forall (\rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,\mathrm{tr}\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \mathrm{Ric}\,y\,a\,b)\,\rho\,x) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a^{\prime} b : \mathrm{Fin}\,n), a \cdot T_{{a^{\prime}}{b}}({y}) = \mathrm{Ric}\,y\,a^{\prime}\,b + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (\nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to (\forall (\nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\mathrm{Ric}})_{{\nu}}({x})} = 1/2 \cdot \href{#d-qiqth-curvature-pd}{\partial_{{\nu}}({\mathrm{tr}})({x})}) \to (\forall (\mu \nu : \mathrm{Fin}\,n), a \cdot T_{{\mu}{\nu}}({x}) = \mathrm{Ric}\,x\,\mu\,\nu - 1/2 \cdot \mathrm{tr}\,x \cdot g_{{\mu}{\nu}}({x}) + (f\,x + 1/2 \cdot \mathrm{tr}\,x) \cdot g_{{\mu}{\nu}}({x})) \wedge \forall (\nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto f\,y + 1/2 \cdot \mathrm{tr}\,y})({x})} = 0
$$

*Proof.* By [Lem 12](#d-qiqth-curvature-pd-add), [Lem 14](#d-qiqth-curvature-pd-const-mul), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 75](#d-qiqth-curvature-div02-add), [Lem 76](#d-qiqth-curvature-div02-scalar-metric). $\square$

<small>Referenced in [Lem 81](#d-qiqth-curvature-einstein-field-equation-real).</small>

<a id="d-qiqth-curvature-einstein-field-equation-real"></a>
**Lemma 81** (`einstein_field_equation_real`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L269)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (T : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathrm{Fin}\,n \to \mathbb{R}) (f : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathbb{R}) (a : \mathbb{R}) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), (\forall (\rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a^{\prime} b : \mathrm{Fin}\,n), a \cdot T_{{a^{\prime}}{b}}({y}) = \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (\nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to (\forall (\mu \nu : \mathrm{Fin}\,n), a \cdot T_{{\mu}{\nu}}({x}) = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + (f\,x + 1/2 \cdot \href{#d-qiqth-curvature-scalarcurv}{R({x})}) \cdot g_{{\mu}{\nu}}({x})) \wedge \forall (\nu : \mathrm{Fin}\,n), \partial_{{\nu}}({\lambda y \mapsto f\,y + 1/2 \cdot \href{#d-qiqth-curvature-scalarcurv}{R({y})}})({x}) = 0
$$

*Proof.* By [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 60](#d-qiqth-curvature-pdiffat-ricci), [Lem 78](#d-qiqth-curvature-twice-contracted-bianchi), [Lem 80](#d-qiqth-curvature-einstein-field-equation). $\square$

<small>Referenced in [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global).</small>

<a id="d-qiqth-curvature-einstein-field-equation-real-global"></a>
**Lemma 82** (`einstein_field_equation_real_global`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L300)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (T : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathrm{Fin}\,n \to \mathbb{R}) (f : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathbb{R}) (a : \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}) (\rho : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \to (\mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot \href{#d-qiqth-curvature-scalarcurv}{R({y})}) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a^{\prime} b : \mathrm{Fin}\,n), a \cdot T_{{a^{\prime}}{b}}({y}) = \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}) (\nu : \mathrm{Fin}\,n), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}) (\mu \nu : \mathrm{Fin}\,n), a \cdot T_{{\mu}{\nu}}({x}) = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Lem 64](#d-qiqth-curvature-const-of-pd-zero), [Lem 81](#d-qiqth-curvature-einstein-field-equation-real). $\square$

<small>Referenced in [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state).</small>

<a id="d-qiqth-curvature-crux-of-pernull"></a>
**Lemma 83** (`crux_of_pernull`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L328)</small>

$$
(\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), T_{{a^{\prime}}{b}}({x}) = T_{{b}{a^{\prime}}}({x})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})} = \href{#d-qiqth-curvature-ricci}{R_{{b}{a^{\prime}}}({x})}) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({x}) - \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})}})({v},{v}) = 0) \to \exists f, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot T_{{a^{\prime}}{b}}({x}) = \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})} + f\,x \cdot g_{{a^{\prime}}{b}}({x})
$$

*Proof.* By [Lem 73](#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general). $\square$

<small>Referenced in [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state).</small>

<a id="d-qiqth-curvature-jacobson-einstein-equation-of-state"></a>
**Lemma 84** (`jacobson_einstein_equation_of_state`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L361)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,4), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (T : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}) (a : \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), T_{{a^{\prime}}{b}}({x}) = T_{{b}{a^{\prime}}}({x})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})} = \href{#d-qiqth-curvature-ricci}{R_{{b}{a^{\prime}}}({x})}) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({x}) - \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})}})({v},{v}) = 0) \to (\forall (f : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}), (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot T_{{a^{\prime}}{b}}({y}) = \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\rho : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \wedge \mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot \href{#d-qiqth-curvature-scalarcurv}{R({y})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\nu : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T_{{\mu}{\nu}}({x}) = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Lem 82](#d-qiqth-curvature-einstein-field-equation-real-global), [Lem 83](#d-qiqth-curvature-crux-of-pernull). $\square$

<small>Referenced in [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr).</small>

<a id="sec-qiqth-fock-boostkms"></a>
## QIQTH.Fock.BoostKMS

<a id="d-qiqth-fock-boostkms-inner-krepl2"></a>
**Lemma 85** (`inner_KrepL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L22)</small>

$$
\langle {\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf}},{\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hg}}\rangle = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta) \cdot \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 87](#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [Lem 134](#d-qiqth-fock-boostkms-norm-tolp-krep-eq-sqrt).</small>

<a id="d-qiqth-fock-boostkms-inner-krepl2-general"></a>
**Lemma 86** (`inner_KrepL2_general`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L33)</small>

$$
\langle {\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf}},{h}\rangle = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta) \cdot h\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 189](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-inner-boostunitary-krepl2"></a>
**Lemma 87** (`inner_boostUnitary_KrepL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L44)</small>

$$
\mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-a)\,f))\,2\,\mathrm{volume} \to \langle {\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hg}},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,(\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf})}\rangle = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta) \cdot \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - a)
$$

*Proof.* By [Lem 85](#d-qiqth-fock-boostkms-inner-krepl2), [Lem 247](#d-qiqth-fock-localization-krep-boost), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2). $\square$

<small>Referenced in [Lem 89](#d-qiqth-fock-boostkms-symm-edge-eq-inner).</small>

<a id="d-qiqth-fock-boostkms-symm-edge-eq-shifted"></a>
**Lemma 88** (`symm_edge_eq_shifted`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L58)</small>

$$
\int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)) \cdot \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t) = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta) \cdot \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - 2 \cdot \pi \cdot t)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 89](#d-qiqth-fock-boostkms-symm-edge-eq-inner).</small>

<a id="d-qiqth-fock-boostkms-symm-edge-eq-inner"></a>
**Lemma 89** (`symm_edge_eq_inner`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L70)</small>

$$
\mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-(2 \cdot \pi \cdot t))\,f))\,2\,\mathrm{volume} \to \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)) \cdot \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t) = \langle {\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hg}},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,(\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf})}\rangle
$$

*Proof.* By [Lem 87](#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [Lem 88](#d-qiqth-fock-boostkms-symm-edge-eq-shifted). $\square$

<small>Referenced in [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner).</small>

<a id="d-qiqth-fock-boostkms-kmsfun"></a>
**Definition 90** (`kmsFun`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L82)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 91](#d-qiqth-fock-boostkms-kmsfun-ofreal), [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [Lem 93](#d-qiqth-fock-boostkms-kmsfun-sub-i), [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 110](#d-qiqth-fock-boostkms-kmsfun-differentiableon), [Lem 127](#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed), [Lem 128](#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le), [Lem 130](#d-qiqth-fock-boostkms-kmsfun-add-left), [Lem 131](#d-qiqth-fock-boostkms-kmsfun-add-right), [Lem 132](#d-qiqth-fock-boostkms-kmsfun-sub-left), [Lem 133](#d-qiqth-fock-boostkms-kmsfun-sub-right), [Lem 139](#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul), [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le), [Def 142](#d-qiqth-fock-boostkms-kmsbcf), [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply), [Lem 144](#d-qiqth-fock-boostkms-dist-kmsbcf-le), [Lem 145](#d-qiqth-fock-boostkms-kmsbcf-congr), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-ofreal"></a>
**Lemma 91** (`kmsFun_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L90)</small>

$$
\href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,t = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)) \cdot \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t)
$$

*Proof.* By [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal). $\square$

<small>Referenced in [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [Lem 93](#d-qiqth-fock-boostkms-kmsfun-sub-i).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner"></a>
**Lemma 92** (`kmsFun_ofReal_eq_inner`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L101)</small>

$$
\mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-(2 \cdot \pi \cdot t))\,f))\,2\,\mathrm{volume} \to \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,t = \langle {\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hg}},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,(\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf})}\rangle
$$

*Proof.* By [Lem 89](#d-qiqth-fock-boostkms-symm-edge-eq-inner), [Lem 91](#d-qiqth-fock-boostkms-kmsfun-ofreal). $\square$

<small>Referenced in [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-sub-i"></a>
**Lemma 93** (`kmsFun_sub_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L110)</small>

$$
(\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \forall (t : \mathbb{R}), \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,(t - i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,t)
$$

*Proof.* By [Lem 91](#d-qiqth-fock-boostkms-kmsfun-ofreal), [Def 246](#d-qiqth-fock-localization-krep), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i). $\square$

<small>Referenced in [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot).</small>

<a id="d-qiqth-fock-boostkms-differentiable-reflkrepcont"></a>
**Lemma 94** (`differentiable_reflKrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L133)</small>

$$
\mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \mathrm{Differentiable}\,\mathbb{C}\,\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u))
$$

*Proof.* By [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Referenced in [Lem 98](#d-qiqth-fock-boostkms-differentiable-kmsintegrand), [Lem 99](#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [Lem 102](#d-qiqth-fock-boostkms-continuous-deriv-reflkrepcont).</small>

<a id="d-qiqth-fock-boostkms-norm-reflkrepcont-le"></a>
**Lemma 95** (`norm_reflKrepCont_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L145)</small>

$$
0 \le m \to \forall \{g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{u : \mathbb{C}\}, -\pi \le u.\mathrm{im} \to u.\mathrm{im} \le 0 \to \|(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u))\| \le (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|g\,x\|) \cdot \exp\,(-(m \cdot \sin\,(-u.\mathrm{im}) \cdot \delta) \cdot \cosh\,u.\mathrm{re})
$$

*Proof.* By [Lem 351](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Referenced in [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 107](#d-qiqth-fock-boostkms-norm-term2-le).</small>

<a id="d-qiqth-fock-boostkms-deriv-reflkrepcont-eq"></a>
**Lemma 96** (`deriv_reflKrepCont_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L159)</small>

$$
\mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (u : \mathbb{C}), \mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,u = (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{deriv}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g)\,((\mathrm{starRingEnd}\,\mathbb{C})\,u))
$$

*Proof.* By [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Referenced in [Lem 97](#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le).</small>

<a id="d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le"></a>
**Lemma 97** (`norm_deriv_reflKrepCont_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L171)</small>

$$
0 \le m \to \forall \{g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{u : \mathbb{C}\}, -\pi \le u.\mathrm{im} \to u.\mathrm{im} \le 0 \to \|\mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,u\| \le 1 / \sqrt 2 \cdot (|m| \cdot \cosh\,u.\mathrm{re} \cdot \exp\,(-(m \cdot \sin\,(-u.\mathrm{im}) \cdot \delta) \cdot \cosh\,u.\mathrm{re}) \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|g\,x\|)
$$

*Proof.* By [Lem 96](#d-qiqth-fock-boostkms-deriv-reflkrepcont-eq), [Lem 350](#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay). $\square$

<small>Referenced in [Lem 106](#d-qiqth-fock-boostkms-norm-term1-le).</small>

<a id="d-qiqth-fock-boostkms-differentiable-kmsintegrand"></a>
**Lemma 98** (`differentiable_kmsIntegrand`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L186)</small>

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (\theta : \mathbb{R}), \mathrm{Differentiable}\,\mathbb{C}\,\lambda z \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)
$$

*Proof.* By [Lem 94](#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Referenced in [Lem 115](#d-qiqth-fock-boostkms-kmsfuncut-continuouson).</small>

<a id="d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z"></a>
**Lemma 99** (`hasDerivAt_kmsIntegrand_z`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L198)</small>

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (\theta : \mathbb{R}) (z : \mathbb{C}), ({\lambda z \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)})'({z})={\mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,(\theta + \pi \cdot z) \cdot \pi \cdot \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z) + (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot (\mathrm{deriv}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,(\theta - \pi \cdot z) \cdot -\pi)}
$$

*Proof.* By [Lem 94](#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Referenced in [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-norm-two-term-le"></a>
**Lemma 100** (`norm_two_term_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L219)</small>

$$
\|A \cdot \pi \cdot C + B \cdot (D \cdot -\pi)\| \le \pi \cdot (\|A\| \cdot \|C\|) + \pi \cdot (\|B\| \cdot \|D\|)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 108](#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound).</small>

<a id="d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta"></a>
**Lemma 101** (`continuous_kmsIntegrand_in_theta`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L228)</small>

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (z : \mathbb{C}), \mathrm{Continuous}\,\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)
$$

*Proof.* By [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Referenced in [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat), [Lem 115](#d-qiqth-fock-boostkms-kmsfuncut-continuouson).</small>

<a id="d-qiqth-fock-boostkms-continuous-deriv-reflkrepcont"></a>
**Lemma 102** (`continuous_deriv_reflKrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L240)</small>

$$
\mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \mathrm{Continuous}\,(\mathrm{deriv}\,\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))
$$

*Proof.* By [Lem 94](#d-qiqth-fock-boostkms-differentiable-reflkrepcont). $\square$

<small>Referenced in [Lem 103](#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta).</small>

<a id="d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta"></a>
**Lemma 103** (`continuous_kmsIntegrand_deriv_in_theta`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L247)</small>

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (z : \mathbb{C}), \mathrm{Continuous}\,\lambda \theta \mapsto \mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,(\theta + \pi \cdot z) \cdot \pi \cdot \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z) + (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot (\mathrm{deriv}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,(\theta - \pi \cdot z) \cdot -\pi)
$$

*Proof.* By [Lem 102](#d-qiqth-fock-boostkms-continuous-deriv-reflkrepcont), [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [Lem 329](#d-qiqth-fock-wedgeanalyticity-continuous-deriv-krepcont). $\square$

<small>Referenced in [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-integrable-kmsintegrand"></a>
**Lemma 104** (`integrable_kmsIntegrand`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L262)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\deltaf \deltag : \mathbb{R}\}, 0 < \deltaf \to 0 < \deltag \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \deltaf \le x\,1 - x\,0 \wedge \deltaf \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \deltag \le x\,1 - x\,0 \wedge \deltag \le x\,1 + x\,0) \to \forall \{z : \mathbb{C}\}, -1 < z.\mathrm{im} \to z.\mathrm{im} < 0 \to \mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z))\,\mathrm{volume}
$$

*Proof.* By [Lem 95](#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [Lem 101](#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [Lem 334](#d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh), [Lem 340](#d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos), [Lem 351](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Referenced in [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-exists-sin-min"></a>
**Lemma 105** (`exists_sin_min`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L366)</small>

$$
0 < \varepsilon \to (\forall z\in \bar{B}\,z_{0}\,\varepsilon, -1 < z.\mathrm{im} \wedge z.\mathrm{im} < 0) \to \exists \sigma\mathrm{min}, 0 < \sigma\mathrm{min} \wedge \forall z\in \bar{B}\,z_{0}\,\varepsilon, \sigma\mathrm{min} \le \sin\,(-(\pi \cdot z.\mathrm{im}))
$$

*Proof.* By [Lem 340](#d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos). $\square$

<small>Referenced in [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-norm-term1-le"></a>
**Lemma 106** (`norm_term1_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L380)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{z : \mathbb{C}\}, -1 < z.\mathrm{im} \to z.\mathrm{im} < 0 \to \forall \{\sigma\mathrm{min} R : \mathbb{R}\}, 0 < \sigma\mathrm{min} \to \sigma\mathrm{min} \le \sin\,(-(\pi \cdot z.\mathrm{im})) \to |z.\mathrm{re}| \le R \to \forall (\theta : \mathbb{R}), \|\mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,(\theta + \pi \cdot z)\| \cdot \|\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)\| \le 1 / \sqrt 2 \cdot (|m| \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|g\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|f\,x\|) \cdot (\exp\,(\pi \cdot R) \cdot \cosh\,\theta \cdot \exp\,(-(m \cdot \sigma\mathrm{min} \cdot \delta \cdot \exp\,(-(\pi \cdot R)) \cdot \cosh\,\theta)))
$$

*Proof.* By [Lem 97](#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le), [Lem 340](#d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos), [Lem 342](#d-qiqth-fock-wedgeanalyticity-prod-norm-bound-cosh-shift), [Lem 351](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Referenced in [Lem 108](#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound).</small>

<a id="d-qiqth-fock-boostkms-norm-term2-le"></a>
**Lemma 107** (`norm_term2_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L420)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{z : \mathbb{C}\}, -1 < z.\mathrm{im} \to z.\mathrm{im} < 0 \to \forall \{\sigma\mathrm{min} R : \mathbb{R}\}, 0 < \sigma\mathrm{min} \to \sigma\mathrm{min} \le \sin\,(-(\pi \cdot z.\mathrm{im})) \to |z.\mathrm{re}| \le R \to \forall (\theta : \mathbb{R}), \|(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z)))\| \cdot \|\mathrm{deriv}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,(\theta - \pi \cdot z)\| \le 1 / \sqrt 2 \cdot (|m| \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|f\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|g\,x\|) \cdot (\exp\,(\pi \cdot R) \cdot \cosh\,\theta \cdot \exp\,(-(m \cdot \sigma\mathrm{min} \cdot \delta \cdot \exp\,(-(\pi \cdot R)) \cdot \cosh\,\theta)))
$$

*Proof.* By [Lem 95](#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [Lem 340](#d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos), [Lem 342](#d-qiqth-fock-wedgeanalyticity-prod-norm-bound-cosh-shift), [Lem 350](#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay). $\square$

<small>Referenced in [Lem 108](#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound).</small>

<a id="d-qiqth-fock-boostkms-kmsintegrand-deriv-bound"></a>
**Lemma 108** (`kmsIntegrand_deriv_bound`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L462)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{z : \mathbb{C}\}, -1 < z.\mathrm{im} \to z.\mathrm{im} < 0 \to \forall \{\sigma\mathrm{min} R : \mathbb{R}\}, 0 < \sigma\mathrm{min} \to \sigma\mathrm{min} \le \sin\,(-(\pi \cdot z.\mathrm{im})) \to |z.\mathrm{re}| \le R \to \forall (\theta : \mathbb{R}), \|\mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,(\theta + \pi \cdot z) \cdot \pi \cdot \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z) + (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot (\mathrm{deriv}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,(\theta - \pi \cdot z) \cdot -\pi)\| \le \pi \cdot ((1 / \sqrt 2 \cdot (|m| \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|g\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|f\,x\|) + 1 / \sqrt 2 \cdot (|m| \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|f\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|g\,x\|)) \cdot (\exp\,(\pi \cdot R) \cdot \cosh\,\theta \cdot \exp\,(-(m \cdot \sigma\mathrm{min} \cdot \delta \cdot \exp\,(-(\pi \cdot R)) \cdot \cosh\,\theta))))
$$

*Proof.* By [Lem 100](#d-qiqth-fock-boostkms-norm-two-term-le), [Lem 106](#d-qiqth-fock-boostkms-norm-term1-le), [Lem 107](#d-qiqth-fock-boostkms-norm-term2-le). $\square$

<small>Referenced in [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-differentiableat"></a>
**Lemma 109** (`kmsFun_differentiableAt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L485)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{z_{0} : \mathbb{C}\}, -1 < z_{0}.\mathrm{im} \to z_{0}.\mathrm{im} < 0 \to \mathrm{DifferentiableAt}\,\mathbb{C}\,(\href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g)\,z_{0}
$$

*Proof.* By [Lem 99](#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [Lem 101](#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [Lem 103](#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta), [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 105](#d-qiqth-fock-boostkms-exists-sin-min), [Lem 108](#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 343](#d-qiqth-fock-wedgeanalyticity-integrable-cosh-mul-exp-neg-const-mul-cosh). $\square$

<small>Referenced in [Lem 110](#d-qiqth-fock-boostkms-kmsfun-differentiableon).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-differentiableon"></a>
**Lemma 110** (`kmsFun_differentiableOn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L559)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \mathrm{DifferentiableOn}\,\mathbb{C}\,(\href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g)\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0)
$$

*Proof.* By [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat). $\square$

<small>Referenced in [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut"></a>
**Definition 111** (`kmsFunCut`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L664)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 112](#d-qiqth-fock-boostkms-norm-kmsfuncut-le), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat), [Lem 114](#d-qiqth-fock-boostkms-kmsfuncut-differentiableon), [Lem 115](#d-qiqth-fock-boostkms-kmsfuncut-continuouson), [Lem 116](#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [Lem 117](#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [Lem 123](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le), [Lem 124](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le), [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le), [Lem 127](#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed), [Lem 128](#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le), [Lem 129](#d-qiqth-fock-boostkms-kmsfuncut-zero), [Lem 139](#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfuncut-le"></a>
**Lemma 112** (`norm_kmsFunCut_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L673)</small>

$$
0 \le m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 \le \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{R : \mathbb{R}\}, 0 \le R \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,z\| \le (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|g\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|f\,x\|) \cdot (2 \cdot R)
$$

*Proof.* By [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 352](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const). $\square$

<small>Referenced in [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-differentiableat"></a>
**Lemma 113** (`kmsFunCut_differentiableAt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L711)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall (\mathrm{Rc} : \mathbb{R}) \{z_{0} : \mathbb{C}\}, -1 < z_{0}.\mathrm{im} \to z_{0}.\mathrm{im} < 0 \to \mathrm{DifferentiableAt}\,\mathbb{C}\,(\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,\mathrm{Rc})\,z_{0}
$$

*Proof.* By [Lem 99](#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [Lem 101](#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [Lem 103](#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta), [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 105](#d-qiqth-fock-boostkms-exists-sin-min), [Lem 108](#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 343](#d-qiqth-fock-wedgeanalyticity-integrable-cosh-mul-exp-neg-const-mul-cosh). $\square$

<small>Referenced in [Lem 114](#d-qiqth-fock-boostkms-kmsfuncut-differentiableon).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-differentiableon"></a>
**Lemma 114** (`kmsFunCut_differentiableOn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L790)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall (\mathrm{Rc} : \mathbb{R}), \mathrm{DifferentiableOn}\,\mathbb{C}\,(\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,\mathrm{Rc})\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0)
$$

*Proof.* By [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat). $\square$

<small>Referenced in [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-continuouson"></a>
**Lemma 115** (`kmsFunCut_continuousOn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L801)</small>

$$
0 \le m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 \le \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall (\mathrm{Rc} : \mathbb{R}), \mathrm{ContinuousOn}\,(\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,\mathrm{Rc})\,(\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0)
$$

*Proof.* By [Lem 98](#d-qiqth-fock-boostkms-differentiable-kmsintegrand), [Lem 101](#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 352](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const). $\square$

<small>Referenced in [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-ofreal"></a>
**Lemma 116** (`kmsFunCut_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L852)</small>

$$
\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,t = \int (\theta : \mathbb{R}) in \mathrm{Icc}\,(-R)\,R, (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)) \cdot \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t)
$$

*Proof.* By [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal). $\square$

<small>Referenced in [Lem 117](#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [Lem 123](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-sub-i"></a>
**Lemma 117** (`kmsFunCut_sub_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L904)</small>

$$
(\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \forall (R t : \mathbb{R}), \href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,(t - i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,t)
$$

*Proof.* By [Lem 116](#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [Def 246](#d-qiqth-fock-localization-krep), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i). $\square$

<small>Referenced in [Lem 124](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le).</small>

<a id="d-qiqth-fock-boostkms-norm-le-of-strip-edges"></a>
**Lemma 118** (`norm_le_of_strip_edges`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L937)</small>

$$
\mathrm{DifferentiableOn}\,\mathbb{C}\,\Phi\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \to \mathrm{ContinuousOn}\,\Phi\,(\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0) \to \mathrm{BddAbove}\,(\mathrm{norm} \circ \Phi '' \mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0) \to (\forall (t : \mathbb{R}), \|\Phi\,t\| \le b) \to (\forall (t : \mathbb{R}), \|\Phi\,(t - i)\| \le b) \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\Phi\,z\| \le b
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-real-l2-inner-le"></a>
**Lemma 119** (`real_L2_inner_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1098)</small>

$$
\mathrm{MemLp}\,u\,2\,\mu \to \mathrm{MemLp}\,v\,2\,\mu \to 0 \le [\mu] u \to 0 \le [\mu] v \to \int (\theta : \mathbb{R}), u\,\theta \cdot v\,\theta \partial \mu \le \sqrt (\int (\theta : \mathbb{R}), {u\,\theta}^{2} \partial \mu) \cdot \sqrt (\int (\theta : \mathbb{R}), {v\,\theta}^{2} \partial \mu)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 120](#d-qiqth-fock-boostkms-tail-term-le).</small>

<a id="d-qiqth-fock-boostkms-tail-term-le"></a>
**Lemma 120** (`tail_term_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1114)</small>

$$
\mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{2})\,2\,\mathrm{volume} \to \forall (R c d : \mathbb{R}), \int (\theta : \mathbb{R}), \{\theta|R < |\theta + c|\}.\mathbf{1}\,1\,\theta \cdot (\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{1}\,(\theta + c)\| \cdot \|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{2}\,(\theta + d)\|) \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{1}\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{2}\,\theta\|}^{2})
$$

*Proof.* By [Lem 119](#d-qiqth-fock-boostkms-real-l2-inner-le). $\square$

<small>Referenced in [Lem 122](#d-qiqth-fock-boostkms-tail-integral-le).</small>

<a id="d-qiqth-fock-boostkms-tail-geom"></a>
**Lemma 121** (`tail_geom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1163)</small>

$$
R < |\theta| \to R < |\theta + a| \vee R < |\theta - a|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 122](#d-qiqth-fock-boostkms-tail-integral-le).</small>

<a id="d-qiqth-fock-boostkms-tail-integral-le"></a>
**Lemma 122** (`tail_integral_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1177)</small>

$$
\mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall (R : \mathbb{R}), \int (\theta : \mathbb{R}), \{\theta|R < |\theta|\}.\mathbf{1}\,1\,\theta \cdot (\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)\| \cdot \|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t)\|) \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [Lem 120](#d-qiqth-fock-boostkms-tail-term-le), [Lem 121](#d-qiqth-fock-boostkms-tail-geom). $\square$

<small>Referenced in [Lem 123](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le"></a>
**Lemma 123** (`norm_kmsFunCut_diff_ofReal_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1268)</small>

$$
\mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{R S : \mathbb{R}\}, R \le S \to \|\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,S\,t - \href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,t\| \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [Lem 116](#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [Lem 122](#d-qiqth-fock-boostkms-tail-integral-le). $\square$

<small>Referenced in [Lem 124](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le), [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le"></a>
**Lemma 124** (`norm_kmsFunCut_diff_sub_I_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1349)</small>

$$
(\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{R S : \mathbb{R}\}, R \le S \to \|\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,S\,(t - i) - \href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,(t - i)\| \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [Lem 117](#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [Lem 123](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le). $\square$

<small>Referenced in [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le"></a>
**Lemma 125** (`norm_kmsFunCut_diff_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1360)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{R S : \mathbb{R}\}, 0 \le R \to R \le S \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,S\,z - \href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,z\| \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [Lem 112](#d-qiqth-fock-boostkms-norm-kmsfuncut-le), [Lem 114](#d-qiqth-fock-boostkms-kmsfuncut-differentiableon), [Lem 115](#d-qiqth-fock-boostkms-kmsfuncut-continuouson), [Lem 118](#d-qiqth-fock-boostkms-norm-le-of-strip-edges), [Lem 123](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le), [Lem 124](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le). $\square$

<small>Referenced in [Lem 128](#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le).</small>

<a id="d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed"></a>
**Lemma 126** (`integrable_kmsFun_integrand_closed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1390)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z))\,\mathrm{volume}
$$

*Proof.* By [Lem 359](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed). $\square$

<small>Referenced in [Lem 127](#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed), [Lem 130](#d-qiqth-fock-boostkms-kmsfun-add-left), [Lem 131](#d-qiqth-fock-boostkms-kmsfun-add-right).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed"></a>
**Lemma 127** (`kmsFunCut_tendsto_closed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1447)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \mathrm{Tendsto}\,(\lambda n \mapsto \href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,(n)\,z)\,\mathrm{atTop}\,(\mathrm{nhds}\,(\href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,z))
$$

*Proof.* By [Lem 126](#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont). $\square$

<small>Referenced in [Lem 128](#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le"></a>
**Lemma 128** (`norm_kmsFun_sub_kmsFunCut_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1472)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{R : \mathbb{R}\}, 0 \le R \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,z - \href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,z\| \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le), [Lem 127](#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed). $\square$

<small>Referenced in [Lem 139](#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-zero"></a>
**Lemma 129** (`kmsFunCut_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1546)</small>

$$
\href{#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,0\,z = 0
$$

*Proof.* By [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont). $\square$

<small>Referenced in [Lem 139](#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-add-left"></a>
**Lemma 130** (`kmsFun_add_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1571)</small>

$$
0 < m \to \forall \{f_{1} f_{2} g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,(f_{1} + f_{2})\,g\,z = \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{1}\,g\,z + \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{2}\,g\,z
$$

*Proof.* By [Lem 126](#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add). $\square$

<small>Referenced in [Lem 132](#d-qiqth-fock-boostkms-kmsfun-sub-left).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-add-right"></a>
**Lemma 131** (`kmsFun_add_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1598)</small>

$$
0 < m \to \forall \{f g_{1} g_{2} : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g_{1} \to \mathrm{HasCompactSupport}\,g_{1} \to \mathrm{Continuous}\,g_{2} \to \mathrm{HasCompactSupport}\,g_{2} \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,(g_{1} + g_{2})\,z = \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g_{1}\,z + \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g_{2}\,z
$$

*Proof.* By [Lem 126](#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add). $\square$

<small>Referenced in [Lem 133](#d-qiqth-fock-boostkms-kmsfun-sub-right).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-sub-left"></a>
**Lemma 132** (`kmsFun_sub_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1624)</small>

$$
0 < m \to \forall \{f_{1} f_{2} g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,(f_{1} - f_{2})\,g\,z = \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{1}\,g\,z - \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{2}\,g\,z
$$

*Proof.* By [Lem 130](#d-qiqth-fock-boostkms-kmsfun-add-left), [Lem 358](#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub). $\square$

<small>Referenced in [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-sub-right"></a>
**Lemma 133** (`kmsFun_sub_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1651)</small>

$$
0 < m \to \forall \{f g_{1} g_{2} : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g_{1} \to \mathrm{HasCompactSupport}\,g_{1} \to \mathrm{Continuous}\,g_{2} \to \mathrm{HasCompactSupport}\,g_{2} \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,(g_{1} - g_{2})\,z = \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g_{1}\,z - \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g_{2}\,z
$$

*Proof.* By [Lem 131](#d-qiqth-fock-boostkms-kmsfun-add-right), [Lem 358](#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub). $\square$

<small>Referenced in [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-boostkms-norm-tolp-krep-eq-sqrt"></a>
**Lemma 134** (`norm_toLp_Krep_eq_sqrt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1678)</small>

$$
\|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf}\| = \sqrt (\int (\theta : \mathbb{R}), {\|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2})
$$

*Proof.* By [Lem 85](#d-qiqth-fock-boostkms-inner-krepl2). $\square$

<small>Referenced in [Lem 139](#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul).</small>

<a id="d-qiqth-fock-boostkms-minkowskifourier-smul"></a>
**Lemma 135** (`minkowskiFourier_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1695)</small>

$$
\href{#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,(\lambda x \mapsto c \cdot f\,x)\,p = c \cdot \href{#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f\,p
$$

*Proof.* By [Def 227](#d-qiqth-fock-localization-minkowskidot). $\square$

<small>Referenced in [Lem 136](#d-qiqth-fock-boostkms-krep-smul).</small>

<a id="d-qiqth-fock-boostkms-krep-smul"></a>
**Lemma 136** (`Krep_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1703)</small>

$$
(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,\lambda x \mapsto c \cdot f\,x) = \lambda \theta \mapsto c \cdot \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta
$$

*Proof.* By [Lem 135](#d-qiqth-fock-boostkms-minkowskifourier-smul), [Def 228](#d-qiqth-fock-localization-massshell), [Def 243](#d-qiqth-fock-localization-minkowskifourier). $\square$

<small>Referenced in [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul).</small>

<a id="d-qiqth-fock-boostkms-krepl2-add"></a>
**Lemma 137** (`KrepL2_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1708)</small>

$$
\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f_{1} + f_{2}))\,\cdots = \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,\mathrm{hf}_{1}L + \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L
$$

*Proof.* By [Lem 355](#d-qiqth-fock-wedgeanalyticity-krep-add). $\square$

<small>Referenced in [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add).</small>

<a id="d-qiqth-fock-boostkms-krepl2-sub"></a>
**Lemma 138** (`KrepL2_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1721)</small>

$$
\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f_{1} - f_{2}))\,\cdots = \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,\mathrm{hf}_{1}L - \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L
$$

*Proof.* By [Lem 356](#d-qiqth-fock-wedgeanalyticity-krep-sub). $\square$

<small>Referenced in [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul"></a>
**Lemma 139** (`norm_kmsFun_le_norm_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1733)</small>

$$
0 < m \to \forall \{f g : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \forall (\mathrm{hfL} : \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume}) (\mathrm{hgL} : \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume}) \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,z\| \le 2 \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hgL}\| \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hfL}\|
$$

*Proof.* By [Def 111](#d-qiqth-fock-boostkms-kmsfuncut), [Lem 128](#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le), [Lem 129](#d-qiqth-fock-boostkms-kmsfuncut-zero), [Lem 134](#d-qiqth-fock-boostkms-norm-tolp-krep-eq-sqrt). $\square$

<small>Referenced in [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfun-sub-le"></a>
**Lemma 140** (`norm_kmsFun_sub_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1762)</small>

$$
0 < m \to \forall \{f_{1} f_{2} g_{1} g_{2} : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{Continuous}\,g_{1} \to \mathrm{HasCompactSupport}\,g_{1} \to \mathrm{Continuous}\,g_{2} \to \mathrm{HasCompactSupport}\,g_{2} \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to \forall (\mathrm{hf}_{1}L : \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,2\,\mathrm{volume}) (\mathrm{hf}_{2}L : \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,2\,\mathrm{volume}) (\mathrm{hg}_{1}L : \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,2\,\mathrm{volume}) (\mathrm{hg}_{2}L : \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,2\,\mathrm{volume}) \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{1}\,g_{1}\,z - \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{2}\,g_{2}\,z\| \le 2 \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,\mathrm{hg}_{1}L\| \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,\mathrm{hf}_{1}L - \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L\| + 2 \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,\mathrm{hg}_{1}L - \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,\mathrm{hg}_{2}L\| \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L\|
$$

*Proof.* By [Lem 132](#d-qiqth-fock-boostkms-kmsfun-sub-left), [Lem 133](#d-qiqth-fock-boostkms-kmsfun-sub-right), [Lem 138](#d-qiqth-fock-boostkms-krepl2-sub), [Lem 139](#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul), [Lem 358](#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub). $\square$

<small>Referenced in [Lem 144](#d-qiqth-fock-boostkms-dist-kmsbcf-le).</small>

<a id="d-qiqth-fock-boostkms-memlp-krep-boosttest"></a>
**Lemma 141** (`memLp_Krep_boostTest`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1811)</small>

$$
\mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \forall (a : \mathbb{R}), \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,a\,f))\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 247](#d-qiqth-fock-localization-krep-boost). $\square$

<small>Referenced in [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot).</small>

<a id="d-qiqth-fock-boostkms-kmsbcf"></a>
**Definition 142** (`kmsBCF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1842)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v), [Def 246](#d-qiqth-fock-localization-krep) — see source for the body.

<small>Referenced in [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply), [Lem 144](#d-qiqth-fock-boostkms-dist-kmsbcf-le), [Lem 145](#d-qiqth-fock-boostkms-kmsbcf-congr), [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-kmsbcf-apply"></a>
**Lemma 143** (`kmsBCF_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1862)</small>

$$
(\href{#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}\,\mathrm{hfc}\,\mathrm{hg}\,\mathrm{hgc}\,h\delta\,\mathrm{hmf}\,\mathrm{hmg}\,\mathrm{hfr}\,\mathrm{hgr}\,\mathrm{hfL}\,\mathrm{hgL})\,z = \href{#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,z
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 144](#d-qiqth-fock-boostkms-dist-kmsbcf-le), [Lem 145](#d-qiqth-fock-boostkms-kmsbcf-congr), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-dist-kmsbcf-le"></a>
**Lemma 144** (`dist_kmsBCF_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1872)</small>

$$
\mathrm{dist}\,(\href{#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}_{1}\,\mathrm{hf}_{1}c\,\mathrm{hg}_{1}\,\mathrm{hg}_{1}c\,h\delta\,\mathrm{hmf}_{1}\,\mathrm{hmg}_{1}\,\mathrm{hf}_{1}r\,\mathrm{hg}_{1}r\,\mathrm{hf}_{1}L\,\mathrm{hg}_{1}L)\,(\href{#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}_{2}\,\mathrm{hf}_{2}c\,\mathrm{hg}_{2}\,\mathrm{hg}_{2}c\,h\delta\,\mathrm{hmf}_{2}\,\mathrm{hmg}_{2}\,\mathrm{hf}_{2}r\,\mathrm{hg}_{2}r\,\mathrm{hf}_{2}L\,\mathrm{hg}_{2}L) \le 2 \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,\mathrm{hg}_{1}L\| \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,\mathrm{hf}_{1}L - \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L\| + 2 \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,\mathrm{hg}_{1}L - \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,\mathrm{hg}_{2}L\| \cdot \|\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L\|
$$

*Proof.* By [Def 90](#d-qiqth-fock-boostkms-kmsfun), [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le), [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply). $\square$

<small>Referenced in [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le).</small>

<a id="d-qiqth-fock-boostkms-kmsbcf-congr"></a>
**Lemma 145** (`kmsBCF_congr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1899)</small>

$$
\href{#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}\,\mathrm{hfc}\,\mathrm{hg}\,\mathrm{hgc}\,h\delta\,\mathrm{hmf}\,\mathrm{hmg}\,\mathrm{hfr}\,\mathrm{hgr}\,\mathrm{hfL}\,\mathrm{hgL} = \href{#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}\,\mathrm{hfc}\,\mathrm{hg}\,\mathrm{hgc}\,h\delta'\,\mathrm{hmf}^{\prime}\,\mathrm{hmg}^{\prime}\,\mathrm{hfr}\,\mathrm{hgr}\,\mathrm{hfL}\,\mathrm{hgL}
$$

*Proof.* By [Def 90](#d-qiqth-fock-boostkms-kmsfun), [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply). $\square$

<small>Referenced in [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr).</small>

<a id="d-qiqth-fock-boostkms-nicetest"></a>
**Lemma 146** (`NiceTest`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1917)</small>

$$
\mathbb{R} \to Type
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 147](#d-qiqth-fock-boostkms-nicetest-mk), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 149](#d-qiqth-fock-boostkms-nicetest-cont), [Lem 150](#d-qiqth-fock-boostkms-nicetest-cpt), [Def 151](#d-qiqth-fock-boostkms-nicetest), [Lem 152](#d-qiqth-fock-boostkms-nicetest-h), [Lem 153](#d-qiqth-fock-boostkms-nicetest-margin), [Lem 154](#d-qiqth-fock-boostkms-nicetest-real), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Def 157](#d-qiqth-fock-boostkms-nicetest-add), [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add), [Lem 159](#d-qiqth-fock-boostkms-nicetest-margin-le), [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 163](#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Def 166](#d-qiqth-fock-boostkms-nicewedgegenset), [Lem 167](#d-qiqth-fock-boostkms-mem-nicewedgegenset), [Lem 168](#d-qiqth-fock-boostkms-nicewedgegenset-add-mem), [Def 169](#d-qiqth-fock-boostkms-nicetest-boost), [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost), [Lem 171](#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [Def 172](#d-qiqth-fock-boostkms-nicetest-zero), [Def 173](#d-qiqth-fock-boostkms-nicetest-smul), [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul), [Lem 176](#d-qiqth-fock-boostkms-zero-mem-nicewedgegenset), [Lem 177](#d-qiqth-fock-boostkms-nicewedgegenset-smul-mem), [Lem 187](#d-qiqth-fock-boostkms-nicewedge-dense-of-total), [Lem 188](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total), [Lem 189](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure), [Def 197](#d-qiqth-fock-boostkms-nicewedgecyclic), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero), [Def 210](#d-qiqth-fock-cyclicwitness-bumpnicetestw).</small>

<a id="d-qiqth-fock-boostkms-nicetest-mk"></a>
**Lemma 147** (`mk`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1923)</small>

$$
\{m : \mathbb{R}\} \to (f : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}) \to \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to (\delta : \mathbb{R}) \to 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \href{#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Def 157](#d-qiqth-fock-boostkms-nicetest-add), [Def 169](#d-qiqth-fock-boostkms-nicetest-boost), [Def 172](#d-qiqth-fock-boostkms-nicetest-zero), [Def 173](#d-qiqth-fock-boostkms-nicetest-smul), [Def 210](#d-qiqth-fock-cyclicwitness-bumpnicetestw).</small>

<a id="d-qiqth-fock-boostkms-nicetest-f"></a>
**Definition 148** (`f`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1925)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest), [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 149](#d-qiqth-fock-boostkms-nicetest-cont), [Lem 150](#d-qiqth-fock-boostkms-nicetest-cpt), [Lem 153](#d-qiqth-fock-boostkms-nicetest-margin), [Lem 154](#d-qiqth-fock-boostkms-nicetest-real), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Def 157](#d-qiqth-fock-boostkms-nicetest-add), [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add), [Lem 159](#d-qiqth-fock-boostkms-nicetest-margin-le), [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Def 169](#d-qiqth-fock-boostkms-nicetest-boost), [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost), [Def 173](#d-qiqth-fock-boostkms-nicetest-smul), [Lem 174](#d-qiqth-fock-boostkms-nicetest-zero-vec), [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul), [Lem 189](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure), [Def 197](#d-qiqth-fock-boostkms-nicewedgecyclic), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-nicetest-cont"></a>
**Lemma 149** (`cont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1926)</small>

$$
\mathrm{Continuous}\,\mathrm{self}.f
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add), [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-cpt"></a>
**Lemma 150** (`cpt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1927)</small>

$$
\mathrm{HasCompactSupport}\,\mathrm{self}.f
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add), [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest"></a>
**Definition 151** (`δ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1929)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest) — see source for the body.

<small>Referenced in [Lem 152](#d-qiqth-fock-boostkms-nicetest-h), [Lem 153](#d-qiqth-fock-boostkms-nicetest-margin), [Def 157](#d-qiqth-fock-boostkms-nicetest-add), [Lem 159](#d-qiqth-fock-boostkms-nicetest-margin-le), [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Def 169](#d-qiqth-fock-boostkms-nicetest-boost), [Def 173](#d-qiqth-fock-boostkms-nicetest-smul), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-h"></a>
**Lemma 152** (`hδ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1930)</small>

$$
0 < \mathrm{self}.\delta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Def 173](#d-qiqth-fock-boostkms-nicetest-smul), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-margin"></a>
**Lemma 153** (`margin`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1931)</small>

$$
\mathrm{self}.f\,x \ne 0 \to \mathrm{self}.\delta \le x\,1 - x\,0 \wedge \mathrm{self}.\delta \le x\,1 + x\,0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 159](#d-qiqth-fock-boostkms-nicetest-margin-le).</small>

<a id="d-qiqth-fock-boostkms-nicetest-real"></a>
**Lemma 154** (`real`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1932)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{self}.f\,x) = \mathrm{self}.f\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-memlp"></a>
**Lemma 155** (`memLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1933)</small>

$$
\mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,\mathrm{self}.f)\,2\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add), [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost), [Lem 174](#d-qiqth-fock-boostkms-nicetest-zero-vec), [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul), [Lem 189](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-nicetest-vec"></a>
**Definition 156** (`vec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1935)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest) — see source for the body.

<small>Referenced in [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 163](#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Def 166](#d-qiqth-fock-boostkms-nicewedgegenset), [Lem 167](#d-qiqth-fock-boostkms-mem-nicewedgegenset), [Lem 168](#d-qiqth-fock-boostkms-nicewedgegenset-add-mem), [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost), [Lem 171](#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [Lem 174](#d-qiqth-fock-boostkms-nicetest-zero-vec), [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul), [Lem 176](#d-qiqth-fock-boostkms-zero-mem-nicewedgegenset), [Lem 177](#d-qiqth-fock-boostkms-nicewedgegenset-smul-mem), [Lem 187](#d-qiqth-fock-boostkms-nicewedge-dense-of-total), [Lem 188](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total), [Lem 189](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-nicetest-add"></a>
**Definition 157** (`add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1939)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest) — see source for the body.

<small>Referenced in [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add), [Lem 168](#d-qiqth-fock-boostkms-nicewedgegenset-add-mem).</small>

<a id="d-qiqth-fock-boostkms-nicetest-vec-add"></a>
**Lemma 158** (`vec_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1958)</small>

$$
(N_{1}.\mathrm{add}\,N_{2}).\mathrm{vec} = N_{1}.\mathrm{vec} + N_{2}.\mathrm{vec}
$$

*Proof.* By [Lem 137](#d-qiqth-fock-boostkms-krepl2-add), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 149](#d-qiqth-fock-boostkms-nicetest-cont), [Lem 150](#d-qiqth-fock-boostkms-nicetest-cpt), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp). $\square$

<small>Referenced in [Lem 168](#d-qiqth-fock-boostkms-nicewedgegenset-add-mem).</small>

<a id="d-qiqth-fock-boostkms-nicetest-margin-le"></a>
**Lemma 159** (`margin_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1987)</small>

$$
\delta_{0} \le N.\delta \to \forall (x : \href{#d-qiqth-fock-localization-v}{V}), N.f\,x \ne 0 \to \delta_{0} \le x\,1 - x\,0 \wedge \delta_{0} \le x\,1 + x\,0
$$

*Proof.* By [Lem 153](#d-qiqth-fock-boostkms-nicetest-margin). $\square$

<small>Referenced in [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf"></a>
**Definition 160** (`bcf`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1994)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest) — see source for the body.

<small>Referenced in [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [Lem 163](#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf-congr"></a>
**Lemma 161** (`bcf_congr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2003)</small>

$$
\href{#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N\,M = \href{#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\cdots \,\cdots \,\cdots \,\cdots \,h\delta'\,\mathrm{hmf}^{\prime}\,\mathrm{hmg}^{\prime}\,\cdots \,\cdots \,\cdots \,\cdots
$$

*Proof.* By [Lem 145](#d-qiqth-fock-boostkms-kmsbcf-congr), [Def 151](#d-qiqth-fock-boostkms-nicetest), [Lem 152](#d-qiqth-fock-boostkms-nicetest-h), [Lem 159](#d-qiqth-fock-boostkms-nicetest-margin-le). $\square$

<small>Referenced in [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le).</small>

<a id="d-qiqth-fock-boostkms-nicetest-dist-bcf-le"></a>
**Lemma 162** (`dist_bcf_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2015)</small>

$$
\mathrm{dist}\,(\href{#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N_{1}\,M_{1})\,(\href{#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N_{2}\,M_{2}) \le 2 \cdot \|M_{1}.\mathrm{vec}\| \cdot \|N_{1}.\mathrm{vec} - N_{2}.\mathrm{vec}\| + 2 \cdot \|M_{1}.\mathrm{vec} - M_{2}.\mathrm{vec}\| \cdot \|N_{2}.\mathrm{vec}\|
$$

*Proof.* By [Def 142](#d-qiqth-fock-boostkms-kmsbcf), [Lem 144](#d-qiqth-fock-boostkms-dist-kmsbcf-le), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 149](#d-qiqth-fock-boostkms-nicetest-cont), [Lem 150](#d-qiqth-fock-boostkms-nicetest-cpt), [Def 151](#d-qiqth-fock-boostkms-nicetest), [Lem 152](#d-qiqth-fock-boostkms-nicetest-h), [Lem 154](#d-qiqth-fock-boostkms-nicetest-real), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Lem 159](#d-qiqth-fock-boostkms-nicetest-margin-le), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr). $\square$

<small>Referenced in [Lem 163](#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq"></a>
**Lemma 163** (`bcf_cauchySeq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2037)</small>

$$
\mathrm{Tendsto}\,(\lambda n \mapsto (N\,n).\mathrm{vec})\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi) \to \mathrm{Tendsto}\,(\lambda n \mapsto (M\,n).\mathrm{vec})\,\mathrm{atTop}\,(\mathrm{nhds}\,\eta) \to \mathrm{CauchySeq}\,\lambda n \mapsto \href{#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,(N\,n)\,(M\,n)
$$

*Proof.* By [Lem 162](#d-qiqth-fock-boostkms-nicetest-dist-bcf-le). $\square$

<small>Referenced in [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top"></a>
**Lemma 164** (`bcf_apply_eq_top`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2087)</small>

$$
z = t \to (\href{#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N\,M)\,z = \langle {M.\mathrm{vec}},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,N.\mathrm{vec}}\rangle
$$

*Proof.* By [Def 90](#d-qiqth-fock-boostkms-kmsfun), [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [Lem 141](#d-qiqth-fock-boostkms-memlp-krep-boosttest), [Def 142](#d-qiqth-fock-boostkms-kmsbcf), [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 149](#d-qiqth-fock-boostkms-nicetest-cont), [Lem 150](#d-qiqth-fock-boostkms-nicetest-cpt), [Def 151](#d-qiqth-fock-boostkms-nicetest), [Lem 154](#d-qiqth-fock-boostkms-nicetest-real), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp). $\square$

<small>Referenced in [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot"></a>
**Lemma 165** (`bcf_apply_eq_bot`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2096)</small>

$$
z = t - i \to (\href{#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N\,M)\,z = \langle {(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,N.\mathrm{vec}},{M.\mathrm{vec}}\rangle
$$

*Proof.* By [Def 90](#d-qiqth-fock-boostkms-kmsfun), [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [Lem 93](#d-qiqth-fock-boostkms-kmsfun-sub-i), [Lem 141](#d-qiqth-fock-boostkms-memlp-krep-boosttest), [Def 142](#d-qiqth-fock-boostkms-kmsbcf), [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 149](#d-qiqth-fock-boostkms-nicetest-cont), [Lem 150](#d-qiqth-fock-boostkms-nicetest-cpt), [Def 151](#d-qiqth-fock-boostkms-nicetest), [Lem 154](#d-qiqth-fock-boostkms-nicetest-real), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 246](#d-qiqth-fock-localization-krep). $\square$

<small>Referenced in [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicewedgegenset"></a>
**Definition 166** (`niceWedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2105)</small>

A definition — see source for the body.

<small>Referenced in [Lem 167](#d-qiqth-fock-boostkms-mem-nicewedgegenset), [Lem 168](#d-qiqth-fock-boostkms-nicewedgegenset-add-mem), [Lem 171](#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [Lem 176](#d-qiqth-fock-boostkms-zero-mem-nicewedgegenset), [Lem 177](#d-qiqth-fock-boostkms-nicewedgegenset-smul-mem), [Def 178](#d-qiqth-fock-boostkms-nicewedgesubmodule), [Lem 180](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [Lem 186](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense), [Lem 187](#d-qiqth-fock-boostkms-nicewedge-dense-of-total), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure), [Lem 193](#d-qiqth-fock-boostkms-stripkmsrvd-boostunitary), [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 220](#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-mem-nicewedgegenset"></a>
**Lemma 167** (`mem_niceWedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2111)</small>

$$
\xi \in \href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m \leftrightarrow \exists N, N.\mathrm{vec} = \xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicewedgegenset-add-mem"></a>
**Lemma 168** (`niceWedgeGenSet_add_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2115)</small>

$$
\xi \in \href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m \to \eta \in \href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m \to \xi + \eta \in \href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m
$$

*Proof.* By [Lem 146](#d-qiqth-fock-boostkms-nicetest), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Def 157](#d-qiqth-fock-boostkms-nicetest-add), [Lem 158](#d-qiqth-fock-boostkms-nicetest-vec-add). $\square$

<small>Referenced in [Def 178](#d-qiqth-fock-boostkms-nicewedgesubmodule).</small>

<a id="d-qiqth-fock-boostkms-nicetest-boost"></a>
**Definition 169** (`boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2149)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest) — see source for the body.

<small>Referenced in [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost), [Lem 171](#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-nicetest-vec-boost"></a>
**Lemma 170** (`vec_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2185)</small>

$$
(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,N.\mathrm{vec} = (N.\mathrm{boost}\,a).\mathrm{vec}
$$

*Proof.* By [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2). $\square$

<small>Referenced in [Lem 171](#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset"></a>
**Lemma 171** (`boostUnitary_mapsTo_niceWedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2190)</small>

$$
\mathrm{MapsTo}\,((\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a))\,(\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m)\,(\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m)
$$

*Proof.* By [Lem 146](#d-qiqth-fock-boostkms-nicetest), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Def 169](#d-qiqth-fock-boostkms-nicetest-boost), [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost). $\square$

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge).</small>

<a id="d-qiqth-fock-boostkms-nicetest-zero"></a>
**Definition 172** (`zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2220)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest) — see source for the body.

<small>Referenced in [Lem 174](#d-qiqth-fock-boostkms-nicetest-zero-vec), [Lem 176](#d-qiqth-fock-boostkms-zero-mem-nicewedgegenset).</small>

<a id="d-qiqth-fock-boostkms-nicetest-smul"></a>
**Definition 173** (`smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2231)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest) — see source for the body.

<small>Referenced in [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul), [Lem 177](#d-qiqth-fock-boostkms-nicewedgegenset-smul-mem).</small>

<a id="d-qiqth-fock-boostkms-nicetest-zero-vec"></a>
**Lemma 174** (`zero_vec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2243)</small>

$$
(\href{#d-qiqth-fock-boostkms-nicetest-zero}{\mathrm{zero}}\,m).\mathrm{vec} = 0
$$

*Proof.* By [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 226](#d-qiqth-fock-localization-v), [Def 246](#d-qiqth-fock-localization-krep), [Lem 249](#d-qiqth-fock-localization-krep-zero). $\square$

<small>Referenced in [Lem 176](#d-qiqth-fock-boostkms-zero-mem-nicewedgegenset).</small>

<a id="d-qiqth-fock-boostkms-nicetest-vec-smul"></a>
**Lemma 175** (`vec_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2251)</small>

$$
(\href{#d-qiqth-fock-boostkms-nicetest-smul}{\mathrm{smul}}\,c\,N).\mathrm{vec} = c \cdot N.\mathrm{vec}
$$

*Proof.* By [Lem 136](#d-qiqth-fock-boostkms-krep-smul), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 226](#d-qiqth-fock-localization-v), [Def 246](#d-qiqth-fock-localization-krep). $\square$

<small>Referenced in [Lem 177](#d-qiqth-fock-boostkms-nicewedgegenset-smul-mem).</small>

<a id="d-qiqth-fock-boostkms-zero-mem-nicewedgegenset"></a>
**Lemma 176** (`zero_mem_niceWedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2262)</small>

$$
0 \in \href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m
$$

*Proof.* By [Lem 146](#d-qiqth-fock-boostkms-nicetest), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Def 172](#d-qiqth-fock-boostkms-nicetest-zero), [Lem 174](#d-qiqth-fock-boostkms-nicetest-zero-vec). $\square$

<small>Referenced in [Def 178](#d-qiqth-fock-boostkms-nicewedgesubmodule).</small>

<a id="d-qiqth-fock-boostkms-nicewedgegenset-smul-mem"></a>
**Lemma 177** (`niceWedgeGenSet_smul_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2266)</small>

$$
\xi \in \href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m \to c \cdot \xi \in \href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m
$$

*Proof.* By [Lem 146](#d-qiqth-fock-boostkms-nicetest), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Def 173](#d-qiqth-fock-boostkms-nicetest-smul), [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul). $\square$

<small>Referenced in [Def 178](#d-qiqth-fock-boostkms-nicewedgesubmodule).</small>

<a id="d-qiqth-fock-boostkms-nicewedgesubmodule"></a>
**Definition 178** (`niceWedgeSubmodule`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2272)</small>

A definition — see source for the body.

<small>Referenced in [Def 179](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule), [Lem 180](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe).</small>

<a id="d-qiqth-fock-boostkms-nicewedgeclosedsubmodule"></a>
**Definition 179** (`niceWedgeClosedSubmodule`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2288)</small>

A definition — see source for the body.

<small>Referenced in [Lem 180](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [Def 181](#d-qiqth-fock-boostkms-nicewedgestandardsubspace), [Lem 186](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense), [Lem 188](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total), [Lem 189](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [Lem 191](#d-qiqth-fock-boostkms-nicewedge-isseparating-of-no-complex-line), [Lem 195](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [Def 196](#d-qiqth-fock-boostkms-nicewedgeseparating), [Lem 220](#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe"></a>
**Lemma 180** (`niceWedgeClosedSubmodule_coe`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2295)</small>

$$
(\href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m) = \overline{{\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}}
$$

*Proof.* By [Def 178](#d-qiqth-fock-boostkms-nicewedgesubmodule). $\square$

<small>Referenced in [Lem 186](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense), [Lem 195](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [Lem 220](#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-nicewedgestandardsubspace"></a>
**Definition 181** (`niceWedgeStandardSubspace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2301)</small>

A definition, built from [Def 179](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule) — see source for the body.

<small>Referenced in [Lem 195](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux), [Thm 225](#d-qiqth-fock-freefield-component-hflux), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-sup-muli-invariant"></a>
**Lemma 182** (`ClosedSubmodule_sup_mulI_invariant`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2316)</small>

$$
(KK.\mathrm{mulI}).\mathrm{mulI} = KK.\mathrm{mulI}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 185](#d-qiqth-fock-boostkms-closedsubmodule-sup-muli-eq-top-of-dense).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-smul-i-mem"></a>
**Lemma 183** (`closedSubmodule_smul_I_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2326)</small>

$$
S.\mathrm{mulI} = S \to \forall \{x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})\}, x \in S \to i \cdot x \in S
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 184](#d-qiqth-fock-boostkms-closedsubmodule-smul-complex-mem).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-smul-complex-mem"></a>
**Lemma 184** (`closedSubmodule_smul_complex_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2337)</small>

$$
S.\mathrm{mulI} = S \to \forall \{x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})\}, x \in S \to \forall (c : \mathbb{C}), c \cdot x \in S
$$

*Proof.* By [Lem 183](#d-qiqth-fock-boostkms-closedsubmodule-smul-i-mem). $\square$

<small>Referenced in [Lem 185](#d-qiqth-fock-boostkms-closedsubmodule-sup-muli-eq-top-of-dense).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-sup-muli-eq-top-of-dense"></a>
**Lemma 185** (`ClosedSubmodule_sup_mulI_eq_top_of_dense`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2351)</small>

$$
\forall G\subseteq K, \mathrm{Dense}\,(\mathrm{span}\,\mathbb{C}\,G) \to KK.\mathrm{mulI} = \top
$$

*Proof.* By [Lem 182](#d-qiqth-fock-boostkms-closedsubmodule-sup-muli-invariant), [Lem 184](#d-qiqth-fock-boostkms-closedsubmodule-smul-complex-mem). $\square$

<small>Referenced in [Lem 186](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense"></a>
**Lemma 186** (`niceWedge_isCyclic_of_dense`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2376)</small>

$$
\mathrm{Dense}\,(\mathrm{span}\,\mathbb{C}\,(\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m)) \to \href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \top
$$

*Proof.* By [Lem 180](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [Lem 185](#d-qiqth-fock-boostkms-closedsubmodule-sup-muli-eq-top-of-dense). $\square$

<small>Referenced in [Lem 188](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-dense-of-total"></a>
**Lemma 187** (`niceWedge_dense_of_total`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2389)</small>

$$
(\forall (h : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (N : \href{#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m), \langle {N.\mathrm{vec}},{h}\rangle = 0) \to h = 0) \to \mathrm{Dense}\,(\mathrm{span}\,\mathbb{C}\,(\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 188](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total"></a>
**Lemma 188** (`niceWedge_isCyclic_of_total`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2410)</small>

$$
(\forall (h : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (N : \href{#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m), \langle {N.\mathrm{vec}},{h}\rangle = 0) \to h = 0) \to \href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \top
$$

*Proof.* By [Lem 186](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense), [Lem 187](#d-qiqth-fock-boostkms-nicewedge-dense-of-total). $\square$

<small>Referenced in [Lem 189](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral"></a>
**Lemma 189** (`niceWedge_isCyclic_of_total_integral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2420)</small>

$$
(\forall (h : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (N : \href{#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m), \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,N.f\,\theta) \cdot h\,\theta = 0) \to h = 0) \to \href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \top
$$

*Proof.* By [Lem 86](#d-qiqth-fock-boostkms-inner-krepl2-general), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Lem 188](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total). $\square$

<small>Referenced in [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux), [Thm 225](#d-qiqth-fock-freefield-component-hflux), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-smul-i-mem-of-mem-muli"></a>
**Lemma 190** (`closedSubmodule_smul_I_mem_of_mem_mulI`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2505)</small>

$$
v \in K.\mathrm{mulI} \to i \cdot v \in K
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 191](#d-qiqth-fock-boostkms-nicewedge-isseparating-of-no-complex-line).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-isseparating-of-no-complex-line"></a>
**Lemma 191** (`niceWedge_isSeparating_of_no_complex_line`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2518)</small>

$$
(\forall v\in \href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m, i \cdot v \in \href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m \to v = 0) \to \href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \bot
$$

*Proof.* By [Lem 190](#d-qiqth-fock-boostkms-closedsubmodule-smul-i-mem-of-mem-muli). $\square$

<small>Referenced in [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux), [Thm 225](#d-qiqth-fock-freefield-component-hflux), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-boostkms-stripkmsrvd-closure"></a>
**Lemma 192** (`stripKMSrvd_closure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2535)</small>

$$
0 < m \to \forall \{\xi \eta : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})\}, \xi \in \overline{{\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}} \to \eta \in \overline{{\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}} \to \exists F, \mathrm{DiffContOnCl}\,\mathbb{C}\,F\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \wedge (\exists C, \forall (z : \mathbb{C}), \|F\,z\| \le C) \wedge (\forall (t : \mathbb{R}), F\,t = \langle {\eta},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,\xi}\rangle) \wedge \forall (t : \mathbb{R}), F\,(t - i) = \langle {(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,\xi},{\eta}\rangle
$$

*Proof.* By [Def 90](#d-qiqth-fock-boostkms-kmsfun), [Lem 110](#d-qiqth-fock-boostkms-kmsfun-differentiableon), [Def 142](#d-qiqth-fock-boostkms-kmsbcf), [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply), [Lem 146](#d-qiqth-fock-boostkms-nicetest), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 149](#d-qiqth-fock-boostkms-nicetest-cont), [Lem 150](#d-qiqth-fock-boostkms-nicetest-cpt), [Def 151](#d-qiqth-fock-boostkms-nicetest), [Lem 152](#d-qiqth-fock-boostkms-nicetest-h), [Lem 154](#d-qiqth-fock-boostkms-nicetest-real), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Lem 159](#d-qiqth-fock-boostkms-nicetest-margin-le), [Def 160](#d-qiqth-fock-boostkms-nicetest-bcf), [Lem 163](#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 167](#d-qiqth-fock-boostkms-mem-nicewedgegenset). $\square$

<small>Referenced in [Lem 193](#d-qiqth-fock-boostkms-stripkmsrvd-boostunitary), [Lem 220](#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-stripkmsrvd-boostunitary"></a>
**Lemma 193** (`stripKMSrvd_boostUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2645)</small>

$$
0 < m \to \href{#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,(\lambda t \mapsto (\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t)))\,(\overline{{\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}})
$$

*Proof.* By [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure). $\square$

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge).</small>

<a id="d-qiqth-fock-boostkms-oneparticlebw-nicewedge"></a>
**Lemma 194** (`oneParticleBW_niceWedge`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2656)</small>

$$
0 < m \to \forall (S : \mathrm{StandardSubspace}\,(\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})) (V : \mathbb{R} \to (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume}) \to L[\mathbb{C}] (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), S.\mathrm{cl} = \overline{{\href{#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}} \to (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,x) \to \forall (t : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [Lem 171](#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [Lem 193](#d-qiqth-fock-boostkms-stripkmsrvd-boostunitary), [Lem 274](#d-qiqth-fock-oneparticle-boostunitary-add-apply), [Lem 275](#d-qiqth-fock-oneparticle-boostunitary-zero-apply), [Lem 279](#d-qiqth-fock-oneparticlebw-continuous-boostunitary-apply), [Def 283](#d-qiqth-fock-oneparticlebw-stripkmsrvd), [Lem 295](#d-qiqth-fock-oneparticlebw-oneparticlebw-complete), [Def 672](#d-qiqth-standardsubspacemodular-projk), [Lem 745](#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [Def 848](#d-qiqth-standardsubspacemodular-gausssmear), [Lem 850](#d-qiqth-standardsubspacemodular-gausssmear-mem-k). $\square$

<small>Referenced in [Lem 195](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard).</small>

<a id="d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard"></a>
**Lemma 195** (`oneParticleBW_niceWedge_of_standard`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2706)</small>

$$
0 < m \to \forall (V : \mathbb{R} \to (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume}) \to L[\mathbb{C}] (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,x) \to \forall (\mathrm{hsep} : \href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \bot ) (\mathrm{hcyc} : \href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \top ) (t : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\mathrm{hsep}\,\mathrm{hcyc})\,t = V\,t
$$

*Proof.* By [Lem 180](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge). $\square$

<small>Referenced in [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder).</small>

<a id="d-qiqth-fock-boostkms-nicewedgeseparating"></a>
**Definition 196** (`NiceWedgeSeparating`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2767)</small>

A definition — see source for the body.

<small>Referenced in [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [Lem 220](#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-nicewedgecyclic"></a>
**Definition 197** (`NiceWedgeCyclic`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2775)</small>

A definition — see source for the body.

<small>Referenced in [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero), [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [Lem 217](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero), [Lem 218](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero"></a>
**Lemma 198** (`niceWedgeCyclic_of_fourier_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2784)</small>

$$
(\forall (\xi : \mathbb{R}), (\mathcal{F}\,N_{0}.\mathrm{vec})\,\xi \ne 0) \to \href{#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m
$$

*Proof.* By [Lem 86](#d-qiqth-fock-boostkms-inner-krepl2-general), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 169](#d-qiqth-fock-boostkms-nicetest-boost), [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost), [Def 246](#d-qiqth-fock-localization-krep), [Def 273](#d-qiqth-fock-oneparticle-boostunitary), [Lem 379](#d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero). $\square$

<small>Referenced in [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw).</small>

<a id="d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder"></a>
**Lemma 199** (`oneParticleBW_niceWedge_reehSchlieder`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2800)</small>

$$
0 < m \to \forall (V : \mathbb{R} \to (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume}) \to L[\mathbb{C}] (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,x) \to \forall (\mathrm{hsep} : \href{#d-qiqth-fock-boostkms-nicewedgeseparating}{\mathrm{NiceWedgeSeparating}}\,m) (\mathrm{hcyc} : \href{#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m) (t : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t = V\,t
$$

*Proof.* By [Lem 195](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard). $\square$

<small>Referenced in [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional).</small>

<a id="sec-qiqth-fock-cyclicwitness"></a>
## QIQTH.Fock.CyclicWitness

<a id="d-qiqth-fock-cyclicwitness-bump1w"></a>
**Definition 200** (`bump1W`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L218)</small>

A definition — see source for the body.

<small>Referenced in [Lem 201](#d-qiqth-fock-cyclicwitness-bump1w-rout), [Lem 202](#d-qiqth-fock-cyclicwitness-bump1w-rin), [Def 203](#d-qiqth-fock-cyclicwitness-bumprealw), [Lem 205](#d-qiqth-fock-cyclicwitness-bumprealw-contdiff), [Lem 206](#d-qiqth-fock-cyclicwitness-bumpcw-contdiff), [Lem 208](#d-qiqth-fock-cyclicwitness-bumprealw-support-subset), [Lem 212](#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [Lem 213](#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of), [Lem 216](#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero), [Lem 217](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-bump1w-rout"></a>
**Lemma 201** (`bump1W_rOut`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L222)</small>

$$
(\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,c).\mathrm{rOut} = R
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 208](#d-qiqth-fock-cyclicwitness-bumprealw-support-subset), [Lem 216](#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-bump1w-rin"></a>
**Lemma 202** (`bump1W_rIn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L224)</small>

$$
(\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,c).\mathrm{rIn} = R / 2
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 216](#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-bumprealw"></a>
**Definition 203** (`bumpRealW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L226)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Def 204](#d-qiqth-fock-cyclicwitness-bumpcw), [Lem 205](#d-qiqth-fock-cyclicwitness-bumprealw-contdiff), [Lem 208](#d-qiqth-fock-cyclicwitness-bumprealw-support-subset), [Lem 209](#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpcw"></a>
**Definition 204** (`bumpCW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L230)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 206](#d-qiqth-fock-cyclicwitness-bumpcw-contdiff), [Lem 207](#d-qiqth-fock-cyclicwitness-bumpcw-continuous), [Lem 209](#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport), [Def 210](#d-qiqth-fock-cyclicwitness-bumpnicetestw), [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [Lem 212](#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [Lem 213](#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of).</small>

<a id="d-qiqth-fock-cyclicwitness-bumprealw-contdiff"></a>
**Lemma 205** (`bumpRealW_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L233)</small>

$$
({\href{#d-qiqth-fock-cyclicwitness-bumprealw}{\mathrm{bump}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}})\in C^{\infty}
$$

*Proof.* By [Def 200](#d-qiqth-fock-cyclicwitness-bump1w). $\square$

<small>Referenced in [Lem 206](#d-qiqth-fock-cyclicwitness-bumpcw-contdiff).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpcw-contdiff"></a>
**Lemma 206** (`bumpCW_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L241)</small>

$$
({\href{#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}})\in C^{\infty}
$$

*Proof.* By [Def 200](#d-qiqth-fock-cyclicwitness-bump1w), [Lem 205](#d-qiqth-fock-cyclicwitness-bumprealw-contdiff). $\square$

<small>Referenced in [Lem 207](#d-qiqth-fock-cyclicwitness-bumpcw-continuous), [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpcw-continuous"></a>
**Lemma 207** (`bumpCW_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L244)</small>

$$
\mathrm{Continuous}\,(\href{#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX})
$$

*Proof.* By [Lem 206](#d-qiqth-fock-cyclicwitness-bumpcw-contdiff). $\square$

<small>Referenced in [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of).</small>

<a id="d-qiqth-fock-cyclicwitness-bumprealw-support-subset"></a>
**Lemma 208** (`bumpRealW_support_subset`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L251)</small>

$$
\mathrm{support}\,(\href{#d-qiqth-fock-cyclicwitness-bumprealw}{\mathrm{bump}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}) \subseteq \{x||x\,0 - \mathrm{cT}| \le R \wedge |x\,1 - \mathrm{cX}| \le R\}
$$

*Proof.* By [Def 200](#d-qiqth-fock-cyclicwitness-bump1w), [Lem 201](#d-qiqth-fock-cyclicwitness-bump1w-rout). $\square$

<small>Referenced in [Lem 209](#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport"></a>
**Lemma 209** (`bumpCW_hasCompactSupport`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L264)</small>

$$
\mathrm{HasCompactSupport}\,(\href{#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX})
$$

*Proof.* By [Def 203](#d-qiqth-fock-cyclicwitness-bumprealw), [Lem 208](#d-qiqth-fock-cyclicwitness-bumprealw-support-subset). $\square$

<small>Referenced in [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpnicetestw"></a>
**Definition 210** (`bumpNiceTestW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L287)</small>

A definition, built from [Lem 146](#d-qiqth-fock-boostkms-nicetest) — see source for the body.

<small>Referenced in [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw).</small>

<a id="d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw"></a>
**Lemma 211** (`niceWedgeCyclic_bumpW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L305)</small>

$$
m \ne 0 \to 2 \cdot R < \mathrm{cX} \to \neg \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\cdots .\mathrm{toSchwartzMap}\,\cdots ) =[\mathrm{volume}] 0 \to \href{#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m
$$

*Proof.* By [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero), [Def 210](#d-qiqth-fock-cyclicwitness-bumpnicetestw), [Lem 403](#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero). $\square$

<small>Referenced in [Lem 217](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw"></a>
**Lemma 212** (`minkowskiFourier_bumpCW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L314)</small>

$$
\href{#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,(\href{#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX})\,p = (\int (y : \mathbb{R}), \exp\,(-i \cdot (p\,0 \cdot y)) \cdot ((\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cT})\,y)) \cdot \int (y : \mathbb{R}), \exp\,(i \cdot (p\,1 \cdot y)) \cdot ((\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cX})\,y)
$$

*Proof.* By [Def 227](#d-qiqth-fock-localization-minkowskidot). $\square$

<small>Referenced in [Lem 213](#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-krep-bumpcw-zero"></a>
**Lemma 213** (`Krep_bumpCW_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L337)</small>

$$
\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX})\,0 = 1 / \sqrt 2 \cdot ((\int (y : \mathbb{R}), \exp\,(-i \cdot (m \cdot y)) \cdot ((\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cT})\,y)) \cdot \int (y : \mathbb{R}), ((\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cX})\,y))
$$

*Proof.* By [Lem 212](#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [Def 228](#d-qiqth-fock-localization-massshell), [Def 243](#d-qiqth-fock-localization-minkowskifourier). $\square$

<small>Referenced in [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of).</small>

<a id="d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of"></a>
**Lemma 214** (`Krep_bumpCW_ne_zero_of`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L347)</small>

$$
\int (y : \mathbb{R}), \exp\,(-i \cdot (m \cdot y)) \cdot ((\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cT})\,y) \ne 0 \to \neg \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}) =[\mathrm{volume}] 0
$$

*Proof.* By [Lem 207](#d-qiqth-fock-cyclicwitness-bumpcw-continuous), [Lem 209](#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport), [Lem 213](#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [Def 226](#d-qiqth-fock-localization-v), [Lem 254](#d-qiqth-fock-localization-krep-continuous). $\square$

<small>Referenced in [Lem 217](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-fourier-re-eq"></a>
**Lemma 215** (`fourier_re_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L373)</small>

$$
(\exp\,(-i \cdot (m \cdot y)) \cdot (g\,y)).\mathrm{re} = \cos\,(m \cdot y) \cdot g\,y
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 216](#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero"></a>
**Lemma 216** (`bump1W_fourier_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L381)</small>

$$
0 < m \to \forall (\mathrm{hR} : 0 < R), m \cdot R < \pi / 2 \to \int (y : \mathbb{R}), \exp\,(-i \cdot (m \cdot y)) \cdot ((\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,0)\,y) \ne 0
$$

*Proof.* By [Lem 201](#d-qiqth-fock-cyclicwitness-bump1w-rout), [Lem 202](#d-qiqth-fock-cyclicwitness-bump1w-rin), [Lem 215](#d-qiqth-fock-cyclicwitness-fourier-re-eq). $\square$

<small>Referenced in [Lem 218](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-pos-mass).</small>

<a id="d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero"></a>
**Lemma 217** (`niceWedgeCyclic_of_bumpW_fourier_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L444)</small>

$$
m \ne 0 \to 2 \cdot R < \mathrm{cX} \to \int (y : \mathbb{R}), \exp\,(-i \cdot (m \cdot y)) \cdot ((\href{#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,0)\,y) \ne 0 \to \href{#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m
$$

*Proof.* By [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of). $\square$

<small>Referenced in [Lem 218](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-pos-mass).</small>

<a id="d-qiqth-fock-cyclicwitness-nicewedgecyclic-pos-mass"></a>
**Lemma 218** (`niceWedgeCyclic_pos_mass`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L451)</small>

$$
0 < m \to \href{#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m
$$

*Proof.* By [Lem 216](#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero), [Lem 217](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero). $\square$

<small>Referenced in [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux), [Thm 225](#d-qiqth-fock-freefield-component-hflux), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-cyclicwitness-strip-eqzero-of-top-edge-zero"></a>
**Lemma 219** (`strip_eqZero_of_top_edge_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L468)</small>

$$
\mathrm{DifferentiableOn}\,\mathbb{C}\,\Phi\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \to \mathrm{ContinuousOn}\,\Phi\,(\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0) \to \mathrm{BddAbove}\,(\mathrm{norm} \circ \Phi '' \mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0) \to (\forall (t : \mathbb{R}), \Phi\,t = 0) \to \forall (t : \mathbb{R}), \Phi\,(t - i) = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 220](#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass"></a>
**Lemma 220** (`niceWedgeSeparating_pos_mass`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L594)</small>

$$
0 < m \to \href{#d-qiqth-fock-boostkms-nicewedgeseparating}{\mathrm{NiceWedgeSeparating}}\,m
$$

*Proof.* By [Def 166](#d-qiqth-fock-boostkms-nicewedgegenset), [Def 179](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule), [Lem 180](#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure), [Lem 219](#d-qiqth-fock-cyclicwitness-strip-eqzero-of-top-edge-zero), [Def 273](#d-qiqth-fock-oneparticle-boostunitary), [Lem 275](#d-qiqth-fock-oneparticle-boostunitary-zero-apply). $\square$

<small>Referenced in [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux), [Thm 225](#d-qiqth-fock-freefield-component-hflux), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional"></a>
**Theorem 221** (`oneParticleBW_niceWedge_unconditional`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L693)</small>

$$
(\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,x) \to \forall (t : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t = V\,t
$$

*Proof.* By [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder). $\square$

<small>Referenced in [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge).</small>

<a id="sec-qiqth-fock-freefieldhflux"></a>
## QIQTH.Fock.FreeFieldHFlux

<a id="d-qiqth-fock-freefield-modularenergy-eq-boostcharge"></a>
**Lemma 222** (`freeField_modularEnergy_eq_boostCharge`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L40)</small>

$$
({\lambda t \mapsto \langle {\xi},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,\xi}\rangle})'({0})={c} \to ({\lambda t \mapsto \langle {\xi},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t)\,\xi}\rangle})'({0})={c}
$$

*Proof.* By [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional). $\square$

<small>Referenced in [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux).</small>

<a id="d-qiqth-fock-hasderivat-inner-boostunitary-imaginary-pos"></a>
**Lemma 223** (`hasDerivAt_inner_boostUnitary_imaginary_pos`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L64)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im}}
$$

*Proof.* By [Lem 282](#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary). $\square$

<small>Referenced in [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux).</small>

<a id="d-qiqth-fock-freefield-oneparticle-hflux"></a>
**Theorem 224** (`freeField_oneParticle_hFlux`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L104)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to \forall (\hbar T_{kk} : \mathbb{R}), 2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im} \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})}
$$

*Proof.* By [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [Lem 223](#d-qiqth-fock-hasderivat-inner-boostunitary-imaginary-pos), [Def 273](#d-qiqth-fock-oneparticle-boostunitary). $\square$

<small>Referenced in [Thm 225](#d-qiqth-fock-freefield-component-hflux), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized).</small>

<a id="d-qiqth-fock-freefield-component-hflux"></a>
**Theorem 225** (`freeField_component_hFlux`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L134)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to \forall (\hbar \mathrm{kd} T_{kk} : \mathbb{R}), 2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im} \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot \mathrm{kd}} \to \mathrm{kd} = 2 \cdot \pi / \hbar \cdot T_{kk}
$$

*Proof.* By [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux). $\square$

<small>Referenced in [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion).</small>

<a id="sec-qiqth-fock-localization"></a>
## QIQTH.Fock.Localization

<a id="d-qiqth-fock-localization-v"></a>
**Definition 226** (`V`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L33)</small>

A definition — see source for the body.

<small>Referenced in [Lem 85](#d-qiqth-fock-boostkms-inner-krepl2), [Lem 86](#d-qiqth-fock-boostkms-inner-krepl2-general), [Lem 87](#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [Lem 88](#d-qiqth-fock-boostkms-symm-edge-eq-shifted), [Lem 89](#d-qiqth-fock-boostkms-symm-edge-eq-inner), [Def 90](#d-qiqth-fock-boostkms-kmsfun), [Lem 91](#d-qiqth-fock-boostkms-kmsfun-ofreal), [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [Lem 93](#d-qiqth-fock-boostkms-kmsfun-sub-i), [Lem 94](#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [Lem 95](#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [Lem 96](#d-qiqth-fock-boostkms-deriv-reflkrepcont-eq), [Lem 97](#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le), [Lem 98](#d-qiqth-fock-boostkms-differentiable-kmsintegrand), [Lem 99](#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [Lem 101](#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [Lem 102](#d-qiqth-fock-boostkms-continuous-deriv-reflkrepcont), [Lem 103](#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta), [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 106](#d-qiqth-fock-boostkms-norm-term1-le), [Lem 107](#d-qiqth-fock-boostkms-norm-term2-le), [Lem 108](#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound), [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 110](#d-qiqth-fock-boostkms-kmsfun-differentiableon), [Def 111](#d-qiqth-fock-boostkms-kmsfuncut), [Lem 112](#d-qiqth-fock-boostkms-norm-kmsfuncut-le), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat), [Lem 114](#d-qiqth-fock-boostkms-kmsfuncut-differentiableon), [Lem 115](#d-qiqth-fock-boostkms-kmsfuncut-continuouson), [Lem 116](#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [Lem 117](#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [Lem 120](#d-qiqth-fock-boostkms-tail-term-le), [Lem 122](#d-qiqth-fock-boostkms-tail-integral-le), [Lem 123](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le), [Lem 124](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le), [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le), [Lem 126](#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [Lem 127](#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed), [Lem 128](#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le), [Lem 129](#d-qiqth-fock-boostkms-kmsfuncut-zero), [Lem 130](#d-qiqth-fock-boostkms-kmsfun-add-left), [Lem 131](#d-qiqth-fock-boostkms-kmsfun-add-right), [Lem 132](#d-qiqth-fock-boostkms-kmsfun-sub-left), [Lem 133](#d-qiqth-fock-boostkms-kmsfun-sub-right), [Lem 134](#d-qiqth-fock-boostkms-norm-tolp-krep-eq-sqrt), [Lem 135](#d-qiqth-fock-boostkms-minkowskifourier-smul), [Lem 136](#d-qiqth-fock-boostkms-krep-smul), [Lem 137](#d-qiqth-fock-boostkms-krepl2-add), [Lem 138](#d-qiqth-fock-boostkms-krepl2-sub), [Lem 139](#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul), [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le), [Lem 141](#d-qiqth-fock-boostkms-memlp-krep-boosttest), [Def 142](#d-qiqth-fock-boostkms-kmsbcf), [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply), [Lem 144](#d-qiqth-fock-boostkms-dist-kmsbcf-le), [Lem 145](#d-qiqth-fock-boostkms-kmsbcf-congr), [Lem 147](#d-qiqth-fock-boostkms-nicetest-mk), [Def 148](#d-qiqth-fock-boostkms-nicetest-f), [Lem 149](#d-qiqth-fock-boostkms-nicetest-cont), [Lem 150](#d-qiqth-fock-boostkms-nicetest-cpt), [Lem 153](#d-qiqth-fock-boostkms-nicetest-margin), [Lem 154](#d-qiqth-fock-boostkms-nicetest-real), [Def 157](#d-qiqth-fock-boostkms-nicetest-add), [Lem 159](#d-qiqth-fock-boostkms-nicetest-margin-le), [Lem 161](#d-qiqth-fock-boostkms-nicetest-bcf-congr), [Def 172](#d-qiqth-fock-boostkms-nicetest-zero), [Def 173](#d-qiqth-fock-boostkms-nicetest-smul), [Lem 174](#d-qiqth-fock-boostkms-nicetest-zero-vec), [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul), [Def 203](#d-qiqth-fock-cyclicwitness-bumprealw), [Def 204](#d-qiqth-fock-cyclicwitness-bumpcw), [Lem 205](#d-qiqth-fock-cyclicwitness-bumprealw-contdiff), [Lem 206](#d-qiqth-fock-cyclicwitness-bumpcw-contdiff), [Lem 207](#d-qiqth-fock-cyclicwitness-bumpcw-continuous), [Lem 208](#d-qiqth-fock-cyclicwitness-bumprealw-support-subset), [Lem 209](#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport), [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [Lem 212](#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of), [Def 227](#d-qiqth-fock-localization-minkowskidot), [Def 228](#d-qiqth-fock-localization-massshell), [Def 229](#d-qiqth-fock-localization-lorentzboost), [Lem 232](#d-qiqth-fock-localization-lorentzboost-zero), [Lem 233](#d-qiqth-fock-localization-lorentzboost-one), [Lem 234](#d-qiqth-fock-localization-massshell-boost), [Lem 235](#d-qiqth-fock-localization-minkowskidot-boost), [Lem 238](#d-qiqth-fock-localization-lorentzboost-apply), [Lem 240](#d-qiqth-fock-localization-measurepreserving-lorentzboost), [Lem 242](#d-qiqth-fock-localization-measurableembedding-lorentzboost), [Def 243](#d-qiqth-fock-localization-minkowskifourier), [Def 244](#d-qiqth-fock-localization-boosttest), [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost), [Def 246](#d-qiqth-fock-localization-krep), [Lem 247](#d-qiqth-fock-localization-krep-boost), [Lem 248](#d-qiqth-fock-localization-minkowskifourier-zero), [Lem 249](#d-qiqth-fock-localization-krep-zero), [Lem 250](#d-qiqth-fock-localization-continuous-minkowskidot-fst), [Lem 251](#d-qiqth-fock-localization-continuous-minkowskidot-snd), [Lem 252](#d-qiqth-fock-localization-minkowskifourier-continuous), [Lem 253](#d-qiqth-fock-localization-continuous-massshell), [Lem 254](#d-qiqth-fock-localization-krep-continuous), [Lem 255](#d-qiqth-fock-localization-krep-aestronglymeasurable), [Lem 259](#d-qiqth-fock-localization-krep-memlp-of-decay), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [Def 296](#d-qiqth-fock-localization-minkbilin), [Lem 297](#d-qiqth-fock-localization-minkbilin-apply), [Lem 298](#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq), [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 307](#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 312](#d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell), [Lem 313](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel), [Def 314](#d-qiqth-fock-wedgeanalyticity-kernelderiv), [Lem 315](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul), [Lem 316](#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x), [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [Lem 325](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le), [Lem 326](#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x), [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont), [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [Lem 329](#d-qiqth-fock-wedgeanalyticity-continuous-deriv-krepcont), [Lem 330](#d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq), [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [Lem 344](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq), [Lem 345](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq), [Lem 346](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay), [Lem 347](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay), [Lem 348](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay), [Lem 349](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay), [Lem 350](#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay), [Lem 351](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen), [Lem 352](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const), [Lem 353](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add), [Lem 355](#d-qiqth-fock-wedgeanalyticity-krep-add), [Lem 356](#d-qiqth-fock-wedgeanalyticity-krep-sub), [Lem 357](#d-qiqth-fock-wedgeanalyticity-memlp-krep-add), [Lem 358](#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub), [Lem 359](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed), [Lem 384](#d-qiqth-fock-wienerl2-integrable-krep), [Def 385](#d-qiqth-fock-wienerl2-ftkrep), [Def 386](#d-qiqth-fock-wienerl2-ftkrep), [Def 387](#d-qiqth-fock-wienerl2-ftkrepf), [Lem 388](#d-qiqth-fock-wienerl2-hasderivat-ftkrep), [Lem 390](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 391](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 392](#d-qiqth-fock-wienerl2-norm-krep-le-exp), [Lem 393](#d-qiqth-fock-wienerl2-continuous-ftkrep), [Lem 394](#d-qiqth-fock-wienerl2-continuous-ftkrep), [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep), [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf), [Lem 397](#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real), [Lem 398](#d-qiqth-fock-wienerl2-ftkrepf-eq-fourier), [Lem 399](#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep), [Lem 403](#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-localization-minkowskidot"></a>
**Definition 227** (`minkowskiDot`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L36)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 135](#d-qiqth-fock-boostkms-minkowskifourier-smul), [Lem 212](#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [Lem 235](#d-qiqth-fock-localization-minkowskidot-boost), [Def 243](#d-qiqth-fock-localization-minkowskifourier), [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost), [Lem 248](#d-qiqth-fock-localization-minkowskifourier-zero), [Lem 250](#d-qiqth-fock-localization-continuous-minkowskidot-fst), [Lem 251](#d-qiqth-fock-localization-continuous-minkowskidot-snd), [Lem 252](#d-qiqth-fock-localization-minkowskifourier-continuous), [Lem 298](#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [Lem 307](#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i).</small>

<a id="d-qiqth-fock-localization-massshell"></a>
**Definition 228** (`massShell`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L42)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 136](#d-qiqth-fock-boostkms-krep-smul), [Lem 213](#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [Lem 230](#d-qiqth-fock-localization-massshell-zero), [Lem 231](#d-qiqth-fock-localization-massshell-one), [Lem 234](#d-qiqth-fock-localization-massshell-boost), [Def 246](#d-qiqth-fock-localization-krep), [Lem 247](#d-qiqth-fock-localization-krep-boost), [Lem 249](#d-qiqth-fock-localization-krep-zero), [Lem 253](#d-qiqth-fock-localization-continuous-massshell), [Lem 254](#d-qiqth-fock-localization-krep-continuous), [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq), [Lem 305](#d-qiqth-fock-wedgeanalyticity-massshell-ofreal), [Lem 307](#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i).</small>

<a id="d-qiqth-fock-localization-lorentzboost"></a>
**Definition 229** (`lorentzBoost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L45)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 232](#d-qiqth-fock-localization-lorentzboost-zero), [Lem 233](#d-qiqth-fock-localization-lorentzboost-one), [Lem 234](#d-qiqth-fock-localization-massshell-boost), [Lem 235](#d-qiqth-fock-localization-minkowskidot-boost), [Lem 238](#d-qiqth-fock-localization-lorentzboost-apply), [Lem 240](#d-qiqth-fock-localization-measurepreserving-lorentzboost), [Lem 242](#d-qiqth-fock-localization-measurableembedding-lorentzboost), [Def 244](#d-qiqth-fock-localization-boosttest), [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost), [Lem 247](#d-qiqth-fock-localization-krep-boost).</small>

<a id="d-qiqth-fock-localization-massshell-zero"></a>
**Lemma 230** (`massShell_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L49)</small>

$$
\href{#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta\,0 = m \cdot \cosh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 234](#d-qiqth-fock-localization-massshell-boost).</small>

<a id="d-qiqth-fock-localization-massshell-one"></a>
**Lemma 231** (`massShell_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L50)</small>

$$
\href{#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta\,1 = m \cdot \sinh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 234](#d-qiqth-fock-localization-massshell-boost).</small>

<a id="d-qiqth-fock-localization-lorentzboost-zero"></a>
**Lemma 232** (`lorentzBoost_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L51)</small>

$$
\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,z\,0 = \cosh\,a \cdot z\,0 + \sinh\,a \cdot z\,1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 234](#d-qiqth-fock-localization-massshell-boost).</small>

<a id="d-qiqth-fock-localization-lorentzboost-one"></a>
**Lemma 233** (`lorentzBoost_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L53)</small>

$$
\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,z\,1 = \sinh\,a \cdot z\,0 + \cosh\,a \cdot z\,1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 234](#d-qiqth-fock-localization-massshell-boost).</small>

<a id="d-qiqth-fock-localization-massshell-boost"></a>
**Lemma 234** (`massShell_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L56)</small>

$$
\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,(\href{#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta) = \href{#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,(\theta + a)
$$

*Proof.* By [Lem 230](#d-qiqth-fock-localization-massshell-zero), [Lem 231](#d-qiqth-fock-localization-massshell-one), [Lem 232](#d-qiqth-fock-localization-lorentzboost-zero), [Lem 233](#d-qiqth-fock-localization-lorentzboost-one). $\square$

<small>Referenced in [Lem 247](#d-qiqth-fock-localization-krep-boost).</small>

<a id="d-qiqth-fock-localization-minkowskidot-boost"></a>
**Lemma 235** (`minkowskiDot_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L67)</small>

$$
\href{#d-qiqth-fock-localization-minkowskidot}{\eta}\,(\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,p)\,(\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,x) = \href{#d-qiqth-fock-localization-minkowskidot}{\eta}\,p\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost).</small>

<a id="d-qiqth-fock-localization-lorentzboostmat"></a>
**Definition 236** (`lorentzBoostMat`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L84)</small>

A definition — see source for the body.

<small>Referenced in [Def 237](#d-qiqth-fock-localization-lorentzboost), [Lem 238](#d-qiqth-fock-localization-lorentzboost-apply), [Lem 239](#d-qiqth-fock-localization-det-lorentzboost).</small>

<a id="d-qiqth-fock-localization-lorentzboost"></a>
**Definition 237** (`lorentzBoostₗ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L88)</small>

A definition — see source for the body.

<small>Referenced in [Lem 238](#d-qiqth-fock-localization-lorentzboost-apply), [Lem 239](#d-qiqth-fock-localization-det-lorentzboost), [Lem 240](#d-qiqth-fock-localization-measurepreserving-lorentzboost), [Def 241](#d-qiqth-fock-localization-lorentzboostle), [Lem 242](#d-qiqth-fock-localization-measurableembedding-lorentzboost).</small>

<a id="d-qiqth-fock-localization-lorentzboost-apply"></a>
**Lemma 238** (`lorentzBoostₗ_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L102)</small>

$$
(\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a)\,z = \href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,z
$$

*Proof.* By [Def 236](#d-qiqth-fock-localization-lorentzboostmat). $\square$

<small>Referenced in [Lem 240](#d-qiqth-fock-localization-measurepreserving-lorentzboost), [Lem 242](#d-qiqth-fock-localization-measurableembedding-lorentzboost).</small>

<a id="d-qiqth-fock-localization-det-lorentzboost"></a>
**Lemma 239** (`det_lorentzBoost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L108)</small>

$$
\mathrm{det}\,(\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a) = 1
$$

*Proof.* By [Def 236](#d-qiqth-fock-localization-lorentzboostmat). $\square$

<small>Referenced in [Lem 240](#d-qiqth-fock-localization-measurepreserving-lorentzboost).</small>

<a id="d-qiqth-fock-localization-measurepreserving-lorentzboost"></a>
**Lemma 240** (`measurePreserving_lorentzBoost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L114)</small>

$$
\mathrm{MeasurePreserving}\,(\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a)\,\mathrm{volume}\,\mathrm{volume}
$$

*Proof.* By [Def 237](#d-qiqth-fock-localization-lorentzboost), [Lem 238](#d-qiqth-fock-localization-lorentzboost-apply), [Lem 239](#d-qiqth-fock-localization-det-lorentzboost). $\square$

<small>Referenced in [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost).</small>

<a id="d-qiqth-fock-localization-lorentzboostle"></a>
**Definition 241** (`lorentzBoostLE`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L145)</small>

A definition — see source for the body.

<small>Referenced in [Lem 242](#d-qiqth-fock-localization-measurableembedding-lorentzboost).</small>

<a id="d-qiqth-fock-localization-measurableembedding-lorentzboost"></a>
**Lemma 242** (`measurableEmbedding_lorentzBoost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L153)</small>

$$
\mathrm{MeasurableEmbedding}\,(\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a)
$$

*Proof.* By [Def 237](#d-qiqth-fock-localization-lorentzboost), [Lem 238](#d-qiqth-fock-localization-lorentzboost-apply), [Def 241](#d-qiqth-fock-localization-lorentzboostle). $\square$

<small>Referenced in [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost).</small>

<a id="d-qiqth-fock-localization-minkowskifourier"></a>
**Definition 243** (`minkowskiFourier`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L165)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 135](#d-qiqth-fock-boostkms-minkowskifourier-smul), [Lem 136](#d-qiqth-fock-boostkms-krep-smul), [Lem 212](#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [Lem 213](#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost), [Def 246](#d-qiqth-fock-localization-krep), [Lem 247](#d-qiqth-fock-localization-krep-boost), [Lem 248](#d-qiqth-fock-localization-minkowskifourier-zero), [Lem 249](#d-qiqth-fock-localization-krep-zero), [Lem 252](#d-qiqth-fock-localization-minkowskifourier-continuous), [Lem 254](#d-qiqth-fock-localization-krep-continuous), [Lem 298](#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal).</small>

<a id="d-qiqth-fock-localization-boosttest"></a>
**Definition 244** (`boostTest`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L170)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 87](#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [Lem 89](#d-qiqth-fock-boostkms-symm-edge-eq-inner), [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [Lem 141](#d-qiqth-fock-boostkms-memlp-krep-boosttest), [Def 169](#d-qiqth-fock-boostkms-nicetest-boost), [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost), [Lem 247](#d-qiqth-fock-localization-krep-boost), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2).</small>

<a id="d-qiqth-fock-localization-minkowskifourier-boost"></a>
**Lemma 245** (`minkowskiFourier_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L173)</small>

$$
\href{#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,(\href{#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,a\,f)\,p = \href{#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f\,(\href{#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,p)
$$

*Proof.* By [Def 227](#d-qiqth-fock-localization-minkowskidot), [Lem 235](#d-qiqth-fock-localization-minkowskidot-boost), [Lem 240](#d-qiqth-fock-localization-measurepreserving-lorentzboost), [Lem 242](#d-qiqth-fock-localization-measurableembedding-lorentzboost). $\square$

<small>Referenced in [Lem 247](#d-qiqth-fock-localization-krep-boost).</small>

<a id="d-qiqth-fock-localization-krep"></a>
**Definition 246** (`Krep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L190)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 85](#d-qiqth-fock-boostkms-inner-krepl2), [Lem 86](#d-qiqth-fock-boostkms-inner-krepl2-general), [Lem 87](#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [Lem 88](#d-qiqth-fock-boostkms-symm-edge-eq-shifted), [Lem 89](#d-qiqth-fock-boostkms-symm-edge-eq-inner), [Lem 91](#d-qiqth-fock-boostkms-kmsfun-ofreal), [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [Lem 93](#d-qiqth-fock-boostkms-kmsfun-sub-i), [Lem 116](#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [Lem 117](#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [Lem 120](#d-qiqth-fock-boostkms-tail-term-le), [Lem 122](#d-qiqth-fock-boostkms-tail-integral-le), [Lem 123](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le), [Lem 124](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le), [Lem 125](#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le), [Lem 126](#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [Lem 127](#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed), [Lem 128](#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le), [Lem 130](#d-qiqth-fock-boostkms-kmsfun-add-left), [Lem 131](#d-qiqth-fock-boostkms-kmsfun-add-right), [Lem 132](#d-qiqth-fock-boostkms-kmsfun-sub-left), [Lem 133](#d-qiqth-fock-boostkms-kmsfun-sub-right), [Lem 134](#d-qiqth-fock-boostkms-norm-tolp-krep-eq-sqrt), [Lem 136](#d-qiqth-fock-boostkms-krep-smul), [Lem 137](#d-qiqth-fock-boostkms-krepl2-add), [Lem 138](#d-qiqth-fock-boostkms-krepl2-sub), [Lem 139](#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul), [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le), [Lem 141](#d-qiqth-fock-boostkms-memlp-krep-boosttest), [Def 142](#d-qiqth-fock-boostkms-kmsbcf), [Lem 143](#d-qiqth-fock-boostkms-kmsbcf-apply), [Lem 144](#d-qiqth-fock-boostkms-dist-kmsbcf-le), [Lem 145](#d-qiqth-fock-boostkms-kmsbcf-congr), [Lem 147](#d-qiqth-fock-boostkms-nicetest-mk), [Lem 155](#d-qiqth-fock-boostkms-nicetest-memlp), [Def 156](#d-qiqth-fock-boostkms-nicetest-vec), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 174](#d-qiqth-fock-boostkms-nicetest-zero-vec), [Lem 175](#d-qiqth-fock-boostkms-nicetest-vec-smul), [Lem 189](#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [Def 197](#d-qiqth-fock-boostkms-nicewedgecyclic), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero), [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [Lem 213](#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of), [Lem 247](#d-qiqth-fock-localization-krep-boost), [Lem 249](#d-qiqth-fock-localization-krep-zero), [Lem 254](#d-qiqth-fock-localization-krep-continuous), [Lem 255](#d-qiqth-fock-localization-krep-aestronglymeasurable), [Lem 259](#d-qiqth-fock-localization-krep-memlp-of-decay), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [Lem 355](#d-qiqth-fock-wedgeanalyticity-krep-add), [Lem 356](#d-qiqth-fock-wedgeanalyticity-krep-sub), [Lem 357](#d-qiqth-fock-wedgeanalyticity-memlp-krep-add), [Lem 358](#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub), [Lem 359](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed), [Lem 384](#d-qiqth-fock-wienerl2-integrable-krep), [Def 385](#d-qiqth-fock-wienerl2-ftkrep), [Def 386](#d-qiqth-fock-wienerl2-ftkrep), [Lem 388](#d-qiqth-fock-wienerl2-hasderivat-ftkrep), [Lem 390](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 391](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 392](#d-qiqth-fock-wienerl2-norm-krep-le-exp), [Lem 393](#d-qiqth-fock-wienerl2-continuous-ftkrep), [Lem 394](#d-qiqth-fock-wienerl2-continuous-ftkrep), [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep), [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf), [Lem 398](#d-qiqth-fock-wienerl2-ftkrepf-eq-fourier), [Lem 399](#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep), [Lem 403](#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-localization-krep-boost"></a>
**Lemma 247** (`Krep_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L197)</small>

$$
\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,a\,f)\,\theta = \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta + a)
$$

*Proof.* By [Def 228](#d-qiqth-fock-localization-massshell), [Def 229](#d-qiqth-fock-localization-lorentzboost), [Lem 234](#d-qiqth-fock-localization-massshell-boost), [Def 243](#d-qiqth-fock-localization-minkowskifourier), [Lem 245](#d-qiqth-fock-localization-minkowskifourier-boost). $\square$

<small>Referenced in [Lem 87](#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [Lem 141](#d-qiqth-fock-boostkms-memlp-krep-boosttest), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2).</small>

<a id="d-qiqth-fock-localization-minkowskifourier-zero"></a>
**Lemma 248** (`minkowskiFourier_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L306)</small>

$$
\href{#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,(\lambda x \mapsto 0)\,p = 0
$$

*Proof.* By [Def 227](#d-qiqth-fock-localization-minkowskidot). $\square$

<small>Referenced in [Lem 249](#d-qiqth-fock-localization-krep-zero).</small>

<a id="d-qiqth-fock-localization-krep-zero"></a>
**Lemma 249** (`Krep_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L310)</small>

$$
(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,\lambda x \mapsto 0) = 0
$$

*Proof.* By [Def 228](#d-qiqth-fock-localization-massshell), [Def 243](#d-qiqth-fock-localization-minkowskifourier), [Lem 248](#d-qiqth-fock-localization-minkowskifourier-zero). $\square$

<small>Referenced in [Lem 174](#d-qiqth-fock-boostkms-nicetest-zero-vec).</small>

<a id="d-qiqth-fock-localization-continuous-minkowskidot-fst"></a>
**Lemma 250** (`continuous_minkowskiDot_fst`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L341)</small>

$$
\mathrm{Continuous}\,\lambda p \mapsto \href{#d-qiqth-fock-localization-minkowskidot}{\eta}\,p\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 252](#d-qiqth-fock-localization-minkowskifourier-continuous).</small>

<a id="d-qiqth-fock-localization-continuous-minkowskidot-snd"></a>
**Lemma 251** (`continuous_minkowskiDot_snd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L345)</small>

$$
\mathrm{Continuous}\,\lambda x \mapsto \href{#d-qiqth-fock-localization-minkowskidot}{\eta}\,p\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 252](#d-qiqth-fock-localization-minkowskifourier-continuous).</small>

<a id="d-qiqth-fock-localization-minkowskifourier-continuous"></a>
**Lemma 252** (`minkowskiFourier_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L349)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{Continuous}\,(\href{#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f)
$$

*Proof.* By [Def 227](#d-qiqth-fock-localization-minkowskidot), [Lem 250](#d-qiqth-fock-localization-continuous-minkowskidot-fst), [Lem 251](#d-qiqth-fock-localization-continuous-minkowskidot-snd). $\square$

<small>Referenced in [Lem 254](#d-qiqth-fock-localization-krep-continuous).</small>

<a id="d-qiqth-fock-localization-continuous-massshell"></a>
**Lemma 253** (`continuous_massShell`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L368)</small>

$$
\mathrm{Continuous}\,(\href{#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 254](#d-qiqth-fock-localization-krep-continuous).</small>

<a id="d-qiqth-fock-localization-krep-continuous"></a>
**Lemma 254** (`Krep_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L374)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{Continuous}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)
$$

*Proof.* By [Def 228](#d-qiqth-fock-localization-massshell), [Def 243](#d-qiqth-fock-localization-minkowskifourier), [Lem 252](#d-qiqth-fock-localization-minkowskifourier-continuous), [Lem 253](#d-qiqth-fock-localization-continuous-massshell). $\square$

<small>Referenced in [Lem 214](#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of), [Lem 255](#d-qiqth-fock-localization-krep-aestronglymeasurable), [Lem 384](#d-qiqth-fock-wienerl2-integrable-krep), [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep), [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-localization-krep-aestronglymeasurable"></a>
**Lemma 255** (`Krep_aestronglyMeasurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L380)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{AEStronglyMeasurable}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{volume}
$$

*Proof.* By [Lem 254](#d-qiqth-fock-localization-krep-continuous). $\square$

<small>Referenced in [Lem 259](#d-qiqth-fock-localization-krep-memlp-of-decay).</small>

<a id="d-qiqth-fock-localization-one-add-sq-le-cosh-sq"></a>
**Lemma 256** (`one_add_sq_le_cosh_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L386)</small>

$$
1 + {\theta}^{2} \le {\cosh\,\theta}^{2}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 257](#d-qiqth-fock-localization-integrable-cosh-inv-sq).</small>

<a id="d-qiqth-fock-localization-integrable-cosh-inv-sq"></a>
**Lemma 257** (`integrable_cosh_inv_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L399)</small>

$$
\mathrm{Integrable}\,(\lambda \theta \mapsto {({\cosh\,\theta}^{2})}^{-1})\,\mathrm{volume}
$$

*Proof.* By [Lem 256](#d-qiqth-fock-localization-one-add-sq-le-cosh-sq). $\square$

<small>Referenced in [Lem 258](#d-qiqth-fock-localization-memlp-cosh-inv).</small>

<a id="d-qiqth-fock-localization-memlp-cosh-inv"></a>
**Lemma 258** (`memLp_cosh_inv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L410)</small>

$$
\mathrm{MemLp}\,(\lambda \theta \mapsto {(\cosh\,\theta)}^{-1})\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 257](#d-qiqth-fock-localization-integrable-cosh-inv-sq). $\square$

<small>Referenced in [Lem 259](#d-qiqth-fock-localization-krep-memlp-of-decay).</small>

<a id="d-qiqth-fock-localization-krep-memlp-of-decay"></a>
**Lemma 259** (`Krep_memLp_of_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/Localization.lean#L419)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \forall \{C : \mathbb{R}\}, (\forall (\theta : \mathbb{R}), \|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\| \le C \cdot {(\cosh\,\theta)}^{-1}) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 255](#d-qiqth-fock-localization-krep-aestronglymeasurable), [Lem 258](#d-qiqth-fock-localization-memlp-cosh-inv). $\square$

<small>Referenced in [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp).</small>

<a id="sec-qiqth-fock-oneparticle"></a>
## QIQTH.Fock.OneParticle

<a id="d-qiqth-fock-oneparticle-mpflow"></a>
**Lemma 260** (`MPFlow`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L48)</small>

$$
\{X : Type\mathrm{u\_2}\} \to [\mathrm{inst} : \mathrm{MeasurableSpace}\,X] \to \mathrm{Measure}\,X \to Type\mathrm{u\_2}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 261](#d-qiqth-fock-oneparticle-mpflow-mk), [Def 262](#d-qiqth-fock-oneparticle-mpflow-flow), [Lem 263](#d-qiqth-fock-oneparticle-mpflow-mp), [Lem 264](#d-qiqth-fock-oneparticle-mpflow-flow-zero), [Lem 265](#d-qiqth-fock-oneparticle-mpflow-flow-add), [Lem 266](#d-qiqth-fock-oneparticle-mpflow-comp-chain), [Def 267](#d-qiqth-fock-oneparticle-mpflow-unitary), [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [Lem 269](#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [Lem 270](#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [Def 271](#d-qiqth-fock-oneparticle-translationflow), [Def 272](#d-qiqth-fock-oneparticle-boostflow).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-mk"></a>
**Lemma 261** (`mk`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L51)</small>

$$
\{X : Type\mathrm{u\_2}\} \to [\mathrm{inst} : \mathrm{MeasurableSpace}\,X] \to \{\mu : \mathrm{Measure}\,X\} \to (\mathrm{flow} : \mathbb{R} \to X \to X) \to (\forall (t : \mathbb{R}), \mathrm{MeasurePreserving}\,(\mathrm{flow}\,t)\,\mu\,\mu) \to \mathrm{flow}\,0 = \mathrm{id} \to (\forall (s t : \mathbb{R}), \mathrm{flow}\,(s + t) = \mathrm{flow}\,s \circ \mathrm{flow}\,t) \to \href{#d-qiqth-fock-oneparticle-mpflow}{\mathrm{MPFlow}}\,\mu
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Def 271](#d-qiqth-fock-oneparticle-translationflow).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-flow"></a>
**Definition 262** (`flow`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L53)</small>

A definition, built from [Lem 260](#d-qiqth-fock-oneparticle-mpflow) — see source for the body.

<small>Referenced in [Lem 263](#d-qiqth-fock-oneparticle-mpflow-mp), [Lem 264](#d-qiqth-fock-oneparticle-mpflow-flow-zero), [Lem 265](#d-qiqth-fock-oneparticle-mpflow-flow-add), [Lem 266](#d-qiqth-fock-oneparticle-mpflow-comp-chain), [Def 267](#d-qiqth-fock-oneparticle-mpflow-unitary), [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [Lem 269](#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [Lem 270](#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [Lem 277](#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [Lem 278](#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-mp"></a>
**Lemma 263** (`mp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L55)</small>

$$
\mathrm{MeasurePreserving}\,(\mathrm{self}.\mathrm{flow}\,t)\,\mu\,\mu
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 266](#d-qiqth-fock-oneparticle-mpflow-comp-chain), [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [Lem 269](#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [Lem 270](#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [Lem 277](#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [Lem 278](#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-flow-zero"></a>
**Lemma 264** (`flow_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L57)</small>

$$
\mathrm{self}.\mathrm{flow}\,0 = \mathrm{id}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 270](#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-flow-add"></a>
**Lemma 265** (`flow_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L59)</small>

$$
\mathrm{self}.\mathrm{flow}\,(s + t) = \mathrm{self}.\mathrm{flow}\,s \circ \mathrm{self}.\mathrm{flow}\,t
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 266](#d-qiqth-fock-oneparticle-mpflow-comp-chain).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-comp-chain"></a>
**Lemma 266** (`comp_chain`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L63)</small>

$$
(\mathrm{cmp}\,(\Phi.\mathrm{flow}\,a)\,\cdots )\,((\mathrm{cmp}\,(\Phi.\mathrm{flow}\,b)\,\cdots )\,g) = (\mathrm{cmp}\,(\Phi.\mathrm{flow}\,(b + a))\,\cdots )\,g
$$

*Proof.* By [Lem 265](#d-qiqth-fock-oneparticle-mpflow-flow-add). $\square$

<small>Referenced in [Lem 269](#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-unitary"></a>
**Definition 267** (`unitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L73)</small>

A definition, built from [Lem 260](#d-qiqth-fock-oneparticle-mpflow) — see source for the body.

<small>Referenced in [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [Lem 269](#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [Lem 270](#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [Def 273](#d-qiqth-fock-oneparticle-boostunitary).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-unitary-apply"></a>
**Lemma 268** (`unitary_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L85)</small>

$$
(\Phi.\mathrm{U}\,t)\,g = (\mathrm{cmp}\,(\Phi.\mathrm{flow}\,(-t))\,\cdots )\,g
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 269](#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [Lem 270](#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [Lem 277](#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [Lem 278](#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-unitary-add-apply"></a>
**Lemma 269** (`unitary_add_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L92)</small>

$$
(\Phi.\mathrm{U}\,(s + t))\,g = (\Phi.\mathrm{U}\,s)\,((\Phi.\mathrm{U}\,t)\,g)
$$

*Proof.* By [Def 262](#d-qiqth-fock-oneparticle-mpflow-flow), [Lem 263](#d-qiqth-fock-oneparticle-mpflow-mp), [Lem 266](#d-qiqth-fock-oneparticle-mpflow-comp-chain), [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply). $\square$

<small>Referenced in [Lem 274](#d-qiqth-fock-oneparticle-boostunitary-add-apply).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply"></a>
**Lemma 270** (`unitary_zero_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L98)</small>

$$
(\Phi.\mathrm{U}\,0)\,g = g
$$

*Proof.* By [Def 262](#d-qiqth-fock-oneparticle-mpflow-flow), [Lem 263](#d-qiqth-fock-oneparticle-mpflow-mp), [Lem 264](#d-qiqth-fock-oneparticle-mpflow-flow-zero), [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply). $\square$

<small>Referenced in [Lem 275](#d-qiqth-fock-oneparticle-boostunitary-zero-apply).</small>

<a id="d-qiqth-fock-oneparticle-translationflow"></a>
**Definition 271** (`translationFlow`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L106)</small>

A definition, built from [Lem 260](#d-qiqth-fock-oneparticle-mpflow) — see source for the body.

<small>Referenced in [Def 272](#d-qiqth-fock-oneparticle-boostflow).</small>

<a id="d-qiqth-fock-oneparticle-boostflow"></a>
**Definition 272** (`boostFlow`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L114)</small>

A definition, built from [Lem 260](#d-qiqth-fock-oneparticle-mpflow) — see source for the body.

<small>Referenced in [Def 273](#d-qiqth-fock-oneparticle-boostunitary), [Lem 274](#d-qiqth-fock-oneparticle-boostunitary-add-apply), [Lem 275](#d-qiqth-fock-oneparticle-boostunitary-zero-apply), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [Lem 277](#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [Lem 278](#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd).</small>

<a id="d-qiqth-fock-oneparticle-boostunitary"></a>
**Definition 273** (`boostUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L120)</small>

A definition — see source for the body.

<small>Referenced in [Lem 87](#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [Lem 89](#d-qiqth-fock-boostkms-symm-edge-eq-inner), [Lem 92](#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [Lem 164](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [Lem 165](#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost), [Lem 171](#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [Lem 192](#d-qiqth-fock-boostkms-stripkmsrvd-closure), [Lem 193](#d-qiqth-fock-boostkms-stripkmsrvd-boostunitary), [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 195](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero), [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [Lem 220](#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass), [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [Lem 223](#d-qiqth-fock-hasderivat-inner-boostunitary-imaginary-pos), [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux), [Lem 274](#d-qiqth-fock-oneparticle-boostunitary-add-apply), [Lem 275](#d-qiqth-fock-oneparticle-boostunitary-zero-apply), [Lem 276](#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [Lem 277](#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [Lem 278](#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd), [Lem 279](#d-qiqth-fock-oneparticlebw-continuous-boostunitary-apply), [Lem 280](#d-qiqth-fock-oneparticlebw-inner-boostunitary-tolp), [Lem 281](#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-wedge), [Lem 282](#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary), [Lem 362](#d-qiqth-fock-wienerl2-boostunitary-tolp), [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary), [Lem 376](#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral), [Lem 377](#d-qiqth-fock-wienerl2-fourier-correlation-eq), [Lem 379](#d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-oneparticle-boostunitary-add-apply"></a>
**Lemma 274** (`boostUnitary_add_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L127)</small>

$$
(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(s + t))\,g = (\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,s)\,((\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,t)\,g)
$$

*Proof.* By [Lem 269](#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [Def 272](#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge).</small>

<a id="d-qiqth-fock-oneparticle-boostunitary-zero-apply"></a>
**Lemma 275** (`boostUnitary_zero_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L132)</small>

$$
(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,0)\,g = g
$$

*Proof.* By [Lem 270](#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [Def 272](#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 220](#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass), [Lem 282](#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary).</small>

<a id="sec-qiqth-fock-oneparticlebw"></a>
## QIQTH.Fock.OneParticleBW

<a id="d-qiqth-fock-oneparticlebw-boostunitary-krepl2"></a>
**Lemma 276** (`boostUnitary_KrepL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L66)</small>

$$
(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,(\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,h) = \mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-a)\,f))\,h^{\prime}
$$

*Proof.* By [Lem 247](#d-qiqth-fock-localization-krep-boost), [Def 262](#d-qiqth-fock-oneparticle-mpflow-flow), [Lem 263](#d-qiqth-fock-oneparticle-mpflow-mp), [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [Def 272](#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Referenced in [Lem 87](#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [Lem 170](#d-qiqth-fock-boostkms-nicetest-vec-boost).</small>

<a id="d-qiqth-fock-oneparticlebw-coefn-boostunitary"></a>
**Lemma 277** (`coeFn_boostUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L96)</small>

$$
((\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,\xi) =[\mathrm{volume}] \lambda \theta \mapsto \xi\,(\theta - a)
$$

*Proof.* By [Def 262](#d-qiqth-fock-oneparticle-mpflow-flow), [Lem 263](#d-qiqth-fock-oneparticle-mpflow-mp), [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [Def 272](#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Referenced in [Lem 280](#d-qiqth-fock-oneparticlebw-inner-boostunitary-tolp), [Lem 362](#d-qiqth-fock-wienerl2-boostunitary-tolp).</small>

<a id="d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd"></a>
**Lemma 278** (`boostUnitary_eq_vadd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L110)</small>

$$
(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,t)\,\xi = \mathrm{mk}\,(-t) +_{v} \xi
$$

*Proof.* By [Def 262](#d-qiqth-fock-oneparticle-mpflow-flow), [Lem 263](#d-qiqth-fock-oneparticle-mpflow-mp), [Lem 268](#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [Def 272](#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Referenced in [Lem 279](#d-qiqth-fock-oneparticlebw-continuous-boostunitary-apply).</small>

<a id="d-qiqth-fock-oneparticlebw-continuous-boostunitary-apply"></a>
**Lemma 279** (`continuous_boostUnitary_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L131)</small>

$$
\mathrm{Continuous}\,\lambda t \mapsto (\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,t)\,\xi
$$

*Proof.* By [Lem 278](#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd). $\square$

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge).</small>

<a id="d-qiqth-fock-oneparticlebw-inner-boostunitary-tolp"></a>
**Lemma 280** (`inner_boostUnitary_toLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L172)</small>

$$
\langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,s)\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f\,(\theta - s)
$$

*Proof.* By [Lem 277](#d-qiqth-fock-oneparticlebw-coefn-boostunitary). $\square$

<small>Referenced in [Lem 281](#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-wedge).</small>

<a id="d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-wedge"></a>
**Lemma 281** (`hasDerivAt_inner_boostUnitary_wedge`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L193)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f\,\theta)\,\mathrm{volume} \to \mathrm{AEStronglyMeasurable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta}
$$

*Proof.* By [Lem 280](#d-qiqth-fock-oneparticlebw-inner-boostunitary-tolp). $\square$

<small>Referenced in [Lem 282](#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary).</small>

<a id="d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary"></a>
**Lemma 282** (`hasDerivAt_inner_boostUnitary_imaginary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L259)</small>

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f\,\theta)\,\mathrm{volume} \to \mathrm{AEStronglyMeasurable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot (2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta).\mathrm{im}}
$$

*Proof.* By [Lem 275](#d-qiqth-fock-oneparticle-boostunitary-zero-apply), [Lem 281](#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-wedge). $\square$

<small>Referenced in [Lem 223](#d-qiqth-fock-hasderivat-inner-boostunitary-imaginary-pos).</small>

<a id="d-qiqth-fock-oneparticlebw-stripkmsrvd"></a>
**Definition 283** (`StripKMSrvd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L480)</small>

A definition — see source for the body.

<small>Referenced in [Lem 193](#d-qiqth-fock-boostkms-stripkmsrvd-boostunitary), [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 284](#d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline), [Lem 286](#d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal), [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [Lem 295](#d-qiqth-fock-oneparticlebw-oneparticlebw-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline"></a>
**Lemma 284** (`stripKMSrvd_real_midline`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L510)</small>

$$
\href{#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,K \to \forall \{\xi \eta : H\}, \xi \in K \to \eta \in K \to \exists f, \mathrm{DiffContOnCl}\,\mathbb{C}\,f\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \wedge (\forall (t : \mathbb{R}), f\,t = \langle {\eta},{(V\,t)\,\xi}\rangle) \wedge \forall (t : \mathbb{R}), (f\,(t - i / 2)).\mathrm{im} = 0
$$

*Proof.* By [Def 895](#d-qiqth-stripuniqueness-negstrip), [Lem 899](#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip). $\square$

<small>Referenced in [Lem 286](#d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal).</small>

<a id="d-qiqth-fock-oneparticlebw-halfstripreal"></a>
**Definition 285** (`HalfStripReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L580)</small>

A definition — see source for the body.

<small>Referenced in [Lem 286](#d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal), [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal"></a>
**Lemma 286** (`stripKMSrvd_halfStripReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L589)</small>

$$
\href{#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,K \to \href{#d-qiqth-fock-oneparticlebw-halfstripreal}{\mathrm{HalfStripReal}}\,V\,K
$$

*Proof.* By [Lem 284](#d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline). $\square$

<small>Referenced in [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison).</small>

<a id="d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd"></a>
**Lemma 287** (`h1_of_stripKMSrvd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L595)</small>

$$
0 < n \to \forall \{\eta : H\}, (\mathrm{Continuous}\,\lambda s \mapsto (V\,s)\,\eta) \to (\forall (s : \mathbb{R}), \|(V\,s)\,\eta\| \le \|\eta\|) \to (\forall (s u : \mathbb{R}), (V\,s)\,((V\,u)\,\eta) = (V\,(s + u))\,\eta) \to (\forall (s : \mathbb{R}), (V\,s)\,\eta \in S.\mathrm{cl}) \to \forall \{\zeta : H\}, (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \href{#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,(t - i / 2))).\mathrm{im} = 0
$$

*Proof.* By [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 745](#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [Lem 845](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [Def 848](#d-qiqth-standardsubspacemodular-gausssmear), [Lem 850](#d-qiqth-standardsubspacemodular-gausssmear-mem-k), [Def 892](#d-qiqth-stripuniqueness-kmshalfstrip), [Def 893](#d-qiqth-stripuniqueness-kmshalfstripopen), [Def 895](#d-qiqth-stripuniqueness-negstrip), [Lem 899](#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip). $\square$

<small>Referenced in [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density).</small>

<a id="d-qiqth-fock-oneparticlebw-comparisondatum"></a>
**Definition 288** (`ComparisonDatum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L641)</small>

A definition — see source for the body.

<small>Referenced in [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison"></a>
**Lemma 289** (`oneParticleBW_of_comparison`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L651)</small>

$$
(\href{#d-qiqth-fock-oneparticlebw-halfstripreal}{\mathrm{HalfStripReal}}\,V\,S.\mathrm{cl} \to \href{#d-qiqth-fock-oneparticlebw-comparisondatum}{\mathrm{ComparisonDatum}}\,S\,V) \to (\forall (t : \mathbb{R}), \mathrm{MapsTo}\,(V\,t)\,S.\mathrm{cl}\,S.\mathrm{cl}) \to \href{#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [Lem 286](#d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal), [Lem 420](#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 845](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k). $\square$

<small>Referenced in [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-gconstancy"></a>
**Definition 290** (`GConstancy`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L677)</small>

A definition — see source for the body.

<small>Referenced in [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy"></a>
**Lemma 291** (`comparisonDatum_of_gConstancy`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L685)</small>

$$
\href{#d-qiqth-fock-oneparticlebw-gconstancy}{\mathrm{GConstancy}}\,S\,V \to \href{#d-qiqth-fock-oneparticlebw-comparisondatum}{\mathrm{ComparisonDatum}}\,S\,V
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 745](#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [Def 766](#d-qiqth-standardsubspacemodular-modconj), [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 793](#d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik), [Lem 845](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary). $\square$

<small>Referenced in [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-gconstancy-of-inputs"></a>
**Lemma 292** (`gConstancy_of_inputs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L711)</small>

$$
(\forall \eta\in S.\mathrm{cl}, \mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (\eta : H) (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (\eta : H) (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (\eta : H), (V\,0)\,\eta = \eta) \to (\forall \eta\in S.\mathrm{cl}, \forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall \eta\in S.\mathrm{cl}, \forall (\zeta : H), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (n : \mathbb{R}), 0 < n \to \forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to (\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)) \to \href{#d-qiqth-fock-oneparticlebw-gconstancy}{\mathrm{GConstancy}}\,S\,V
$$

*Proof.* By [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 419](#d-qiqth-standardsubspacemodular-gconstancy-xi-of-density). $\square$

<small>Referenced in [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs"></a>
**Lemma 293** (`oneParticleBW_of_inputs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L738)</small>

$$
(\forall \eta\in S.\mathrm{cl}, \mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (\eta : H) (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (\eta : H) (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (\eta : H), (V\,0)\,\eta = \eta) \to (\forall \eta\in S.\mathrm{cl}, \forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall \eta\in S.\mathrm{cl}, \forall (\zeta : H), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (n : \mathbb{R}), 0 < n \to \forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to (\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)) \to (\forall (t : \mathbb{R}), \mathrm{MapsTo}\,(V\,t)\,S.\mathrm{cl}\,S.\mathrm{cl}) \to \href{#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [Def 285](#d-qiqth-fock-oneparticlebw-halfstripreal), [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs). $\square$

<small>Referenced in [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density"></a>
**Lemma 294** (`oneParticleBW_of_stripKMSrvd_density`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L768)</small>

$$
(\forall \eta\in S.\mathrm{cl}, \mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (\eta : H) (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (\eta : H) (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (\eta : H), (V\,0)\,\eta = \eta) \to (\forall \eta\in S.\mathrm{cl}, \forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)) \to (\forall (t : \mathbb{R}), \mathrm{MapsTo}\,(V\,t)\,S.\mathrm{cl}\,S.\mathrm{cl}) \to \href{#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Def 437](#d-qiqth-devicevecf), [Def 776](#d-qiqth-standardsubspacemodular-modconjbilin), [Def 859](#d-qiqth-standardsubspacemodular-gausssmearc). $\square$

<small>Referenced in [Lem 295](#d-qiqth-fock-oneparticlebw-oneparticlebw-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-complete"></a>
**Lemma 295** (`oneParticleBW_complete`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L798)</small>

$$
(\forall \eta\in S.\mathrm{cl}, \mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (\eta : H) (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (\eta : H) (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (\eta : H), (V\,0)\,\eta = \eta) \to (\forall \eta\in S.\mathrm{cl}, \forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall (t : \mathbb{R}), \mathrm{MapsTo}\,(V\,t)\,S.\mathrm{cl}\,S.\mathrm{cl}) \to \href{#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density). $\square$

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge).</small>

<a id="sec-qiqth-fock-schwartzdecay"></a>
## QIQTH.Fock.SchwartzDecay

<a id="d-qiqth-fock-localization-minkbilin"></a>
**Definition 296** (`minkBilin`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L35)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 297](#d-qiqth-fock-localization-minkbilin-apply), [Lem 298](#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq).</small>

<a id="d-qiqth-fock-localization-minkbilin-apply"></a>
**Lemma 297** (`minkBilin_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L43)</small>

$$
(\href{#d-qiqth-fock-localization-minkbilin}{\eta}\,v)\,w = (v\,0 \cdot w\,0 - v\,1 \cdot w\,1) / (2 \cdot \pi)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 298](#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq).</small>

<a id="d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral"></a>
**Lemma 298** (`minkowskiFourier_eq_fourierIntegral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L49)</small>

$$
\href{#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f\,p = \mathcal{F}\,\mathrm{e}\,\mathrm{volume}\,\href{#d-qiqth-fock-localization-minkbilin}{\eta}.\mathrm{toLinearMap}_{12}\,f\,p
$$

*Proof.* By [Def 227](#d-qiqth-fock-localization-minkowskidot), [Lem 297](#d-qiqth-fock-localization-minkbilin-apply). $\square$

<small>Referenced in [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq).</small>

<a id="d-qiqth-fock-localization-abs-sinh-le-cosh"></a>
**Lemma 299** (`abs_sinh_le_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L67)</small>

$$
|\sinh\,\theta| \le \cosh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 300](#d-qiqth-fock-localization-schwartz-krep-memlp), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq).</small>

<a id="d-qiqth-fock-localization-schwartz-krep-memlp"></a>
**Lemma 300** (`schwartz_Krep_memLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L74)</small>

$$
m \ne 0 \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume}
$$

*Proof.* By [Def 228](#d-qiqth-fock-localization-massshell), [Def 243](#d-qiqth-fock-localization-minkowskifourier), [Lem 259](#d-qiqth-fock-localization-krep-memlp-of-decay), [Def 296](#d-qiqth-fock-localization-minkbilin), [Lem 297](#d-qiqth-fock-localization-minkbilin-apply), [Lem 298](#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [Lem 299](#d-qiqth-fock-localization-abs-sinh-le-cosh). $\square$

<small>Referenced in [Lem 403](#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-localization-schwartz-krep-decay-sq"></a>
**Lemma 301** (`schwartz_Krep_decay_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/SchwartzDecay.lean#L165)</small>

$$
m \ne 0 \to \forall (\theta : \mathbb{R}), \|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f)\,\theta\| \le 16 \cdot {\pi}^{2} \cdot (((\int (v : \href{#d-qiqth-fock-localization-v}{V}), \|f\,v\|) + \int (v : \href{#d-qiqth-fock-localization-v}{V}), \|\mathrm{D}\,\mathbb{R}\,1\,(f)\,v\|) + \int (v : \href{#d-qiqth-fock-localization-v}{V}), \|\mathrm{D}\,\mathbb{R}\,2\,(f)\,v\|) / (\sqrt 2 \cdot {m}^{2}) \cdot {({\cosh\,\theta}^{2})}^{-1}
$$

*Proof.* By [Def 228](#d-qiqth-fock-localization-massshell), [Def 243](#d-qiqth-fock-localization-minkowskifourier), [Def 296](#d-qiqth-fock-localization-minkbilin), [Lem 297](#d-qiqth-fock-localization-minkbilin-apply), [Lem 298](#d-qiqth-fock-localization-minkowskifourier-eq-fourierintegral), [Lem 299](#d-qiqth-fock-localization-abs-sinh-le-cosh). $\square$

<small>Referenced in [Lem 384](#d-qiqth-fock-wienerl2-integrable-krep), [Lem 392](#d-qiqth-fock-wienerl2-norm-krep-le-exp).</small>

<a id="sec-qiqth-fock-wedgeanalyticity"></a>
## QIQTH.Fock.WedgeAnalyticity

<a id="d-qiqth-fock-wedgeanalyticity-minkowskidot"></a>
**Definition 302** (`minkowskiDotℂ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L24)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 307](#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 312](#d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell), [Lem 313](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel), [Lem 316](#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x), [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [Lem 344](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq), [Lem 349](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-massshell"></a>
**Definition 303** (`massShellℂ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L27)</small>

A definition — see source for the body.

<small>Referenced in [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 305](#d-qiqth-fock-wedgeanalyticity-massshell-ofreal), [Lem 306](#d-qiqth-fock-wedgeanalyticity-massshell-add-pi-i), [Lem 307](#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 312](#d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell), [Lem 313](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel), [Lem 316](#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x), [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [Lem 344](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq), [Lem 349](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krepcont"></a>
**Definition 304** (`KrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L31)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Def 90](#d-qiqth-fock-boostkms-kmsfun), [Lem 91](#d-qiqth-fock-boostkms-kmsfun-ofreal), [Lem 93](#d-qiqth-fock-boostkms-kmsfun-sub-i), [Lem 94](#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [Lem 95](#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [Lem 96](#d-qiqth-fock-boostkms-deriv-reflkrepcont-eq), [Lem 97](#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le), [Lem 98](#d-qiqth-fock-boostkms-differentiable-kmsintegrand), [Lem 99](#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [Lem 101](#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [Lem 102](#d-qiqth-fock-boostkms-continuous-deriv-reflkrepcont), [Lem 103](#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta), [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 106](#d-qiqth-fock-boostkms-norm-term1-le), [Lem 107](#d-qiqth-fock-boostkms-norm-term2-le), [Lem 108](#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound), [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Def 111](#d-qiqth-fock-boostkms-kmsfuncut), [Lem 112](#d-qiqth-fock-boostkms-norm-kmsfuncut-le), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat), [Lem 115](#d-qiqth-fock-boostkms-kmsfuncut-continuouson), [Lem 116](#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [Lem 117](#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [Lem 126](#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [Lem 127](#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed), [Lem 129](#d-qiqth-fock-boostkms-kmsfuncut-zero), [Lem 130](#d-qiqth-fock-boostkms-kmsfun-add-left), [Lem 131](#d-qiqth-fock-boostkms-kmsfun-add-right), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont), [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [Lem 329](#d-qiqth-fock-wedgeanalyticity-continuous-deriv-krepcont), [Lem 330](#d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [Lem 349](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay), [Lem 350](#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay), [Lem 351](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen), [Lem 352](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const), [Lem 353](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add), [Lem 355](#d-qiqth-fock-wedgeanalyticity-krep-add), [Lem 359](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed).</small>

<a id="d-qiqth-fock-wedgeanalyticity-massshell-ofreal"></a>
**Lemma 305** (`massShellℂ_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L39)</small>

$$
\href{#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,(\theta)\,i = (\href{#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta\,i)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 307](#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal).</small>

<a id="d-qiqth-fock-wedgeanalyticity-massshell-add-pi-i"></a>
**Lemma 306** (`massShellℂ_add_pi_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L45)</small>

$$
\href{#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,(\zeta + \pi \cdot i) = -\href{#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,\zeta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i).</small>

<a id="d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal"></a>
**Lemma 307** (`minkowskiDotℂ_massShellℂ_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L53)</small>

$$
\href{#d-qiqth-fock-wedgeanalyticity-minkowskidot}{\eta}\,(\href{#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,\theta)\,x = (\href{#d-qiqth-fock-localization-minkowskidot}{\eta}\,(\href{#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta)\,x)
$$

*Proof.* By [Lem 305](#d-qiqth-fock-wedgeanalyticity-massshell-ofreal). $\square$

<small>Referenced in [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krepcont-ofreal"></a>
**Lemma 308** (`KrepCont_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L58)</small>

$$
\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,\theta = \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta
$$

*Proof.* By [Def 227](#d-qiqth-fock-localization-minkowskidot), [Def 228](#d-qiqth-fock-localization-massshell), [Def 243](#d-qiqth-fock-localization-minkowskifourier), [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell), [Lem 307](#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal). $\square$

<small>Referenced in [Lem 91](#d-qiqth-fock-boostkms-kmsfun-ofreal), [Lem 116](#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [Lem 355](#d-qiqth-fock-wedgeanalyticity-krep-add), [Lem 359](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-ofreal-add-ofreal-mul-i"></a>
**Lemma 309** (`cosh_ofReal_add_ofReal_mul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L69)</small>

$$
\mathrm{cosh}\,(\theta + \mathrm{lam} \cdot i) = (\cosh\,\theta \cdot \cos\,\mathrm{lam}) + (\sinh\,\theta \cdot \sin\,\mathrm{lam}) \cdot i
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 344](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq).</small>

<a id="d-qiqth-fock-wedgeanalyticity-sinh-ofreal-add-ofreal-mul-i"></a>
**Lemma 310** (`sinh_ofReal_add_ofReal_mul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L77)</small>

$$
\mathrm{sinh}\,(\theta + \mathrm{lam} \cdot i) = (\sinh\,\theta \cdot \cos\,\mathrm{lam}) + (\cosh\,\theta \cdot \sin\,\mathrm{lam}) \cdot i
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 344](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq).</small>

<a id="d-qiqth-fock-wedgeanalyticity-kernel"></a>
**Definition 311** (`kernel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L111)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 313](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel), [Def 314](#d-qiqth-fock-wedgeanalyticity-kernelderiv), [Lem 315](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul), [Lem 316](#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x), [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [Lem 325](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le), [Lem 326](#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x), [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont), [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i), [Lem 344](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq), [Lem 345](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq), [Lem 346](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay), [Lem 347](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay), [Lem 348](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay), [Lem 349](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell"></a>
**Lemma 312** (`hasDerivAt_minkowskiDotℂ_massShellℂ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L115)</small>

$$
({\lambda \zeta \mapsto \href{#d-qiqth-fock-wedgeanalyticity-minkowskidot}{\eta}\,(\href{#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,\zeta)\,x})'({\zeta})={m \cdot \mathrm{sinh}\,\zeta \cdot (x\,0) - m \cdot \mathrm{cosh}\,\zeta \cdot (x\,1)}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 313](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel).</small>

<a id="d-qiqth-fock-wedgeanalyticity-hasderivat-kernel"></a>
**Lemma 313** (`hasDerivAt_kernel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L128)</small>

$$
({\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x})'({\zeta})={\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta \cdot (-i \cdot (m \cdot \mathrm{sinh}\,\zeta \cdot (x\,0) - m \cdot \mathrm{cosh}\,\zeta \cdot (x\,1)))}
$$

*Proof.* By [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell), [Lem 312](#d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell). $\square$

<small>Referenced in [Lem 315](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul).</small>

<a id="d-qiqth-fock-wedgeanalyticity-kernelderiv"></a>
**Definition 314** (`kernelDeriv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L142)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 315](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul), [Lem 325](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le), [Lem 326](#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x), [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont), [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [Lem 330](#d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq), [Lem 348](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay), [Lem 350](#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul"></a>
**Lemma 315** (`hasDerivAt_kernel_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L147)</small>

$$
({\lambda \zeta \mapsto \href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta \cdot f\,x})'({\zeta})={\href{#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta \cdot f\,x}
$$

*Proof.* By [Lem 313](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel). $\square$

<small>Referenced in [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont).</small>

<a id="d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x"></a>
**Lemma 316** (`continuous_kernel_in_x`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L153)</small>

$$
\mathrm{Continuous}\,\lambda x \mapsto \href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta
$$

*Proof.* By [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell). $\square$

<small>Referenced in [Lem 326](#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x), [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm"></a>
**Lemma 317** (`norm_exp_le_exp_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L159)</small>

$$
\|\exp\,z\| \le \exp\,\|z\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 318](#d-qiqth-fock-wedgeanalyticity-norm-exp-neg-le-exp-norm), [Lem 319](#d-qiqth-fock-wedgeanalyticity-norm-cosh-le), [Lem 322](#d-qiqth-fock-wedgeanalyticity-norm-sinh-le), [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-exp-neg-le-exp-norm"></a>
**Lemma 318** (`norm_exp_neg_le_exp_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L163)</small>

$$
\|\exp\,(-z)\| \le \exp\,\|z\|
$$

*Proof.* By [Lem 317](#d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm). $\square$

<small>Referenced in [Lem 319](#d-qiqth-fock-wedgeanalyticity-norm-cosh-le), [Lem 322](#d-qiqth-fock-wedgeanalyticity-norm-sinh-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-cosh-le"></a>
**Lemma 319** (`norm_cosh_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L167)</small>

$$
\|\mathrm{cosh}\,\zeta\| \le \exp\,\|\zeta\|
$$

*Proof.* By [Lem 317](#d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm), [Lem 318](#d-qiqth-fock-wedgeanalyticity-norm-exp-neg-le-exp-norm). $\square$

<small>Referenced in [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [Lem 325](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-cosh-le-cosh-re"></a>
**Lemma 320** (`norm_cosh_le_cosh_re`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L178)</small>

$$
\|\mathrm{cosh}\,\zeta\| \le \cosh\,\zeta.\mathrm{re}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 348](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-sinh-le-cosh-re"></a>
**Lemma 321** (`norm_sinh_le_cosh_re`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L187)</small>

$$
\|\mathrm{sinh}\,\zeta\| \le \cosh\,\zeta.\mathrm{re}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 348](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-sinh-le"></a>
**Lemma 322** (`norm_sinh_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L196)</small>

$$
\|\mathrm{sinh}\,\zeta\| \le \exp\,\|\zeta\|
$$

*Proof.* By [Lem 317](#d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm), [Lem 318](#d-qiqth-fock-wedgeanalyticity-norm-exp-neg-le-exp-norm). $\square$

<small>Referenced in [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [Lem 325](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-term-le"></a>
**Lemma 323** (`norm_term_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L207)</small>

$$
\|c\| \le \exp\,r \to \|s\| \le \exp\,r \to \forall (a b : \mathbb{R}), \|m \cdot c \cdot a - m \cdot s \cdot b\| \le |m| \cdot \exp\,r \cdot (|a| + |b|)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [Lem 325](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-le"></a>
**Lemma 324** (`norm_kernel_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L220)</small>

$$
\|\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta\| \le \exp\,(|m| \cdot \exp\,\|\zeta\| \cdot (|x\,0| + |x\,1|))
$$

*Proof.* By [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell), [Lem 317](#d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm), [Lem 319](#d-qiqth-fock-wedgeanalyticity-norm-cosh-le), [Lem 322](#d-qiqth-fock-wedgeanalyticity-norm-sinh-le), [Lem 323](#d-qiqth-fock-wedgeanalyticity-norm-term-le). $\square$

<small>Referenced in [Lem 325](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le"></a>
**Lemma 325** (`norm_kernelDeriv_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L228)</small>

$$
\|\href{#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta\| \le \exp\,(|m| \cdot \exp\,\|\zeta\| \cdot (|x\,0| + |x\,1|)) \cdot (|m| \cdot \exp\,\|\zeta\| \cdot (|x\,0| + |x\,1|))
$$

*Proof.* By [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 319](#d-qiqth-fock-wedgeanalyticity-norm-cosh-le), [Lem 322](#d-qiqth-fock-wedgeanalyticity-norm-sinh-le), [Lem 323](#d-qiqth-fock-wedgeanalyticity-norm-term-le), [Lem 324](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le). $\square$

<small>Referenced in [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont).</small>

<a id="d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x"></a>
**Lemma 326** (`continuous_kernelDeriv_in_x`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L239)</small>

$$
\mathrm{Continuous}\,\lambda x \mapsto \href{#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta
$$

*Proof.* By [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 316](#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x). $\square$

<small>Referenced in [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont).</small>

<a id="d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont"></a>
**Lemma 327** (`hasDerivAt_KrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L246)</small>

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall (\zeta_{0} : \mathbb{C}), ({\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f})'({\zeta_{0}})={1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \href{#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta_{0} \cdot f\,x}
$$

*Proof.* By [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 315](#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul), [Lem 316](#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x), [Lem 325](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le), [Lem 326](#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x). $\square$

<small>Referenced in [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [Lem 330](#d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq).</small>

<a id="d-qiqth-fock-wedgeanalyticity-differentiable-krepcont"></a>
**Lemma 328** (`differentiable_KrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L289)</small>

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Differentiable}\,\mathbb{C}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)
$$

*Proof.* By [Def 314](#d-qiqth-fock-wedgeanalyticity-kernelderiv), [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont). $\square$

<small>Referenced in [Lem 94](#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [Lem 96](#d-qiqth-fock-boostkms-deriv-reflkrepcont-eq), [Lem 98](#d-qiqth-fock-boostkms-differentiable-kmsintegrand), [Lem 99](#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [Lem 101](#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [Lem 103](#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta), [Lem 329](#d-qiqth-fock-wedgeanalyticity-continuous-deriv-krepcont), [Lem 353](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine).</small>

<a id="d-qiqth-fock-wedgeanalyticity-continuous-deriv-krepcont"></a>
**Lemma 329** (`continuous_deriv_KrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L294)</small>

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,(\mathrm{deriv}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f))
$$

*Proof.* By [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Referenced in [Lem 103](#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta).</small>

<a id="d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq"></a>
**Lemma 330** (`deriv_KrepCont_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L300)</small>

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall (\zeta : \mathbb{C}), \mathrm{deriv}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,\zeta = 1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \href{#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta \cdot f\,x
$$

*Proof.* By [Lem 327](#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont). $\square$

<small>Referenced in [Lem 350](#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i"></a>
**Lemma 331** (`kernel_add_pi_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L307)</small>

$$
\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,(\theta + \pi \cdot i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\theta)
$$

*Proof.* By [Def 227](#d-qiqth-fock-localization-minkowskidot), [Def 228](#d-qiqth-fock-localization-massshell), [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell), [Lem 306](#d-qiqth-fock-wedgeanalyticity-massshell-add-pi-i), [Lem 307](#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal). $\square$

<small>Referenced in [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i"></a>
**Lemma 332** (`KrepCont_add_pi_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L319)</small>

$$
(\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to \forall (\theta : \mathbb{R}), \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta + \pi \cdot i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta)
$$

*Proof.* By [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Lem 331](#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i). $\square$

<small>Referenced in [Lem 93](#d-qiqth-fock-boostkms-kmsfun-sub-i), [Lem 117](#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [Lem 359](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed).</small>

<a id="d-qiqth-fock-wedgeanalyticity-sq-div-eight-le-cosh"></a>
**Lemma 333** (`sq_div_eight_le_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L360)</small>

$$
{\theta}^{2} / 8 \le \cosh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 334](#d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh).</small>

<a id="d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh"></a>
**Lemma 334** (`integrable_exp_neg_const_mul_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L375)</small>

$$
0 < c \to \mathrm{Integrable}\,(\lambda \theta \mapsto \exp\,(-(c \cdot \cosh\,\theta)))\,\mathrm{volume}
$$

*Proof.* By [Lem 333](#d-qiqth-fock-wedgeanalyticity-sq-div-eight-le-cosh). $\square$

<small>Referenced in [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 343](#d-qiqth-fock-wedgeanalyticity-integrable-cosh-mul-exp-neg-const-mul-cosh), [Lem 353](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine).</small>

<a id="d-qiqth-fock-wedgeanalyticity-abs-sinh-le-cosh"></a>
**Lemma 335** (`abs_sinh_le_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L386)</small>

$$
|\sinh\,\theta| \le \cosh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 338](#d-qiqth-fock-wedgeanalyticity-cosh-add-le-exp-abs-mul), [Lem 339](#d-qiqth-fock-wedgeanalyticity-exp-neg-abs-mul-le-cosh-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-add-abs-sinh"></a>
**Lemma 336** (`cosh_add_abs_sinh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L392)</small>

$$
\cosh\,s + |\sinh\,s| = \exp\,|s|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 338](#d-qiqth-fock-wedgeanalyticity-cosh-add-le-exp-abs-mul).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-sub-abs-sinh"></a>
**Lemma 337** (`cosh_sub_abs_sinh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L402)</small>

$$
\cosh\,s - |\sinh\,s| = \exp\,(-|s|)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 339](#d-qiqth-fock-wedgeanalyticity-exp-neg-abs-mul-le-cosh-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-add-le-exp-abs-mul"></a>
**Lemma 338** (`cosh_add_le_exp_abs_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L412)</small>

$$
\cosh\,(\theta + s) \le \exp\,|s| \cdot \cosh\,\theta
$$

*Proof.* By [Lem 335](#d-qiqth-fock-wedgeanalyticity-abs-sinh-le-cosh), [Lem 336](#d-qiqth-fock-wedgeanalyticity-cosh-add-abs-sinh). $\square$

<small>Referenced in [Lem 341](#d-qiqth-fock-wedgeanalyticity-cosh-shift-exp-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-exp-neg-abs-mul-le-cosh-add"></a>
**Lemma 339** (`exp_neg_abs_mul_le_cosh_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L421)</small>

$$
\exp\,(-|s|) \cdot \cosh\,\theta \le \cosh\,(\theta + s)
$$

*Proof.* By [Lem 335](#d-qiqth-fock-wedgeanalyticity-abs-sinh-le-cosh), [Lem 337](#d-qiqth-fock-wedgeanalyticity-cosh-sub-abs-sinh). $\square$

<small>Referenced in [Lem 341](#d-qiqth-fock-wedgeanalyticity-cosh-shift-exp-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos"></a>
**Lemma 340** (`sin_neg_pi_mul_pos`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L440)</small>

$$
-1 < w \to w < 0 \to 0 < \sin\,(-(\pi \cdot w))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 105](#d-qiqth-fock-boostkms-exists-sin-min), [Lem 106](#d-qiqth-fock-boostkms-norm-term1-le), [Lem 107](#d-qiqth-fock-boostkms-norm-term2-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-shift-exp-le"></a>
**Lemma 341** (`cosh_shift_exp_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L444)</small>

$$
|s| \le S \to 0 < c_{0} \to c_{0} \le c \to \cosh\,(\theta + s) \cdot \exp\,(-(c \cdot \cosh\,(\theta + s))) \le \exp\,S \cdot \cosh\,\theta \cdot \exp\,(-(c_{0} \cdot \exp\,(-S) \cdot \cosh\,\theta))
$$

*Proof.* By [Lem 338](#d-qiqth-fock-wedgeanalyticity-cosh-add-le-exp-abs-mul), [Lem 339](#d-qiqth-fock-wedgeanalyticity-exp-neg-abs-mul-le-cosh-add). $\square$

<small>Referenced in [Lem 342](#d-qiqth-fock-wedgeanalyticity-prod-norm-bound-cosh-shift).</small>

<a id="d-qiqth-fock-wedgeanalyticity-prod-norm-bound-cosh-shift"></a>
**Lemma 342** (`prod_norm_bound_cosh_shift`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L466)</small>

$$
\mathrm{na} \le \mathrm{Cd} \cdot (\cosh\,(\theta + s) \cdot \exp\,(-(c \cdot \cosh\,(\theta + s)))) \to \mathrm{nb} \le \mathrm{Cb} \to 0 \le \mathrm{nb} \to 0 \le \mathrm{Cb} \to 0 \le \mathrm{Cd} \to |s| \le S \to 0 < c_{0} \to c_{0} \le c \to \mathrm{na} \cdot \mathrm{nb} \le \mathrm{Cd} \cdot \mathrm{Cb} \cdot (\exp\,S \cdot \cosh\,\theta \cdot \exp\,(-(c_{0} \cdot \exp\,(-S) \cdot \cosh\,\theta)))
$$

*Proof.* By [Lem 341](#d-qiqth-fock-wedgeanalyticity-cosh-shift-exp-le). $\square$

<small>Referenced in [Lem 106](#d-qiqth-fock-boostkms-norm-term1-le), [Lem 107](#d-qiqth-fock-boostkms-norm-term2-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-integrable-cosh-mul-exp-neg-const-mul-cosh"></a>
**Lemma 343** (`integrable_cosh_mul_exp_neg_const_mul_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L480)</small>

$$
0 < c \to \mathrm{Integrable}\,(\lambda s \mapsto \cosh\,s \cdot \exp\,(-(c \cdot \cosh\,s)))\,\mathrm{volume}
$$

*Proof.* By [Lem 334](#d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh). $\square$

<small>Referenced in [Lem 109](#d-qiqth-fock-boostkms-kmsfun-differentiableat), [Lem 113](#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-eq"></a>
**Lemma 344** (`norm_kernel_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L516)</small>

$$
\|\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,(\theta + \mathrm{lam} \cdot i)\| = \exp\,(m \cdot \sin\,\mathrm{lam} \cdot (\sinh\,\theta \cdot x\,0 - \cosh\,\theta \cdot x\,1))
$$

*Proof.* By [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell), [Lem 309](#d-qiqth-fock-wedgeanalyticity-cosh-ofreal-add-ofreal-mul-i), [Lem 310](#d-qiqth-fock-wedgeanalyticity-sinh-ofreal-add-ofreal-mul-i). $\square$

<small>Referenced in [Lem 345](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq), [Lem 346](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-eq"></a>
**Lemma 345** (`norm_kernel_eq'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L528)</small>

$$
\|\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta\| = \exp\,(m \cdot \sin\,\zeta.\mathrm{im} \cdot (\sinh\,\zeta.\mathrm{re} \cdot x\,0 - \cosh\,\zeta.\mathrm{re} \cdot x\,1))
$$

*Proof.* By [Lem 344](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq). $\square$

<small>Referenced in [Lem 347](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay"></a>
**Lemma 346** (`norm_kernel_le_exp_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L536)</small>

$$
0 \le m \to \forall \{x : \href{#d-qiqth-fock-localization-v}{V}\} \{\delta : \mathbb{R}\}, \delta \le x\,1 - x\,0 \to \delta \le x\,1 + x\,0 \to \forall \{\theta \mathrm{lam} : \mathbb{R}\}, 0 \le \mathrm{lam} \to \mathrm{lam} \le \pi \to \|\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,(\theta + \mathrm{lam} \cdot i)\| \le \exp\,(-(m \cdot \sin\,\mathrm{lam} \cdot \delta) \cdot \cosh\,\theta)
$$

*Proof.* By [Lem 344](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq). $\square$

<small>Referenced in [Lem 349](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay"></a>
**Lemma 347** (`norm_kernel_le_exp_decay'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L553)</small>

$$
0 \le m \to \forall \{x : \href{#d-qiqth-fock-localization-v}{V}\} \{\delta : \mathbb{R}\}, \delta \le x\,1 - x\,0 \to \delta \le x\,1 + x\,0 \to \forall \{\zeta : \mathbb{C}\}, 0 \le \zeta.\mathrm{im} \to \zeta.\mathrm{im} \le \pi \to \|\href{#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta\| \le \exp\,(-(m \cdot \sin\,\zeta.\mathrm{im} \cdot \delta) \cdot \cosh\,\zeta.\mathrm{re})
$$

*Proof.* By [Lem 345](#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq). $\square$

<small>Referenced in [Lem 348](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay"></a>
**Lemma 348** (`norm_kernelDeriv_le_exp_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L568)</small>

$$
0 \le m \to \forall \{x : \href{#d-qiqth-fock-localization-v}{V}\} \{\delta : \mathbb{R}\}, \delta \le x\,1 - x\,0 \to \delta \le x\,1 + x\,0 \to \forall \{\zeta : \mathbb{C}\}, 0 \le \zeta.\mathrm{im} \to \zeta.\mathrm{im} \le \pi \to \|\href{#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta\| \le \exp\,(-(m \cdot \sin\,\zeta.\mathrm{im} \cdot \delta) \cdot \cosh\,\zeta.\mathrm{re}) \cdot (|m| \cdot \cosh\,\zeta.\mathrm{re} \cdot (|x\,0| + |x\,1|))
$$

*Proof.* By [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 320](#d-qiqth-fock-wedgeanalyticity-norm-cosh-le-cosh-re), [Lem 321](#d-qiqth-fock-wedgeanalyticity-norm-sinh-le-cosh-re), [Lem 347](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay). $\square$

<small>Referenced in [Lem 350](#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay"></a>
**Lemma 349** (`norm_KrepCont_le_exp_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L592)</small>

$$
0 \le m \to \forall \{f : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{\theta \mathrm{lam} : \mathbb{R}\}, 0 \le \mathrm{lam} \to \mathrm{lam} \le \pi \to \|\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta + \mathrm{lam} \cdot i)\| \le (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|f\,x\|) \cdot \exp\,(-(m \cdot \sin\,\mathrm{lam} \cdot \delta) \cdot \cosh\,\theta)
$$

*Proof.* By [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell), [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 346](#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay). $\square$

<small>Referenced in [Lem 351](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay"></a>
**Lemma 350** (`norm_deriv_KrepCont_le_exp_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L621)</small>

$$
0 \le m \to \forall \{f : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{\zeta : \mathbb{C}\}, 0 \le \zeta.\mathrm{im} \to \zeta.\mathrm{im} \le \pi \to \|\mathrm{deriv}\,(\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,\zeta\| \le 1 / \sqrt 2 \cdot (|m| \cdot \cosh\,\zeta.\mathrm{re} \cdot \exp\,(-(m \cdot \sin\,\zeta.\mathrm{im} \cdot \delta) \cdot \cosh\,\zeta.\mathrm{re}) \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|f\,x\|)
$$

*Proof.* By [Def 314](#d-qiqth-fock-wedgeanalyticity-kernelderiv), [Lem 330](#d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq), [Lem 348](#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay). $\square$

<small>Referenced in [Lem 97](#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le), [Lem 107](#d-qiqth-fock-boostkms-norm-term2-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen"></a>
**Lemma 351** (`norm_KrepCont_le_exp_decay_gen`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L655)</small>

$$
0 \le m \to \forall \{f : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{w : \mathbb{C}\}, 0 \le w.\mathrm{im} \to w.\mathrm{im} \le \pi \to \|\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,w\| \le (1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|f\,x\|) \cdot \exp\,(-(m \cdot \sin\,w.\mathrm{im} \cdot \delta) \cdot \cosh\,w.\mathrm{re})
$$

*Proof.* By [Lem 349](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay). $\square$

<small>Referenced in [Lem 95](#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [Lem 104](#d-qiqth-fock-boostkms-integrable-kmsintegrand), [Lem 106](#d-qiqth-fock-boostkms-norm-term1-le), [Lem 352](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const), [Lem 353](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const"></a>
**Lemma 352** (`norm_KrepCont_le_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L666)</small>

$$
0 \le m \to \forall \{f : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, 0 \le \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{w : \mathbb{C}\}, 0 \le w.\mathrm{im} \to w.\mathrm{im} \le \pi \to \|\href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,w\| \le 1 / \sqrt 2 \cdot \int (x : \href{#d-qiqth-fock-localization-v}{V}), \|f\,x\|
$$

*Proof.* By [Lem 351](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Referenced in [Lem 112](#d-qiqth-fock-boostkms-norm-kmsfuncut-le), [Lem 115](#d-qiqth-fock-boostkms-kmsfuncut-continuouson).</small>

<a id="d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine"></a>
**Lemma 353** (`memLp_KrepCont_affine`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L724)</small>

$$
0 < m \to \forall \{f : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{c_{0} : \mathbb{C}\}, 0 < c_{0}.\mathrm{im} \to c_{0}.\mathrm{im} < \pi \to \mathrm{MemLp}\,(\lambda \theta \mapsto \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta + c_{0}))\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 328](#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [Lem 334](#d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh), [Lem 351](#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Referenced in [Lem 359](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krepcont-add"></a>
**Lemma 354** (`KrepCont_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L757)</small>

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \forall (\zeta : \mathbb{C}), \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,(f_{1} + f_{2})\,\zeta = \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f_{1}\,\zeta + \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f_{2}\,\zeta
$$

*Proof.* By [Def 302](#d-qiqth-fock-wedgeanalyticity-minkowskidot), [Def 303](#d-qiqth-fock-wedgeanalyticity-massshell), [Def 311](#d-qiqth-fock-wedgeanalyticity-kernel), [Lem 316](#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x). $\square$

<small>Referenced in [Lem 130](#d-qiqth-fock-boostkms-kmsfun-add-left), [Lem 131](#d-qiqth-fock-boostkms-kmsfun-add-right), [Lem 355](#d-qiqth-fock-wedgeanalyticity-krep-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krep-add"></a>
**Lemma 355** (`Krep_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L775)</small>

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \forall (\theta : \mathbb{R}), \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f_{1} + f_{2})\,\theta = \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1}\,\theta + \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2}\,\theta
$$

*Proof.* By [Def 304](#d-qiqth-fock-wedgeanalyticity-krepcont), [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Lem 354](#d-qiqth-fock-wedgeanalyticity-krepcont-add). $\square$

<small>Referenced in [Lem 137](#d-qiqth-fock-boostkms-krepl2-add), [Lem 356](#d-qiqth-fock-wedgeanalyticity-krep-sub), [Lem 357](#d-qiqth-fock-wedgeanalyticity-memlp-krep-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krep-sub"></a>
**Lemma 356** (`Krep_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L783)</small>

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \forall (\theta : \mathbb{R}), \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f_{1} - f_{2})\,\theta = \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1}\,\theta - \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2}\,\theta
$$

*Proof.* By [Lem 355](#d-qiqth-fock-wedgeanalyticity-krep-add). $\square$

<small>Referenced in [Lem 138](#d-qiqth-fock-boostkms-krepl2-sub), [Lem 358](#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub).</small>

<a id="d-qiqth-fock-wedgeanalyticity-memlp-krep-add"></a>
**Lemma 357** (`memLp_Krep_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L793)</small>

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f_{1} + f_{2}))\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 355](#d-qiqth-fock-wedgeanalyticity-krep-add). $\square$

<small>Referenced in [Lem 137](#d-qiqth-fock-boostkms-krepl2-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-memlp-krep-sub"></a>
**Lemma 358** (`memLp_Krep_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L804)</small>

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f_{1} - f_{2}))\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 356](#d-qiqth-fock-wedgeanalyticity-krep-sub). $\square$

<small>Referenced in [Lem 132](#d-qiqth-fock-boostkms-kmsfun-sub-left), [Lem 133](#d-qiqth-fock-boostkms-kmsfun-sub-right), [Lem 138](#d-qiqth-fock-boostkms-krepl2-sub), [Lem 140](#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed"></a>
**Lemma 359** (`memLp_KrepCont_affine_closed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L814)</small>

$$
0 < m \to \forall \{f : \href{#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to \mathrm{MemLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \forall \{c_{0} : \mathbb{C}\}, 0 \le c_{0}.\mathrm{im} \to c_{0}.\mathrm{im} \le \pi \to \mathrm{MemLp}\,(\lambda \theta \mapsto \href{#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta + c_{0}))\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 308](#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [Lem 332](#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [Lem 353](#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine). $\square$

<small>Referenced in [Lem 126](#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed).</small>

<a id="sec-qiqth-fock-wienerl2"></a>
## QIQTH.Fock.WienerL2

<a id="d-qiqth-fock-wienerl2-schwartztranslate"></a>
**Definition 360** (`schwartzTranslate`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L31)</small>

A definition — see source for the body.

<small>Referenced in [Lem 361](#d-qiqth-fock-wienerl2-schwartztranslate-apply), [Lem 362](#d-qiqth-fock-wienerl2-boostunitary-tolp), [Lem 370](#d-qiqth-fock-wienerl2-fourier-schwartztranslate), [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary).</small>

<a id="d-qiqth-fock-wienerl2-schwartztranslate-apply"></a>
**Lemma 361** (`schwartzTranslate_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L45)</small>

$$
((\href{#d-qiqth-fock-wienerl2-schwartztranslate}{\tau}\,a)\,f)\,x = f\,(x + a)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 362](#d-qiqth-fock-wienerl2-boostunitary-tolp), [Lem 370](#d-qiqth-fock-wienerl2-fourier-schwartztranslate).</small>

<a id="d-qiqth-fock-wienerl2-boostunitary-tolp"></a>
**Lemma 362** (`boostUnitary_toLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L49)</small>

$$
(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,(f.\mathrm{toLp}\,2\,\mathrm{volume}) = ((\href{#d-qiqth-fock-wienerl2-schwartztranslate}{\tau}\,(-a))\,f).\mathrm{toLp}\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 277](#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [Lem 361](#d-qiqth-fock-wienerl2-schwartztranslate-apply). $\square$

<small>Referenced in [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary).</small>

<a id="d-qiqth-fock-wienerl2-modchar"></a>
**Definition 363** (`modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L73)</small>

A definition — see source for the body.

<small>Referenced in [Lem 364](#d-qiqth-fock-wienerl2-norm-modchar), [Lem 365](#d-qiqth-fock-wienerl2-continuous-modchar), [Lem 366](#d-qiqth-fock-wienerl2-memlp-modchar-smul), [Def 367](#d-qiqth-fock-wienerl2-modl2), [Lem 368](#d-qiqth-fock-wienerl2-coefn-modl2), [Lem 369](#d-qiqth-fock-wienerl2-norm-modl2), [Lem 370](#d-qiqth-fock-wienerl2-fourier-schwartztranslate), [Lem 371](#d-qiqth-fock-wienerl2-modl2-sub), [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary), [Lem 375](#d-qiqth-fock-wienerl2-conj-modchar), [Lem 376](#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral), [Lem 377](#d-qiqth-fock-wienerl2-fourier-correlation-eq).</small>

<a id="d-qiqth-fock-wienerl2-norm-modchar"></a>
**Lemma 364** (`norm_modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L76)</small>

$$
\|\href{#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c\,\xi\| = 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 366](#d-qiqth-fock-wienerl2-memlp-modchar-smul), [Lem 369](#d-qiqth-fock-wienerl2-norm-modl2).</small>

<a id="d-qiqth-fock-wienerl2-continuous-modchar"></a>
**Lemma 365** (`continuous_modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L80)</small>

$$
\mathrm{Continuous}\,(\href{#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 366](#d-qiqth-fock-wienerl2-memlp-modchar-smul).</small>

<a id="d-qiqth-fock-wienerl2-memlp-modchar-smul"></a>
**Lemma 366** (`memLp_modChar_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L83)</small>

$$
\mathrm{MemLp}\,(\lambda \xi \mapsto \href{#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c\,\xi \cdot g\,\xi)\,2\,\mathrm{volume}
$$

*Proof.* By [Lem 364](#d-qiqth-fock-wienerl2-norm-modchar), [Lem 365](#d-qiqth-fock-wienerl2-continuous-modchar). $\square$

<small>Referenced in [Def 367](#d-qiqth-fock-wienerl2-modl2), [Lem 368](#d-qiqth-fock-wienerl2-coefn-modl2).</small>

<a id="d-qiqth-fock-wienerl2-modl2"></a>
**Definition 367** (`modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L91)</small>

A definition — see source for the body.

<small>Referenced in [Lem 368](#d-qiqth-fock-wienerl2-coefn-modl2), [Lem 369](#d-qiqth-fock-wienerl2-norm-modl2), [Lem 371](#d-qiqth-fock-wienerl2-modl2-sub), [Lem 372](#d-qiqth-fock-wienerl2-isometry-modl2), [Lem 373](#d-qiqth-fock-wienerl2-continuous-modl2), [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary), [Lem 376](#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral).</small>

<a id="d-qiqth-fock-wienerl2-coefn-modl2"></a>
**Lemma 368** (`coeFn_modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L95)</small>

$$
(\href{#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,g) =[\mathrm{volume}] \lambda \xi \mapsto \href{#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c\,\xi \cdot g\,\xi
$$

*Proof.* By [Lem 366](#d-qiqth-fock-wienerl2-memlp-modchar-smul). $\square$

<small>Referenced in [Lem 369](#d-qiqth-fock-wienerl2-norm-modl2), [Lem 371](#d-qiqth-fock-wienerl2-modl2-sub), [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary), [Lem 376](#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral).</small>

<a id="d-qiqth-fock-wienerl2-norm-modl2"></a>
**Lemma 369** (`norm_modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L107)</small>

$$
\|\href{#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,g\| = \|g\|
$$

*Proof.* By [Def 363](#d-qiqth-fock-wienerl2-modchar), [Lem 364](#d-qiqth-fock-wienerl2-norm-modchar), [Lem 368](#d-qiqth-fock-wienerl2-coefn-modl2). $\square$

<small>Referenced in [Lem 372](#d-qiqth-fock-wienerl2-isometry-modl2).</small>

<a id="d-qiqth-fock-wienerl2-fourier-schwartztranslate"></a>
**Lemma 370** (`fourier_schwartzTranslate`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L125)</small>

$$
(\mathcal{F}\,((\href{#d-qiqth-fock-wienerl2-schwartztranslate}{\tau}\,(-a))\,f))\,w = \href{#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,(-(2 \cdot \pi \cdot a))\,w \cdot (\mathcal{F}\,f)\,w
$$

*Proof.* By [Lem 361](#d-qiqth-fock-wienerl2-schwartztranslate-apply). $\square$

<small>Referenced in [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary).</small>

<a id="d-qiqth-fock-wienerl2-modl2-sub"></a>
**Lemma 371** (`modL2_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L148)</small>

$$
\href{#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,(g - h) = \href{#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,g - \href{#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c\,h
$$

*Proof.* By [Def 363](#d-qiqth-fock-wienerl2-modchar), [Lem 368](#d-qiqth-fock-wienerl2-coefn-modl2). $\square$

<small>Referenced in [Lem 372](#d-qiqth-fock-wienerl2-isometry-modl2).</small>

<a id="d-qiqth-fock-wienerl2-isometry-modl2"></a>
**Lemma 372** (`isometry_modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L156)</small>

$$
\mathrm{Isometry}\,(\href{#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c)
$$

*Proof.* By [Lem 369](#d-qiqth-fock-wienerl2-norm-modl2), [Lem 371](#d-qiqth-fock-wienerl2-modl2-sub). $\square$

<small>Referenced in [Lem 373](#d-qiqth-fock-wienerl2-continuous-modl2).</small>

<a id="d-qiqth-fock-wienerl2-continuous-modl2"></a>
**Lemma 373** (`continuous_modL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L161)</small>

$$
\mathrm{Continuous}\,(\href{#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,c)
$$

*Proof.* By [Lem 372](#d-qiqth-fock-wienerl2-isometry-modl2). $\square$

<small>Referenced in [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary).</small>

<a id="d-qiqth-fock-wienerl2-fourierl2-boostunitary"></a>
**Lemma 374** (`fourierL2_boostUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L163)</small>

$$
\mathcal{F}\,((\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,g) = \href{#d-qiqth-fock-wienerl2-modl2}{\mathrm{modL2}}\,(-(2 \cdot \pi \cdot a))\,(\mathcal{F}\,g)
$$

*Proof.* By [Def 360](#d-qiqth-fock-wienerl2-schwartztranslate), [Lem 362](#d-qiqth-fock-wienerl2-boostunitary-tolp), [Def 363](#d-qiqth-fock-wienerl2-modchar), [Lem 368](#d-qiqth-fock-wienerl2-coefn-modl2), [Lem 370](#d-qiqth-fock-wienerl2-fourier-schwartztranslate), [Lem 373](#d-qiqth-fock-wienerl2-continuous-modl2). $\square$

<small>Referenced in [Lem 376](#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral).</small>

<a id="d-qiqth-fock-wienerl2-conj-modchar"></a>
**Lemma 375** (`conj_modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L192)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,c\,\xi) = \href{#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,(-c)\,\xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 376](#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral).</small>

<a id="d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral"></a>
**Lemma 376** (`inner_boostUnitary_eq_integral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L200)</small>

$$
\langle {(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,g_{0}},{h}\rangle = \int (\xi : \mathbb{R}), \href{#d-qiqth-fock-wienerl2-modchar}{\chi_{\mathrm{mod}}}\,(2 \cdot \pi \cdot a)\,\xi \cdot ((\mathrm{starRingEnd}\,\mathbb{C})\,((\mathcal{F}\,g_{0})\,\xi) \cdot (\mathcal{F}\,h)\,\xi)
$$

*Proof.* By [Def 367](#d-qiqth-fock-wienerl2-modl2), [Lem 368](#d-qiqth-fock-wienerl2-coefn-modl2), [Lem 374](#d-qiqth-fock-wienerl2-fourierl2-boostunitary), [Lem 375](#d-qiqth-fock-wienerl2-conj-modchar). $\square$

<small>Referenced in [Lem 377](#d-qiqth-fock-wienerl2-fourier-correlation-eq).</small>

<a id="d-qiqth-fock-wienerl2-fourier-correlation-eq"></a>
**Lemma 377** (`fourier_correlation_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L223)</small>

$$
\mathcal{F}\,(\lambda \xi \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,((\mathcal{F}\,g_{0})\,\xi) \cdot (\mathcal{F}\,h)\,\xi)\,w = \langle {(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-w))\,g_{0}},{h}\rangle
$$

*Proof.* By [Def 363](#d-qiqth-fock-wienerl2-modchar), [Lem 376](#d-qiqth-fock-wienerl2-inner-boostunitary-eq-integral). $\square$

<small>Referenced in [Lem 379](#d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-ae-eq-zero-of-fourier-eq-zero"></a>
**Lemma 378** (`ae_eq_zero_of_fourier_eq_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L239)</small>

$$
\mathrm{Integrable}\,k\,\mathrm{volume} \to (\forall (w : \mathbb{R}), \mathcal{F}\,k\,w = 0) \to k =[\mathrm{volume}] 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 379](#d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero), [Lem 402](#d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero"></a>
**Lemma 379** (`boost_orbit_total_of_fourier_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L268)</small>

$$
(\forall (\xi : \mathbb{R}), (\mathcal{F}\,g_{0})\,\xi \ne 0) \to (\forall (a : \mathbb{R}), \langle {(\href{#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,g_{0}},{h}\rangle = 0) \to h = 0
$$

*Proof.* By [Lem 377](#d-qiqth-fock-wienerl2-fourier-correlation-eq), [Lem 378](#d-qiqth-fock-wienerl2-ae-eq-zero-of-fourier-eq-zero). $\square$

<small>Referenced in [Lem 198](#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-ae-ne-zero-of-analyticonnhd"></a>
**Lemma 380** (`ae_ne_zero_of_analyticOnNhd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L291)</small>

$$
\mathrm{AnalyticOnNhd}\,\mathbb{R}\,F \to (\exists x, F\,x \ne 0) \to \forall (x : \mathbb{R}), F\,x \ne 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 402](#d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-integrable-exp-neg-mul-abs"></a>
**Lemma 381** (`integrable_exp_neg_mul_abs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L324)</small>

$$
0 < b \to \mathrm{Integrable}\,(\lambda x \mapsto \exp\,(-b \cdot |x|))\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 382](#d-qiqth-fock-wienerl2-integrable-abs-mul-exp-neg-mul-abs), [Lem 384](#d-qiqth-fock-wienerl2-integrable-krep), [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep).</small>

<a id="d-qiqth-fock-wienerl2-integrable-abs-mul-exp-neg-mul-abs"></a>
**Lemma 382** (`integrable_abs_mul_exp_neg_mul_abs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L348)</small>

$$
0 < d \to \mathrm{Integrable}\,(\lambda \theta \mapsto |\theta| \cdot \exp\,(-d \cdot |\theta|))\,\mathrm{volume}
$$

*Proof.* By [Lem 381](#d-qiqth-fock-wienerl2-integrable-exp-neg-mul-abs). $\square$

<small>Referenced in [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-inv-cosh-sq-le-exp"></a>
**Lemma 383** (`inv_cosh_sq_le_exp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L369)</small>

$$
{({\cosh\,\theta}^{2})}^{-1} \le 4 \cdot \exp\,(-2 \cdot |\theta|)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 384](#d-qiqth-fock-wienerl2-integrable-krep), [Lem 392](#d-qiqth-fock-wienerl2-norm-krep-le-exp).</small>

<a id="d-qiqth-fock-wienerl2-integrable-krep"></a>
**Lemma 384** (`integrable_Krep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L386)</small>

$$
m \ne 0 \to \mathrm{Integrable}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{volume}
$$

*Proof.* By [Lem 254](#d-qiqth-fock-localization-krep-continuous), [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq), [Lem 381](#d-qiqth-fock-wienerl2-integrable-exp-neg-mul-abs), [Lem 383](#d-qiqth-fock-wienerl2-inv-cosh-sq-le-exp). $\square$

<small>Referenced in [Lem 403](#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-ftkrep"></a>
**Definition 385** (`ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L410)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Def 387](#d-qiqth-fock-wienerl2-ftkrepf), [Lem 388](#d-qiqth-fock-wienerl2-hasderivat-ftkrep), [Lem 391](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 393](#d-qiqth-fock-wienerl2-continuous-ftkrep), [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep), [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf), [Lem 398](#d-qiqth-fock-wienerl2-ftkrepf-eq-fourier).</small>

<a id="d-qiqth-fock-wienerl2-ftkrep"></a>
**Definition 386** (`ftKrep'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L414)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 388](#d-qiqth-fock-wienerl2-hasderivat-ftkrep), [Lem 390](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 394](#d-qiqth-fock-wienerl2-continuous-ftkrep), [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf), [Lem 397](#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real).</small>

<a id="d-qiqth-fock-wienerl2-ftkrepf"></a>
**Definition 387** (`ftKrepF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L419)</small>

A definition, built from [Def 226](#d-qiqth-fock-localization-v) — see source for the body.

<small>Referenced in [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf), [Lem 397](#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real), [Lem 398](#d-qiqth-fock-wienerl2-ftkrepf-eq-fourier), [Lem 399](#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep).</small>

<a id="d-qiqth-fock-wienerl2-hasderivat-ftkrep"></a>
**Lemma 388** (`hasDerivAt_ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L422)</small>

$$
({\lambda \zeta \mapsto \href{#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,f\,\zeta\,\theta})'({\zeta_{0}})={\href{#d-qiqth-fock-wienerl2-ftkrep}{\hat{K}}\,m\,f\,\zeta_{0}\,\theta}
$$

*Proof.* By [Def 246](#d-qiqth-fock-localization-krep). $\square$

<small>Referenced in [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-ftkrep-exp-re"></a>
**Lemma 389** (`ftKrep_exp_re`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L434)</small>

$$
(-2 \cdot \pi \cdot i \cdot \theta \cdot \zeta).\mathrm{re} = 2 \cdot \pi \cdot \theta \cdot \zeta.\mathrm{im}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 390](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 391](#d-qiqth-fock-wienerl2-norm-ftkrep).</small>

<a id="d-qiqth-fock-wienerl2-norm-ftkrep"></a>
**Lemma 390** (`norm_ftKrep'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L443)</small>

$$
\|\href{#d-qiqth-fock-wienerl2-ftkrep}{\hat{K}}\,m\,f\,\zeta\,\theta\| = 2 \cdot \pi \cdot |\theta| \cdot \exp\,(2 \cdot \pi \cdot \theta \cdot \zeta.\mathrm{im}) \cdot \|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|
$$

*Proof.* By [Lem 389](#d-qiqth-fock-wienerl2-ftkrep-exp-re). $\square$

<small>Referenced in [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-norm-ftkrep"></a>
**Lemma 391** (`norm_ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L455)</small>

$$
\|\href{#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,f\,\zeta\,\theta\| = \exp\,(2 \cdot \pi \cdot \theta \cdot \zeta.\mathrm{im}) \cdot \|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|
$$

*Proof.* By [Lem 389](#d-qiqth-fock-wienerl2-ftkrep-exp-re). $\square$

<small>Referenced in [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep).</small>

<a id="d-qiqth-fock-wienerl2-norm-krep-le-exp"></a>
**Lemma 392** (`norm_Krep_le_exp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L461)</small>

$$
m \ne 0 \to \exists C, 0 \le C \wedge \forall (\theta : \mathbb{R}), \|\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f)\,\theta\| \le C \cdot \exp\,(-2 \cdot |\theta|)
$$

*Proof.* By [Lem 301](#d-qiqth-fock-localization-schwartz-krep-decay-sq), [Lem 383](#d-qiqth-fock-wienerl2-inv-cosh-sq-le-exp). $\square$

<small>Referenced in [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep), [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-continuous-ftkrep"></a>
**Lemma 393** (`continuous_ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L475)</small>

$$
\mathrm{Continuous}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f) \to \forall (\zeta : \mathbb{C}), \mathrm{Continuous}\,\lambda \theta \mapsto \href{#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,f\,\zeta\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep), [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-continuous-ftkrep"></a>
**Lemma 394** (`continuous_ftKrep'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L479)</small>

$$
\mathrm{Continuous}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f) \to \forall (\zeta : \mathbb{C}), \mathrm{Continuous}\,\lambda \theta \mapsto \href{#d-qiqth-fock-wienerl2-ftkrep}{\hat{K}}\,m\,f\,\zeta\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-integrable-ftkrep"></a>
**Lemma 395** (`integrable_ftKrep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L484)</small>

$$
m \ne 0 \to \forall \{\zeta : \mathbb{C}\}, |\zeta.\mathrm{im}| < 1 / \pi \to \mathrm{Integrable}\,(\lambda \theta \mapsto \href{#d-qiqth-fock-wienerl2-ftkrep}{\mathrm{ftKrep}}\,m\,(f)\,\zeta\,\theta)\,\mathrm{volume}
$$

*Proof.* By [Def 246](#d-qiqth-fock-localization-krep), [Lem 254](#d-qiqth-fock-localization-krep-continuous), [Lem 381](#d-qiqth-fock-wienerl2-integrable-exp-neg-mul-abs), [Lem 391](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 392](#d-qiqth-fock-wienerl2-norm-krep-le-exp), [Lem 393](#d-qiqth-fock-wienerl2-continuous-ftkrep). $\square$

<small>Referenced in [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf).</small>

<a id="d-qiqth-fock-wienerl2-hasderivat-ftkrepf"></a>
**Lemma 396** (`hasDerivAt_ftKrepF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L506)</small>

$$
m \ne 0 \to \forall \{\zeta_{0} : \mathbb{C}\}, |\zeta_{0}.\mathrm{im}| < 1 / \pi \to ({\href{#d-qiqth-fock-wienerl2-ftkrepf}{\hat{K}}\,m\,f})'({\zeta_{0}})={\int (\theta : \mathbb{R}), \href{#d-qiqth-fock-wienerl2-ftkrep}{\hat{K}}\,m\,(f)\,\zeta_{0}\,\theta}
$$

*Proof.* By [Def 246](#d-qiqth-fock-localization-krep), [Lem 254](#d-qiqth-fock-localization-krep-continuous), [Lem 382](#d-qiqth-fock-wienerl2-integrable-abs-mul-exp-neg-mul-abs), [Def 385](#d-qiqth-fock-wienerl2-ftkrep), [Lem 388](#d-qiqth-fock-wienerl2-hasderivat-ftkrep), [Lem 390](#d-qiqth-fock-wienerl2-norm-ftkrep), [Lem 392](#d-qiqth-fock-wienerl2-norm-krep-le-exp), [Lem 393](#d-qiqth-fock-wienerl2-continuous-ftkrep), [Lem 394](#d-qiqth-fock-wienerl2-continuous-ftkrep), [Lem 395](#d-qiqth-fock-wienerl2-integrable-ftkrep). $\square$

<small>Referenced in [Lem 397](#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real).</small>

<a id="d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real"></a>
**Lemma 397** (`analyticOnNhd_ftKrepF_real`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L559)</small>

$$
m \ne 0 \to \mathrm{AnalyticOnNhd}\,\mathbb{R}\,(\lambda \xi \mapsto \href{#d-qiqth-fock-wienerl2-ftkrepf}{\hat{K}}\,m\,f\,\xi)
$$

*Proof.* By [Def 386](#d-qiqth-fock-wienerl2-ftkrep), [Lem 396](#d-qiqth-fock-wienerl2-hasderivat-ftkrepf). $\square$

<small>Referenced in [Lem 399](#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep).</small>

<a id="d-qiqth-fock-wienerl2-ftkrepf-eq-fourier"></a>
**Lemma 398** (`ftKrepF_eq_fourier`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L577)</small>

$$
\href{#d-qiqth-fock-wienerl2-ftkrepf}{\hat{K}}\,m\,f\,\xi = \mathcal{F}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\xi
$$

*Proof.* By [Def 385](#d-qiqth-fock-wienerl2-ftkrep). $\square$

<small>Referenced in [Lem 399](#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep).</small>

<a id="d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep"></a>
**Lemma 399** (`analyticOnNhd_fourier_Krep`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L591)</small>

$$
m \ne 0 \to \mathrm{AnalyticOnNhd}\,\mathbb{R}\,(\lambda \xi \mapsto \mathcal{F}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\xi)
$$

*Proof.* By [Def 387](#d-qiqth-fock-wienerl2-ftkrepf), [Lem 397](#d-qiqth-fock-wienerl2-analyticonnhd-ftkrepf-real), [Lem 398](#d-qiqth-fock-wienerl2-ftkrepf-eq-fourier). $\square$

<small>Referenced in [Lem 403](#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-integral-smul-fourierl2-eq"></a>
**Lemma 400** (`integral_smul_fourierL2_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L602)</small>

$$
\mathrm{Integrable}\,g\,\mathrm{volume} \to \forall (\mathrm{hg2} : \mathrm{MemLp}\,g\,2\,\mathrm{volume}) (\varphi : \mathrm{SchwartzMap}\,\mathbb{R}\,\mathbb{C}), \int (x : \mathbb{R}), \varphi\,x \cdot (\mathcal{F}\,(\mathrm{toLp}\,g\,\mathrm{hg2}))\,x = \int (x : \mathbb{R}), \varphi\,x \cdot \mathcal{F}\,g\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 401](#d-qiqth-fock-wienerl2-fourierl2-tolp-ae-eq).</small>

<a id="d-qiqth-fock-wienerl2-fourierl2-tolp-ae-eq"></a>
**Lemma 401** (`fourierL2_toLp_ae_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L633)</small>

$$
\mathrm{Integrable}\,g\,\mathrm{volume} \to \forall (\mathrm{hg2} : \mathrm{MemLp}\,g\,2\,\mathrm{volume}), (\mathcal{F}\,(\mathrm{toLp}\,g\,\mathrm{hg2})) =[\mathrm{volume}] \mathcal{F}\,g
$$

*Proof.* By [Lem 400](#d-qiqth-fock-wienerl2-integral-smul-fourierl2-eq). $\square$

<small>Referenced in [Lem 402](#d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero"></a>
**Lemma 402** (`fourierL2_toLp_ne_zero_of_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L654)</small>

$$
\mathrm{Integrable}\,g\,\mathrm{volume} \to \forall (\mathrm{hg2} : \mathrm{MemLp}\,g\,2\,\mathrm{volume}), \mathrm{AnalyticOnNhd}\,\mathbb{R}\,(\lambda \xi \mapsto \mathcal{F}\,g\,\xi) \to \neg g =[\mathrm{volume}] 0 \to \forall (\xi : \mathbb{R}), (\mathcal{F}\,(\mathrm{toLp}\,g\,\mathrm{hg2}))\,\xi \ne 0
$$

*Proof.* By [Lem 378](#d-qiqth-fock-wienerl2-ae-eq-zero-of-fourier-eq-zero), [Lem 380](#d-qiqth-fock-wienerl2-ae-ne-zero-of-analyticonnhd), [Lem 401](#d-qiqth-fock-wienerl2-fourierl2-tolp-ae-eq). $\square$

<small>Referenced in [Lem 403](#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero).</small>

<a id="d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero"></a>
**Lemma 403** (`fourierL2_Krep_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WienerL2.lean#L669)</small>

$$
\neg \href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,\mathrm{fS} =[\mathrm{volume}] 0 \to \forall (\xi : \mathbb{R}), (\mathcal{F}\,(\mathrm{toLp}\,(\href{#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,\mathrm{fS})\,\cdots ))\,\xi \ne 0
$$

*Proof.* By [Lem 384](#d-qiqth-fock-wienerl2-integrable-krep), [Lem 399](#d-qiqth-fock-wienerl2-analyticonnhd-fourier-krep), [Lem 402](#d-qiqth-fock-wienerl2-fourierl2-tolp-ne-zero-of-ne-zero). $\square$

<small>Referenced in [Lem 211](#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw).</small>

<a id="sec-qiqth-hregexplicitkg"></a>
## QIQTH.HregExplicitKG

<a id="d-qiqth-curvature-kglagr-contdiff"></a>
**Lemma 404** (`kgLagr_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/HregExplicitKG.lean#L23)</small>

$$
({\varphi})\in C^{\infty} \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to ({\href{#d-qiqth-curvature-kglagr}{\mathrm{kgLagr}}\,m\,\varphi\,\mathrm{gi}})\in C^{\infty}
$$

*Proof.* By [Lem 2](#d-qiqth-curvature-contdiff-pd), [Def 10](#d-qiqth-curvature-pd). $\square$

<small>Referenced in [Lem 405](#d-qiqth-curvature-kgstress-contdiff).</small>

<a id="d-qiqth-curvature-kgstress-contdiff"></a>
**Lemma 405** (`kgStress_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/HregExplicitKG.lean#L35)</small>

$$
({\varphi})\in C^{\infty} \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-kgstress}{T({y})\,a\,b}})\in C^{\infty}
$$

*Proof.* By [Lem 2](#d-qiqth-curvature-contdiff-pd), [Def 10](#d-qiqth-curvature-pd), [Lem 404](#d-qiqth-curvature-kglagr-contdiff), [Def 407](#d-qiqth-curvature-kglagr). $\square$

<small>Referenced in [Lem 406](#d-qiqth-curvature-hreg-kg).</small>

<a id="d-qiqth-curvature-hreg-kg"></a>
**Lemma 406** (`hreg_kg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/HregExplicitKG.lean#L47)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to ({\varphi})\in C^{\infty} \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (f : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}), (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot \href{#d-qiqth-curvature-kgstress}{T({y})\,a^{\prime}\,b} = \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\rho : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \wedge \mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot \href{#d-qiqth-curvature-scalarcurv}{R({y})}
$$

*Proof.* By [Lem 6](#d-qiqth-curvature-scalarcurv-contdiff), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 79](#d-qiqth-curvature-metric-contraction-trace), [Lem 405](#d-qiqth-curvature-kgstress-contdiff). $\square$

<small>Referenced in [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="sec-qiqth-kgstressconservation"></a>
## QIQTH.KGStressConservation

<a id="d-qiqth-curvature-kglagr"></a>
**Definition 407** (`kgLagr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L26)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 404](#d-qiqth-curvature-kglagr-contdiff), [Lem 405](#d-qiqth-curvature-kgstress-contdiff), [Def 408](#d-qiqth-curvature-kgstress), [Lem 475](#d-qiqth-wedgekmstogr-bl-kgstress-null), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-curvature-kgstress"></a>
**Definition 408** (`kgStress`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L32)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 405](#d-qiqth-curvature-kgstress-contdiff), [Lem 406](#d-qiqth-curvature-hreg-kg), [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Lem 475](#d-qiqth-wedgekmstogr-bl-kgstress-null), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo).</small>

<a id="d-qiqth-curvature-kghess"></a>
**Definition 409** (`kgHess`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L69)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Def 410](#d-qiqth-curvature-boxfield).</small>

<a id="d-qiqth-curvature-boxfield"></a>
**Definition 410** (`boxField`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KGStressConservation.lean#L98)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo).</small>

<a id="sec-qiqth-kmscorrelation"></a>
## QIQTH.KMSCorrelation

<a id="d-qiqth-standardsubspacemodular-gfunction-eq-zero-const"></a>
**Lemma 411** (`gFunction_eq_zero_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L192)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to \forall (t : \mathbb{R}), ((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,t))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,t) = ((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,0))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,0)
$$

*Proof.* By [Lem 469](#d-qiqth-gfunction-norm-le), [Lem 473](#d-qiqth-diffcontoncl-gfunction), [Lem 867](#d-qiqth-standardsubspacemodular-gausssmearc-norm-le), [Def 893](#d-qiqth-stripuniqueness-kmshalfstripopen), [Lem 894](#d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip). $\square$

<small>Referenced in [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-entire"></a>
**Lemma 412** (`gConstancy_entire`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L232)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to \forall (t : \mathbb{R}), \langle {(V\,t)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))}\rangle = \langle {\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)}\rangle
$$

*Proof.* By [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [Lem 463](#d-qiqth-gfunction-zero), [Lem 464](#d-qiqth-gfunction-real-eq). $\square$

<small>Referenced in [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all"></a>
**Lemma 413** (`gFunction_top_edge_real_all`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L253)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to (\forall (s : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to \forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0
$$

*Proof.* By [Lem 465](#d-qiqth-gfunction-top-edge-real). $\square$

<small>Referenced in [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom"></a>
**Lemma 414** (`gConstancy_entire_of_bottom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L268)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to (\forall (s : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to \forall (t : \mathbb{R}), \langle {(V\,t)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))}\rangle = \langle {\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)}\rangle
$$

*Proof.* By [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 413](#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all). $\square$

<small>Referenced in [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit"></a>
**Lemma 415** (`gConstancy_of_entireVec_limit`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L288)</small>

$$
(\mathrm{Continuous}\,\lambda s \mapsto (V\,s)\,\eta) \to (\forall (s : \mathbb{R}), \|(V\,s)\,\eta\| \le \|\eta\|) \to (V\,0)\,\eta = \eta \to (\forall (n : \mathbb{R}), 0 < n \to \langle {(V\,t)\,(\href{#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta)},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\href{#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle) \to \langle {(V\,t)\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

*Proof.* By [Def 848](#d-qiqth-standardsubspacemodular-gausssmear), [Lem 858](#d-qiqth-standardsubspacemodular-entirevec-tendsto). $\square$

<small>Referenced in [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-real-smul"></a>
**Lemma 416** (`gConstancy_real_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L308)</small>

$$
\langle {(V\,t)\,v},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {v},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle \to \langle {(V\,t)\,(c \cdot v)},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {c \cdot v},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom"></a>
**Lemma 417** (`gConstancy_eta_of_bottom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L317)</small>

$$
(\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (V\,0)\,\eta = \eta \to (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to (\forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall (n : \mathbb{R}), 0 < n \to \forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to \forall (t : \mathbb{R}), \langle {(V\,t)\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))}\rangle = \langle {\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)}\rangle
$$

*Proof.* By [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 415](#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit), [Lem 416](#d-qiqth-standardsubspacemodular-gconstancy-real-smul), [Def 852](#d-qiqth-standardsubspacemodular-entirevec). $\square$

<small>Referenced in [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-of-tendsto-xi"></a>
**Lemma 418** (`gConstancy_of_tendsto_xi`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L340)</small>

$$
\mathrm{Tendsto}\,\xis\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi) \to (\forall (k : \mathbb{N}), \langle {(V\,t)\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\mathrm{s}\,k))}\rangle = \langle {\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\mathrm{s}\,k)}\rangle) \to \langle {(V\,t)\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 419](#d-qiqth-standardsubspacemodular-gconstancy-xi-of-density).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-xi-of-density"></a>
**Lemma 419** (`gConstancy_xi_of_density`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L359)</small>

$$
(\forall (\zeta : H), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \langle {(V\,t)\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))}\rangle = \langle {\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)}\rangle) \to (\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)) \to \forall \xi\in S.\mathrm{cl}, \langle {(V\,t)\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

*Proof.* By [Lem 418](#d-qiqth-standardsubspacemodular-gconstancy-of-tendsto-xi). $\square$

<small>Referenced in [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare"></a>
**Lemma 420** (`modUnitary_eq_of_orbit_compare`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L474)</small>

$$
(\forall \eta\in S.\mathrm{cl}, (V\,t)\,\eta \in S.\mathrm{cl}) \to (\forall \eta\in S.\mathrm{cl}, (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\eta \in S.\mathrm{cl}) \to (\forall \eta\in S.\mathrm{cl}, \forall (w : H), (\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,w = 0 \to \langle {w},{(V\,t)\,\eta}\rangle = \langle {w},{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\eta}\rangle) \to \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Lem 690](#d-qiqth-standardsubspacemodular-clm-eq-of-eqon-k), [Lem 745](#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [Lem 795](#d-qiqth-standardsubspacemodular-eq-of-mem-k-of-inner-perp-ik). $\square$

<small>Referenced in [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison).</small>

<a id="d-qiqth-standardsubspacemodular-clm-eq-of-inner-self-eq"></a>
**Lemma 421** (`clm_eq_of_inner_self_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L494)</small>

$$
(\forall (\xi : H), \langle {A\,\xi},{\xi}\rangle = \langle {B\,\xi},{\xi}\rangle) \to A = B
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 422](#d-qiqth-standardsubspacemodular-borelfc-congr-ae).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-congr-ae"></a>
**Lemma 422** (`borelFC_congr_ae`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L512)</small>

$$
(\forall (x : H), f =[\href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x] g) \to \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf} = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg}
$$

*Proof.* By [Lem 421](#d-qiqth-standardsubspacemodular-clm-eq-of-inner-self-eq), [Lem 446](#d-qiqth-rvdspec-borelfc-diag). $\square$

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq).</small>

<a id="d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq"></a>
**Lemma 423** (`deviceOpC_neg_half_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L534)</small>

$$
\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots = \href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S
$$

*Proof.* By [Lem 422](#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [Def 431](#d-qiqth-rvdspecmeasure), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 449](#d-qiqth-rvdspecmeasure-endpoints), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Def 875](#d-qiqth-standardsubspacemodular-devchar), [Lem 880](#d-qiqth-standardsubspacemodular-devchar-neg-half-i). $\square$

<small>Referenced in [Lem 424](#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half"></a>
**Lemma 424** (`modConj_deviceOpC_neg_half`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L562)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots )\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta)
$$

*Proof.* By [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Def 709](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 785](#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj). $\square$

<small>Referenced in [Lem 425](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq"></a>
**Lemma 425** (`modConj_deviceVecF_bottom_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L575)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)) = (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta))
$$

*Proof.* By [Lem 424](#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [Def 436](#d-qiqth-deviceopc), [Lem 467](#d-qiqth-modconj-devicevecf-bottom). $\square$

<small>Referenced in [Lem 426](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed"></a>
**Lemma 426** (`modConj_deviceVecF_bottom_eq_fixed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L584)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta = \zeta \to \forall (t : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)) = (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)
$$

*Proof.* By [Lem 425](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq). $\square$

<small>Referenced in [Lem 427](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k"></a>
**Lemma 427** (`modConj_deviceVecF_bottom_eq_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L594)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (t : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)) = (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)
$$

*Proof.* By [Lem 426](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k). $\square$

<small>Referenced in [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k"></a>
**Lemma 428** (`gFunction_bottom_eq_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L605)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (w : H) (t : \mathbb{R}), ((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)))\,w = \langle {(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)},{w}\rangle
$$

*Proof.* By [Lem 427](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k), [Def 766](#d-qiqth-standardsubspacemodular-modconj), [Lem 777](#d-qiqth-standardsubspacemodular-modconjbilin-apply). $\square$

<small>Referenced in [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match"></a>
**Lemma 429** (`gFunction_bottom_real_of_kms_match`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L686)</small>

$$
0 < n \to \forall (\eta : H) \{\zeta : H\}, (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (t : \mathbb{R}), (\mathrm{Continuous}\,\lambda s \mapsto (V\,s)\,\eta) \to (\forall (s : \mathbb{R}), \|(V\,s)\,\eta\| \le \|\eta\|) \to \forall \{f : \mathbb{C} \to \mathbb{C}\} \{M : \mathbb{R}\}, \mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to (\forall z\in \href{#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, \|f\,z\| \le M) \to (\forall (s : \mathbb{R}), f\,s = \href{#d-qiqth-standardsubspacemodular-corrc}{\mathrm{corrC}}\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))\,V\,n\,\eta\,s) \to (f\,(t - i / 2)).\mathrm{im} = 0 \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,(t - i / 2))).\mathrm{im} = 0
$$

*Proof.* By [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k). $\square$

<small>Referenced in [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms"></a>
**Lemma 430** (`gFunction_bottom_real_of_faithful_kms`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L734)</small>

$$
0 < n \to \forall (\eta : H) \{\zeta : H\}, (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (t : \mathbb{R}), (\mathrm{Continuous}\,\lambda s \mapsto (V\,s)\,\eta) \to (\forall (s : \mathbb{R}), \|(V\,s)\,\eta\| \le \|\eta\|) \to (\forall (s u : \mathbb{R}), (V\,s)\,((V\,u)\,\eta) = (V\,(s + u))\,\eta) \to \forall \{f : \mathbb{C} \to \mathbb{C}\} \{M : \mathbb{R}\}, \mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to (\forall z\in \href{#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, \|f\,z\| \le M) \to (\forall (s : \mathbb{R}), f\,s = \langle {(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)},{(V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)}\rangle) \to (f\,(t - i / 2)).\mathrm{im} = 0 \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,(t - i / 2))).\mathrm{im} = 0
$$

*Proof.* By [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 861](#d-qiqth-standardsubspacemodular-gausssmearc-ofreal), [Def 865](#d-qiqth-standardsubspacemodular-corrc). $\square$

<small>Referenced in [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd).</small>

<a id="sec-qiqth-modularrelativeentropy"></a>
## QIQTH.ModularRelativeEntropy

<a id="d-qiqth-rvdspecmeasure"></a>
**Definition 431** (`rvdSpecMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L44)</small>

A definition, built from [Def 692](#d-qiqth-standardsubspacemodular-rvdrc) — see source for the body.

<small>Referenced in [Lem 422](#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 445](#d-qiqth-borelfc-apply-norm-sq), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset), [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset), [Lem 449](#d-qiqth-rvdspecmeasure-endpoints), [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 458](#d-qiqth-hasderivat-devicevecf), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq), [Lem 472](#d-qiqth-devicevecf-continuouson).</small>

<a id="d-qiqth-devspecreal"></a>
**Definition 432** (`devSpecReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L434)</small>

A definition, built from [Def 692](#d-qiqth-standardsubspacemodular-rvdrc) — see source for the body.

<small>Referenced in [Lem 433](#d-qiqth-devspecreal-measurable), [Lem 434](#d-qiqth-devspecreal-norm-le), [Def 435](#d-qiqth-deviceopreal), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-devspecreal-measurable"></a>
**Lemma 433** (`devSpecReal_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L439)</small>

$$
\mathrm{Measurable}\,(\href{#d-qiqth-devspecreal}{\chi_{\mathrm{dev}}}\,S\,t)
$$

*Proof.* By [Def 875](#d-qiqth-standardsubspacemodular-devchar), [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar). $\square$

<small>Referenced in [Def 435](#d-qiqth-deviceopreal), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-devspecreal-norm-le"></a>
**Lemma 434** (`devSpecReal_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L442)</small>

$$
\|\href{#d-qiqth-devspecreal}{\chi_{\mathrm{dev}}}\,S\,t\,\omega\| \le \sqrt 2
$$

*Proof.* By [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 882](#d-qiqth-standardsubspacemodular-devchar-norm-le-icc). $\square$

<small>Referenced in [Def 435](#d-qiqth-deviceopreal), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-deviceopreal"></a>
**Definition 435** (`deviceOpReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L447)</small>

A definition — see source for the body.

<small>Referenced in [Lem 439](#d-qiqth-deviceopc-ofreal), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 460](#d-qiqth-devicevecf-real-eq).</small>

<a id="d-qiqth-deviceopc"></a>
**Definition 436** (`deviceOpC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L453)</small>

A definition — see source for the body.

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Lem 424](#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [Lem 425](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq), [Def 437](#d-qiqth-devicevecf), [Lem 438](#d-qiqth-devicevecf-eq-of-mem), [Lem 439](#d-qiqth-deviceopc-ofreal), [Lem 440](#d-qiqth-deviceopc-norm-le), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 455](#d-qiqth-deviceopc-sub), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 458](#d-qiqth-hasderivat-devicevecf), [Lem 460](#d-qiqth-devicevecf-real-eq), [Lem 466](#d-qiqth-devicevecf-bottom-eq), [Lem 467](#d-qiqth-modconj-devicevecf-bottom), [Lem 468](#d-qiqth-devicevecf-norm-le), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 472](#d-qiqth-devicevecf-continuouson).</small>

<a id="d-qiqth-devicevecf"></a>
**Definition 437** (`deviceVecF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L465)</small>

A definition — see source for the body.

<small>Referenced in [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 413](#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 425](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq), [Lem 426](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed), [Lem 427](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k), [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 438](#d-qiqth-devicevecf-eq-of-mem), [Lem 458](#d-qiqth-hasderivat-devicevecf), [Lem 459](#d-qiqth-differentiableon-devicevecf), [Lem 460](#d-qiqth-devicevecf-real-eq), [Lem 461](#d-qiqth-differentiableon-gfunction), [Lem 462](#d-qiqth-devicevecf-zero), [Lem 463](#d-qiqth-gfunction-zero), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 466](#d-qiqth-devicevecf-bottom-eq), [Lem 467](#d-qiqth-modconj-devicevecf-bottom), [Lem 468](#d-qiqth-devicevecf-norm-le), [Lem 469](#d-qiqth-gfunction-norm-le), [Lem 472](#d-qiqth-devicevecf-continuouson), [Lem 473](#d-qiqth-diffcontoncl-gfunction).</small>

<a id="d-qiqth-devicevecf-eq-of-mem"></a>
**Lemma 438** (`deviceVecF_eq_of_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L475)</small>

$$
\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z = (\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1})\,\zeta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 458](#d-qiqth-hasderivat-devicevecf), [Lem 460](#d-qiqth-devicevecf-real-eq), [Lem 466](#d-qiqth-devicevecf-bottom-eq), [Lem 472](#d-qiqth-devicevecf-continuouson).</small>

<a id="d-qiqth-deviceopc-ofreal"></a>
**Lemma 439** (`deviceOpC_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L480)</small>

$$
\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,t\,\cdots \,\cdots = \href{#d-qiqth-deviceopreal}{\mathrm{dev}}\,S\,t
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 460](#d-qiqth-devicevecf-real-eq).</small>

<a id="d-qiqth-deviceopc-norm-le"></a>
**Lemma 440** (`deviceOpC_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L485)</small>

$$
\|\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1}\| \le 2 \cdot \sqrt 2
$$

*Proof.* By [Def 556](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [Lem 567](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Def 875](#d-qiqth-standardsubspacemodular-devchar). $\square$

<small>Referenced in [Lem 468](#d-qiqth-devicevecf-norm-le).</small>

<a id="d-qiqth-deviceopreal-zero"></a>
**Lemma 441** (`deviceOpReal_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L495)</small>

$$
\href{#d-qiqth-deviceopreal}{\mathrm{dev}}\,S\,0 = \href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S
$$

*Proof.* By [Def 432](#d-qiqth-devspecreal), [Lem 433](#d-qiqth-devspecreal-measurable), [Lem 434](#d-qiqth-devspecreal-norm-le), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Def 749](#d-qiqth-standardsubspacemodular-speccoord), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Lem 806](#d-qiqth-standardsubspacemodular-cfccont-star), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Def 875](#d-qiqth-standardsubspacemodular-devchar), [Lem 879](#d-qiqth-standardsubspacemodular-devchar-zero). $\square$

<small>Referenced in [Lem 443](#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-cfccont-sqrttwosub-eq"></a>
**Lemma 442** (`cfcCont_sqrtTwoSub_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L541)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,\{\mathrm{toFun} :=\lambda \omega \mapsto \sqrt (2 - \omega) , \mathrm{continuous\_toFun} :=\cdots \} = \href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S
$$

*Proof.* By [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Def 749](#d-qiqth-standardsubspacemodular-speccoord), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 802](#d-qiqth-standardsubspacemodular-cfccont-one), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Lem 804](#d-qiqth-standardsubspacemodular-cfccont-add), [Lem 805](#d-qiqth-standardsubspacemodular-cfccont-smul), [Lem 806](#d-qiqth-standardsubspacemodular-cfccont-star), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord). $\square$

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq).</small>

<a id="d-qiqth-deviceopreal-eq"></a>
**Lemma 443** (`deviceOpReal_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L605)</small>

$$
\href{#d-qiqth-deviceopreal}{\mathrm{dev}}\,S\,t = \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t \cdot \href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S
$$

*Proof.* By [Def 432](#d-qiqth-devspecreal), [Lem 433](#d-qiqth-devspecreal-measurable), [Lem 434](#d-qiqth-devspecreal-norm-le), [Lem 441](#d-qiqth-deviceopreal-zero), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 727](#d-qiqth-standardsubspacemodular-modchar), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 877](#d-qiqth-standardsubspacemodular-devchar-ofreal), [Lem 879](#d-qiqth-standardsubspacemodular-devchar-zero). $\square$

<small>Referenced in [Lem 460](#d-qiqth-devicevecf-real-eq).</small>

<a id="d-qiqth-borelfc-inner-self"></a>
**Lemma 444** (`borelFC_inner_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L632)</small>

$$
\langle {(\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\mathrm{hg}\,\mathrm{hC0}\,\mathrm{hC})\,\zeta},{(\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\mathrm{hg}\,\mathrm{hC0}\,\mathrm{hC})\,\zeta}\rangle = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S))), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,\omega) \cdot g\,\omega \partial \href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 667](#d-qiqth-spectraltheorem-inner-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Lem 735](#d-qiqth-standardsubspacemodular-borelfc-adjoint). $\square$

<small>Referenced in [Lem 445](#d-qiqth-borelfc-apply-norm-sq).</small>

<a id="d-qiqth-borelfc-apply-norm-sq"></a>
**Lemma 445** (`borelFC_apply_norm_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L656)</small>

$$
{\|(\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\mathrm{hg}\,\mathrm{hC0}\,\mathrm{hC})\,\zeta\|}^{2} = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S))), {\|g\,\omega\|}^{2} \partial \href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta
$$

*Proof.* By [Lem 444](#d-qiqth-borelfc-inner-self). $\square$

<small>Referenced in [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 470](#d-qiqth-deviceopc-diff-normsq).</small>

<a id="d-qiqth-rvdspec-borelfc-diag"></a>
**Lemma 446** (`rvdSpec_borelFC_diag`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L677)</small>

$$
\langle {x},{(\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC})\,x}\rangle = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S))), f\,\omega \partial \href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 667](#d-qiqth-spectraltheorem-inner-borelfc). $\square$

<small>Referenced in [Lem 422](#d-qiqth-standardsubspacemodular-borelfc-congr-ae).</small>

<a id="d-qiqth-rvdspecmeasure-zero-levelset"></a>
**Lemma 447** (`rvdSpecMeasure_zero_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L690)</small>

$$
(\href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x)\,\{\omega|\omega = 0\} = 0
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 840](#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset). $\square$

<small>Referenced in [Lem 449](#d-qiqth-rvdspecmeasure-endpoints).</small>

<a id="d-qiqth-rvdspecmeasure-two-levelset"></a>
**Lemma 448** (`rvdSpecMeasure_two_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L701)</small>

$$
(\href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x)\,\{\omega|\omega = 2\} = 0
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset). $\square$

<small>Referenced in [Lem 449](#d-qiqth-rvdspecmeasure-endpoints).</small>

<a id="d-qiqth-rvdspecmeasure-endpoints"></a>
**Lemma 449** (`rvdSpecMeasure_endpoints`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L712)</small>

$$
(\href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x)\,\{\omega|\omega = 0 \vee \omega = 2\} = 0
$$

*Proof.* By [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset), [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset). $\square$

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq).</small>

<a id="d-qiqth-deviceopc-bottomedge-eq"></a>
**Lemma 450** (`deviceOpC_bottomEdge_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L724)</small>

$$
\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(t - i / 2)\,\cdots \,\cdots = \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t \cdot \href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 727](#d-qiqth-standardsubspacemodular-modchar), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 871](#d-qiqth-standardsubspacemodular-modcharc-ofreal), [Lem 872](#d-qiqth-standardsubspacemodular-modcharc-add), [Def 875](#d-qiqth-standardsubspacemodular-devchar), [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar), [Lem 882](#d-qiqth-standardsubspacemodular-devchar-norm-le-icc). $\square$

<small>Referenced in [Lem 466](#d-qiqth-devicevecf-bottom-eq).</small>

<a id="d-qiqth-devcharderiv-norm-le-slab"></a>
**Lemma 451** (`devCharDeriv_norm_le_slab`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L778)</small>

$$
0 < \beta_{0} \to \beta_{1} < 1/2 \to \forall \{w : \mathbb{C}\}, w \in \mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-\beta_{1})\,(-\beta_{0}) \to \|i \cdot (\log\,((2 - \omega) / \omega)) \cdot \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,w\,\omega\| \le \sqrt 2 \cdot (2 / \beta_{0} + \log\,2) + \sqrt 2 \cdot (2 / (1/2 - \beta_{1}) + \log\,2)
$$

*Proof.* By [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 885](#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le). $\square$

<small>Referenced in [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Def 456](#d-qiqth-devicederivopc), [Lem 457](#d-qiqth-deviceopc-slope-normsq).</small>

<a id="d-qiqth-devchar-slope-norm-le"></a>
**Lemma 452** (`devChar_slope_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L807)</small>

$$
0 < \beta_{0} \to \beta_{1} < 1/2 \to \forall \{z z_{0} : \mathbb{C}\}, z \in \mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-\beta_{1})\,(-\beta_{0}) \to z_{0} \in \mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-\beta_{1})\,(-\beta_{0}) \to \|\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\| \le (\sqrt 2 \cdot (2 / \beta_{0} + \log\,2) + \sqrt 2 \cdot (2 / (1/2 - \beta_{1}) + \log\,2)) \cdot \|z - z_{0}\|
$$

*Proof.* By [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 885](#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le), [Lem 887](#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc). $\square$

<small>Referenced in [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq).</small>

<a id="d-qiqth-tendsto-devchar-slope"></a>
**Lemma 453** (`tendsto_devChar_slope`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L857)</small>

$$
\mathrm{Tendsto}\,(\lambda z \mapsto (\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega) / (z - z_{0}))\,(\mathcal{N}\,z_{0}\,\{z_{0}\}^{c})\,(\mathrm{nhds}\,(i \cdot (\log\,((2 - \omega) / \omega)) \cdot \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega))
$$

*Proof.* By [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 887](#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc). $\square$

<small>Referenced in [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq).</small>

<a id="d-qiqth-tendsto-integral-devchar-remainder-sq"></a>
**Lemma 454** (`tendsto_integral_devChar_remainder_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L874)</small>

$$
0 < \beta_{0} \to \beta_{1} < 1/2 \to \forall \{z_{0} : \mathbb{C}\}, z_{0} \in \mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-\beta_{1})\,(-\beta_{0}) \to \mathrm{Tendsto}\,(\lambda z \mapsto \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S))), {\|(\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega) / (z - z_{0}) - i \cdot (\log\,((2 - \omega) / \omega)) \cdot \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\|}^{2} \partial \href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta)\,(\mathcal{N}\,z_{0}\,\{z_{0}\}^{c})\,(\mathrm{nhds}\,0)
$$

*Proof.* By [Lem 451](#d-qiqth-devcharderiv-norm-le-slab), [Lem 452](#d-qiqth-devchar-slope-norm-le), [Lem 453](#d-qiqth-tendsto-devchar-slope), [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 521](#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar). $\square$

<small>Referenced in [Lem 458](#d-qiqth-hasderivat-devicevecf).</small>

<a id="d-qiqth-deviceopc-sub"></a>
**Lemma 455** (`deviceOpC_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L950)</small>

$$
\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1} - \href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z_{0}\,\mathrm{hz02}\,\mathrm{hz01} = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\cdots \,\cdots \,\cdots
$$

*Proof.* By [Lem 799](#d-qiqth-standardsubspacemodular-borelfc-sub). $\square$

<small>Referenced in [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 470](#d-qiqth-deviceopc-diff-normsq).</small>

<a id="d-qiqth-devicederivopc"></a>
**Definition 456** (`deviceDerivOpC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L972)</small>

A definition — see source for the body.

<small>Referenced in [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 458](#d-qiqth-hasderivat-devicevecf), [Lem 459](#d-qiqth-differentiableon-devicevecf).</small>

<a id="d-qiqth-deviceopc-slope-normsq"></a>
**Lemma 457** (`deviceOpC_slope_normSq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L991)</small>

$$
{\|{(z - z_{0})}^{-1} \cdot ((\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1})\,\zeta - (\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z_{0}\,\mathrm{hz02}\,\mathrm{hz01})\,\zeta) - (\href{#d-qiqth-devicederivopc}{\mathrm{dev}{}'}\,S\,z_{0}\,h\beta_{0}\,h\beta_{1}\,\mathrm{hz}_{0})\,\zeta\|}^{2} = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S))), {\|(\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega) / (z - z_{0}) - i \cdot (\log\,((2 - \omega) / \omega)) \cdot \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\|}^{2} \partial \href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta
$$

*Proof.* By [Lem 445](#d-qiqth-borelfc-apply-norm-sq), [Lem 451](#d-qiqth-devcharderiv-norm-le-slab), [Lem 455](#d-qiqth-deviceopc-sub), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 797](#d-qiqth-standardsubspacemodular-borelfc-smul), [Lem 799](#d-qiqth-standardsubspacemodular-borelfc-sub), [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar), [Lem 882](#d-qiqth-standardsubspacemodular-devchar-norm-le-icc). $\square$

<small>Referenced in [Lem 458](#d-qiqth-hasderivat-devicevecf).</small>

<a id="d-qiqth-hasderivat-devicevecf"></a>
**Lemma 458** (`hasDerivAt_deviceVecF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1015)</small>

$$
({\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta})'({z_{0}})={(\href{#d-qiqth-devicederivopc}{\mathrm{dev}{}'}\,S\,z_{0}\,h\beta_{0}\,h\beta_{1}\,\mathrm{hz}_{0})\,\zeta}
$$

*Proof.* By [Def 431](#d-qiqth-rvdspecmeasure), [Def 436](#d-qiqth-deviceopc), [Lem 438](#d-qiqth-devicevecf-eq-of-mem), [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 875](#d-qiqth-standardsubspacemodular-devchar). $\square$

<small>Referenced in [Lem 459](#d-qiqth-differentiableon-devicevecf).</small>

<a id="d-qiqth-differentiableon-devicevecf"></a>
**Lemma 459** (`differentiableOn_deviceVecF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1048)</small>

$$
\mathrm{DifferentiableOn}\,\mathbb{C}\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta)\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-(1/2))\,0)
$$

*Proof.* By [Def 456](#d-qiqth-devicederivopc), [Lem 458](#d-qiqth-hasderivat-devicevecf). $\square$

<small>Referenced in [Lem 461](#d-qiqth-differentiableon-gfunction).</small>

<a id="d-qiqth-devicevecf-real-eq"></a>
**Lemma 460** (`deviceVecF_real_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1062)</small>

$$
\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,t = (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)
$$

*Proof.* By [Def 435](#d-qiqth-deviceopreal), [Def 436](#d-qiqth-deviceopc), [Lem 438](#d-qiqth-devicevecf-eq-of-mem), [Lem 439](#d-qiqth-deviceopc-ofreal), [Lem 443](#d-qiqth-deviceopreal-eq). $\square$

<small>Referenced in [Lem 462](#d-qiqth-devicevecf-zero), [Lem 464](#d-qiqth-gfunction-real-eq).</small>

<a id="d-qiqth-differentiableon-gfunction"></a>
**Lemma 461** (`differentiableOn_gFunction`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1072)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{DifferentiableOn}\,\mathbb{C}\,(\lambda z \mapsto ((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z))\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-(1/2))\,0)
$$

*Proof.* By [Lem 459](#d-qiqth-differentiableon-devicevecf), [Lem 864](#d-qiqth-standardsubspacemodular-differentiable-gausssmearc). $\square$

<small>Referenced in [Lem 473](#d-qiqth-diffcontoncl-gfunction).</small>

<a id="d-qiqth-devicevecf-zero"></a>
**Lemma 462** (`deviceVecF_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1089)</small>

$$
\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,0 = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta
$$

*Proof.* By [Lem 460](#d-qiqth-devicevecf-real-eq), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero). $\square$

<small>Referenced in [Lem 463](#d-qiqth-gfunction-zero).</small>

<a id="d-qiqth-gfunction-zero"></a>
**Lemma 463** (`gFunction_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1098)</small>

$$
((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,0))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,0) = \langle {(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)},{\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta}\rangle
$$

*Proof.* By [Lem 462](#d-qiqth-devicevecf-zero), [Lem 777](#d-qiqth-standardsubspacemodular-modconjbilin-apply), [Lem 866](#d-qiqth-standardsubspacemodular-gausssmearc-zero). $\square$

<small>Referenced in [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire).</small>

<a id="d-qiqth-gfunction-real-eq"></a>
**Lemma 464** (`gFunction_real_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1107)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to \forall (t : \mathbb{R}), ((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,t))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,t) = \langle {(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))},{(V\,t)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)}\rangle
$$

*Proof.* By [Lem 460](#d-qiqth-devicevecf-real-eq), [Lem 777](#d-qiqth-standardsubspacemodular-modconjbilin-apply), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary), [Lem 861](#d-qiqth-standardsubspacemodular-gausssmearc-ofreal). $\square$

<small>Referenced in [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 465](#d-qiqth-gfunction-top-edge-real).</small>

<a id="d-qiqth-gfunction-top-edge-real"></a>
**Lemma 465** (`gFunction_top_edge_real`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1120)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (t : \mathbb{R}), (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,t)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,t)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta) \to (((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,t))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,t)).\mathrm{im} = 0
$$

*Proof.* By [Lem 464](#d-qiqth-gfunction-real-eq), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 745](#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [Def 766](#d-qiqth-standardsubspacemodular-modconj), [Lem 791](#d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k), [Lem 794](#d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik), [Lem 845](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary). $\square$

<small>Referenced in [Lem 413](#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all).</small>

<a id="d-qiqth-devicevecf-bottom-eq"></a>
**Lemma 466** (`deviceVecF_bottom_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1138)</small>

$$
\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2) = (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots )\,\zeta)
$$

*Proof.* By [Lem 438](#d-qiqth-devicevecf-eq-of-mem), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq). $\square$

<small>Referenced in [Lem 467](#d-qiqth-modconj-devicevecf-bottom).</small>

<a id="d-qiqth-modconj-devicevecf-bottom"></a>
**Lemma 467** (`modConj_deviceVecF_bottom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1156)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)) = (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots )\,\zeta))
$$

*Proof.* By [Lem 466](#d-qiqth-devicevecf-bottom-eq), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary). $\square$

<small>Referenced in [Lem 425](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq).</small>

<a id="d-qiqth-devicevecf-norm-le"></a>
**Lemma 468** (`deviceVecF_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1170)</small>

$$
\|\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z\| \le 2 \cdot \sqrt 2 \cdot \|\zeta\|
$$

*Proof.* By [Def 436](#d-qiqth-deviceopc), [Lem 440](#d-qiqth-deviceopc-norm-le). $\square$

<small>Referenced in [Lem 469](#d-qiqth-gfunction-norm-le).</small>

<a id="d-qiqth-gfunction-norm-le"></a>
**Lemma 469** (`gFunction_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1182)</small>

$$
\|((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)\| \le 2 \cdot \sqrt 2 \cdot \|\zeta\| \cdot \|\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z\|
$$

*Proof.* By [Lem 468](#d-qiqth-devicevecf-norm-le), [Def 766](#d-qiqth-standardsubspacemodular-modconj), [Lem 768](#d-qiqth-standardsubspacemodular-modconj-norm), [Lem 777](#d-qiqth-standardsubspacemodular-modconjbilin-apply). $\square$

<small>Referenced in [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const).</small>

<a id="d-qiqth-deviceopc-diff-normsq"></a>
**Lemma 470** (`deviceOpC_diff_normSq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1198)</small>

$$
{\|(\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z\,\mathrm{hz2}\,\mathrm{hz1})\,\zeta - (\href{#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,z_{0}\,\mathrm{hz02}\,\mathrm{hz01})\,\zeta\|}^{2} = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S))), {\|\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\|}^{2} \partial \href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta
$$

*Proof.* By [Lem 445](#d-qiqth-borelfc-apply-norm-sq), [Lem 455](#d-qiqth-deviceopc-sub), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar), [Lem 882](#d-qiqth-standardsubspacemodular-devchar-norm-le-icc). $\square$

<small>Referenced in [Lem 472](#d-qiqth-devicevecf-continuouson).</small>

<a id="d-qiqth-tendsto-integral-devchar-diff-sq"></a>
**Lemma 471** (`tendsto_integral_devChar_diff_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1213)</small>

$$
z_{0}.\mathrm{im} \le 0 \to -(1/2) \le z_{0}.\mathrm{im} \to \mathrm{Tendsto}\,(\lambda z \mapsto \int (\omega : (\mathrm{sp}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S))), {\|\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,\omega - \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z_{0}\,\omega\|}^{2} \partial \href{#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,\zeta)\,(\mathcal{N}\,z_{0}\,(\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-(1/2))\,0))\,(\mathrm{nhds}\,0)
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 521](#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar), [Lem 882](#d-qiqth-standardsubspacemodular-devchar-norm-le-icc), [Lem 887](#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc). $\square$

<small>Referenced in [Lem 472](#d-qiqth-devicevecf-continuouson).</small>

<a id="d-qiqth-devicevecf-continuouson"></a>
**Lemma 472** (`deviceVecF_continuousOn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1257)</small>

$$
\mathrm{ContinuousOn}\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta)\,(\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-(1/2))\,0)
$$

*Proof.* By [Def 431](#d-qiqth-rvdspecmeasure), [Def 436](#d-qiqth-deviceopc), [Lem 438](#d-qiqth-devicevecf-eq-of-mem), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 875](#d-qiqth-standardsubspacemodular-devchar). $\square$

<small>Referenced in [Lem 473](#d-qiqth-diffcontoncl-gfunction).</small>

<a id="d-qiqth-diffcontoncl-gfunction"></a>
**Lemma 473** (`diffContOnCl_gFunction`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ModularRelativeEntropy.lean#L1279)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{DiffContOnCl}\,\mathbb{C}\,(\lambda z \mapsto ((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z))\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-(1/2))\,0)
$$

*Proof.* By [Lem 461](#d-qiqth-differentiableon-gfunction), [Lem 472](#d-qiqth-devicevecf-continuouson), [Lem 864](#d-qiqth-standardsubspacemodular-differentiable-gausssmearc). $\square$

<small>Referenced in [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const).</small>

<a id="sec-qiqth-qiqtgrcomplete"></a>
## QIQTH.QiqtGrComplete

<a id="d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete"></a>
**Theorem 474** (`qiqt_gr_freefield_complete`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrComplete.lean#L27)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\varphi : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}) (m \eta \hbar a : \mathbb{R}), \hbar \ne 0 \to 0 < \hbar \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to ({\varphi})\in C^{\infty} \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}), \href{#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}) (p : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \iota \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}) (r : \iota), 0 \le p\,x\,v\,t\,r) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}), \sum_{r} p\,x\,v\,t\,r = 1) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), p\,x\,v\,0 = \lambda x \mapsto {((\#\,\iota))}^{-1}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \eta \cdot A({x},{v},{0}) = \log\,(\#\,\iota)) \to \forall (W : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to W\,x\,v\,x = v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda t \mapsto \href{#d-qiqth-branchledger-shannon}{S({p\,x\,v\,t})}})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda t \mapsto \href{#d-qiqth-branchledger-shannon}{S({p\,x\,v\,t})} + \href{#d-qiqth-relentpositivity-kl}{D_{\mathrm{KL}}({p\,x\,v\,t}\,\|\,{p\,x\,v\,0})}})'({0})={2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={-\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \href{#d-qiqth-branchledger-shannon}{S({p\,x\,v\,t})} \le \eta \cdot A({x},{v},{t})) \to \forall (\mathrm{mw} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot \href{#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo). $\square$

<a id="sec-qiqth-qiqtgrfreefield"></a>
## QIQTH.QiqtGrFreeField

<a id="d-qiqth-wedgekmstogr-bl-kgstress-null"></a>
**Lemma 475** (`BL_kgStress_null`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrFreeField.lean#L30)</small>

$$
\href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v}) = {(\sum_{a} v\,a \cdot \href{#d-qiqth-curvature-pd}{\partial_{{a}}({\varphi})({x})})}^{2}
$$

*Proof.* By [Def 407](#d-qiqth-curvature-kglagr). $\square$

<small>Referenced in [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy).</small>

<a id="d-qiqth-wedgekmstogr-freefield-kd-conclusion"></a>
**Lemma 476** (`freeField_kd_conclusion`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrFreeField.lean#L52)</small>

$$
(\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(f\,x\,v)\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({f\,x\,v})'({\theta})={f^{\prime}\,x\,v\,\theta}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(f^{\prime}\,x\,v)\,\mathrm{volume}) \to \forall (B : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|f^{\prime}\,x\,v\,\theta\| \le B\,x\,v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to 2 \cdot \pi / \hbar \cdot \href{#d-qiqth-einsteineos-bl}{({T\,x})({v},{v})} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x\,v\,\theta) \cdot f^{\prime}\,x\,v\,\theta)).\mathrm{im}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,(f\,x\,v)\,\cdots },{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,(\mathrm{mw}\,x\,v)\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,(f\,x\,v)\,\cdots )}\rangle})'({0})={i \cdot (\dot{K}({x},{v}))}) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot \href{#d-qiqth-einsteineos-bl}{({T\,x})({v},{v})}
$$

*Proof.* By [Thm 225](#d-qiqth-fock-freefield-component-hflux). $\square$

<small>Referenced in [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-wedgekmstogr-qiqt-gr-freefield"></a>
**Theorem 477** (`qiqt_gr_freefield`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrFreeField.lean#L85)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\varphi : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}) (m \eta \hbar a : \mathbb{R}), \hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to ({\varphi})\in C^{\infty} \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}), \href{#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (\mathrm{Sf} \mathrm{KE} A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} \mathrm{kd} \mathrm{ad} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{KE}\,x\,v})'({0})={\dot{K}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0) \to \forall (\mathrm{mw} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}) (\mathrm{hmw} : \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v) (\mathrm{ff} \mathrm{ff}^{\prime} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{C}) (\mathrm{hf2} : \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}) \to \forall (\mathrm{Bd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to 2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,(\mathrm{ff}\,x\,v)\,\cdots },{(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,(\mathrm{mw}\,x\,v)\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,(\mathrm{ff}\,x\,v)\,\cdots )}\rangle})'({0})={i \cdot (\dot{K}({x},{v}))}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto \href{#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot \href{#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Def 11](#d-qiqth-curvature-pdiffat), [Def 32](#d-qiqth-curvature-scalarcurv), [Lem 406](#d-qiqth-curvature-hreg-kg), [Def 407](#d-qiqth-curvature-kglagr), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete). $\square$

<small>Referenced in [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized).</small>

<a id="d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized"></a>
**Theorem 478** (`qiqt_gr_freefield_localized`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrFreeField.lean#L156)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\varphi : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}) (m \eta \hbar a : \mathbb{R}), \hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to ({\varphi})\in C^{\infty} \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}), \href{#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (\mathrm{Sf} \mathrm{KE} A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} \mathrm{ad} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0) \to \forall (\mathrm{mw} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v) \to \forall (\mathrm{ff} \mathrm{ff}^{\prime} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{C}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}) \to \forall (\mathrm{Bd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to 2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto \href{#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot \href{#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield). $\square$

<small>Referenced in [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized).</small>

<a id="d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized"></a>
**Theorem 479** (`qiqt_gr_freefield_localized'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrFreeField.lean#L207)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\varphi : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}) (m \eta \hbar a : \mathbb{R}), \hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to ({\varphi})\in C^{\infty} \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}), \href{#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (\mathrm{Sf} \mathrm{KE} A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} \mathrm{ad} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0) \to \forall (\mathrm{mw} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v) \to \forall (\mathrm{ff} \mathrm{ff}^{\prime} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{C}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}) \to \forall (\mathrm{Bd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to 2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}) \to \forall (W : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to W\,x\,v\,x = v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x})) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot \href{#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Lem 3](#d-qiqth-curvature-christoffel-contdiff), [Def 31](#d-qiqth-curvature-ricci), [Thm 478](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri). $\square$

<small>Referenced in [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy).</small>

<a id="d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy"></a>
**Theorem 480** (`qiqt_gr_freefield_nullEnergy`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrFreeField.lean#L268)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\varphi : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}) (m \eta \hbar a : \mathbb{R}), \hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to ({\varphi})\in C^{\infty} \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}), \href{#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (\mathrm{Sf} \mathrm{KE} A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} \mathrm{ad} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0) \to \forall (\mathrm{mw} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v) \to \forall (\mathrm{ff} \mathrm{ff}^{\prime} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{C}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}) \to \forall (\mathrm{Bd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to 2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \href{#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({x})})}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}) \to \forall (W : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to W\,x\,v\,x = v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x})) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot \href{#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Lem 475](#d-qiqth-wedgekmstogr-bl-kgstress-null), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized). $\square$

<small>Referenced in [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom).</small>

<a id="d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom"></a>
**Theorem 481** (`qiqt_gr_freefield_geom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrFreeField.lean#L333)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\varphi : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}) (m \eta \hbar a : \mathbb{R}), \hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to ({\varphi})\in C^{\infty} \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}), \href{#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (\mathrm{Sf} \mathrm{KE} A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}) (W : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to W\,x\,v\,x = v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{KE}\,x\,v})'({0})={2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={-\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0) \to \forall (\mathrm{mw} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v) \to \forall (\mathrm{ff} \mathrm{ff}^{\prime} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{C}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}) \to \forall (\mathrm{Bd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to 2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \href{#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({x})})}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot \href{#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy). $\square$

<small>Referenced in [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo).</small>

<a id="sec-qiqth-qiqtgrthermo"></a>
## QIQTH.QiqtGrThermo

<a id="d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo"></a>
**Theorem 482** (`qiqt_gr_freefield_thermo`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtGrThermo.lean#L36)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (\varphi : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}) (m \eta \hbar a : \mathbb{R}), \hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to ({\varphi})\in C^{\infty} \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}), \href{#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}) (p : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \iota \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}) (r : \iota), 0 \le p\,x\,v\,t\,r) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (t : \mathbb{R}), \sum_{r} p\,x\,v\,t\,r = 1) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), p\,x\,v\,0 = \lambda x \mapsto {((\#\,\iota))}^{-1}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \eta \cdot A({x},{v},{0}) = \log\,(\#\,\iota)) \to \forall (W : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to W\,x\,v\,x = v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto W\,x\,v\,y\,\mu})\in C^{\infty}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} W\,x\,v\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({y})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{\nu}}{}^{{\mu}}({x})} = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda t \mapsto \href{#d-qiqth-branchledger-shannon}{S({p\,x\,v\,t})}})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda t \mapsto \href{#d-qiqth-branchledger-shannon}{S({p\,x\,v\,t})} + \href{#d-qiqth-relentpositivity-kl}{D_{\mathrm{KL}}({p\,x\,v\,t}\,\|\,{p\,x\,v\,0})}})'({0})={2 \cdot \pi / \hbar \cdot ({\href{#d-qiqth-curvature-kgstress}{T({x})}})({v},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={-\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \href{#d-qiqth-branchledger-shannon}{S({p\,x\,v\,t})} \le \eta \cdot A({x},{v},{t})) \to \forall (\mathrm{mw} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), 0 < \mathrm{mw}\,x\,v) \to \forall (\mathrm{ff} \mathrm{ff}^{\prime} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{C}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{MemLp}\,(\mathrm{ff}\,x\,v)\,2\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{Integrable}\,(\mathrm{ff}\,x\,v)\,\mathrm{volume}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), ({\mathrm{ff}\,x\,v})'({\theta})={\mathrm{ff}^{\prime}\,x\,v\,\theta}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \mathrm{AEStronglyMeasurable}\,(\mathrm{ff}^{\prime}\,x\,v)\,\mathrm{volume}) \to \forall (\mathrm{Bd} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}) (\theta : \mathbb{R}), \|\mathrm{ff}^{\prime}\,x\,v\,\theta\| \le \mathrm{Bd}\,x\,v) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to 2 \cdot \pi / \hbar \cdot \cdots = \cdots .\mathrm{im}) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot \href{#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Lem 7](#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom). $\square$

<small>Referenced in [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete).</small>

<a id="sec-qiqth-qiqttogr"></a>
## QIQTH.QiqtToGR

<a id="d-qiqth-qiqttogr-hfocus-of-raychaudhuri"></a>
**Lemma 483** (`hFocus_of_raychaudhuri`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtToGR.lean#L32)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,4), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,4), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu : \mathrm{Fin}\,4), \sum_{\nu} V\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}), \sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})} = 0 \to \forall (\mathrm{ad} : \mathbb{R}), \mathrm{ad} = -\sum_{\nu} V\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x}) \to \mathrm{ad} = ({\lambda i j \mapsto \href{#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({V\,x},{V\,x})
$$

*Proof.* By [Lem 497](#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium). $\square$

<small>Referenced in [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized).</small>

<a id="d-qiqth-qiqttogr-bl-pernull-of-modular"></a>
**Lemma 484** (`bl_pernull_of_modular`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtToGR.lean#L55)</small>

$$
\hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to k^{\prime} = \eta \cdot a^{\prime} \to k^{\prime} = 2 \cdot \pi / \hbar \cdot \href{#d-qiqth-einsteineos-bl}{({T})({v},{v})} \to a^{\prime} = \href{#d-qiqth-einsteineos-bl}{({\mathrm{Ric}})({v},{v})} \to \href{#d-qiqth-einsteineos-bl}{({\lambda i j \mapsto a \cdot T\,i\,j - \mathrm{Ric}\,i\,j})({v},{v})} = 0
$$

*Proof.* By [Lem 8](#d-qiqth-curvature-bl-smul-sub). $\square$

<small>Referenced in [Lem 485](#d-qiqth-qiqttogr-bl-pernull-of-qiqt).</small>

<a id="d-qiqth-qiqttogr-bl-pernull-of-qiqt"></a>
**Lemma 485** (`bl_pernull_of_qiqt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtToGR.lean#L75)</small>

$$
\hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to ({S})'({0})={s^{\prime}} \to ({\mathrm{KE}})'({0})={k^{\prime}} \to ({A})'({0})={a^{\prime}} \to (\text{for }t\text{ near }0,\; S\,t \le \eta \cdot A\,t) \to S\,0 = \eta \cdot A\,0 \to (\forall (t : \mathbb{R}), 0 \le \mathrm{KE}\,t - S\,t) \to \mathrm{KE}\,0 - S\,0 = 0 \to k^{\prime} = 2 \cdot \pi / \hbar \cdot \href{#d-qiqth-einsteineos-bl}{({T})({v},{v})} \to a^{\prime} = \href{#d-qiqth-einsteineos-bl}{({\mathrm{Ric}})({v},{v})} \to \href{#d-qiqth-einsteineos-bl}{({\lambda i j \mapsto a \cdot T\,i\,j - \mathrm{Ric}\,i\,j})({v},{v})} = 0
$$

*Proof.* By [Lem 67](#d-qiqth-differentialarealaw-differential-area-law-of-relentropy), [Lem 484](#d-qiqth-qiqttogr-bl-pernull-of-modular). $\square$

<small>Referenced in [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr).</small>

<a id="d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr"></a>
**Theorem 486** (`qiqt_bekenstein_gives_gr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/QiqtToGR.lean#L102)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (T : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}) (\eta \hbar a : \mathbb{R}), \hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), T_{{a^{\prime}}{b}}({x}) = T_{{b}{a^{\prime}}}({x})) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (S \mathrm{KE} A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} \mathrm{kd} \mathrm{ad} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({S\,x\,v})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{KE}\,x\,v})'({0})={\dot{K}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; S({x},{v},{t}) \le \eta \cdot A({x},{v},{t})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to S({x},{v},{0}) = \eta \cdot A({x},{v},{0})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - S({x},{v},{t})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{KE}({x},{v},{0}) - S({x},{v},{0}) = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot \href{#d-qiqth-einsteineos-bl}{({T\,x})({v},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto \href{#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})) \to (\forall (f : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}), (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot T_{{a^{\prime}}{b}}({y}) = \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\rho : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \wedge \mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot \href{#d-qiqth-curvature-scalarcurv}{R({y})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\nu : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T_{{\mu}{\nu}}({x}) = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Lem 3](#d-qiqth-curvature-christoffel-contdiff), [Def 27](#d-qiqth-curvature-christoffel), [Lem 84](#d-qiqth-curvature-jacobson-einstein-equation-of-state), [Lem 485](#d-qiqth-qiqttogr-bl-pernull-of-qiqt), [Lem 504](#d-qiqth-curvature-ricci-symm). $\square$

<small>Referenced in [Thm 900](#d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete).</small>

<a id="sec-qiqth-raychaudhuri"></a>
## QIQTH.Raychaudhuri

<a id="d-qiqth-curvature-covderiv2vec"></a>
**Definition 487** (`covDeriv2Vec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L28)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Lem 489](#d-qiqth-curvature-ricci-identity), [Lem 490](#d-qiqth-curvature-ricci-identity-contracted), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing), [Lem 495](#d-qiqth-curvature-geodesic-leibniz), [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic).</small>

<a id="d-qiqth-curvature-pd-covderivvec"></a>
**Lemma 488** (`pd_covDerivVec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L36)</small>

$$
(\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mu \nu \rho : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \partial_{{\mu}}({\lambda y \mapsto \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\rho}}({y})}})({x}) = \partial_{{\mu}}({\lambda y \mapsto \href{#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda z \mapsto V\,z\,\rho})({y})}})({x}) + \sum_{\sigma} (\partial_{{\mu}}({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\sigma}}({y})}})({x}) \cdot V\,x\,\sigma + \href{#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\sigma}}({x})} \cdot \href{#d-qiqth-curvature-pd}{\partial_{{\mu}}({\lambda y \mapsto V\,y\,\sigma})({x})})
$$

*Proof.* By [Def 11](#d-qiqth-curvature-pdiffat), [Lem 12](#d-qiqth-curvature-pd-add), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Lem 26](#d-qiqth-curvature-pdiffat-pd). $\square$

<small>Referenced in [Lem 489](#d-qiqth-curvature-ricci-identity).</small>

<a id="d-qiqth-curvature-ricci-identity"></a>
**Lemma 489** (`ricci_identity`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L57)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mu \nu \rho : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\mu\,\nu\,\rho\,x - \href{#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\nu\,\mu\,\rho\,x = \sum_{\sigma} \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,x \cdot V\,x\,\sigma
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Lem 25](#d-qiqth-curvature-pd-comm), [Lem 28](#d-qiqth-curvature-christoffel-symm), [Def 34](#d-qiqth-curvature-covderivvec), [Lem 488](#d-qiqth-curvature-pd-covderivvec). $\square$

<small>Referenced in [Lem 490](#d-qiqth-curvature-ricci-identity-contracted).</small>

<a id="d-qiqth-curvature-ricci-identity-contracted"></a>
**Lemma 490** (`ricci_identity_contracted`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L93)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\mu} (\href{#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\mu\,\nu\,\mu\,x - \href{#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\nu\,\mu\,\mu\,x) = \sum_{\sigma} \href{#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} \cdot V\,x\,\sigma
$$

*Proof.* By [Def 29](#d-qiqth-curvature-riemann), [Lem 489](#d-qiqth-curvature-ricci-identity). $\square$

<small>Referenced in [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing).</small>

<a id="d-qiqth-curvature-expansion"></a>
**Definition 491** (`expansion`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L110)</small>

A definition, built from [Def 9](#d-qiqth-curvature-point) — see source for the body.

<small>Referenced in [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Thm 479](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [Thm 480](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [Thm 481](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace), [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing), [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic), [Lem 497](#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium).</small>

<a id="d-qiqth-curvature-covderiv2vec-trace"></a>
**Lemma 492** (`covDeriv2Vec_trace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L115)</small>

$$
(\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\mu} \href{#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\nu\,\mu\,\mu\,x = \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x})
$$

*Proof.* By [Def 11](#d-qiqth-curvature-pdiffat), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 19](#d-qiqth-curvature-pdiffat-add), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 26](#d-qiqth-curvature-pdiffat-pd), [Def 34](#d-qiqth-curvature-covderivvec). $\square$

<small>Referenced in [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing).</small>

<a id="d-qiqth-curvature-raychaudhuri-focusing"></a>
**Lemma 493** (`raychaudhuri_focusing`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L134)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\nu} V\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x}) = \sum_{\nu} \sum_{\mu} V\,x\,\nu \cdot \href{#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\mu\,\nu\,\mu\,x - \sum_{\nu} \sum_{\sigma} \href{#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} \cdot V\,x\,\sigma \cdot V\,x\,\nu
$$

*Proof.* By [Lem 490](#d-qiqth-curvature-ricci-identity-contracted), [Lem 492](#d-qiqth-curvature-covderiv2vec-trace). $\square$

<small>Referenced in [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic).</small>

<a id="d-qiqth-curvature-geodesic-divergence-leibniz"></a>
**Lemma 494** (`geodesic_divergence_leibniz`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L162)</small>

$$
(\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (\mu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\nu} (\href{#d-qiqth-curvature-pd}{\partial_{{\mu}}({\lambda y \mapsto V\,y\,\nu})({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})} + V\,x\,\nu \cdot \partial_{{\mu}}({\lambda y \mapsto \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})}})({x})) = 0
$$

*Proof.* By [Def 11](#d-qiqth-curvature-pdiffat), [Lem 15](#d-qiqth-curvature-pd-const), [Lem 16](#d-qiqth-curvature-pdiffat-of-contdiff), [Lem 17](#d-qiqth-curvature-pdiffat-mul), [Lem 19](#d-qiqth-curvature-pdiffat-add), [Lem 20](#d-qiqth-curvature-pdiffat-sum), [Lem 21](#d-qiqth-curvature-pd-sum), [Lem 22](#d-qiqth-curvature-pd-mul), [Lem 26](#d-qiqth-curvature-pdiffat-pd). $\square$

<small>Referenced in [Lem 495](#d-qiqth-curvature-geodesic-leibniz).</small>

<a id="d-qiqth-curvature-geodesic-leibniz"></a>
**Lemma 495** (`geodesic_leibniz`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L186)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\nu} \sum_{\mu} V\,x\,\nu \cdot \href{#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\mu\,\nu\,\mu\,x = -\sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})}
$$

*Proof.* By [Def 10](#d-qiqth-curvature-pd), [Lem 494](#d-qiqth-curvature-geodesic-divergence-leibniz). $\square$

<small>Referenced in [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic).</small>

<a id="d-qiqth-curvature-raychaudhuri-geodesic"></a>
**Lemma 496** (`raychaudhuri_geodesic`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L239)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\nu} V\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x}) = -\sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})} - \sum_{\nu} \sum_{\sigma} \href{#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} \cdot V\,x\,\sigma \cdot V\,x\,\nu
$$

*Proof.* By [Def 487](#d-qiqth-curvature-covderiv2vec), [Lem 493](#d-qiqth-curvature-raychaudhuri-focusing), [Lem 495](#d-qiqth-curvature-geodesic-leibniz). $\square$

<small>Referenced in [Lem 497](#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium).</small>

<a id="d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium"></a>
**Lemma 497** (`raychaudhuri_focusing_at_equilibrium`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L259)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\mu} \sum_{\nu} \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})} = 0 \to \sum_{\nu} V\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{#d-qiqth-curvature-expansion}{\theta({y})}})({x}) = -\sum_{\nu} \sum_{\sigma} \href{#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} \cdot V\,x\,\sigma \cdot V\,x\,\nu
$$

*Proof.* By [Lem 496](#d-qiqth-curvature-raychaudhuri-geodesic). $\square$

<small>Referenced in [Lem 483](#d-qiqth-qiqttogr-hfocus-of-raychaudhuri).</small>

<a id="sec-qiqth-recordcontract"></a>
## QIQTH.RecordContract

<a id="d-qiqth-recordcontract-shannon-eq-sum-negmullog"></a>
**Lemma 498** (`shannon_eq_sum_negMulLog`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RecordContract.lean#L122)</small>

$$
\href{#d-qiqth-branchledger-shannon}{S({p})} = \sum_{i s} (p\,i).\mathrm{nml}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 499](#d-qiqth-recordcontract-shannon-le-log-card), [Lem 500](#d-qiqth-recordcontract-shannon-uniform-eq-log-card).</small>

<a id="d-qiqth-recordcontract-shannon-le-log-card"></a>
**Lemma 499** (`shannon_le_log_card`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RecordContract.lean#L128)</small>

$$
(\forall (i : \iota), 0 \le p\,i) \to \sum_{i} p\,i = 1 \to \href{#d-qiqth-branchledger-shannon}{S({p})} \le \log\,(\#\,\iota)
$$

*Proof.* By [Lem 498](#d-qiqth-recordcontract-shannon-eq-sum-negmullog). $\square$

<small>Referenced in [Lem 7](#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model).</small>

<a id="d-qiqth-recordcontract-shannon-uniform-eq-log-card"></a>
**Lemma 500** (`shannon_uniform_eq_log_card`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RecordContract.lean#L165)</small>

$$
(\href{#d-qiqth-branchledger-shannon}{S({\lambda x \mapsto {((\#\,\iota))}^{-1}})}) = \log\,(\#\,\iota)
$$

*Proof.* By [Lem 498](#d-qiqth-recordcontract-shannon-eq-sum-negmullog). $\square$

<small>Referenced in [Lem 7](#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model).</small>

<a id="sec-qiqth-relentpositivity"></a>
## QIQTH.RelEntPositivity

<a id="d-qiqth-relentpositivity-kl"></a>
**Definition 501** (`KL`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RelEntPositivity.lean#L65)</small>

A definition — see source for the body.

<small>Referenced in [Lem 7](#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model), [Thm 474](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [Thm 482](#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [Lem 502](#d-qiqth-relentpositivity-kl-classical-nonneg).</small>

<a id="d-qiqth-relentpositivity-kl-classical-nonneg"></a>
**Lemma 502** (`KL_classical_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RelEntPositivity.lean#L78)</small>

$$
(\forall i\in s, 0 \le p\,i) \to (\forall i\in s, 0 < q\,i) \to \sum_{i s} p\,i = 1 \to \sum_{i s} q\,i = 1 \to 0 \le \href{#d-qiqth-relentpositivity-kl}{D_{\mathrm{KL}}({p}\,\|\,{q})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 7](#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model).</small>

<a id="sec-qiqth-riccisymm"></a>
## QIQTH.RicciSymm

<a id="d-qiqth-curvature-lowered-riemann-pair-symm"></a>
**Lemma 503** (`lowered_riemann_pair_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RicciSymm.lean#L21)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (a b c d : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\alpha} g_{{a}{\alpha}}({x}) \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,b\,c\,d\,x = \sum_{\alpha} g_{{c}{\alpha}}({x}) \cdot \href{#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,d\,a\,b\,x
$$

*Proof.* By [Lem 30](#d-qiqth-curvature-riemann-antisymm), [Lem 40](#d-qiqth-curvature-riemann-first-bianchi), [Lem 57](#d-qiqth-curvature-lowered-riemann-antisymm). $\square$

<small>Referenced in [Lem 504](#d-qiqth-curvature-ricci-symm).</small>

<a id="d-qiqth-curvature-ricci-symm"></a>
**Lemma 504** (`ricci_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RicciSymm.lean#L84)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\sigma \nu : \mathrm{Fin}\,n) (x : \href{#d-qiqth-curvature-point}{M^{{n}}}), \href{#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} = \href{#d-qiqth-curvature-ricci}{R_{{\nu}{\sigma}}({x})}
$$

*Proof.* By [Def 29](#d-qiqth-curvature-riemann), [Lem 503](#d-qiqth-curvature-lowered-riemann-pair-symm). $\square$

<small>Referenced in [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr).</small>

<a id="sec-qiqth-spectral-pvm"></a>
## QIQTH.Spectral.PVM

<a id="d-qiqth-spectral-projectionvaluedmeasure"></a>
**Lemma 505** (`ProjectionValuedMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L325)</small>

$$
(\Omega : Type\mathrm{u\_3}) \to (H : Type\mathrm{u\_4}) \to [\mathrm{MeasurableSpace}\,\Omega] \to [\mathrm{inst} : \mathrm{NormedAddCommGroup}\,H] \to [\mathrm{InnerProductSpace}\,\mathbb{C}\,H] \to [\mathrm{CompleteSpace}\,H] \to Type(max\mathrm{u\_3} \mathrm{u\_4})
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 506](#d-qiqth-spectral-projectionvaluedmeasure-mk), [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Lem 508](#d-qiqth-spectral-projectionvaluedmeasure-issa), [Lem 509](#d-qiqth-spectral-projectionvaluedmeasure-isidem), [Lem 510](#d-qiqth-spectral-projectionvaluedmeasure-e-univ), [Lem 511](#d-qiqth-spectral-projectionvaluedmeasure-e-inter), [Lem 512](#d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq), [Lem 513](#d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem), [Lem 514](#d-qiqth-spectral-projectionvaluedmeasure-inner-e-self), [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [Lem 517](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ), [Def 518](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple), [Lem 519](#d-qiqth-spectral-projectionvaluedmeasure-inner-integralsimple-left), [Lem 520](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal), [Lem 521](#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [Lem 522](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul), [Lem 523](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure), [Lem 524](#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable), [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 526](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul), [Lem 527](#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram), [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 529](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [Lem 530](#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul), [Lem 531](#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg), [Lem 532](#d-qiqth-spectral-projectionvaluedmeasure-diagint-conj), [Lem 533](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left), [Lem 534](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-right), [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [Lem 536](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right), [Lem 537](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left), [Lem 538](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure), [Lem 539](#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd), [Lem 540](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg), [Lem 541](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left), [Lem 542](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left), [Lem 543](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left), [Lem 544](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left), [Lem 545](#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [Lem 546](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right), [Lem 547](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-right), [Lem 548](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add), [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le), [Def 550](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Def 551](#d-qiqth-spectral-projectionvaluedmeasure-intborel), [Lem 552](#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel), [Lem 553](#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le), [Lem 554](#d-qiqth-spectral-projectionvaluedmeasure-diagint-const), [Lem 555](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const), [Def 556](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 558](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [Lem 559](#d-qiqth-spectral-projectionvaluedmeasure-diagint-add), [Lem 560](#d-qiqth-spectral-projectionvaluedmeasure-diagint-finsetsum), [Lem 561](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f), [Lem 562](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum), [Lem 563](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add), [Lem 564](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul-f), [Lem 565](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f), [Lem 566](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [Lem 567](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le), [Lem 568](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [Lem 570](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator), [Lem 571](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner), [Lem 572](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator), [Lem 573](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 575](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq), [Lem 576](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq), [Lem 577](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [Lem 579](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul), [Lem 581](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated), [Lem 582](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated), [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-mk"></a>
**Lemma 506** (`mk`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L332)</small>

$$
\{\Omega : Type\mathrm{u\_3}\} \to \{H : Type\mathrm{u\_4}\} \to [\mathrm{inst} : \mathrm{MeasurableSpace}\,\Omega] \to [\mathrm{inst\_1} : \mathrm{NormedAddCommGroup}\,H] \to [\mathrm{inst\_2} : \mathrm{InnerProductSpace}\,\mathbb{C}\,H] \to [\mathrm{inst\_3} : \mathrm{CompleteSpace}\,H] \to (E : \mathrm{Set}\,\Omega \to H \to L[\mathbb{C}] H) \to (\forall s : \mathrm{Set}\,\Omega, \mathrm{MeasurableSet}\,s \to \mathrm{IsSelfAdjoint}\,(E\,s)) \to (\forall s : \mathrm{Set}\,\Omega, \mathrm{MeasurableSet}\,s \to \mathrm{IsIdempotentElem}\,(E\,s)) \to E\,\emptyset = 0 \to E = 1 \to (\forall s t : \mathrm{Set}\,\Omega, \mathrm{MeasurableSet}\,s \to \mathrm{MeasurableSet}\,t \to E\,(s \cap t) = E\,s \cdot E\,t) \to (\forall \{A : \mathbb{N} \to \mathrm{Set}\,\Omega\}, (\forall (n : \mathbb{N}), \mathrm{MeasurableSet}\,(A\,n)) \to (\mathrm{Pairwise}\,\lambda m n \mapsto \mathrm{Disjoint}\,(A\,m)\,(A\,n)) \to \forall (x : H), \mathrm{HasSum}\,(\lambda n \mapsto (E\,(A\,n))\,x)\,((E\,(\bigcup n, A\,n))\,x)) \to \href{#d-qiqth-spectral-projectionvaluedmeasure}{\mathrm{ProjectionValuedMeasure}}\,\Omega\,H
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-e"></a>
**Definition 507** (`E`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L334)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset), [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset), [Lem 508](#d-qiqth-spectral-projectionvaluedmeasure-issa), [Lem 509](#d-qiqth-spectral-projectionvaluedmeasure-isidem), [Lem 510](#d-qiqth-spectral-projectionvaluedmeasure-e-univ), [Lem 511](#d-qiqth-spectral-projectionvaluedmeasure-e-inter), [Lem 512](#d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq), [Lem 513](#d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem), [Lem 514](#d-qiqth-spectral-projectionvaluedmeasure-inner-e-self), [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [Lem 517](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ), [Def 518](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple), [Lem 519](#d-qiqth-spectral-projectionvaluedmeasure-inner-integralsimple-left), [Lem 520](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal), [Lem 522](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul), [Lem 523](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure), [Lem 538](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure), [Lem 571](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner), [Lem 572](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator), [Lem 573](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 575](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq), [Lem 576](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq), [Lem 671](#d-qiqth-spectraltheorem-borelfc-indicator), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset), [Lem 840](#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-issa"></a>
**Lemma 508** (`isSA`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L335)</small>

$$
\mathrm{MeasurableSet}\,s \to \mathrm{IsSelfAdjoint}\,(\mathrm{self}.E\,s)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 512](#d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-isidem"></a>
**Lemma 509** (`isIdem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L336)</small>

$$
\mathrm{MeasurableSet}\,s \to \mathrm{IsIdempotentElem}\,(\mathrm{self}.E\,s)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 513](#d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-e-univ"></a>
**Lemma 510** (`E_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L338)</small>

$$
\mathrm{self}.E = 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 517](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-e-inter"></a>
**Lemma 511** (`E_inter`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L339)</small>

$$
\mathrm{MeasurableSet}\,s \to \mathrm{MeasurableSet}\,t \to \mathrm{self}.E\,(s \cap t) = \mathrm{self}.E\,s \cdot \mathrm{self}.E\,t
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 575](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq"></a>
**Lemma 512** (`adjoint_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L349)</small>

$$
\mathrm{MeasurableSet}\,s \to {{P.E\,s}}^{\dagger} = P.E\,s
$$

*Proof.* By [Lem 508](#d-qiqth-spectral-projectionvaluedmeasure-issa). $\square$

<small>Referenced in [Lem 514](#d-qiqth-spectral-projectionvaluedmeasure-inner-e-self).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem"></a>
**Lemma 513** (`E_apply_idem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L353)</small>

$$
\mathrm{MeasurableSet}\,s \to \forall (x : H), (P.E\,s)\,((P.E\,s)\,x) = (P.E\,s)\,x
$$

*Proof.* By [Lem 509](#d-qiqth-spectral-projectionvaluedmeasure-isidem). $\square$

<small>Referenced in [Lem 514](#d-qiqth-spectral-projectionvaluedmeasure-inner-e-self).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-inner-e-self"></a>
**Lemma 514** (`inner_E_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L357)</small>

$$
\mathrm{MeasurableSet}\,s \to \forall (x : H), \langle {x},{(P.E\,s)\,x}\rangle = {\|(P.E\,s)\,x\|}^{2}
$$

*Proof.* By [Lem 512](#d-qiqth-spectral-projectionvaluedmeasure-adjoint-eq), [Lem 513](#d-qiqth-spectral-projectionvaluedmeasure-e-apply-idem). $\square$

<small>Referenced in [Lem 571](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure"></a>
**Definition 515** (`scalarMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L371)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Def 431](#d-qiqth-rvdspecmeasure), [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset), [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset), [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [Lem 517](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ), [Lem 520](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal), [Lem 521](#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [Lem 522](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul), [Lem 523](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure), [Lem 524](#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable), [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 526](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul), [Lem 527](#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram), [Lem 532](#d-qiqth-spectral-projectionvaluedmeasure-diagint-conj), [Lem 538](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure), [Lem 539](#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd), [Lem 545](#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [Lem 554](#d-qiqth-spectral-projectionvaluedmeasure-diagint-const), [Lem 559](#d-qiqth-spectral-projectionvaluedmeasure-diagint-add), [Lem 560](#d-qiqth-spectral-projectionvaluedmeasure-diagint-finsetsum), [Lem 562](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum), [Lem 564](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul-f), [Lem 570](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator), [Lem 571](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner), [Lem 581](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply"></a>
**Lemma 516** (`scalarMeasure_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L399)</small>

$$
\mathrm{MeasurableSet}\,s \to (P.\mu\,x)\,s = {{{\|(P.E\,s)\,x\|}^{2}}}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset), [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset), [Lem 517](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ), [Lem 520](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal), [Lem 522](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul), [Lem 523](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure), [Lem 538](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ"></a>
**Lemma 517** (`scalarMeasure_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L404)</small>

$$
(P.\mu\,x) = {{{\|x\|}^{2}}}
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Lem 510](#d-qiqth-spectral-projectionvaluedmeasure-e-univ), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Referenced in [Lem 521](#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [Lem 545](#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [Lem 554](#d-qiqth-spectral-projectionvaluedmeasure-diagint-const).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-integralsimple"></a>
**Definition 518** (`integralSimple`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L413)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Lem 519](#d-qiqth-spectral-projectionvaluedmeasure-inner-integralsimple-left), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 575](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq), [Lem 576](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq), [Lem 577](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [Lem 579](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-inner-integralsimple-left"></a>
**Lemma 519** (`inner_integralSimple_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L419)</small>

$$
\langle {x},{(P.\textstyle\int\,t\,c\,\mathrm{sets})\,y}\rangle = \sum_{i t} c\,i \cdot \langle {x},{(P.E\,(\mathrm{sets}\,i))\,y}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal"></a>
**Lemma 520** (`scalarMeasure_toReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L477)</small>

$$
\mathrm{MeasurableSet}\,s \to ((P.\mu\,x)\,s).\mathrm{toReal} = {\|(P.E\,s)\,x\|}^{2}
$$

*Proof.* By [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Referenced in [Lem 571](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure"></a>
**Lemma 521** (`instIsFiniteMeasure_scalarMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L532)</small>

$$
\mathrm{IsFiniteMeasure}\,(P.\mu\,x)
$$

*Proof.* By [Lem 517](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ). $\square$

<small>Referenced in [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq), [Lem 524](#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable), [Lem 545](#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [Lem 581](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul"></a>
**Lemma 522** (`scalarMeasure_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L554)</small>

$$
P.\mu\,(c \cdot x) = {{{\|c\|}^{2}}} \cdot P.\mu\,x
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Referenced in [Lem 526](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure"></a>
**Lemma 523** (`scalarMeasure_parallelogram_measure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L563)</small>

$$
P.\mu\,(x + y) + P.\mu\,(x - y) = 2 \cdot P.\mu\,x + 2 \cdot P.\mu\,y
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Referenced in [Lem 527](#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable"></a>
**Lemma 524** (`integrable_boundedMeasurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L581)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x : H), \mathrm{Integrable}\,f\,(P.\mu\,x)
$$

*Proof.* By [Lem 521](#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure). $\square$

<small>Referenced in [Lem 527](#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram), [Lem 539](#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd), [Lem 545](#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [Lem 559](#d-qiqth-spectral-projectionvaluedmeasure-diagint-add), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint"></a>
**Definition 525** (`diagInt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L589)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 526](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul), [Lem 527](#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram), [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 529](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [Lem 530](#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul), [Lem 531](#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg), [Lem 532](#d-qiqth-spectral-projectionvaluedmeasure-diagint-conj), [Lem 533](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left), [Lem 534](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-right), [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [Lem 537](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left), [Lem 539](#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd), [Lem 540](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg), [Lem 541](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left), [Lem 545](#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le), [Lem 547](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-right), [Lem 548](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add), [Lem 554](#d-qiqth-spectral-projectionvaluedmeasure-diagint-const), [Lem 555](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const), [Lem 559](#d-qiqth-spectral-projectionvaluedmeasure-diagint-add), [Lem 560](#d-qiqth-spectral-projectionvaluedmeasure-diagint-finsetsum), [Lem 561](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f), [Lem 562](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum), [Lem 564](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul-f), [Lem 565](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f), [Lem 570](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator), [Lem 571](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner), [Lem 572](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator), [Lem 581](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated), [Lem 582](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-smul"></a>
**Lemma 526** (`diagInt_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L595)</small>

$$
P.\textstyle\int\,f\,(c \cdot x) = ({\|c\|}^{2}) \cdot P.\textstyle\int\,f\,x
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 522](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-smul). $\square$

<small>Referenced in [Lem 530](#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram"></a>
**Lemma 527** (`diagInt_parallelogram`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L602)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H), P.\textstyle\int\,f\,(x + y) + P.\textstyle\int\,f\,(x - y) = 2 \cdot P.\textstyle\int\,f\,x + 2 \cdot P.\textstyle\int\,f\,y
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 523](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-parallelogram-measure), [Lem 524](#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable). $\square$

<small>Referenced in [Lem 529](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag"></a>
**Definition 528** (`bilinDiag`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L618)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 529](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [Lem 536](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right), [Lem 537](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left), [Lem 540](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg), [Lem 541](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left), [Lem 542](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left), [Lem 543](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left), [Lem 544](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left), [Lem 546](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right), [Lem 547](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-right), [Lem 548](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add), [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le), [Def 550](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 552](#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel), [Lem 553](#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le), [Lem 555](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 558](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [Lem 561](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f), [Lem 562](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum), [Lem 563](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add), [Lem 565](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f), [Lem 566](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [Lem 568](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [Lem 572](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator), [Lem 573](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 582](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated), [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul), [Lem 667](#d-qiqth-spectraltheorem-inner-borelfc), [Lem 735](#d-qiqth-standardsubspacemodular-borelfc-adjoint), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left"></a>
**Lemma 529** (`bilinDiag_add_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L627)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y z : H), P.\mathrm{bd}\,f\,(x + y)\,z = P.\mathrm{bd}\,f\,x\,z + P.\mathrm{bd}\,f\,y\,z
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 527](#d-qiqth-spectral-projectionvaluedmeasure-diagint-parallelogram). $\square$

<small>Referenced in [Lem 536](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right), [Lem 542](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left), [Lem 544](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left), [Def 550](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul"></a>
**Lemma 530** (`diagInt_unit_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L646)</small>

$$
\|c\| = 1 \to \forall (x : H), P.\textstyle\int\,f\,(c \cdot x) = P.\textstyle\int\,f\,x
$$

*Proof.* By [Lem 526](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul). $\square$

<small>Referenced in [Lem 531](#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg), [Lem 533](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left), [Lem 534](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-right).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-neg"></a>
**Lemma 531** (`diagInt_neg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L652)</small>

$$
P.\textstyle\int\,f\,(-x) = P.\textstyle\int\,f\,x
$$

*Proof.* By [Lem 530](#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul). $\square$

<small>Referenced in [Lem 533](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left), [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [Lem 537](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left), [Lem 541](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-conj"></a>
**Lemma 532** (`diagInt_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L656)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(P.\textstyle\int\,f\,x) = P.\textstyle\int\,(\lambda \omega \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\omega))\,x
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure). $\square$

<small>Referenced in [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left"></a>
**Lemma 533** (`diagInt_I_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L662)</small>

$$
P.\textstyle\int\,f\,(i \cdot y + x) = P.\textstyle\int\,f\,(i \cdot x - y)
$$

*Proof.* By [Lem 530](#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul), [Lem 531](#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg). $\square$

<small>Referenced in [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-i-right"></a>
**Lemma 534** (`diagInt_I_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L673)</small>

$$
P.\textstyle\int\,f\,(i \cdot y - x) = P.\textstyle\int\,f\,(i \cdot x + y)
$$

*Proof.* By [Lem 530](#d-qiqth-spectral-projectionvaluedmeasure-diagint-unit-smul). $\square$

<small>Referenced in [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm"></a>
**Lemma 535** (`bilinDiag_conj_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L683)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(P.\mathrm{bd}\,f\,y\,x) = P.\mathrm{bd}\,(\lambda \omega \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\omega))\,x\,y
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 531](#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg), [Lem 532](#d-qiqth-spectral-projectionvaluedmeasure-diagint-conj), [Lem 533](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-left), [Lem 534](#d-qiqth-spectral-projectionvaluedmeasure-diagint-i-right). $\square$

<small>Referenced in [Lem 536](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right), [Lem 546](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right), [Lem 735](#d-qiqth-standardsubspacemodular-borelfc-adjoint).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-right"></a>
**Lemma 536** (`bilinDiag_add_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L696)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y z : H), P.\mathrm{bd}\,f\,x\,(y + z) = P.\mathrm{bd}\,f\,x\,y + P.\mathrm{bd}\,f\,x\,z
$$

*Proof.* By [Lem 529](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm). $\square$

<small>Referenced in [Def 550](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left"></a>
**Lemma 537** (`bilinDiag_I_smul_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L712)</small>

$$
P.\mathrm{bd}\,f\,(i \cdot x)\,y = (\mathrm{starRingEnd}\,\mathbb{C})\,i \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 531](#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg). $\square$

<small>Referenced in [Lem 544](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure"></a>
**Lemma 538** (`scalarMeasure_odd_measure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L723)</small>

$$
0 \le r \to P.\mu\,(r \cdot x + y) + {{r}} \cdot P.\mu\,(x - y) = P.\mu\,(r \cdot x - y) + {{r}} \cdot P.\mu\,(x + y)
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply). $\square$

<small>Referenced in [Lem 539](#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-odd"></a>
**Lemma 539** (`diagInt_odd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L750)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H) \{r : \mathbb{R}\}, 0 \le r \to P.\textstyle\int\,f\,(r \cdot x + y) + r \cdot P.\textstyle\int\,f\,(x - y) = P.\textstyle\int\,f\,(r \cdot x - y) + r \cdot P.\textstyle\int\,f\,(x + y)
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 524](#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable), [Lem 538](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-odd-measure). $\square$

<small>Referenced in [Lem 540](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg"></a>
**Lemma 540** (`bilinDiag_real_smul_left_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L768)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H) \{r : \mathbb{R}\}, 0 \le r \to P.\mathrm{bd}\,f\,(r \cdot x)\,y = r \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 539](#d-qiqth-spectral-projectionvaluedmeasure-diagint-odd). $\square$

<small>Referenced in [Lem 543](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left"></a>
**Lemma 541** (`bilinDiag_zero_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L779)</small>

$$
P.\mathrm{bd}\,f\,0\,y = 0
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 531](#d-qiqth-spectral-projectionvaluedmeasure-diagint-neg). $\square$

<small>Referenced in [Lem 542](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left), [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left"></a>
**Lemma 542** (`bilinDiag_neg_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L784)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H), P.\mathrm{bd}\,f\,(-x)\,y = -P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Lem 529](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [Lem 541](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left). $\square$

<small>Referenced in [Lem 543](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left"></a>
**Lemma 543** (`bilinDiag_real_smul_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L792)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H) (r : \mathbb{R}), P.\mathrm{bd}\,f\,(r \cdot x)\,y = r \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Lem 540](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left-nonneg), [Lem 542](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-neg-left). $\square$

<small>Referenced in [Lem 544](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left"></a>
**Lemma 544** (`bilinDiag_smul_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L804)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (c : \mathbb{C}) (x y : H), P.\mathrm{bd}\,f\,(c \cdot x)\,y = (\mathrm{starRingEnd}\,\mathbb{C})\,c \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Lem 529](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-left), [Lem 537](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-i-smul-left), [Lem 543](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-real-smul-left). $\square$

<small>Referenced in [Lem 546](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right), [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le"></a>
**Lemma 545** (`diagInt_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L819)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, 0 \le C \to (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x : H), \|P.\textstyle\int\,f\,x\| \le C \cdot {\|x\|}^{2}
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 517](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ), [Lem 521](#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure), [Lem 524](#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable). $\square$

<small>Referenced in [Lem 548](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right"></a>
**Lemma 546** (`bilinDiag_smul_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L833)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (c : \mathbb{C}) (x y : H), P.\mathrm{bd}\,f\,x\,(c \cdot y) = c \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [Lem 544](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left). $\square$

<small>Referenced in [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-right"></a>
**Lemma 547** (`bilinDiag_zero_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L846)</small>

$$
P.\mathrm{bd}\,f\,x\,0 = 0
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint). $\square$

<small>Referenced in [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add"></a>
**Lemma 548** (`bilinDiag_norm_le_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L850)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, 0 \le C \to (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H), \|P.\mathrm{bd}\,f\,x\,y\| \le C \cdot ({\|x\|}^{2} + {\|y\|}^{2})
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 545](#d-qiqth-spectral-projectionvaluedmeasure-diagint-norm-le). $\square$

<small>Referenced in [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le"></a>
**Lemma 549** (`bilinDiag_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L882)</small>

$$
\mathrm{Measurable}\,f \to \forall \{C : \mathbb{R}\}, 0 \le C \to (\forall (\omega : \Omega), \|f\,\omega\| \le C) \to \forall (x y : H), \|P.\mathrm{bd}\,f\,x\,y\| \le 2 \cdot C \cdot \|x\| \cdot \|y\|
$$

*Proof.* By [Lem 541](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-left), [Lem 544](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-left), [Lem 546](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-right), [Lem 547](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-zero-right), [Lem 548](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le-add). $\square$

<small>Referenced in [Def 551](#d-qiqth-spectral-projectionvaluedmeasure-intborel), [Lem 552](#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel), [Lem 553](#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag"></a>
**Definition 550** (`bilinDiagₗ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L917)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Def 551](#d-qiqth-spectral-projectionvaluedmeasure-intborel), [Lem 552](#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-intborel"></a>
**Definition 551** (`intBorel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L927)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Lem 552](#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel), [Lem 553](#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le), [Def 556](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 567](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-inner-intborel"></a>
**Lemma 552** (`inner_intBorel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L936)</small>

$$
\langle {(P.\textstyle\int\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC})\,x},{y}\rangle = P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le), [Def 550](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag). $\square$

<small>Referenced in [Lem 553](#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le"></a>
**Lemma 553** (`intBorel_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L945)</small>

$$
\|P.\textstyle\int\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}\| \le 2 \cdot C
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 549](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-norm-le), [Lem 552](#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel). $\square$

<small>Referenced in [Lem 567](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-const"></a>
**Lemma 554** (`diagInt_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L964)</small>

$$
P.\textstyle\int\,(\lambda x \mapsto c)\,z = {\|z\|}^{2} \cdot c
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 517](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-univ). $\square$

<small>Referenced in [Lem 555](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const"></a>
**Lemma 555** (`bilinDiag_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L971)</small>

$$
P.\mathrm{bd}\,(\lambda x \mapsto c)\,x\,y = c \cdot \langle {x},{y}\rangle
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 554](#d-qiqth-spectral-projectionvaluedmeasure-diagint-const). $\square$

<small>Referenced in [Lem 558](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc"></a>
**Definition 556** (`boundedFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1000)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Lem 440](#d-qiqth-deviceopc-norm-le), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 558](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [Lem 563](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add), [Lem 566](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [Lem 567](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le), [Lem 568](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [Lem 573](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 577](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [Lem 579](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul), [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 669](#d-qiqth-spectraltheorem-borelfc-one), [Lem 801](#d-qiqth-standardsubspacemodular-cfccont-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc"></a>
**Lemma 557** (`inner_boundedFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1007)</small>

$$
\langle {x},{(P.\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC})\,y}\rangle = P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Def 551](#d-qiqth-spectral-projectionvaluedmeasure-intborel), [Lem 552](#d-qiqth-spectral-projectionvaluedmeasure-inner-intborel). $\square$

<small>Referenced in [Lem 558](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [Lem 563](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add), [Lem 566](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [Lem 568](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [Lem 573](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul), [Lem 667](#d-qiqth-spectraltheorem-inner-borelfc).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const"></a>
**Lemma 558** (`boundedFC_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1013)</small>

$$
P.\Phi\,\cdots \,\cdots \,\cdots = c \cdot 1
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 555](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-const), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc). $\square$

<small>Referenced in [Lem 669](#d-qiqth-spectraltheorem-borelfc-one), [Lem 670](#d-qiqth-spectraltheorem-borelfc-const).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-add"></a>
**Lemma 559** (`diagInt_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1023)</small>

$$
\mathrm{Measurable}\,f \to \mathrm{Measurable}\,g \to \forall \{\mathrm{Cf} \mathrm{Cg} : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le \mathrm{Cf}) \to (\forall (\omega : \Omega), \|g\,\omega\| \le \mathrm{Cg}) \to \forall (z : H), P.\textstyle\int\,(\lambda \omega \mapsto f\,\omega + g\,\omega)\,z = P.\textstyle\int\,f\,z + P.\textstyle\int\,g\,z
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 524](#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable). $\square$

<small>Referenced in [Lem 561](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-finsetsum"></a>
**Lemma 560** (`diagInt_finsetSum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1031)</small>

$$
(\forall i\in t, \mathrm{Integrable}\,(F\,i)\,(P.\mu\,z)) \to P.\textstyle\int\,(\lambda \omega \mapsto \sum_{i t} F\,i\,\omega)\,z = \sum_{i t} P.\textstyle\int\,(F\,i)\,z
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 562](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f"></a>
**Lemma 561** (`bilinDiag_add_f`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1039)</small>

$$
\mathrm{Measurable}\,f \to \mathrm{Measurable}\,g \to \forall \{\mathrm{Cf} \mathrm{Cg} : \mathbb{R}\}, (\forall (\omega : \Omega), \|f\,\omega\| \le \mathrm{Cf}) \to (\forall (\omega : \Omega), \|g\,\omega\| \le \mathrm{Cg}) \to \forall (x y : H), P.\mathrm{bd}\,(\lambda \omega \mapsto f\,\omega + g\,\omega)\,x\,y = P.\mathrm{bd}\,f\,x\,y + P.\mathrm{bd}\,g\,x\,y
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 559](#d-qiqth-spectral-projectionvaluedmeasure-diagint-add). $\square$

<small>Referenced in [Lem 563](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum"></a>
**Lemma 562** (`bilinDiag_finsetSum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1048)</small>

$$
(\forall (z : H), \forall i\in t, \mathrm{Integrable}\,(F\,i)\,(P.\mu\,z)) \to \forall (x y : H), P.\mathrm{bd}\,(\lambda \omega \mapsto \sum_{i t} F\,i\,\omega)\,x\,y = \sum_{i t} P.\mathrm{bd}\,(F\,i)\,x\,y
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 560](#d-qiqth-spectral-projectionvaluedmeasure-diagint-finsetsum). $\square$

<small>Referenced in [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add"></a>
**Lemma 563** (`boundedFC_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1058)</small>

$$
P.\Phi\,\cdots \,\cdots \,\cdots = P.\Phi\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} + P.\Phi\,\mathrm{hg}\,\mathrm{hCg0}\,\mathrm{hCg}
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 561](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-add-f). $\square$

<small>Referenced in [Lem 796](#d-qiqth-standardsubspacemodular-borelfc-add).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-smul-f"></a>
**Lemma 564** (`diagInt_smul_f`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1071)</small>

$$
P.\textstyle\int\,(\lambda \omega \mapsto c \cdot f\,\omega)\,z = c \cdot P.\textstyle\int\,f\,z
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure). $\square$

<small>Referenced in [Lem 565](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f"></a>
**Lemma 565** (`bilinDiag_smul_f`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1077)</small>

$$
P.\mathrm{bd}\,(\lambda \omega \mapsto c \cdot f\,\omega)\,x\,y = c \cdot P.\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 564](#d-qiqth-spectral-projectionvaluedmeasure-diagint-smul-f). $\square$

<small>Referenced in [Lem 566](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul"></a>
**Lemma 566** (`boundedFC_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1084)</small>

$$
P.\Phi\,\cdots \,\cdots \,\cdots = c \cdot P.\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 565](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f). $\square$

<small>Referenced in [Lem 797](#d-qiqth-standardsubspacemodular-borelfc-smul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le"></a>
**Lemma 567** (`boundedFC_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1095)</small>

$$
\|P.\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}\| \le 2 \cdot C
$$

*Proof.* By [Def 551](#d-qiqth-spectral-projectionvaluedmeasure-intborel), [Lem 553](#d-qiqth-spectral-projectionvaluedmeasure-intborel-norm-le). $\square$

<small>Referenced in [Lem 440](#d-qiqth-deviceopc-norm-le), [Lem 801](#d-qiqth-standardsubspacemodular-cfccont-norm-le).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr"></a>
**Lemma 568** (`boundedFC_congr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1105)</small>

$$
f = f^{\prime} \to P.\Phi\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} = P.\Phi\,\mathrm{hf}^{\prime}\,\mathrm{hCf0}^{\prime}\,\mathrm{hCf}^{\prime}
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc). $\square$

<small>Referenced in [Lem 577](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [Lem 579](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-norm-indicatorone-le"></a>
**Lemma 569** (`norm_indicatorOne_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1118)</small>

$$
\|s.\mathbf{1}\,(\lambda x \mapsto 1)\,\omega\| \le 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 573](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 577](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [Lem 579](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul), [Lem 671](#d-qiqth-spectraltheorem-borelfc-indicator), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator"></a>
**Lemma 570** (`diagInt_indicator`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1125)</small>

$$
\mathrm{MeasurableSet}\,s \to \forall (z : H), P.\textstyle\int\,(s.\mathbf{1}\,\lambda x \mapsto 1)\,z = ((P.\mu\,z)\,s).\mathrm{toReal}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 571](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner"></a>
**Lemma 571** (`diagInt_indicator_eq_inner`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1132)</small>

$$
\mathrm{MeasurableSet}\,s \to \forall (z : H), P.\textstyle\int\,(s.\mathbf{1}\,\lambda x \mapsto 1)\,z = \langle {z},{(P.E\,s)\,z}\rangle
$$

*Proof.* By [Lem 514](#d-qiqth-spectral-projectionvaluedmeasure-inner-e-self), [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 520](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-toreal), [Lem 570](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator). $\square$

<small>Referenced in [Lem 572](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator"></a>
**Lemma 572** (`bilinDiag_indicator`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1139)</small>

$$
\mathrm{MeasurableSet}\,s \to \forall (x y : H), P.\mathrm{bd}\,(s.\mathbf{1}\,\lambda x \mapsto 1)\,x\,y = \langle {x},{(P.E\,s)\,y}\rangle
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 571](#d-qiqth-spectral-projectionvaluedmeasure-diagint-indicator-eq-inner). $\square$

<small>Referenced in [Lem 573](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator"></a>
**Lemma 573** (`boundedFC_indicator`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1154)</small>

$$
P.\Phi\,\cdots \,\cdots \,\cdots = P.E\,s
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 572](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator). $\square$

<small>Referenced in [Lem 671](#d-qiqth-spectraltheorem-borelfc-indicator).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple"></a>
**Lemma 574** (`boundedFC_eq_integralSimple`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1176)</small>

$$
P.\Phi\,\cdots \,\cdots \,\cdots = P.\textstyle\int\,t\,c\,\mathrm{sets}
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Lem 519](#d-qiqth-spectral-projectionvaluedmeasure-inner-integralsimple-left), [Lem 524](#d-qiqth-spectral-projectionvaluedmeasure-integrable-boundedmeasurable), [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 562](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-finsetsum), [Lem 565](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-smul-f), [Lem 572](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-indicator). $\square$

<small>Referenced in [Lem 577](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [Lem 579](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq"></a>
**Lemma 575** (`integralSimple_mul_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1206)</small>

$$
(\forall i\in t, \mathrm{MeasurableSet}\,(A\,i)) \to (\forall j\in s, \mathrm{MeasurableSet}\,(B\,j)) \to P.\textstyle\int\,t\,a\,A \cdot P.\textstyle\int\,s\,b\,B = \sum_{i t} \sum_{j s} (a\,i \cdot b\,j) \cdot P.E\,(A\,i \cap B\,j)
$$

*Proof.* By [Lem 511](#d-qiqth-spectral-projectionvaluedmeasure-e-inter). $\square$

<small>Referenced in [Lem 576](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq"></a>
**Lemma 576** (`integralSimple_product_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1220)</small>

$$
(\forall i\in t, \mathrm{MeasurableSet}\,(A\,i)) \to (\forall j\in s, \mathrm{MeasurableSet}\,(B\,j)) \to (P.\textstyle\int\,(t \times s)\,(\lambda p \mapsto a\,p.1 \cdot b\,p.2)\,\lambda p \mapsto A\,p.1 \cap B\,p.2) = P.\textstyle\int\,t\,a\,A \cdot P.\textstyle\int\,s\,b\,B
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Lem 575](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-mul-eq). $\square$

<small>Referenced in [Lem 577](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul"></a>
**Lemma 577** (`boundedFC_simple_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1230)</small>

$$
P.\Phi\,\cdots \,\cdots \,\cdots = P.\textstyle\int\,t\,a\,A \cdot P.\textstyle\int\,s\,b\,B
$$

*Proof.* By [Lem 568](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 576](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple-product-eq). $\square$

<small>Referenced in [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-simplefunc-eq-sum"></a>
**Lemma 578** (`simpleFunc_eq_sum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1277)</small>

$$
\varphi\,a = \sum_{y \varphi \mathrm{range}} y \cdot (\varphi ^{-1}{}' \{y\}).\mathbf{1}\,(\lambda x \mapsto 1)\,a
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 579](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc), [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc"></a>
**Lemma 579** (`boundedFC_simpleFunc`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1291)</small>

$$
P.\Phi\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC} = P.\textstyle\int\,\varphi.\mathrm{range}\,\mathrm{id}\,\lambda y \mapsto \varphi ^{-1}{}' \{y\}
$$

*Proof.* By [Lem 568](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [Lem 569](#d-qiqth-spectral-projectionvaluedmeasure-norm-indicatorone-le), [Lem 574](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-eq-integralsimple), [Lem 578](#d-qiqth-spectral-projectionvaluedmeasure-simplefunc-eq-sum). $\square$

<small>Referenced in [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul"></a>
**Lemma 580** (`boundedFC_simpleFunc_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1300)</small>

$$
P.\Phi\,\mathrm{hfp}\,\mathrm{hC0p}\,\mathrm{hCp} = P.\Phi\,\mathrm{hf}\varphi\,\mathrm{hC0}\varphi\,\mathrm{hC}\varphi \cdot P.\Phi\,\mathrm{hf}\psi\,\mathrm{hC0}\psi\,\mathrm{hC}\psi
$$

*Proof.* By [Def 518](#d-qiqth-spectral-projectionvaluedmeasure-integralsimple), [Lem 568](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [Lem 569](#d-qiqth-spectral-projectionvaluedmeasure-norm-indicatorone-le), [Lem 577](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simple-mul), [Lem 578](#d-qiqth-spectral-projectionvaluedmeasure-simplefunc-eq-sum), [Lem 579](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc). $\square$

<small>Referenced in [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated"></a>
**Lemma 581** (`tendsto_diagInt_of_dominated`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1318)</small>

$$
(\forall (n : \mathbb{N}), \mathrm{Measurable}\,(f\,n)) \to (\forall (n : \mathbb{N}) (\omega : \Omega), \|f\,n\,\omega\| \le C) \to (\forall (\omega : \Omega), \mathrm{Tendsto}\,(\lambda n \mapsto f\,n\,\omega)\,\mathrm{atTop}\,(\mathrm{nhds}\,(g\,\omega))) \to \forall (z : H), \mathrm{Tendsto}\,(\lambda n \mapsto P.\textstyle\int\,(f\,n)\,z)\,\mathrm{atTop}\,(\mathrm{nhds}\,(P.\textstyle\int\,g\,z))
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Lem 521](#d-qiqth-spectral-projectionvaluedmeasure-instisfinitemeasure-scalarmeasure). $\square$

<small>Referenced in [Lem 582](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated"></a>
**Lemma 582** (`tendsto_bilinDiag_of_dominated`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1352)</small>

$$
(\forall (n : \mathbb{N}), \mathrm{Measurable}\,(f\,n)) \to (\forall (n : \mathbb{N}) (\omega : \Omega), \|f\,n\,\omega\| \le C) \to (\forall (\omega : \Omega), \mathrm{Tendsto}\,(\lambda n \mapsto f\,n\,\omega)\,\mathrm{atTop}\,(\mathrm{nhds}\,(g\,\omega))) \to \forall (x y : H), \mathrm{Tendsto}\,(\lambda n \mapsto P.\mathrm{bd}\,(f\,n)\,x\,y)\,\mathrm{atTop}\,(\mathrm{nhds}\,(P.\mathrm{bd}\,g\,x\,y))
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Lem 581](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-diagint-of-dominated). $\square$

<small>Referenced in [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-approxseq"></a>
**Definition 583** (`approxSeq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1369)</small>

A definition — see source for the body.

<small>Referenced in [Lem 584](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-tendsto), [Lem 585](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-norm-le), [Lem 586](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-measurable), [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-approxseq-tendsto"></a>
**Lemma 584** (`approxSeq_tendsto`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1376)</small>

$$
\mathrm{Tendsto}\,(\lambda n \mapsto (\href{#d-qiqth-spectral-projectionvaluedmeasure-approxseq}{\mathrm{aseq}}\,f\,\mathrm{hf}\,n)\,\omega)\,\mathrm{atTop}\,(\mathrm{nhds}\,(f\,\omega))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-approxseq-norm-le"></a>
**Lemma 585** (`approxSeq_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1381)</small>

$$
\|(\href{#d-qiqth-spectral-projectionvaluedmeasure-approxseq}{\mathrm{aseq}}\,f\,\mathrm{hf}\,n)\,\omega\| \le \|f\,\omega\| + \|f\,\omega\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-approxseq-measurable"></a>
**Lemma 586** (`approxSeq_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1385)</small>

$$
\mathrm{Measurable}\,(\href{#d-qiqth-spectral-projectionvaluedmeasure-approxseq}{\mathrm{aseq}}\,f\,\mathrm{hf}\,n)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left), [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left"></a>
**Lemma 587** (`boundedFC_mul_simpleFunc_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1391)</small>

$$
P.\Phi\,\mathrm{hfp}\,\mathrm{hC0p}\,\mathrm{hCp} = P.\Phi\,\mathrm{hf}\varphi\,\mathrm{hC0}\varphi\,\mathrm{hC}\varphi \cdot P.\Phi\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg}
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 580](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-simplefunc-mul), [Lem 582](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated), [Def 583](#d-qiqth-spectral-projectionvaluedmeasure-approxseq), [Lem 584](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-tendsto), [Lem 585](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-norm-le), [Lem 586](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-measurable). $\square$

<small>Referenced in [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul).</small>

<a id="d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul"></a>
**Lemma 588** (`boundedFC_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/PVM.lean#L1433)</small>

$$
P.\Phi\,\mathrm{hfp}\,\mathrm{hC0p}\,\mathrm{hCp} = P.\Phi\,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf} \cdot P.\Phi\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg}
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc), [Lem 582](#d-qiqth-spectral-projectionvaluedmeasure-tendsto-bilindiag-of-dominated), [Def 583](#d-qiqth-spectral-projectionvaluedmeasure-approxseq), [Lem 584](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-tendsto), [Lem 585](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-norm-le), [Lem 586](#d-qiqth-spectral-projectionvaluedmeasure-approxseq-measurable), [Lem 587](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul-simplefunc-left). $\square$

<small>Referenced in [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul).</small>

<a id="sec-qiqth-spectral-spectraltheorem"></a>
## QIQTH.Spectral.SpectralTheorem

<a id="d-qiqth-spectraltheorem-qform-congr-simp"></a>
**Lemma 589** (`congr_simp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean)</small>

$$
s = \mathrm{s\_1} \to \forall (z \mathrm{z\_1} : H), z = \mathrm{z\_1} \to \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,z = \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,\mathrm{s\_1}\,\mathrm{z\_1}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 608](#d-qiqth-spectraltheorem-qform-neg), [Lem 617](#d-qiqth-spectraltheorem-bform-zero-right).</small>

<a id="d-qiqth-spectraltheorem-bform-congr-simp"></a>
**Lemma 590** (`congr_simp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean)</small>

$$
s = \mathrm{s\_1} \to \forall (u \mathrm{u\_1} : H), u = \mathrm{u\_1} \to \forall (v \mathrm{v\_1} : H), v = \mathrm{v\_1} \to \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v = \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,\mathrm{s\_1}\,\mathrm{u\_1}\,\mathrm{v\_1}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 624](#d-qiqth-spectraltheorem-bform-neg-right).</small>

<a id="d-qiqth-spectraltheorem-specproj-congr-simp"></a>
**Lemma 591** (`congr_simp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean)</small>

$$
s = \mathrm{s\_1} \to \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s = \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,\mathrm{s\_1}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 649](#d-qiqth-spectraltheorem-specproj-finset-sum).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-congr-simp"></a>
**Lemma 592** (`congr_simp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean)</small>

$$
x = \mathrm{x\_1} \to \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x = \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,\mathrm{x\_1}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 605](#d-qiqth-spectraltheorem-specmeasure-zero).</small>

<a id="d-qiqth-spectraltheorem-specfunctional"></a>
**Definition 593** (`specFunctional`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L84)</small>

A definition — see source for the body.

<small>Referenced in [Def 594](#d-qiqth-spectraltheorem-specplm).</small>

<a id="d-qiqth-spectraltheorem-specplm"></a>
**Definition 594** (`specPLM`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L100)</small>

A definition — see source for the body.

<small>Referenced in [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 596](#d-qiqth-spectraltheorem-integral-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure).</small>

<a id="d-qiqth-spectraltheorem-specmeasure"></a>
**Definition 595** (`specMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L111)</small>

A definition — see source for the body.

<small>Referenced in [Lem 592](#d-qiqth-spectraltheorem-specmeasure-congr-simp), [Lem 596](#d-qiqth-spectraltheorem-integral-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Lem 598](#d-qiqth-spectraltheorem-specmeasure-real-univ), [Lem 599](#d-qiqth-spectraltheorem-specmeasure-real-le), [Lem 600](#d-qiqth-spectraltheorem-specmeasure-smul), [Lem 601](#d-qiqth-spectraltheorem-specmeasure-parallelogram), [Lem 602](#d-qiqth-spectraltheorem-specmeasure-add), [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 604](#d-qiqth-spectraltheorem-qform-nonneg), [Lem 605](#d-qiqth-spectraltheorem-specmeasure-zero), [Lem 606](#d-qiqth-spectraltheorem-qform-zero), [Lem 607](#d-qiqth-spectraltheorem-qform-smul), [Lem 609](#d-qiqth-spectraltheorem-qform-parallelogram), [Lem 610](#d-qiqth-spectraltheorem-qform-add), [Lem 634](#d-qiqth-spectraltheorem-cform-empty), [Lem 644](#d-qiqth-spectraltheorem-qform-union), [Lem 650](#d-qiqth-spectraltheorem-specproj-hassum), [Lem 652](#d-qiqth-spectraltheorem-integral-specmeasure-cont), [Lem 653](#d-qiqth-spectraltheorem-specmeasure-engine), [Lem 654](#d-qiqth-spectraltheorem-specmeasure-engine-measure), [Lem 655](#d-qiqth-spectraltheorem-withdensity-real-setintegral), [Lem 656](#d-qiqth-spectraltheorem-specmeasure-setengine-nonneg), [Lem 658](#d-qiqth-spectraltheorem-specmeasure-setengine), [Lem 660](#d-qiqth-spectraltheorem-integral-specmeasure-polarization), [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure), [Lem 662](#d-qiqth-spectraltheorem-bform-specproj), [Lem 665](#d-qiqth-spectraltheorem-re-inner-t-eq-integral), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord).</small>

<a id="d-qiqth-spectraltheorem-integral-specmeasure"></a>
**Lemma 596** (`integral_specMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L118)</small>

$$
\int (s : (\mathrm{sp}\,\mathbb{R}\,T)), f\,s \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x = \mathrm{re}\,(\langle {x},{((\mathrm{cfcHom}\,\mathrm{ha})\,f.\mathrm{toContinuousMap})\,x}\rangle)
$$

*Proof.* By [Def 594](#d-qiqth-spectraltheorem-specplm). $\square$

<small>Referenced in [Lem 598](#d-qiqth-spectraltheorem-specmeasure-real-univ), [Lem 600](#d-qiqth-spectraltheorem-specmeasure-smul), [Lem 601](#d-qiqth-spectraltheorem-specmeasure-parallelogram), [Lem 602](#d-qiqth-spectraltheorem-specmeasure-add), [Lem 652](#d-qiqth-spectraltheorem-integral-specmeasure-cont), [Lem 665](#d-qiqth-spectraltheorem-re-inner-t-eq-integral).</small>

<a id="d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure"></a>
**Lemma 597** (`instIsFiniteMeasureElemRealSpectrumContinuousLinearMapComplexIdSpecMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L124)</small>

$$
\mathrm{IsFiniteMeasure}\,(\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x)
$$

*Proof.* By [Def 594](#d-qiqth-spectraltheorem-specplm). $\square$

<small>Referenced in [Lem 599](#d-qiqth-spectraltheorem-specmeasure-real-le), [Lem 600](#d-qiqth-spectraltheorem-specmeasure-smul), [Lem 601](#d-qiqth-spectraltheorem-specmeasure-parallelogram), [Lem 602](#d-qiqth-spectraltheorem-specmeasure-add), [Lem 609](#d-qiqth-spectraltheorem-qform-parallelogram), [Lem 610](#d-qiqth-spectraltheorem-qform-add), [Lem 644](#d-qiqth-spectraltheorem-qform-union), [Lem 650](#d-qiqth-spectraltheorem-specproj-hassum), [Lem 654](#d-qiqth-spectraltheorem-specmeasure-engine-measure), [Lem 656](#d-qiqth-spectraltheorem-specmeasure-setengine-nonneg), [Lem 658](#d-qiqth-spectraltheorem-specmeasure-setengine), [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure), [Lem 662](#d-qiqth-spectraltheorem-bform-specproj), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-real-univ"></a>
**Lemma 598** (`specMeasure_real_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L130)</small>

$$
(\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x).\mathrm{real} = {\|x\|}^{2}
$$

*Proof.* By [Lem 596](#d-qiqth-spectraltheorem-integral-specmeasure). $\square$

<small>Referenced in [Lem 599](#d-qiqth-spectraltheorem-specmeasure-real-le), [Lem 638](#d-qiqth-spectraltheorem-qform-univ).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-real-le"></a>
**Lemma 599** (`specMeasure_real_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L175)</small>

$$
(\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z).\mathrm{real}\,B \le {\|z\|}^{2}
$$

*Proof.* By [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Lem 598](#d-qiqth-spectraltheorem-specmeasure-real-univ). $\square$

<small>Referenced in [Lem 621](#d-qiqth-spectraltheorem-bform-abs-le), [Lem 647](#d-qiqth-spectraltheorem-specproj-le-one).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-smul"></a>
**Lemma 600** (`specMeasure_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L193)</small>

$$
\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(c \cdot x) = {\|c\|_{+}}^{2} \cdot \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x
$$

*Proof.* By [Lem 596](#d-qiqth-spectraltheorem-integral-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure). $\square$

<small>Referenced in [Lem 605](#d-qiqth-spectraltheorem-specmeasure-zero), [Lem 607](#d-qiqth-spectraltheorem-qform-smul).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-parallelogram"></a>
**Lemma 601** (`specMeasure_parallelogram`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L206)</small>

$$
\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + y) + \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - y) = 2 \cdot \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x + 2 \cdot \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,y
$$

*Proof.* By [Lem 596](#d-qiqth-spectraltheorem-integral-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure). $\square$

<small>Referenced in [Lem 609](#d-qiqth-spectraltheorem-qform-parallelogram).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-add"></a>
**Lemma 602** (`specMeasure_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L227)</small>

$$
\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + a + b) + \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - a) + \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - b) = \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - a - b) + \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + a) + \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + b)
$$

*Proof.* By [Lem 596](#d-qiqth-spectraltheorem-integral-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure). $\square$

<small>Referenced in [Lem 610](#d-qiqth-spectraltheorem-qform-add).</small>

<a id="d-qiqth-spectraltheorem-qform"></a>
**Definition 603** (`qForm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L256)</small>

A definition — see source for the body.

<small>Referenced in [Lem 589](#d-qiqth-spectraltheorem-qform-congr-simp), [Lem 604](#d-qiqth-spectraltheorem-qform-nonneg), [Lem 606](#d-qiqth-spectraltheorem-qform-zero), [Lem 607](#d-qiqth-spectraltheorem-qform-smul), [Lem 608](#d-qiqth-spectraltheorem-qform-neg), [Lem 609](#d-qiqth-spectraltheorem-qform-parallelogram), [Lem 610](#d-qiqth-spectraltheorem-qform-add), [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 612](#d-qiqth-spectraltheorem-qform-add-expand), [Lem 613](#d-qiqth-spectraltheorem-bform-self), [Lem 614](#d-qiqth-spectraltheorem-bform-comm), [Lem 615](#d-qiqth-spectraltheorem-bform-add-right), [Lem 616](#d-qiqth-spectraltheorem-qform-real-smul), [Lem 617](#d-qiqth-spectraltheorem-bform-zero-right), [Lem 619](#d-qiqth-spectraltheorem-bform-sq-le), [Lem 621](#d-qiqth-spectraltheorem-bform-abs-le), [Lem 625](#d-qiqth-spectraltheorem-bform-i-smul), [Lem 634](#d-qiqth-spectraltheorem-cform-empty), [Lem 638](#d-qiqth-spectraltheorem-qform-univ), [Lem 639](#d-qiqth-spectraltheorem-bform-univ), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [Lem 643](#d-qiqth-spectraltheorem-specproj-ispositive), [Lem 644](#d-qiqth-spectraltheorem-qform-union), [Lem 645](#d-qiqth-spectraltheorem-cform-union-disjoint), [Lem 647](#d-qiqth-spectraltheorem-specproj-le-one), [Lem 648](#d-qiqth-spectraltheorem-norm-specproj-sq-le), [Lem 650](#d-qiqth-spectraltheorem-specproj-hassum), [Lem 658](#d-qiqth-spectraltheorem-specmeasure-setengine), [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure), [Lem 662](#d-qiqth-spectraltheorem-bform-specproj), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-qform-nonneg"></a>
**Lemma 604** (`qForm_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L260)</small>

$$
0 \le \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,z
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure). $\square$

<small>Referenced in [Lem 619](#d-qiqth-spectraltheorem-bform-sq-le), [Lem 621](#d-qiqth-spectraltheorem-bform-abs-le), [Lem 643](#d-qiqth-spectraltheorem-specproj-ispositive).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-zero"></a>
**Lemma 605** (`specMeasure_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L263)</small>

$$
\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,0 = 0
$$

*Proof.* By [Lem 592](#d-qiqth-spectraltheorem-specmeasure-congr-simp), [Lem 600](#d-qiqth-spectraltheorem-specmeasure-smul). $\square$

<small>Referenced in [Lem 606](#d-qiqth-spectraltheorem-qform-zero).</small>

<a id="d-qiqth-spectraltheorem-qform-zero"></a>
**Lemma 606** (`qForm_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L268)</small>

$$
\href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,0 = 0
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 605](#d-qiqth-spectraltheorem-specmeasure-zero). $\square$

<small>Referenced in [Lem 613](#d-qiqth-spectraltheorem-bform-self).</small>

<a id="d-qiqth-spectraltheorem-qform-smul"></a>
**Lemma 607** (`qForm_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L272)</small>

$$
\href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(c \cdot z) = {\|c\|}^{2} \cdot \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,z
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 600](#d-qiqth-spectraltheorem-specmeasure-smul). $\square$

<small>Referenced in [Lem 608](#d-qiqth-spectraltheorem-qform-neg), [Lem 613](#d-qiqth-spectraltheorem-bform-self), [Lem 616](#d-qiqth-spectraltheorem-qform-real-smul), [Lem 625](#d-qiqth-spectraltheorem-bform-i-smul).</small>

<a id="d-qiqth-spectraltheorem-qform-neg"></a>
**Lemma 608** (`qForm_neg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L277)</small>

$$
\href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(-z) = \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,z
$$

*Proof.* By [Lem 589](#d-qiqth-spectraltheorem-qform-congr-simp), [Lem 607](#d-qiqth-spectraltheorem-qform-smul). $\square$

<small>Referenced in [Lem 614](#d-qiqth-spectraltheorem-bform-comm).</small>

<a id="d-qiqth-spectraltheorem-qform-parallelogram"></a>
**Lemma 609** (`qForm_parallelogram`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L282)</small>

$$
\href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(x + y) + \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(x - y) = 2 \cdot \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,x + 2 \cdot \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,y
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Lem 601](#d-qiqth-spectraltheorem-specmeasure-parallelogram). $\square$

<small>Referenced in [Lem 612](#d-qiqth-spectraltheorem-qform-add-expand).</small>

<a id="d-qiqth-spectraltheorem-qform-add"></a>
**Lemma 610** (`qForm_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L294)</small>

$$
\href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(x + a + b) + \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(x - a) + \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(x - b) = \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(x - a - b) + \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(x + a) + \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(x + b)
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Lem 602](#d-qiqth-spectraltheorem-specmeasure-add). $\square$

<small>Referenced in [Lem 615](#d-qiqth-spectraltheorem-bform-add-right).</small>

<a id="d-qiqth-spectraltheorem-bform"></a>
**Definition 611** (`bForm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L301)</small>

A definition — see source for the body.

<small>Referenced in [Lem 590](#d-qiqth-spectraltheorem-bform-congr-simp), [Lem 612](#d-qiqth-spectraltheorem-qform-add-expand), [Lem 613](#d-qiqth-spectraltheorem-bform-self), [Lem 614](#d-qiqth-spectraltheorem-bform-comm), [Lem 615](#d-qiqth-spectraltheorem-bform-add-right), [Lem 617](#d-qiqth-spectraltheorem-bform-zero-right), [Def 618](#d-qiqth-spectraltheorem-bformright), [Lem 619](#d-qiqth-spectraltheorem-bform-sq-le), [Lem 620](#d-qiqth-spectraltheorem-bform-sub-right), [Lem 621](#d-qiqth-spectraltheorem-bform-abs-le), [Lem 622](#d-qiqth-spectraltheorem-bform-continuous-right), [Lem 623](#d-qiqth-spectraltheorem-bform-real-smul-right), [Lem 624](#d-qiqth-spectraltheorem-bform-neg-right), [Lem 625](#d-qiqth-spectraltheorem-bform-i-smul), [Lem 626](#d-qiqth-spectraltheorem-bform-i-comm), [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 628](#d-qiqth-spectraltheorem-cform-add-right), [Lem 629](#d-qiqth-spectraltheorem-cform-norm-le), [Lem 634](#d-qiqth-spectraltheorem-cform-empty), [Lem 636](#d-qiqth-spectraltheorem-cform-hermitian), [Lem 639](#d-qiqth-spectraltheorem-bform-univ), [Lem 640](#d-qiqth-spectraltheorem-cform-univ), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [Lem 645](#d-qiqth-spectraltheorem-cform-union-disjoint), [Lem 657](#d-qiqth-spectraltheorem-bform-sub-left), [Lem 658](#d-qiqth-spectraltheorem-specmeasure-setengine), [Lem 659](#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure), [Lem 662](#d-qiqth-spectraltheorem-bform-specproj), [Lem 663](#d-qiqth-spectraltheorem-specproj-inter).</small>

<a id="d-qiqth-spectraltheorem-qform-add-expand"></a>
**Lemma 612** (`qForm_add_expand`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L305)</small>

$$
\href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(p + q) = \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,p + \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,q + 2 \cdot \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,p\,q
$$

*Proof.* By [Lem 609](#d-qiqth-spectraltheorem-qform-parallelogram). $\square$

<small>Referenced in [Lem 619](#d-qiqth-spectraltheorem-bform-sq-le).</small>

<a id="d-qiqth-spectraltheorem-bform-self"></a>
**Lemma 613** (`bForm_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L312)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,u = \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,u
$$

*Proof.* By [Lem 606](#d-qiqth-spectraltheorem-qform-zero), [Lem 607](#d-qiqth-spectraltheorem-qform-smul). $\square$

<small>Referenced in [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj).</small>

<a id="d-qiqth-spectraltheorem-bform-comm"></a>
**Lemma 614** (`bForm_comm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L320)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v = \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,v\,u
$$

*Proof.* By [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 608](#d-qiqth-spectraltheorem-qform-neg). $\square$

<small>Referenced in [Lem 636](#d-qiqth-spectraltheorem-cform-hermitian), [Lem 657](#d-qiqth-spectraltheorem-bform-sub-left).</small>

<a id="d-qiqth-spectraltheorem-bform-add-right"></a>
**Lemma 615** (`bForm_add_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L326)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,(v + w) = \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v + \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,w
$$

*Proof.* By [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 610](#d-qiqth-spectraltheorem-qform-add). $\square$

<small>Referenced in [Def 618](#d-qiqth-spectraltheorem-bformright), [Lem 620](#d-qiqth-spectraltheorem-bform-sub-right), [Lem 628](#d-qiqth-spectraltheorem-cform-add-right).</small>

<a id="d-qiqth-spectraltheorem-qform-real-smul"></a>
**Lemma 616** (`qForm_real_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L339)</small>

$$
\href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,(r \cdot z) = {r}^{2} \cdot \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,z
$$

*Proof.* By [Lem 607](#d-qiqth-spectraltheorem-qform-smul). $\square$

<small>Referenced in [Lem 619](#d-qiqth-spectraltheorem-bform-sq-le).</small>

<a id="d-qiqth-spectraltheorem-bform-zero-right"></a>
**Lemma 617** (`bForm_zero_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L344)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,0 = 0
$$

*Proof.* By [Lem 589](#d-qiqth-spectraltheorem-qform-congr-simp), [Def 603](#d-qiqth-spectraltheorem-qform). $\square$

<small>Referenced in [Def 618](#d-qiqth-spectraltheorem-bformright).</small>

<a id="d-qiqth-spectraltheorem-bformright"></a>
**Definition 618** (`bFormRight`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L348)</small>

A definition — see source for the body.

<small>Referenced in [Lem 619](#d-qiqth-spectraltheorem-bform-sq-le), [Lem 623](#d-qiqth-spectraltheorem-bform-real-smul-right).</small>

<a id="d-qiqth-spectraltheorem-bform-sq-le"></a>
**Lemma 619** (`bForm_sq_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L354)</small>

$$
{\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v}^{2} \le \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,u \cdot \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,v
$$

*Proof.* By [Lem 604](#d-qiqth-spectraltheorem-qform-nonneg), [Lem 612](#d-qiqth-spectraltheorem-qform-add-expand), [Lem 616](#d-qiqth-spectraltheorem-qform-real-smul), [Def 618](#d-qiqth-spectraltheorem-bformright). $\square$

<small>Referenced in [Lem 621](#d-qiqth-spectraltheorem-bform-abs-le).</small>

<a id="d-qiqth-spectraltheorem-bform-sub-right"></a>
**Lemma 620** (`bForm_sub_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L386)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,(v - w) = \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v - \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,w
$$

*Proof.* By [Lem 615](#d-qiqth-spectraltheorem-bform-add-right). $\square$

<small>Referenced in [Lem 622](#d-qiqth-spectraltheorem-bform-continuous-right), [Lem 657](#d-qiqth-spectraltheorem-bform-sub-left).</small>

<a id="d-qiqth-spectraltheorem-bform-abs-le"></a>
**Lemma 621** (`bForm_abs_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L393)</small>

$$
|\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v| \le \|u\| \cdot \|v\|
$$

*Proof.* By [Lem 599](#d-qiqth-spectraltheorem-specmeasure-real-le), [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 604](#d-qiqth-spectraltheorem-qform-nonneg), [Lem 619](#d-qiqth-spectraltheorem-bform-sq-le). $\square$

<small>Referenced in [Lem 622](#d-qiqth-spectraltheorem-bform-continuous-right), [Lem 629](#d-qiqth-spectraltheorem-cform-norm-le).</small>

<a id="d-qiqth-spectraltheorem-bform-continuous-right"></a>
**Lemma 622** (`bForm_continuous_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L407)</small>

$$
\mathrm{Continuous}\,\lambda v \mapsto \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v
$$

*Proof.* By [Lem 620](#d-qiqth-spectraltheorem-bform-sub-right), [Lem 621](#d-qiqth-spectraltheorem-bform-abs-le). $\square$

<small>Referenced in [Lem 623](#d-qiqth-spectraltheorem-bform-real-smul-right).</small>

<a id="d-qiqth-spectraltheorem-bform-real-smul-right"></a>
**Lemma 623** (`bForm_real_smul_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L415)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,(r \cdot v) = r \cdot \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v
$$

*Proof.* By [Def 618](#d-qiqth-spectraltheorem-bformright), [Lem 622](#d-qiqth-spectraltheorem-bform-continuous-right). $\square$

<small>Referenced in [Lem 624](#d-qiqth-spectraltheorem-bform-neg-right).</small>

<a id="d-qiqth-spectraltheorem-bform-neg-right"></a>
**Lemma 624** (`bForm_neg_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L421)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,(-v) = -\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v
$$

*Proof.* By [Lem 590](#d-qiqth-spectraltheorem-bform-congr-simp), [Lem 623](#d-qiqth-spectraltheorem-bform-real-smul-right). $\square$

<small>Referenced in [Lem 626](#d-qiqth-spectraltheorem-bform-i-comm).</small>

<a id="d-qiqth-spectraltheorem-bform-i-smul"></a>
**Lemma 625** (`bForm_I_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L426)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,(i \cdot u)\,(i \cdot v) = \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v
$$

*Proof.* By [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 607](#d-qiqth-spectraltheorem-qform-smul). $\square$

<small>Referenced in [Lem 626](#d-qiqth-spectraltheorem-bform-i-comm).</small>

<a id="d-qiqth-spectraltheorem-bform-i-comm"></a>
**Lemma 626** (`bForm_I_comm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L434)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,(i \cdot x)\,y = -\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,x\,(i \cdot y)
$$

*Proof.* By [Lem 624](#d-qiqth-spectraltheorem-bform-neg-right), [Lem 625](#d-qiqth-spectraltheorem-bform-i-smul). $\square$

<small>Referenced in [Lem 636](#d-qiqth-spectraltheorem-cform-hermitian).</small>

<a id="d-qiqth-spectraltheorem-cform"></a>
**Definition 627** (`cForm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L443)</small>

A definition — see source for the body.

<small>Referenced in [Lem 628](#d-qiqth-spectraltheorem-cform-add-right), [Lem 629](#d-qiqth-spectraltheorem-cform-norm-le), [Def 630](#d-qiqth-spectraltheorem-cformclm), [Lem 631](#d-qiqth-spectraltheorem-cformclm-norm-le), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj), [Lem 634](#d-qiqth-spectraltheorem-cform-empty), [Lem 635](#d-qiqth-spectraltheorem-specproj-empty), [Lem 636](#d-qiqth-spectraltheorem-cform-hermitian), [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint), [Lem 640](#d-qiqth-spectraltheorem-cform-univ), [Lem 641](#d-qiqth-spectraltheorem-specproj-univ), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [Lem 645](#d-qiqth-spectraltheorem-cform-union-disjoint), [Lem 646](#d-qiqth-spectraltheorem-specproj-union-disjoint), [Lem 659](#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [Lem 663](#d-qiqth-spectraltheorem-specproj-inter).</small>

<a id="d-qiqth-spectraltheorem-cform-add-right"></a>
**Lemma 628** (`cForm_add_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L448)</small>

$$
\href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,s\,x\,(y + z) = \href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,s\,x\,y + \href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,s\,x\,z
$$

*Proof.* By [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 615](#d-qiqth-spectraltheorem-bform-add-right). $\square$

<small>Referenced in [Def 630](#d-qiqth-spectraltheorem-cformclm), [Lem 631](#d-qiqth-spectraltheorem-cformclm-norm-le).</small>

<a id="d-qiqth-spectraltheorem-cform-norm-le"></a>
**Lemma 629** (`cForm_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L530)</small>

$$
\|\href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,s\,x\,y\| \le 2 \cdot \|x\| \cdot \|y\|
$$

*Proof.* By [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 621](#d-qiqth-spectraltheorem-bform-abs-le). $\square$

<small>Referenced in [Def 630](#d-qiqth-spectraltheorem-cformclm), [Lem 631](#d-qiqth-spectraltheorem-cformclm-norm-le).</small>

<a id="d-qiqth-spectraltheorem-cformclm"></a>
**Definition 630** (`cFormCLM`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L546)</small>

A definition — see source for the body.

<small>Referenced in [Lem 631](#d-qiqth-spectraltheorem-cformclm-norm-le), [Def 632](#d-qiqth-spectraltheorem-specproj), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj).</small>

<a id="d-qiqth-spectraltheorem-cformclm-norm-le"></a>
**Lemma 631** (`cFormCLM_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L558)</small>

$$
\|\href{#d-qiqth-spectraltheorem-cformclm}{\mathrm{cFormCLM}}\,T\,\mathrm{ha}\,s\,x\| \le 2 \cdot \|x\|
$$

*Proof.* By [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 628](#d-qiqth-spectraltheorem-cform-add-right), [Lem 629](#d-qiqth-spectraltheorem-cform-norm-le). $\square$

<small>Referenced in [Def 632](#d-qiqth-spectraltheorem-specproj), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj).</small>

<a id="d-qiqth-spectraltheorem-specproj"></a>
**Definition 632** (`specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L563)</small>

A definition — see source for the body.

<small>Referenced in [Lem 591](#d-qiqth-spectraltheorem-specproj-congr-simp), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj), [Lem 635](#d-qiqth-spectraltheorem-specproj-empty), [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint), [Lem 641](#d-qiqth-spectraltheorem-specproj-univ), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [Lem 643](#d-qiqth-spectraltheorem-specproj-ispositive), [Lem 646](#d-qiqth-spectraltheorem-specproj-union-disjoint), [Lem 647](#d-qiqth-spectraltheorem-specproj-le-one), [Lem 648](#d-qiqth-spectraltheorem-norm-specproj-sq-le), [Lem 649](#d-qiqth-spectraltheorem-specproj-finset-sum), [Lem 650](#d-qiqth-spectraltheorem-specproj-hassum), [Lem 659](#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure), [Lem 662](#d-qiqth-spectraltheorem-bform-specproj), [Lem 663](#d-qiqth-spectraltheorem-specproj-inter), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-inner-specproj"></a>
**Lemma 633** (`inner_specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L580)</small>

$$
\langle {(\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,x},{y}\rangle = \href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,s\,x\,y
$$

*Proof.* By [Def 630](#d-qiqth-spectraltheorem-cformclm), [Lem 631](#d-qiqth-spectraltheorem-cformclm-norm-le). $\square$

<small>Referenced in [Lem 635](#d-qiqth-spectraltheorem-specproj-empty), [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint), [Lem 641](#d-qiqth-spectraltheorem-specproj-univ), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [Lem 646](#d-qiqth-spectraltheorem-specproj-union-disjoint), [Lem 659](#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [Lem 663](#d-qiqth-spectraltheorem-specproj-inter).</small>

<a id="d-qiqth-spectraltheorem-cform-empty"></a>
**Lemma 634** (`cForm_empty`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L586)</small>

$$
\href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,\emptyset \,x\,y = 0
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Def 603](#d-qiqth-spectraltheorem-qform), [Def 611](#d-qiqth-spectraltheorem-bform). $\square$

<small>Referenced in [Lem 635](#d-qiqth-spectraltheorem-specproj-empty).</small>

<a id="d-qiqth-spectraltheorem-specproj-empty"></a>
**Lemma 635** (`specProj_empty`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L591)</small>

$$
\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,\emptyset = 0
$$

*Proof.* By [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj), [Lem 634](#d-qiqth-spectraltheorem-cform-empty). $\square$

<small>Referenced in [Lem 649](#d-qiqth-spectraltheorem-specproj-finset-sum), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectraltheorem-cform-hermitian"></a>
**Lemma 636** (`cForm_hermitian`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L596)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,s\,y\,x) = \href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,s\,x\,y
$$

*Proof.* By [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 614](#d-qiqth-spectraltheorem-bform-comm), [Lem 626](#d-qiqth-spectraltheorem-bform-i-comm). $\square$

<small>Referenced in [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint).</small>

<a id="d-qiqth-spectraltheorem-specproj-isselfadjoint"></a>
**Lemma 637** (`specProj_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L605)</small>

$$
\mathrm{IsSelfAdjoint}\,(\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)
$$

*Proof.* By [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj), [Lem 636](#d-qiqth-spectraltheorem-cform-hermitian). $\square$

<small>Referenced in [Lem 643](#d-qiqth-spectraltheorem-specproj-ispositive), [Lem 647](#d-qiqth-spectraltheorem-specproj-le-one), [Lem 648](#d-qiqth-spectraltheorem-norm-specproj-sq-le), [Lem 659](#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [Lem 663](#d-qiqth-spectraltheorem-specproj-inter), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-qform-univ"></a>
**Lemma 638** (`qForm_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L613)</small>

$$
\href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,z = {\|z\|}^{2}
$$

*Proof.* By [Lem 598](#d-qiqth-spectraltheorem-specmeasure-real-univ). $\square$

<small>Referenced in [Lem 639](#d-qiqth-spectraltheorem-bform-univ).</small>

<a id="d-qiqth-spectraltheorem-bform-univ"></a>
**Lemma 639** (`bForm_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L617)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,x\,y = \mathrm{re}\,(\langle {x},{y}\rangle)
$$

*Proof.* By [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 638](#d-qiqth-spectraltheorem-qform-univ). $\square$

<small>Referenced in [Lem 640](#d-qiqth-spectraltheorem-cform-univ).</small>

<a id="d-qiqth-spectraltheorem-cform-univ"></a>
**Lemma 640** (`cForm_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L624)</small>

$$
\href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,x\,y = \langle {x},{y}\rangle
$$

*Proof.* By [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 639](#d-qiqth-spectraltheorem-bform-univ). $\square$

<small>Referenced in [Lem 641](#d-qiqth-spectraltheorem-specproj-univ).</small>

<a id="d-qiqth-spectraltheorem-specproj-univ"></a>
**Lemma 641** (`specProj_univ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L637)</small>

$$
\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha} = 1
$$

*Proof.* By [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj), [Lem 640](#d-qiqth-spectraltheorem-cform-univ). $\square$

<small>Referenced in [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectraltheorem-reapplyinnerself-specproj"></a>
**Lemma 642** (`reApplyInnerSelf_specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L643)</small>

$$
(\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s).\mathrm{reApplyInnerSelf}\,x = \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,x
$$

*Proof.* By [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 613](#d-qiqth-spectraltheorem-bform-self), [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj). $\square$

<small>Referenced in [Lem 643](#d-qiqth-spectraltheorem-specproj-ispositive), [Lem 647](#d-qiqth-spectraltheorem-specproj-le-one), [Lem 648](#d-qiqth-spectraltheorem-norm-specproj-sq-le), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-specproj-ispositive"></a>
**Lemma 643** (`specProj_isPositive`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L654)</small>

$$
(\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s).\mathrm{IsPositive}
$$

*Proof.* By [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 604](#d-qiqth-spectraltheorem-qform-nonneg), [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj). $\square$

<small>Referenced in [Lem 648](#d-qiqth-spectraltheorem-norm-specproj-sq-le).</small>

<a id="d-qiqth-spectraltheorem-qform-union"></a>
**Lemma 644** (`qForm_union`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L661)</small>

$$
\mathrm{Disjoint}\,s\,t \to \mathrm{MeasurableSet}\,t \to \forall (z : H), \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,(s \cup t)\,z = \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,z + \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,t\,z
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure). $\square$

<small>Referenced in [Lem 645](#d-qiqth-spectraltheorem-cform-union-disjoint).</small>

<a id="d-qiqth-spectraltheorem-cform-union-disjoint"></a>
**Lemma 645** (`cForm_union_disjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L667)</small>

$$
\mathrm{Disjoint}\,s\,t \to \mathrm{MeasurableSet}\,t \to \forall (x y : H), \href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,(s \cup t)\,x\,y = \href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,s\,x\,y + \href{#d-qiqth-spectraltheorem-cform}{\mathrm{cForm}}\,T\,\mathrm{ha}\,t\,x\,y
$$

*Proof.* By [Def 603](#d-qiqth-spectraltheorem-qform), [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 644](#d-qiqth-spectraltheorem-qform-union). $\square$

<small>Referenced in [Lem 646](#d-qiqth-spectraltheorem-specproj-union-disjoint).</small>

<a id="d-qiqth-spectraltheorem-specproj-union-disjoint"></a>
**Lemma 646** (`specProj_union_disjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L677)</small>

$$
\mathrm{Disjoint}\,s\,t \to \mathrm{MeasurableSet}\,t \to \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(s \cup t) = \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s + \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,t
$$

*Proof.* By [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj), [Lem 645](#d-qiqth-spectraltheorem-cform-union-disjoint). $\square$

<small>Referenced in [Lem 649](#d-qiqth-spectraltheorem-specproj-finset-sum), [Lem 650](#d-qiqth-spectraltheorem-specproj-hassum).</small>

<a id="d-qiqth-spectraltheorem-specproj-le-one"></a>
**Lemma 647** (`specProj_le_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L687)</small>

$$
\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s \le 1
$$

*Proof.* By [Lem 599](#d-qiqth-spectraltheorem-specmeasure-real-le), [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj). $\square$

<small>Referenced in [Lem 648](#d-qiqth-spectraltheorem-norm-specproj-sq-le).</small>

<a id="d-qiqth-spectraltheorem-norm-specproj-sq-le"></a>
**Lemma 648** (`norm_specProj_sq_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L703)</small>

$$
{\|(\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,x\|}^{2} \le \href{#d-qiqth-spectraltheorem-qform}{\mathrm{qForm}}\,T\,\mathrm{ha}\,s\,x
$$

*Proof.* By [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [Lem 643](#d-qiqth-spectraltheorem-specproj-ispositive), [Lem 647](#d-qiqth-spectraltheorem-specproj-le-one). $\square$

<small>Referenced in [Lem 650](#d-qiqth-spectraltheorem-specproj-hassum).</small>

<a id="d-qiqth-spectraltheorem-specproj-finset-sum"></a>
**Lemma 649** (`specProj_finset_sum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L726)</small>

$$
(\forall (n : \mathbb{N}), \mathrm{MeasurableSet}\,(A\,n)) \to (\mathrm{Pairwise}\,\lambda m n \mapsto \mathrm{Disjoint}\,(A\,m)\,(A\,n)) \to \forall (F : \mathrm{Finset}\,\mathbb{N}), \sum_{n F} \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(A\,n) = \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(\bigcup n\in F, A\,n)
$$

*Proof.* By [Lem 591](#d-qiqth-spectraltheorem-specproj-congr-simp), [Lem 635](#d-qiqth-spectraltheorem-specproj-empty), [Lem 646](#d-qiqth-spectraltheorem-specproj-union-disjoint). $\square$

<small>Referenced in [Lem 650](#d-qiqth-spectraltheorem-specproj-hassum).</small>

<a id="d-qiqth-spectraltheorem-specproj-hassum"></a>
**Lemma 650** (`specProj_hasSum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L743)</small>

$$
(\forall (n : \mathbb{N}), \mathrm{MeasurableSet}\,(A\,n)) \to (\mathrm{Pairwise}\,\lambda m n \mapsto \mathrm{Disjoint}\,(A\,m)\,(A\,n)) \to \forall (x : H), \mathrm{HasSum}\,(\lambda n \mapsto (\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(A\,n))\,x)\,((\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(\bigcup n, A\,n))\,x)
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 646](#d-qiqth-spectraltheorem-specproj-union-disjoint), [Lem 648](#d-qiqth-spectraltheorem-norm-specproj-sq-le), [Lem 649](#d-qiqth-spectraltheorem-specproj-finset-sum). $\square$

<small>Referenced in [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint).</small>

<a id="d-qiqth-spectraltheorem-inner-cfchom-mul"></a>
**Lemma 651** (`inner_cfcHom_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L822)</small>

$$
\langle {((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x},{((\mathrm{cfcHom}\,\mathrm{ha})\,h)\,y}\rangle = \langle {x},{((\mathrm{cfcHom}\,\mathrm{ha})\,(g \cdot h))\,y}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 653](#d-qiqth-spectraltheorem-specmeasure-engine).</small>

<a id="d-qiqth-spectraltheorem-integral-specmeasure-cont"></a>
**Lemma 652** (`integral_specMeasure_cont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L834)</small>

$$
\int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), h\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z = \mathrm{re}\,(\langle {z},{((\mathrm{cfcHom}\,\mathrm{ha})\,h)\,z}\rangle)
$$

*Proof.* By [Lem 596](#d-qiqth-spectraltheorem-integral-specmeasure). $\square$

<small>Referenced in [Lem 653](#d-qiqth-spectraltheorem-specmeasure-engine), [Lem 660](#d-qiqth-spectraltheorem-integral-specmeasure-polarization).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-engine"></a>
**Lemma 653** (`specMeasure_engine`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L842)</small>

$$
\int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), h\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x + v) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), h\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x - v) = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), (h \cdot g)\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), (h \cdot g)\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)
$$

*Proof.* By [Lem 651](#d-qiqth-spectraltheorem-inner-cfchom-mul), [Lem 652](#d-qiqth-spectraltheorem-integral-specmeasure-cont). $\square$

<small>Referenced in [Lem 654](#d-qiqth-spectraltheorem-specmeasure-engine-measure).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-engine-measure"></a>
**Lemma 654** (`specMeasure_engine_measure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L862)</small>

$$
(\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), 0 \le g\,\omega) \to \forall (x v : H), (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x + v) + (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)).\mathrm{wd}\,\lambda \omega \mapsto {{g\,\omega}}) = \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x - v) + (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v)).\mathrm{wd}\,\lambda \omega \mapsto {{g\,\omega}}
$$

*Proof.* By [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Lem 653](#d-qiqth-spectraltheorem-specmeasure-engine). $\square$

<small>Referenced in [Lem 656](#d-qiqth-spectraltheorem-specmeasure-setengine-nonneg).</small>

<a id="d-qiqth-spectraltheorem-withdensity-real-setintegral"></a>
**Lemma 655** (`withDensity_real_setIntegral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L905)</small>

$$
(\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), 0 \le g\,\omega) \to \forall (z : H) \{s : \mathrm{Set}\,(\mathrm{sp}\,\mathbb{R}\,T)\}, \mathrm{MeasurableSet}\,s \to ((\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z).\mathrm{wd}\,\lambda \omega \mapsto {{g\,\omega}}).\mathrm{real}\,s = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,z
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 656](#d-qiqth-spectraltheorem-specmeasure-setengine-nonneg).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-setengine-nonneg"></a>
**Lemma 656** (`specMeasure_setEngine_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L915)</small>

$$
(\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), 0 \le g\,\omega) \to \forall (x v : H) \{s : \mathrm{Set}\,(\mathrm{sp}\,\mathbb{R}\,T)\}, \mathrm{MeasurableSet}\,s \to (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x + v)).\mathrm{real}\,s - (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x - v)).\mathrm{real}\,s = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)
$$

*Proof.* By [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Lem 654](#d-qiqth-spectraltheorem-specmeasure-engine-measure), [Lem 655](#d-qiqth-spectraltheorem-withdensity-real-setintegral). $\square$

<small>Referenced in [Lem 658](#d-qiqth-spectraltheorem-specmeasure-setengine).</small>

<a id="d-qiqth-spectraltheorem-bform-sub-left"></a>
**Lemma 657** (`bForm_sub_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L938)</small>

$$
\href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,(u - w)\,v = \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,u\,v - \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,w\,v
$$

*Proof.* By [Lem 614](#d-qiqth-spectraltheorem-bform-comm), [Lem 620](#d-qiqth-spectraltheorem-bform-sub-right). $\square$

<small>Referenced in [Lem 658](#d-qiqth-spectraltheorem-specmeasure-setengine).</small>

<a id="d-qiqth-spectraltheorem-specmeasure-setengine"></a>
**Lemma 658** (`specMeasure_setEngine`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L944)</small>

$$
\mathrm{MeasurableSet}\,s \to (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x + v)).\mathrm{real}\,s - (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(((\mathrm{cfcHom}\,\mathrm{ha})\,g)\,x - v)).\mathrm{real}\,s = \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)) in s, g\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)
$$

*Proof.* By [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Def 603](#d-qiqth-spectraltheorem-qform), [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 656](#d-qiqth-spectraltheorem-specmeasure-setengine-nonneg), [Lem 657](#d-qiqth-spectraltheorem-bform-sub-left). $\square$

<small>Referenced in [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure).</small>

<a id="d-qiqth-spectraltheorem-re-inner-cfchom-specproj"></a>
**Lemma 659** (`re_inner_cfcHom_specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L987)</small>

$$
\mathrm{re}\,(\langle {x},{((\mathrm{cfcHom}\,\mathrm{ha})\,h)\,((\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,v)}\rangle) = \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,s\,(((\mathrm{cfcHom}\,\mathrm{ha})\,h)\,x)\,v
$$

*Proof.* By [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj), [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint). $\square$

<small>Referenced in [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure).</small>

<a id="d-qiqth-spectraltheorem-integral-specmeasure-polarization"></a>
**Lemma 660** (`integral_specMeasure_polarization`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1005)</small>

$$
\int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), f\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(w + u) - \int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), f\,\omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(w - u) = 4 \cdot \mathrm{re}\,(\langle {w},{((\mathrm{cfcHom}\,\mathrm{ha})\,f)\,u}\rangle)
$$

*Proof.* By [Lem 652](#d-qiqth-spectraltheorem-integral-specmeasure-cont). $\square$

<small>Referenced in [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure).</small>

<a id="d-qiqth-spectraltheorem-specproj-engine-measure"></a>
**Lemma 661** (`specProj_engine_measure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1019)</small>

$$
\mathrm{MeasurableSet}\,s \to \forall (x v : H), \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + (\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,v) + (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - v)).\mathrm{restr}\,s = \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x - (\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,v) + (\href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,(x + v)).\mathrm{restr}\,s
$$

*Proof.* By [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Def 603](#d-qiqth-spectraltheorem-qform), [Def 611](#d-qiqth-spectraltheorem-bform), [Lem 658](#d-qiqth-spectraltheorem-specmeasure-setengine), [Lem 659](#d-qiqth-spectraltheorem-re-inner-cfchom-specproj), [Lem 660](#d-qiqth-spectraltheorem-integral-specmeasure-polarization). $\square$

<small>Referenced in [Lem 662](#d-qiqth-spectraltheorem-bform-specproj).</small>

<a id="d-qiqth-spectraltheorem-bform-specproj"></a>
**Lemma 662** (`bForm_specProj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1045)</small>

$$
\mathrm{MeasurableSet}\,s \to \mathrm{MeasurableSet}\,t \to \forall (x v : H), \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,t\,x\,((\href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s)\,v) = \href{#d-qiqth-spectraltheorem-bform}{\mathrm{bForm}}\,T\,\mathrm{ha}\,(s \cap t)\,x\,v
$$

*Proof.* By [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Def 603](#d-qiqth-spectraltheorem-qform), [Lem 661](#d-qiqth-spectraltheorem-specproj-engine-measure). $\square$

<small>Referenced in [Lem 663](#d-qiqth-spectraltheorem-specproj-inter).</small>

<a id="d-qiqth-spectraltheorem-specproj-inter"></a>
**Lemma 663** (`specProj_inter`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1057)</small>

$$
\mathrm{MeasurableSet}\,s \to \mathrm{MeasurableSet}\,t \to \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,(s \cap t) = \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,s \cdot \href{#d-qiqth-spectraltheorem-specproj}{E}\,T\,\mathrm{ha}\,t
$$

*Proof.* By [Def 611](#d-qiqth-spectraltheorem-bform), [Def 627](#d-qiqth-spectraltheorem-cform), [Lem 633](#d-qiqth-spectraltheorem-inner-specproj), [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint), [Lem 662](#d-qiqth-spectraltheorem-bform-specproj). $\square$

<small>Referenced in [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure).</small>

<a id="d-qiqth-spectraltheorem-pvm-of-selfadjoint"></a>
**Definition 664** (`PVM_of_selfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1073)</small>

A definition, built from [Lem 505](#d-qiqth-spectral-projectionvaluedmeasure) — see source for the body.

<small>Referenced in [Def 431](#d-qiqth-rvdspecmeasure), [Lem 440](#d-qiqth-deviceopc-norm-le), [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset), [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset), [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 667](#d-qiqth-spectraltheorem-inner-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Lem 669](#d-qiqth-spectraltheorem-borelfc-one), [Lem 670](#d-qiqth-spectraltheorem-borelfc-const), [Lem 671](#d-qiqth-spectraltheorem-borelfc-indicator), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 735](#d-qiqth-standardsubspacemodular-borelfc-adjoint), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [Lem 796](#d-qiqth-standardsubspacemodular-borelfc-add), [Lem 797](#d-qiqth-standardsubspacemodular-borelfc-smul), [Lem 801](#d-qiqth-standardsubspacemodular-cfccont-norm-le), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset), [Lem 840](#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset).</small>

<a id="d-qiqth-spectraltheorem-re-inner-t-eq-integral"></a>
**Lemma 665** (`re_inner_T_eq_integral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1090)</small>

$$
\int (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), \omega \partial \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x = \mathrm{re}\,(\langle {x},{T\,x}\rangle)
$$

*Proof.* By [Lem 596](#d-qiqth-spectraltheorem-integral-specmeasure). $\square$

<small>Referenced in [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord).</small>

<a id="d-qiqth-spectraltheorem-borelfc"></a>
**Definition 666** (`borelFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1110)</small>

A definition — see source for the body.

<small>Referenced in [Lem 422](#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Def 435](#d-qiqth-deviceopreal), [Def 436](#d-qiqth-deviceopc), [Lem 440](#d-qiqth-deviceopc-norm-le), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 445](#d-qiqth-borelfc-apply-norm-sq), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 455](#d-qiqth-deviceopc-sub), [Def 456](#d-qiqth-devicederivopc), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 667](#d-qiqth-spectraltheorem-inner-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Lem 669](#d-qiqth-spectraltheorem-borelfc-one), [Lem 670](#d-qiqth-spectraltheorem-borelfc-const), [Lem 671](#d-qiqth-spectraltheorem-borelfc-indicator), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 735](#d-qiqth-standardsubspacemodular-borelfc-adjoint), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 748](#d-qiqth-standardsubspacemodular-borelfc-comm), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 796](#d-qiqth-standardsubspacemodular-borelfc-add), [Lem 797](#d-qiqth-standardsubspacemodular-borelfc-smul), [Lem 798](#d-qiqth-standardsubspacemodular-borelfc-neg), [Lem 799](#d-qiqth-standardsubspacemodular-borelfc-sub), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 801](#d-qiqth-standardsubspacemodular-cfccont-norm-le), [Lem 802](#d-qiqth-standardsubspacemodular-cfccont-one), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Lem 804](#d-qiqth-standardsubspacemodular-cfccont-add), [Lem 805](#d-qiqth-standardsubspacemodular-cfccont-smul), [Lem 806](#d-qiqth-standardsubspacemodular-cfccont-star), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-spectraltheorem-inner-borelfc"></a>
**Lemma 667** (`inner_borelFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1116)</small>

$$
\langle {x},{(\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC})\,y}\rangle = (\href{#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,T\,\mathrm{ha}).\mathrm{bd}\,f\,x\,y
$$

*Proof.* By [Lem 557](#d-qiqth-spectral-projectionvaluedmeasure-inner-boundedfc). $\square$

<small>Referenced in [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 735](#d-qiqth-standardsubspacemodular-borelfc-adjoint), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc).</small>

<a id="d-qiqth-spectraltheorem-borelfc-mul"></a>
**Lemma 668** (`borelFC_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1122)</small>

$$
\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hfp}\,\mathrm{hC0p}\,\mathrm{hCp} = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf} \cdot \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg}
$$

*Proof.* By [Lem 588](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-mul), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Referenced in [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 748](#d-qiqth-standardsubspacemodular-borelfc-comm), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-spectraltheorem-borelfc-one"></a>
**Lemma 669** (`borelFC_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1130)</small>

$$
\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = 1
$$

*Proof.* By [Def 556](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [Lem 558](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Referenced in [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 802](#d-qiqth-standardsubspacemodular-cfccont-one).</small>

<a id="d-qiqth-spectraltheorem-borelfc-const"></a>
**Lemma 670** (`borelFC_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1137)</small>

$$
\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = c \cdot 1
$$

*Proof.* By [Lem 558](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-const), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Referenced in [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-spectraltheorem-borelfc-indicator"></a>
**Lemma 671** (`borelFC_indicator`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Spectral/SpectralTheorem.lean#L1143)</small>

$$
\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = (\href{#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,T\,\mathrm{ha}).E\,s
$$

*Proof.* By [Lem 573](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-indicator). $\square$

<small>Referenced in [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="sec-qiqth-standardsubspacemodular"></a>
## QIQTH.StandardSubspaceModular

<a id="d-qiqth-standardsubspacemodular-projk"></a>
**Definition 672** (`projK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L44)</small>

A definition — see source for the body.

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [Lem 295](#d-qiqth-fock-oneparticlebw-oneparticlebw-complete), [Lem 413](#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 419](#d-qiqth-standardsubspacemodular-gconstancy-xi-of-density), [Lem 420](#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare), [Lem 427](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k), [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 675](#d-qiqth-standardsubspacemodular-projk-idem), [Lem 677](#d-qiqth-standardsubspacemodular-rvdr-apply), [Lem 678](#d-qiqth-standardsubspacemodular-rvdr-inner-self), [Lem 679](#d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg), [Lem 680](#d-qiqth-standardsubspacemodular-norm-projk-apply-le), [Lem 682](#d-qiqth-standardsubspacemodular-rvdr-inner-self-le), [Lem 684](#d-qiqth-standardsubspacemodular-rvdr-eq-zero), [Lem 685](#d-qiqth-standardsubspacemodular-projk-isselfadjoint), [Lem 687](#d-qiqth-standardsubspacemodular-projik-smul-i), [Lem 688](#d-qiqth-standardsubspacemodular-projk-smul-i), [Lem 689](#d-qiqth-standardsubspacemodular-rvdr-smul-i), [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Lem 698](#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [Lem 699](#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero), [Lem 701](#d-qiqth-standardsubspacemodular-rvdr-le-two), [Lem 702](#d-qiqth-standardsubspacemodular-rvdpmq-smul-i), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 724](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr), [Lem 744](#d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq), [Lem 745](#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [Lem 746](#d-qiqth-standardsubspacemodular-modunitary-commute-projk-of), [Lem 747](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 791](#d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [Lem 793](#d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik), [Lem 794](#d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik), [Lem 795](#d-qiqth-standardsubspacemodular-eq-of-mem-k-of-inner-perp-ik), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs), [Lem 850](#d-qiqth-standardsubspacemodular-gausssmear-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-projik"></a>
**Definition 673** (`projIK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L48)</small>

A definition — see source for the body.

<small>Referenced in [Def 288](#d-qiqth-fock-oneparticlebw-comparisondatum), [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 420](#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare), [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 676](#d-qiqth-standardsubspacemodular-projik-idem), [Lem 677](#d-qiqth-standardsubspacemodular-rvdr-apply), [Lem 678](#d-qiqth-standardsubspacemodular-rvdr-inner-self), [Lem 679](#d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg), [Lem 681](#d-qiqth-standardsubspacemodular-norm-projik-apply-le), [Lem 682](#d-qiqth-standardsubspacemodular-rvdr-inner-self-le), [Lem 684](#d-qiqth-standardsubspacemodular-rvdr-eq-zero), [Lem 686](#d-qiqth-standardsubspacemodular-projik-isselfadjoint), [Lem 687](#d-qiqth-standardsubspacemodular-projik-smul-i), [Lem 688](#d-qiqth-standardsubspacemodular-projk-smul-i), [Lem 689](#d-qiqth-standardsubspacemodular-rvdr-smul-i), [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Lem 698](#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [Lem 699](#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero), [Lem 701](#d-qiqth-standardsubspacemodular-rvdr-le-two), [Lem 702](#d-qiqth-standardsubspacemodular-rvdpmq-smul-i), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 724](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr), [Lem 744](#d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 791](#d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [Lem 793](#d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik), [Lem 794](#d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik), [Lem 795](#d-qiqth-standardsubspacemodular-eq-of-mem-k-of-inner-perp-ik), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr"></a>
**Definition 674** (`rvdR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L52)</small>

A definition — see source for the body.

<small>Referenced in [Lem 677](#d-qiqth-standardsubspacemodular-rvdr-apply), [Lem 678](#d-qiqth-standardsubspacemodular-rvdr-inner-self), [Lem 679](#d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg), [Lem 682](#d-qiqth-standardsubspacemodular-rvdr-inner-self-le), [Lem 683](#d-qiqth-standardsubspacemodular-rvdr-inner-symm), [Lem 684](#d-qiqth-standardsubspacemodular-rvdr-eq-zero), [Lem 689](#d-qiqth-standardsubspacemodular-rvdr-smul-i), [Lem 691](#d-qiqth-standardsubspacemodular-rvdr-smul-complex), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 693](#d-qiqth-standardsubspacemodular-rvdrc-apply), [Lem 694](#d-qiqth-standardsubspacemodular-rvdrc-issymmetric), [Lem 695](#d-qiqth-standardsubspacemodular-rvdrc-ispositive), [Lem 699](#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero), [Lem 701](#d-qiqth-standardsubspacemodular-rvdr-le-two), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 705](#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric), [Lem 706](#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 724](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr), [Lem 725](#d-qiqth-standardsubspacemodular-rvdpmq-anticommute-rvdr-sub-one), [Lem 744](#d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq), [Lem 746](#d-qiqth-standardsubspacemodular-modunitary-commute-projk-of), [Lem 747](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute), [Lem 756](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdr), [Lem 780](#d-qiqth-standardsubspacemodular-rvdpmq-rvdrc), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [Lem 828](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs).</small>

<a id="d-qiqth-standardsubspacemodular-projk-idem"></a>
**Lemma 675** (`projK_idem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L55)</small>

$$
\mathrm{IsIdempotentElem}\,(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 724](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr).</small>

<a id="d-qiqth-standardsubspacemodular-projik-idem"></a>
**Lemma 676** (`projIK_idem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L59)</small>

$$
\mathrm{IsIdempotentElem}\,(\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 724](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr), [Lem 795](#d-qiqth-standardsubspacemodular-eq-of-mem-k-of-inner-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-apply"></a>
**Lemma 677** (`rvdR_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L63)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi = (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi + (\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,\xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 678](#d-qiqth-standardsubspacemodular-rvdr-inner-self), [Lem 689](#d-qiqth-standardsubspacemodular-rvdr-smul-i), [Lem 699](#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-inner-self"></a>
**Lemma 678** (`rvdR_inner_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L67)</small>

$$
\langle {(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi},{\xi}\rangle = {\|(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi\|}^{2} + {\|(\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,\xi\|}^{2}
$$

*Proof.* By [Lem 677](#d-qiqth-standardsubspacemodular-rvdr-apply). $\square$

<small>Referenced in [Lem 679](#d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg), [Lem 682](#d-qiqth-standardsubspacemodular-rvdr-inner-self-le), [Lem 684](#d-qiqth-standardsubspacemodular-rvdr-eq-zero).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg"></a>
**Lemma 679** (`rvdR_inner_self_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L80)</small>

$$
0 \le \langle {(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi},{\xi}\rangle
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 678](#d-qiqth-standardsubspacemodular-rvdr-inner-self). $\square$

<small>Referenced in [Lem 695](#d-qiqth-standardsubspacemodular-rvdrc-ispositive).</small>

<a id="d-qiqth-standardsubspacemodular-norm-projk-apply-le"></a>
**Lemma 680** (`norm_projK_apply_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L85)</small>

$$
\|(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi\| \le \|\xi\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 682](#d-qiqth-standardsubspacemodular-rvdr-inner-self-le).</small>

<a id="d-qiqth-standardsubspacemodular-norm-projik-apply-le"></a>
**Lemma 681** (`norm_projIK_apply_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L89)</small>

$$
\|(\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,\xi\| \le \|\xi\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 682](#d-qiqth-standardsubspacemodular-rvdr-inner-self-le).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-inner-self-le"></a>
**Lemma 682** (`rvdR_inner_self_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L93)</small>

$$
\langle {(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi},{\xi}\rangle \le 2 \cdot {\|\xi\|}^{2}
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 678](#d-qiqth-standardsubspacemodular-rvdr-inner-self), [Lem 680](#d-qiqth-standardsubspacemodular-norm-projk-apply-le), [Lem 681](#d-qiqth-standardsubspacemodular-norm-projik-apply-le). $\square$

<small>Referenced in [Lem 701](#d-qiqth-standardsubspacemodular-rvdr-le-two).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-inner-symm"></a>
**Lemma 683** (`rvdR_inner_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L106)</small>

$$
\langle {(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,x},{y}\rangle = \langle {x},{(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,y}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 694](#d-qiqth-standardsubspacemodular-rvdrc-issymmetric), [Lem 701](#d-qiqth-standardsubspacemodular-rvdr-le-two).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-eq-zero"></a>
**Lemma 684** (`rvdR_eq_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L117)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi = 0 \to \xi = 0
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 678](#d-qiqth-standardsubspacemodular-rvdr-inner-self). $\square$

<small>Referenced in [Lem 699](#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero).</small>

<a id="d-qiqth-standardsubspacemodular-projk-isselfadjoint"></a>
**Lemma 685** (`projK_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L166)</small>

$$
\mathrm{IsSelfAdjoint}\,(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 698](#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint).</small>

<a id="d-qiqth-standardsubspacemodular-projik-isselfadjoint"></a>
**Lemma 686** (`projIK_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L170)</small>

$$
\mathrm{IsSelfAdjoint}\,(\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 698](#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [Lem 794](#d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-projik-smul-i"></a>
**Lemma 687** (`projIK_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L223)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,(i \cdot \xi) = i \cdot (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 688](#d-qiqth-standardsubspacemodular-projk-smul-i), [Lem 689](#d-qiqth-standardsubspacemodular-rvdr-smul-i), [Lem 702](#d-qiqth-standardsubspacemodular-rvdpmq-smul-i), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i), [Lem 794](#d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-projk-smul-i"></a>
**Lemma 688** (`projK_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L244)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,(i \cdot \xi) = i \cdot (\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,\xi
$$

*Proof.* By [Lem 687](#d-qiqth-standardsubspacemodular-projik-smul-i). $\square$

<small>Referenced in [Lem 689](#d-qiqth-standardsubspacemodular-rvdr-smul-i), [Lem 702](#d-qiqth-standardsubspacemodular-rvdpmq-smul-i), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-smul-i"></a>
**Lemma 689** (`rvdR_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L255)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,(i \cdot \xi) = i \cdot (\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 677](#d-qiqth-standardsubspacemodular-rvdr-apply), [Lem 687](#d-qiqth-standardsubspacemodular-projik-smul-i), [Lem 688](#d-qiqth-standardsubspacemodular-projk-smul-i). $\square$

<small>Referenced in [Lem 691](#d-qiqth-standardsubspacemodular-rvdr-smul-complex), [Lem 694](#d-qiqth-standardsubspacemodular-rvdrc-issymmetric).</small>

<a id="d-qiqth-standardsubspacemodular-clm-eq-of-eqon-k"></a>
**Lemma 690** (`clm_eq_of_eqOn_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L263)</small>

$$
(\forall x\in S.\mathrm{cl}, A\,x = B\,x) \to A = B
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 420](#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-smul-complex"></a>
**Lemma 691** (`rvdR_smul_complex`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L288)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,(c \cdot x) = c \cdot (\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,x
$$

*Proof.* By [Lem 689](#d-qiqth-standardsubspacemodular-rvdr-smul-i). $\square$

<small>Referenced in [Def 692](#d-qiqth-standardsubspacemodular-rvdrc).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc"></a>
**Definition 692** (`rvdRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L310)</small>

A definition — see source for the body.

<small>Referenced in [Lem 422](#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Def 431](#d-qiqth-rvdspecmeasure), [Def 432](#d-qiqth-devspecreal), [Lem 433](#d-qiqth-devspecreal-measurable), [Lem 434](#d-qiqth-devspecreal-norm-le), [Def 435](#d-qiqth-deviceopreal), [Def 436](#d-qiqth-deviceopc), [Lem 440](#d-qiqth-deviceopc-norm-le), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 445](#d-qiqth-borelfc-apply-norm-sq), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset), [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset), [Lem 449](#d-qiqth-rvdspecmeasure-endpoints), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 451](#d-qiqth-devcharderiv-norm-le-slab), [Lem 452](#d-qiqth-devchar-slope-norm-le), [Lem 453](#d-qiqth-tendsto-devchar-slope), [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 455](#d-qiqth-deviceopc-sub), [Def 456](#d-qiqth-devicederivopc), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 458](#d-qiqth-hasderivat-devicevecf), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq), [Lem 472](#d-qiqth-devicevecf-continuouson), [Lem 693](#d-qiqth-standardsubspacemodular-rvdrc-apply), [Lem 694](#d-qiqth-standardsubspacemodular-rvdrc-issymmetric), [Lem 695](#d-qiqth-standardsubspacemodular-rvdrc-ispositive), [Lem 696](#d-qiqth-standardsubspacemodular-rvdrc-nonneg), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 705](#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric), [Def 708](#d-qiqth-standardsubspacemodular-rvdsqrtr), [Lem 710](#d-qiqth-standardsubspacemodular-rvdsqrtr-nonneg), [Lem 712](#d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self), [Lem 714](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc), [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 721](#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Def 749](#d-qiqth-standardsubspacemodular-speccoord), [Lem 750](#d-qiqth-standardsubspacemodular-speccoord-measurable), [Lem 751](#d-qiqth-standardsubspacemodular-speccoord-norm-le), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 756](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdr), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 779](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [Lem 780](#d-qiqth-standardsubspacemodular-rvdpmq-rvdrc), [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [Lem 782](#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [Lem 783](#d-qiqth-standardsubspacemodular-modconjsqrtr-sq), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 801](#d-qiqth-standardsubspacemodular-cfccont-norm-le), [Lem 802](#d-qiqth-standardsubspacemodular-cfccont-one), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Lem 804](#d-qiqth-standardsubspacemodular-cfccont-add), [Lem 805](#d-qiqth-standardsubspacemodular-cfccont-smul), [Lem 806](#d-qiqth-standardsubspacemodular-cfccont-star), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Def 808](#d-qiqth-standardsubspacemodular-cfccont), [Lem 809](#d-qiqth-standardsubspacemodular-cfccont-continuous), [Def 810](#d-qiqth-standardsubspacemodular-covm), [Lem 811](#d-qiqth-standardsubspacemodular-spectrum-subset-cov), [Def 812](#d-qiqth-standardsubspacemodular-incl), [Def 814](#d-qiqth-standardsubspacemodular-cfc), [Lem 815](#d-qiqth-standardsubspacemodular-cfc-one), [Lem 816](#d-qiqth-standardsubspacemodular-cfc-mul), [Lem 817](#d-qiqth-standardsubspacemodular-cfc-add), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul), [Lem 819](#d-qiqth-standardsubspacemodular-cfc-continuous), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 828](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 834](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint), [Lem 835](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective), [Lem 836](#d-qiqth-standardsubspacemodular-rvdrc-injective), [Lem 837](#d-qiqth-standardsubspacemodular-rvdtwosubrc-injective), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset), [Lem 840](#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset), [Lem 842](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs), [Lem 846](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-apply"></a>
**Lemma 693** (`rvdRC_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L317)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,x = (\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 695](#d-qiqth-standardsubspacemodular-rvdrc-ispositive), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-issymmetric"></a>
**Lemma 694** (`rvdRC_isSymmetric`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L327)</small>

$$
((\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)).\mathrm{IsSymmetric}
$$

*Proof.* By [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 683](#d-qiqth-standardsubspacemodular-rvdr-inner-symm), [Lem 689](#d-qiqth-standardsubspacemodular-rvdr-smul-i). $\square$

<small>Referenced in [Lem 695](#d-qiqth-standardsubspacemodular-rvdrc-ispositive), [Lem 705](#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-ispositive"></a>
**Lemma 695** (`rvdRC_isPositive`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L338)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S).\mathrm{IsPositive}
$$

*Proof.* By [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 679](#d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg), [Lem 693](#d-qiqth-standardsubspacemodular-rvdrc-apply), [Lem 694](#d-qiqth-standardsubspacemodular-rvdrc-issymmetric). $\square$

<small>Referenced in [Lem 696](#d-qiqth-standardsubspacemodular-rvdrc-nonneg).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-nonneg"></a>
**Lemma 696** (`rvdRC_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L347)</small>

$$
0 \le \href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S
$$

*Proof.* By [Lem 695](#d-qiqth-standardsubspacemodular-rvdrc-ispositive). $\square$

<small>Referenced in [Lem 712](#d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq"></a>
**Definition 697** (`rvdPmQ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L359)</small>

A definition — see source for the body.

<small>Referenced in [Lem 698](#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [Lem 699](#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero), [Lem 700](#d-qiqth-standardsubspacemodular-rvdpmq-injective), [Lem 702](#d-qiqth-standardsubspacemodular-rvdpmq-smul-i), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 721](#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 724](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr), [Lem 725](#d-qiqth-standardsubspacemodular-rvdpmq-anticommute-rvdr-sub-one), [Lem 726](#d-qiqth-standardsubspacemodular-rvdpmq-smul-conj), [Lem 744](#d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq), [Lem 746](#d-qiqth-standardsubspacemodular-modunitary-commute-projk-of), [Lem 747](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute), [Lem 757](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 764](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply), [Def 766](#d-qiqth-standardsubspacemodular-modconj), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 768](#d-qiqth-standardsubspacemodular-modconj-norm), [Lem 771](#d-qiqth-standardsubspacemodular-rvdpmq-real-inner-symm), [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i), [Lem 780](#d-qiqth-standardsubspacemodular-rvdpmq-rvdrc), [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [Lem 788](#d-qiqth-standardsubspacemodular-rvdt-modconj), [Lem 789](#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [Lem 828](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 835](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs), [Lem 844](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint"></a>
**Lemma 698** (`rvdPmQ_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L363)</small>

$$
\mathrm{IsSelfAdjoint}\,(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 685](#d-qiqth-standardsubspacemodular-projk-isselfadjoint), [Lem 686](#d-qiqth-standardsubspacemodular-projik-isselfadjoint). $\square$

<small>Referenced in [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-eq-zero"></a>
**Lemma 699** (`rvdPmQ_eq_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L367)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi = 0 \to \xi = 0
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 677](#d-qiqth-standardsubspacemodular-rvdr-apply), [Lem 684](#d-qiqth-standardsubspacemodular-rvdr-eq-zero). $\square$

<small>Referenced in [Lem 700](#d-qiqth-standardsubspacemodular-rvdpmq-injective).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-injective"></a>
**Lemma 700** (`rvdPmQ_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L387)</small>

$$
\mathrm{Injective}\,(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)
$$

*Proof.* By [Lem 699](#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero). $\square$

<small>Referenced in [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 835](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-le-two"></a>
**Lemma 701** (`rvdR_le_two`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L393)</small>

$$
(2 \cdot 1 - \href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S).\mathrm{IsPositive}
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 682](#d-qiqth-standardsubspacemodular-rvdr-inner-self-le), [Lem 683](#d-qiqth-standardsubspacemodular-rvdr-inner-symm). $\square$

<small>Referenced in [Lem 706](#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-smul-i"></a>
**Lemma 702** (`rvdPmQ_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L424)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,(i \cdot \xi) = -(i \cdot (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi)
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 687](#d-qiqth-standardsubspacemodular-projik-smul-i), [Lem 688](#d-qiqth-standardsubspacemodular-projk-smul-i). $\square$

<small>Referenced in [Lem 726](#d-qiqth-standardsubspacemodular-rvdpmq-smul-conj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc"></a>
**Definition 703** (`rvdTwoSubRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L444)</small>

A definition — see source for the body.

<small>Referenced in [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 705](#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric), [Lem 706](#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive), [Lem 707](#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg), [Def 709](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [Lem 711](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-nonneg), [Lem 713](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [Lem 714](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc), [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 721](#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 779](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [Lem 780](#d-qiqth-standardsubspacemodular-rvdpmq-rvdrc), [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [Lem 782](#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [Lem 783](#d-qiqth-standardsubspacemodular-modconjsqrtr-sq), [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 828](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 834](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint), [Lem 835](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective), [Lem 836](#d-qiqth-standardsubspacemodular-rvdrc-injective), [Lem 837](#d-qiqth-standardsubspacemodular-rvdtwosubrc-injective), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset), [Lem 842](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs), [Lem 846](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-apply"></a>
**Lemma 704** (`rvdTwoSubRC_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L449)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,x = 2 \cdot x - (\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,x
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik). $\square$

<small>Referenced in [Lem 705](#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [Lem 828](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric"></a>
**Lemma 705** (`rvdTwoSubRC_isSymmetric`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L453)</small>

$$
((\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)).\mathrm{IsSymmetric}
$$

*Proof.* By [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 694](#d-qiqth-standardsubspacemodular-rvdrc-issymmetric), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply). $\square$

<small>Referenced in [Lem 706](#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive"></a>
**Lemma 706** (`rvdTwoSubRC_isPositive`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L465)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S).\mathrm{IsPositive}
$$

*Proof.* By [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 701](#d-qiqth-standardsubspacemodular-rvdr-le-two), [Lem 705](#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric). $\square$

<small>Referenced in [Lem 707](#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg"></a>
**Lemma 707** (`rvdTwoSubRC_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L473)</small>

$$
0 \le \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S
$$

*Proof.* By [Lem 706](#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive). $\square$

<small>Referenced in [Lem 713](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr"></a>
**Definition 708** (`rvdSqrtR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L477)</small>

A definition — see source for the body.

<small>Referenced in [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 413](#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 419](#d-qiqth-standardsubspacemodular-gconstancy-xi-of-density), [Lem 424](#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [Lem 425](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq), [Lem 426](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed), [Lem 427](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k), [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 460](#d-qiqth-devicevecf-real-eq), [Lem 462](#d-qiqth-devicevecf-zero), [Lem 463](#d-qiqth-gfunction-zero), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 710](#d-qiqth-standardsubspacemodular-rvdsqrtr-nonneg), [Lem 712](#d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self), [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 718](#d-qiqth-standardsubspacemodular-rvdt-nonneg), [Lem 779](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [Lem 783](#d-qiqth-standardsubspacemodular-modconjsqrtr-sq), [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj), [Lem 785](#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [Lem 786](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr), [Lem 787](#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k), [Lem 846](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrttwosubr"></a>
**Definition 709** (`rvdSqrtTwoSubR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L480)</small>

A definition — see source for the body.

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Lem 424](#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 711](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-nonneg), [Lem 713](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 718](#d-qiqth-standardsubspacemodular-rvdt-nonneg), [Lem 779](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj), [Lem 785](#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [Lem 786](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr), [Lem 787](#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k), [Lem 846](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr-nonneg"></a>
**Lemma 710** (`rvdSqrtR_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L483)</small>

$$
0 \le \href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc). $\square$

<small>Referenced in [Lem 718](#d-qiqth-standardsubspacemodular-rvdt-nonneg), [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrttwosubr-nonneg"></a>
**Lemma 711** (`rvdSqrtTwoSubR_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L486)</small>

$$
0 \le \href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S
$$

*Proof.* By [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc). $\square$

<small>Referenced in [Lem 718](#d-qiqth-standardsubspacemodular-rvdt-nonneg).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self"></a>
**Lemma 712** (`rvdSqrtR_mul_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L489)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S = \href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S
$$

*Proof.* By [Lem 696](#d-qiqth-standardsubspacemodular-rvdrc-nonneg). $\square$

<small>Referenced in [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 783](#d-qiqth-standardsubspacemodular-modconjsqrtr-sq).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self"></a>
**Lemma 713** (`rvdSqrtTwoSubR_mul_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L493)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S = \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S
$$

*Proof.* By [Lem 707](#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg). $\square$

<small>Referenced in [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc"></a>
**Lemma 714** (`rvdRC_commute_rvdTwoSubRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L498)</small>

$$
\mathrm{Commute}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,(\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 779](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [Lem 834](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint), [Lem 836](#d-qiqth-standardsubspacemodular-rvdrc-injective).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr"></a>
**Lemma 715** (`rvdSqrtR_commute_rvdSqrtTwoSubR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L504)</small>

$$
\mathrm{Commute}\,(\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 714](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc). $\square$

<small>Referenced in [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 718](#d-qiqth-standardsubspacemodular-rvdt-nonneg), [Lem 787](#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt"></a>
**Definition 716** (`rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L513)</small>

A definition — see source for the body.

<small>Referenced in [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 718](#d-qiqth-standardsubspacemodular-rvdt-nonneg), [Lem 719](#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint), [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 764](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply), [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Def 766](#d-qiqth-standardsubspacemodular-modconj), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 768](#d-qiqth-standardsubspacemodular-modconj-norm), [Lem 770](#d-qiqth-standardsubspacemodular-rvdt-real-inner-symm), [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i), [Lem 779](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [Lem 787](#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [Lem 788](#d-qiqth-standardsubspacemodular-rvdt-modconj), [Lem 789](#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k), [Lem 846](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-sq"></a>
**Lemma 717** (`rvdT_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L516)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S = \href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S
$$

*Proof.* By [Def 708](#d-qiqth-standardsubspacemodular-rvdsqrtr), [Def 709](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [Lem 712](#d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self), [Lem 713](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr). $\square$

<small>Referenced in [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-nonneg"></a>
**Lemma 718** (`rvdT_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L533)</small>

$$
0 \le \href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S
$$

*Proof.* By [Def 708](#d-qiqth-standardsubspacemodular-rvdsqrtr), [Def 709](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [Lem 710](#d-qiqth-standardsubspacemodular-rvdsqrtr-nonneg), [Lem 711](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-nonneg), [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr). $\square$

<small>Referenced in [Lem 719](#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint), [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-isselfadjoint"></a>
**Lemma 719** (`rvdT_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L538)</small>

$$
\mathrm{IsSelfAdjoint}\,(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)
$$

*Proof.* By [Lem 718](#d-qiqth-standardsubspacemodular-rvdt-nonneg). $\square$

<small>Referenced in [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Lem 770](#d-qiqth-standardsubspacemodular-rvdt-real-inner-symm).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply"></a>
**Lemma 720** (`rvdRC_mul_rvdTwoSubRC_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L551)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi = (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi)
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 675](#d-qiqth-standardsubspacemodular-projk-idem), [Lem 676](#d-qiqth-standardsubspacemodular-projik-idem), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply). $\square$

<small>Referenced in [Lem 721](#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 835](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-commute-a"></a>
**Lemma 721** (`rvdPmQ_commute_A`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L567)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi)
$$

*Proof.* By [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply). $\square$

<small>Referenced in [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-injective"></a>
**Lemma 722** (`rvdT_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L575)</small>

$$
\mathrm{Injective}\,(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Lem 700](#d-qiqth-standardsubspacemodular-rvdpmq-injective), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply). $\square$

<small>Referenced in [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-norm-eq"></a>
**Lemma 723** (`rvdT_norm_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L607)</small>

$$
\|(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi\| = \|(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi\|
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 698](#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 719](#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply). $\square$

<small>Referenced in [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 768](#d-qiqth-standardsubspacemodular-modconj-norm).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr"></a>
**Lemma 724** (`rvdPmQ_mul_rvdR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L627)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S = (2 \cdot 1 - \href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S) \cdot \href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 675](#d-qiqth-standardsubspacemodular-projk-idem), [Lem 676](#d-qiqth-standardsubspacemodular-projik-idem). $\square$

<small>Referenced in [Lem 725](#d-qiqth-standardsubspacemodular-rvdpmq-anticommute-rvdr-sub-one), [Lem 828](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-anticommute-rvdr-sub-one"></a>
**Lemma 725** (`rvdPmQ_anticommute_rvdR_sub_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L645)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot (\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S - 1) = -((\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S - 1) \cdot \href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)
$$

*Proof.* By [Lem 724](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr). $\square$

<small>Referenced in [Lem 780](#d-qiqth-standardsubspacemodular-rvdpmq-rvdrc).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-smul-conj"></a>
**Lemma 726** (`rvdPmQ_smul_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L671)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,(c \cdot \xi) = (\mathrm{starRingEnd}\,\mathbb{C})\,c \cdot (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi
$$

*Proof.* By [Lem 702](#d-qiqth-standardsubspacemodular-rvdpmq-smul-i). $\square$

<small>Referenced in [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="sec-qiqth-standardsubspacemodularflow"></a>
## QIQTH.StandardSubspaceModularFlow

<a id="d-qiqth-standardsubspacemodular-modchar"></a>
**Definition 727** (`modChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L39)</small>

A definition — see source for the body.

<small>Referenced in [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 728](#d-qiqth-standardsubspacemodular-modchar-measurable), [Lem 729](#d-qiqth-standardsubspacemodular-modchar-norm), [Lem 730](#d-qiqth-standardsubspacemodular-modchar-zero), [Lem 731](#d-qiqth-standardsubspacemodular-modchar-add), [Lem 732](#d-qiqth-standardsubspacemodular-modchar-conj), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 830](#d-qiqth-standardsubspacemodular-modchar-reflect), [Def 831](#d-qiqth-standardsubspacemodular-h), [Lem 832](#d-qiqth-standardsubspacemodular-tw-h), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 871](#d-qiqth-standardsubspacemodular-modcharc-ofreal), [Lem 877](#d-qiqth-standardsubspacemodular-devchar-ofreal).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-measurable"></a>
**Lemma 728** (`modChar_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L47)</small>

$$
\mathrm{Measurable}\,(\href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-norm"></a>
**Lemma 729** (`modChar_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L54)</small>

$$
\|\href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r\| = 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-zero"></a>
**Lemma 730** (`modChar_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L63)</small>

$$
\href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,0\,r = 1
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-add"></a>
**Lemma 731** (`modChar_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L70)</small>

$$
\href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,(s + t)\,r = \href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,s\,r \cdot \href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-conj"></a>
**Lemma 732** (`modChar_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L81)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r) = \href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,(-t)\,r
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint).</small>

<a id="d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure"></a>
**Lemma 733** (`scalarMeasure_eq_specMeasure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L94)</small>

$$
(\href{#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,T\,\mathrm{ha}).\mu\,x = \href{#d-qiqth-spectraltheorem-specmeasure}{\mu_{\mathrm{sp}}}\,T\,\mathrm{ha}\,x
$$

*Proof.* By [Def 507](#d-qiqth-spectral-projectionvaluedmeasure-e), [Lem 516](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure-apply), [Lem 597](#d-qiqth-spectraltheorem-instisfinitemeasureelemrealspectrumcontinuouslinearmapcomplexidspecmeasure), [Def 603](#d-qiqth-spectraltheorem-qform), [Def 632](#d-qiqth-spectraltheorem-specproj), [Lem 637](#d-qiqth-spectraltheorem-specproj-isselfadjoint), [Lem 642](#d-qiqth-spectraltheorem-reapplyinnerself-specproj), [Lem 663](#d-qiqth-spectraltheorem-specproj-inter). $\square$

<small>Referenced in [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-congr"></a>
**Lemma 734** (`borelFC_congr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L127)</small>

$$
f = f^{\prime} \to \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}^{\prime}\,\mathrm{hCf0}^{\prime}\,\mathrm{hCf}^{\prime}
$$

*Proof.* By [Lem 568](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-congr), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Referenced in [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 748](#d-qiqth-standardsubspacemodular-borelfc-comm), [Lem 798](#d-qiqth-standardsubspacemodular-borelfc-neg), [Lem 802](#d-qiqth-standardsubspacemodular-cfccont-one), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Lem 804](#d-qiqth-standardsubspacemodular-cfccont-add), [Lem 805](#d-qiqth-standardsubspacemodular-cfccont-smul), [Lem 806](#d-qiqth-standardsubspacemodular-cfccont-star), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-adjoint"></a>
**Lemma 735** (`borelFC_adjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L134)</small>

$$
{{\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}}}^{\dagger} = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hcf}\,\mathrm{hC0}^{\prime}\,\mathrm{hcfb}
$$

*Proof.* By [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Lem 535](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag-conj-symm), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 667](#d-qiqth-spectraltheorem-inner-borelfc). $\square$

<small>Referenced in [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 806](#d-qiqth-standardsubspacemodular-cfccont-star).</small>

<a id="d-qiqth-standardsubspacemodular-modspecfun"></a>
**Definition 736** (`modSpecFun`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L147)</small>

A definition, built from [Def 692](#d-qiqth-standardsubspacemodular-rvdrc) — see source for the body.

<small>Referenced in [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-modspecfun-measurable"></a>
**Lemma 737** (`modSpecFun_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L151)</small>

$$
\mathrm{Measurable}\,(\href{#d-qiqth-standardsubspacemodular-modspecfun}{f_{\mathrm{mod}}}\,S\,t)
$$

*Proof.* By [Def 727](#d-qiqth-standardsubspacemodular-modchar), [Lem 728](#d-qiqth-standardsubspacemodular-modchar-measurable). $\square$

<small>Referenced in [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-modspecfun-norm-le"></a>
**Lemma 738** (`modSpecFun_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L154)</small>

$$
\|\href{#d-qiqth-standardsubspacemodular-modspecfun}{f_{\mathrm{mod}}}\,S\,t\,\omega\| \le 1
$$

*Proof.* By [Lem 729](#d-qiqth-standardsubspacemodular-modchar-norm). $\square$

<small>Referenced in [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint"></a>
**Lemma 739** (`rvdRC_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L157)</small>

$$
\mathrm{IsSelfAdjoint}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)
$$

*Proof.* By [Lem 696](#d-qiqth-standardsubspacemodular-rvdrc-nonneg). $\square$

<small>Referenced in [Lem 422](#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Def 431](#d-qiqth-rvdspecmeasure), [Def 435](#d-qiqth-deviceopreal), [Def 436](#d-qiqth-deviceopc), [Lem 440](#d-qiqth-deviceopc-norm-le), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 444](#d-qiqth-borelfc-inner-self), [Lem 445](#d-qiqth-borelfc-apply-norm-sq), [Lem 446](#d-qiqth-rvdspec-borelfc-diag), [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset), [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 455](#d-qiqth-deviceopc-sub), [Def 456](#d-qiqth-devicederivopc), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq), [Def 740](#d-qiqth-standardsubspacemodular-modunitary), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 752](#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 801](#d-qiqth-standardsubspacemodular-cfccont-norm-le), [Lem 802](#d-qiqth-standardsubspacemodular-cfccont-one), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Lem 804](#d-qiqth-standardsubspacemodular-cfccont-add), [Lem 805](#d-qiqth-standardsubspacemodular-cfccont-smul), [Lem 806](#d-qiqth-standardsubspacemodular-cfccont-star), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 834](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset), [Lem 840](#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary"></a>
**Definition 740** (`modUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L161)</small>

A definition — see source for the body.

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 195](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [Lem 199](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [Thm 221](#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [Lem 222](#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [Thm 224](#d-qiqth-fock-freefield-oneparticle-hflux), [Thm 225](#d-qiqth-fock-freefield-component-hflux), [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Def 288](#d-qiqth-fock-oneparticlebw-comparisondatum), [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [Def 290](#d-qiqth-fock-oneparticlebw-gconstancy), [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [Lem 295](#d-qiqth-fock-oneparticlebw-oneparticlebw-complete), [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 415](#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit), [Lem 416](#d-qiqth-standardsubspacemodular-gconstancy-real-smul), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 418](#d-qiqth-standardsubspacemodular-gconstancy-of-tendsto-xi), [Lem 419](#d-qiqth-standardsubspacemodular-gconstancy-xi-of-density), [Lem 420](#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare), [Lem 425](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq), [Lem 426](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed), [Lem 427](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k), [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 443](#d-qiqth-deviceopreal-eq), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 460](#d-qiqth-devicevecf-real-eq), [Lem 462](#d-qiqth-devicevecf-zero), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 466](#d-qiqth-devicevecf-bottom-eq), [Lem 467](#d-qiqth-modconj-devicevecf-bottom), [Lem 476](#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield), [Lem 741](#d-qiqth-standardsubspacemodular-modunitary-zero), [Lem 742](#d-qiqth-standardsubspacemodular-modunitary-add), [Lem 743](#d-qiqth-standardsubspacemodular-modunitary-adjoint), [Lem 746](#d-qiqth-standardsubspacemodular-modunitary-commute-projk-of), [Lem 747](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 756](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdr), [Lem 757](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs), [Lem 844](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq), [Lem 845](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [Lem 846](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-zero"></a>
**Lemma 741** (`modUnitary_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L166)</small>

$$
\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,0 = 1
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 669](#d-qiqth-spectraltheorem-borelfc-one), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 730](#d-qiqth-standardsubspacemodular-modchar-zero), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 462](#d-qiqth-devicevecf-zero).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-add"></a>
**Lemma 742** (`modUnitary_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L174)</small>

$$
\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,(s + t) = \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,s \cdot \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 731](#d-qiqth-standardsubspacemodular-modchar-add), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-adjoint"></a>
**Lemma 743** (`modUnitary_adjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L190)</small>

$$
{{\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t}}^{\dagger} = \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,(-t)
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 732](#d-qiqth-standardsubspacemodular-modchar-conj), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 735](#d-qiqth-standardsubspacemodular-borelfc-adjoint), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq"></a>
**Lemma 744** (`rvdR_add_rvdPmQ_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L317)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S + \href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S = 2 \cdot \href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S
$$

*Proof.* By [Def 673](#d-qiqth-standardsubspacemodular-projik). $\square$

<small>Referenced in [Lem 746](#d-qiqth-standardsubspacemodular-modunitary-commute-projk-of).</small>

<a id="d-qiqth-standardsubspacemodular-mem-k-iff-projk"></a>
**Lemma 745** (`mem_K_iff_projK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L323)</small>

$$
\xi \in S.\mathrm{cl} \leftrightarrow (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi = \xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 420](#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 747](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute), [Lem 850](#d-qiqth-standardsubspacemodular-gausssmear-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-projk-of"></a>
**Lemma 746** (`modUnitary_commute_projK_of`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L328)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi) \to (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi) \to (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)
$$

*Proof.* By [Lem 744](#d-qiqth-standardsubspacemodular-rvdr-add-rvdpmq-eq). $\square$

<small>Referenced in [Lem 747](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute"></a>
**Lemma 747** (`modUnitary_mapsTo_K_of_commute`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L340)</small>

$$
(\forall (\xi : H), (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)) \to (\forall (\xi : H), (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)) \to \forall \xi\in S.\mathrm{cl}, (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi \in S.\mathrm{cl}
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Lem 745](#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [Lem 746](#d-qiqth-standardsubspacemodular-modunitary-commute-projk-of). $\square$

<small>Referenced in [Lem 757](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-comm"></a>
**Lemma 748** (`borelFC_comm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L379)</small>

$$
(\mathrm{Measurable}\,\lambda \omega \mapsto f\,\omega \cdot g\,\omega) \to 0 \le \mathrm{Cfg} \to (\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), \|f\,\omega \cdot g\,\omega\| \le \mathrm{Cfg}) \to (\mathrm{Measurable}\,\lambda \omega \mapsto g\,\omega \cdot f\,\omega) \to 0 \le \mathrm{Cgf} \to (\forall (\omega : (\mathrm{sp}\,\mathbb{R}\,T)), \|g\,\omega \cdot f\,\omega\| \le \mathrm{Cgf}) \to \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf} \cdot \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg} = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg} \cdot \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf}
$$

*Proof.* By [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr). $\square$

<small>Referenced in [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc).</small>

<a id="d-qiqth-standardsubspacemodular-speccoord"></a>
**Definition 749** (`specCoord`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L392)</small>

A definition, built from [Def 692](#d-qiqth-standardsubspacemodular-rvdrc) — see source for the body.

<small>Referenced in [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 750](#d-qiqth-standardsubspacemodular-speccoord-measurable), [Lem 751](#d-qiqth-standardsubspacemodular-speccoord-norm-le), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-speccoord-measurable"></a>
**Lemma 750** (`specCoord_measurable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L396)</small>

$$
\mathrm{Measurable}\,(\href{#d-qiqth-standardsubspacemodular-speccoord}{\mathrm{sc}}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-speccoord-norm-le"></a>
**Lemma 751** (`specCoord_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L399)</small>

$$
\|\href{#d-qiqth-standardsubspacemodular-speccoord}{\mathrm{sc}}\,S\,\omega\| \le \|\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S\| \cdot \|1\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc"></a>
**Lemma 752** (`rvdRC_spectrum_mem_Icc`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L404)</small>

$$
\omega \in \mathrm{Icc}\,0\,2
$$

*Proof.* By [Lem 696](#d-qiqth-standardsubspacemodular-rvdrc-nonneg), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 706](#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive), [Lem 707](#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Lem 434](#d-qiqth-devspecreal-norm-le), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 451](#d-qiqth-devcharderiv-norm-le-slab), [Lem 452](#d-qiqth-devchar-slope-norm-le), [Lem 453](#d-qiqth-tendsto-devchar-slope), [Lem 455](#d-qiqth-deviceopc-sub), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq).</small>

<a id="d-qiqth-standardsubspacemodular-diagint-speccoord"></a>
**Lemma 753** (`diagInt_specCoord`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L425)</small>

$$
(\href{#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).\textstyle\int\,(\href{#d-qiqth-standardsubspacemodular-speccoord}{\mathrm{sc}}\,S)\,z = \langle {z},{(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,z}\rangle
$$

*Proof.* By [Def 515](#d-qiqth-spectral-projectionvaluedmeasure-scalarmeasure), [Def 595](#d-qiqth-spectraltheorem-specmeasure), [Lem 665](#d-qiqth-spectraltheorem-re-inner-t-eq-integral), [Lem 694](#d-qiqth-standardsubspacemodular-rvdrc-issymmetric), [Lem 733](#d-qiqth-standardsubspacemodular-scalarmeasure-eq-specmeasure). $\square$

<small>Referenced in [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc"></a>
**Lemma 754** (`rvdRC_eq_borelFC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L441)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\cdots \,\cdots \,\cdots
$$

*Proof.* By [Def 525](#d-qiqth-spectral-projectionvaluedmeasure-diagint), [Def 528](#d-qiqth-spectral-projectionvaluedmeasure-bilindiag), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Lem 667](#d-qiqth-spectraltheorem-inner-borelfc), [Lem 753](#d-qiqth-standardsubspacemodular-diagint-speccoord). $\square$

<small>Referenced in [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc"></a>
**Lemma 755** (`modUnitary_commute_rvdRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L463)</small>

$$
\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t \cdot \href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S = \href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 748](#d-qiqth-standardsubspacemodular-borelfc-comm), [Def 749](#d-qiqth-standardsubspacemodular-speccoord), [Lem 750](#d-qiqth-standardsubspacemodular-speccoord-measurable), [Lem 751](#d-qiqth-standardsubspacemodular-speccoord-norm-le), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc). $\square$

<small>Referenced in [Lem 756](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdr), [Lem 846](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdr"></a>
**Lemma 756** (`modUnitary_commute_rvdR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L482)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdr}{\mathrm{rvdR}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc). $\square$

<small>Referenced in [Lem 757](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d"></a>
**Lemma 757** (`modUnitary_mapsTo_K_of_commute_D`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L489)</small>

$$
(\forall (\xi : H), (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)) \to \forall \xi\in S.\mathrm{cl}, (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi \in S.\mathrm{cl}
$$

*Proof.* By [Lem 747](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute), [Lem 756](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdr). $\square$

<small>Referenced in [Lem 845](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k).</small>

<a id="d-qiqth-standardsubspacemodular-restrictscalars-star"></a>
**Lemma 758** (`restrictScalars_star`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L503)</small>

$$
\mathrm{res}\,\mathbb{R}\,({{Y}}^{*}) = {{\mathrm{res}\,\mathbb{R}\,Y}}^{*}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Lem 842](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange).</small>

<a id="d-qiqth-standardsubspacemodular-realcommutant"></a>
**Definition 759** (`realCommutant`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L512)</small>

A definition — see source for the body.

<small>Referenced in [Lem 760](#d-qiqth-standardsubspacemodular-realcommutant-isclosed), [Lem 761](#d-qiqth-standardsubspacemodular-commute-of-mem-elemental).</small>

<a id="d-qiqth-standardsubspacemodular-realcommutant-isclosed"></a>
**Lemma 760** (`realCommutant_isClosed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L540)</small>

$$
\mathrm{IsClosed}\,(\href{#d-qiqth-standardsubspacemodular-realcommutant}{\mathcal{M}{}'}\,D\,\mathrm{hD})
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 761](#d-qiqth-standardsubspacemodular-commute-of-mem-elemental).</small>

<a id="d-qiqth-standardsubspacemodular-commute-of-mem-elemental"></a>
**Lemma 761** (`commute_of_mem_elemental`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L557)</small>

$$
\mathrm{IsSelfAdjoint}\,D \to D \cdot \mathrm{res}\,\mathbb{R}\,B = \mathrm{res}\,\mathbb{R}\,B \cdot D \to \forall \{Y : H \to L[\mathbb{C}] H\}, Y \in \mathrm{elem}\,\mathbb{R}\,B \to D \cdot \mathrm{res}\,\mathbb{R}\,Y = \mathrm{res}\,\mathbb{R}\,Y \cdot D
$$

*Proof.* By [Def 759](#d-qiqth-standardsubspacemodular-realcommutant), [Lem 760](#d-qiqth-standardsubspacemodular-realcommutant-isclosed). $\square$

<small>Referenced in [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-sqrt-mem-elemental"></a>
**Lemma 762** (`sqrt_mem_elemental`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L565)</small>

$$
0 \le B \to \mathrm{sqrt}\,B \in \mathrm{elem}\,\mathbb{R}\,B
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt"></a>
**Lemma 763** (`rvdPmQ_commute_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L571)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S) = \mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S) \cdot \href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 696](#d-qiqth-standardsubspacemodular-rvdrc-nonneg), [Lem 698](#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 707](#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg), [Lem 714](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc), [Lem 717](#d-qiqth-standardsubspacemodular-rvdt-sq), [Lem 718](#d-qiqth-standardsubspacemodular-rvdt-nonneg), [Lem 721](#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [Lem 761](#d-qiqth-standardsubspacemodular-commute-of-mem-elemental), [Lem 762](#d-qiqth-standardsubspacemodular-sqrt-mem-elemental). $\square$

<small>Referenced in [Lem 764](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply"></a>
**Lemma 764** (`rvdPmQ_commute_rvdT_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L589)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi)
$$

*Proof.* By [Lem 763](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt). $\square$

<small>Referenced in [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange"></a>
**Lemma 765** (`rvdT_restrictScalars_denseRange`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L601)</small>

$$
\mathrm{DenseRange}\,(\mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S))
$$

*Proof.* By [Lem 719](#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint), [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 758](#d-qiqth-standardsubspacemodular-restrictscalars-star). $\square$

<small>Referenced in [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 768](#d-qiqth-standardsubspacemodular-modconj-norm), [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i), [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modconj"></a>
**Definition 766** (`modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L624)</small>

A definition — see source for the body.

<small>Referenced in [Def 290](#d-qiqth-fock-oneparticlebw-gconstancy), [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 415](#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit), [Lem 416](#d-qiqth-standardsubspacemodular-gconstancy-real-smul), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 418](#d-qiqth-standardsubspacemodular-gconstancy-of-tendsto-xi), [Lem 419](#d-qiqth-standardsubspacemodular-gconstancy-xi-of-density), [Lem 424](#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [Lem 425](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq), [Lem 426](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed), [Lem 427](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k), [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [Lem 463](#d-qiqth-gfunction-zero), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 467](#d-qiqth-modconj-devicevecf-bottom), [Lem 469](#d-qiqth-gfunction-norm-le), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 768](#d-qiqth-standardsubspacemodular-modconj-norm), [Lem 769](#d-qiqth-standardsubspacemodular-modconj-inner-map), [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i), [Lem 775](#d-qiqth-standardsubspacemodular-modconj-smul-conj), [Def 776](#d-qiqth-standardsubspacemodular-modconjbilin), [Lem 777](#d-qiqth-standardsubspacemodular-modconjbilin-apply), [Lem 778](#d-qiqth-standardsubspacemodular-modconj-inner-conj), [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [Lem 782](#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [Lem 783](#d-qiqth-standardsubspacemodular-modconjsqrtr-sq), [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj), [Lem 785](#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [Lem 786](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr), [Lem 787](#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [Lem 788](#d-qiqth-standardsubspacemodular-rvdt-modconj), [Lem 789](#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 791](#d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [Lem 793](#d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdt"></a>
**Lemma 767** (`modConj_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L628)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi
$$

*Proof.* By [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange). $\square$

<small>Referenced in [Lem 768](#d-qiqth-standardsubspacemodular-modconj-norm), [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i), [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect), [Lem 788](#d-qiqth-standardsubspacemodular-rvdt-modconj), [Lem 789](#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-norm"></a>
**Lemma 768** (`modConj_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L634)</small>

$$
\|(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta\| = \|\eta\|
$$

*Proof.* By [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 723](#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt). $\square$

<small>Referenced in [Lem 469](#d-qiqth-gfunction-norm-le), [Lem 769](#d-qiqth-standardsubspacemodular-modconj-inner-map).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-inner-map"></a>
**Lemma 769** (`modConj_inner_map`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L643)</small>

$$
\langle {(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta}\rangle = \langle {\eta},{\zeta}\rangle
$$

*Proof.* By [Lem 768](#d-qiqth-standardsubspacemodular-modconj-norm). $\square$

<small>Referenced in [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 778](#d-qiqth-standardsubspacemodular-modconj-inner-conj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-real-inner-symm"></a>
**Lemma 770** (`rvdT_real_inner_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L648)</small>

$$
\langle {(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,x},{y}\rangle = \langle {x},{(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,y}\rangle
$$

*Proof.* By [Lem 719](#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint). $\square$

<small>Referenced in [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-real-inner-symm"></a>
**Lemma 771** (`rvdPmQ_real_inner_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L659)</small>

$$
\langle {(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,x},{y}\rangle = \langle {x},{(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,y}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-isselfadjoint"></a>
**Lemma 772** (`modConj_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L665)</small>

$$
\langle {(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta},{\zeta}\rangle = \langle {\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta}\rangle
$$

*Proof.* By [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 764](#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply), [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 770](#d-qiqth-standardsubspacemodular-rvdt-real-inner-symm), [Lem 771](#d-qiqth-standardsubspacemodular-rvdpmq-real-inner-symm). $\square$

<small>Referenced in [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 778](#d-qiqth-standardsubspacemodular-modconj-inner-conj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-sq"></a>
**Lemma 773** (`modConj_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L688)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta) = \eta
$$

*Proof.* By [Lem 769](#d-qiqth-standardsubspacemodular-modconj-inner-map), [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint). $\square$

<small>Referenced in [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 424](#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [Lem 778](#d-qiqth-standardsubspacemodular-modconj-inner-conj), [Lem 782](#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [Lem 783](#d-qiqth-standardsubspacemodular-modconjsqrtr-sq), [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj), [Lem 785](#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [Lem 786](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr), [Lem 788](#d-qiqth-standardsubspacemodular-rvdt-modconj), [Lem 789](#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj), [Lem 791](#d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k), [Lem 793](#d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-smul-i"></a>
**Lemma 774** (`modConj_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L693)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(i \cdot \eta) = -i \cdot (\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Lem 687](#d-qiqth-standardsubspacemodular-projik-smul-i), [Lem 688](#d-qiqth-standardsubspacemodular-projk-smul-i), [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt). $\square$

<small>Referenced in [Lem 775](#d-qiqth-standardsubspacemodular-modconj-smul-conj), [Lem 778](#d-qiqth-standardsubspacemodular-modconj-inner-conj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-smul-conj"></a>
**Lemma 775** (`modConj_smul_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L730)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(c \cdot \eta) = (\mathrm{starRingEnd}\,\mathbb{C})\,c \cdot (\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta
$$

*Proof.* By [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i). $\square$

<small>Referenced in [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconjbilin"></a>
**Definition 776** (`modConjBilin`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L748)</small>

A definition — see source for the body.

<small>Referenced in [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 413](#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 461](#d-qiqth-differentiableon-gfunction), [Lem 463](#d-qiqth-gfunction-zero), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 469](#d-qiqth-gfunction-norm-le), [Lem 473](#d-qiqth-diffcontoncl-gfunction), [Lem 777](#d-qiqth-standardsubspacemodular-modconjbilin-apply).</small>

<a id="d-qiqth-standardsubspacemodular-modconjbilin-apply"></a>
**Lemma 777** (`modConjBilin_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L766)</small>

$$
((\href{#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,v)\,w = \langle {(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,v},{w}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 428](#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [Lem 463](#d-qiqth-gfunction-zero), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 469](#d-qiqth-gfunction-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-inner-conj"></a>
**Lemma 778** (`modConj_inner_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L777)</small>

$$
\langle {(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta},{(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta}\rangle = (\mathrm{starRingEnd}\,\mathbb{C})\,(\langle {\eta},{\zeta}\rangle)
$$

*Proof.* By [Lem 769](#d-qiqth-standardsubspacemodular-modconj-inner-map), [Lem 772](#d-qiqth-standardsubspacemodular-modconj-isselfadjoint), [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 774](#d-qiqth-standardsubspacemodular-modconj-smul-i). $\square$

<small>Referenced in [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt"></a>
**Lemma 779** (`rvdRC_commute_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L797)</small>

$$
\mathrm{Commute}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)
$$

*Proof.* By [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Def 708](#d-qiqth-standardsubspacemodular-rvdsqrtr), [Def 709](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [Lem 714](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc). $\square$

<small>Referenced in [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-rvdrc"></a>
**Lemma 780** (`rvdPmQ_rvdRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L806)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi)
$$

*Proof.* By [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 725](#d-qiqth-standardsubspacemodular-rvdpmq-anticommute-rvdr-sub-one). $\square$

<small>Referenced in [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect"></a>
**Lemma 781** (`modConj_rvdRC_reflect`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L820)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)
$$

*Proof.* By [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 779](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [Lem 780](#d-qiqth-standardsubspacemodular-rvdpmq-rvdrc). $\square$

<small>Referenced in [Lem 782](#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj"></a>
**Lemma 782** (`modConj_rvdRC_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L832)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi
$$

*Proof.* By [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 781](#d-qiqth-standardsubspacemodular-modconj-rvdrc-reflect). $\square$

<small>Referenced in [Lem 783](#d-qiqth-standardsubspacemodular-modconjsqrtr-sq), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconjsqrtr-sq"></a>
**Lemma 783** (`modConjSqrtR_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L838)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi))))) = (\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 712](#d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self), [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 782](#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj). $\square$

<small>Referenced in [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj"></a>
**Lemma 784** (`modConj_rvdSqrtR_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L848)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)\,\xi
$$

*Proof.* By [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 710](#d-qiqth-standardsubspacemodular-rvdsqrtr-nonneg), [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 775](#d-qiqth-standardsubspacemodular-modconj-smul-conj), [Lem 778](#d-qiqth-standardsubspacemodular-modconj-inner-conj), [Lem 783](#d-qiqth-standardsubspacemodular-modconjsqrtr-sq). $\square$

<small>Referenced in [Lem 785](#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [Lem 786](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj"></a>
**Lemma 785** (`modConj_rvdSqrtTwoSubR_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L891)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\xi
$$

*Proof.* By [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj). $\square$

<small>Referenced in [Lem 424](#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [Lem 787](#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdsqrtr"></a>
**Lemma 786** (`modConj_rvdSqrtR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L899)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,y) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,y)
$$

*Proof.* By [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 784](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj). $\square$

<small>Referenced in [Lem 787](#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [Lem 838](#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdt-modconj"></a>
**Lemma 787** (`modConj_rvdT_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L915)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,\xi
$$

*Proof.* By [Def 708](#d-qiqth-standardsubspacemodular-rvdsqrtr), [Def 709](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [Lem 785](#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj), [Lem 786](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr). $\square$

<small>Referenced in [Lem 788](#d-qiqth-standardsubspacemodular-rvdt-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-modconj"></a>
**Lemma 788** (`rvdT_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L926)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta) = (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\eta
$$

*Proof.* By [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 787](#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj). $\square$

<small>Referenced in [Lem 789](#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj"></a>
**Lemma 789** (`modConj_rvdPmQ_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L935)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi
$$

*Proof.* By [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 788](#d-qiqth-standardsubspacemodular-rvdt-modconj). $\square$

<small>Referenced in [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-projik-modconj"></a>
**Lemma 790** (`modConj_projIK_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L941)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = \xi - (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi
$$

*Proof.* By [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 677](#d-qiqth-standardsubspacemodular-rvdr-apply), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 693](#d-qiqth-standardsubspacemodular-rvdrc-apply), [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 782](#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [Lem 789](#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj). $\square$

<small>Referenced in [Lem 791](#d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-projik-modconj-eq-zero-of-mem-k"></a>
**Lemma 791** (`projIK_modConj_eq_zero_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L956)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,\xi = \xi \to (\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi) = 0
$$

*Proof.* By [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 790](#d-qiqth-standardsubspacemodular-modconj-projik-modconj). $\square$

<small>Referenced in [Lem 465](#d-qiqth-gfunction-top-edge-real).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-projk-modconj"></a>
**Lemma 792** (`modConj_projK_modConj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L967)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)) = \xi - (\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,\xi
$$

*Proof.* By [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 677](#d-qiqth-standardsubspacemodular-rvdr-apply), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 693](#d-qiqth-standardsubspacemodular-rvdrc-apply), [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 782](#d-qiqth-standardsubspacemodular-modconj-rvdrc-modconj), [Lem 789](#d-qiqth-standardsubspacemodular-modconj-rvdpmq-modconj). $\square$

<small>Referenced in [Lem 793](#d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik"></a>
**Lemma 793** (`projK_modConj_eq_self_of_perp_IK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L982)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,w = 0 \to (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,w) = (\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,w
$$

*Proof.* By [Lem 773](#d-qiqth-standardsubspacemodular-modconj-sq), [Lem 792](#d-qiqth-standardsubspacemodular-modconj-projk-modconj). $\square$

<small>Referenced in [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy).</small>

<a id="d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik"></a>
**Lemma 794** (`inner_real_of_mem_K_perp_IK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1056)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,x = x \to (\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,y = 0 \to (\langle {x},{y}\rangle).\mathrm{im} = 0
$$

*Proof.* By [Lem 686](#d-qiqth-standardsubspacemodular-projik-isselfadjoint), [Lem 687](#d-qiqth-standardsubspacemodular-projik-smul-i). $\square$

<small>Referenced in [Lem 465](#d-qiqth-gfunction-top-edge-real).</small>

<a id="d-qiqth-standardsubspacemodular-eq-of-mem-k-of-inner-perp-ik"></a>
**Lemma 795** (`eq_of_mem_K_of_inner_perp_IK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1073)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,a = a \to (\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,b = b \to (\forall (w : H), (\href{#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,w = 0 \to \langle {w},{a}\rangle = \langle {w},{b}\rangle) \to a = b
$$

*Proof.* By [Lem 676](#d-qiqth-standardsubspacemodular-projik-idem). $\square$

<small>Referenced in [Lem 420](#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-add"></a>
**Lemma 796** (`borelFC_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1110)</small>

$$
\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} + \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hCg0}\,\mathrm{hCg}
$$

*Proof.* By [Lem 563](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-add), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Referenced in [Lem 799](#d-qiqth-standardsubspacemodular-borelfc-sub), [Lem 804](#d-qiqth-standardsubspacemodular-cfccont-add).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-smul"></a>
**Lemma 797** (`borelFC_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1119)</small>

$$
\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = c \cdot \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}
$$

*Proof.* By [Lem 566](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-smul), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint). $\square$

<small>Referenced in [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 798](#d-qiqth-standardsubspacemodular-borelfc-neg), [Lem 805](#d-qiqth-standardsubspacemodular-cfccont-smul).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-neg"></a>
**Lemma 798** (`borelFC_neg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1127)</small>

$$
\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\mathrm{hC0}\,\cdots = -\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hC0}\,\mathrm{hC}
$$

*Proof.* By [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 797](#d-qiqth-standardsubspacemodular-borelfc-smul). $\square$

<small>Referenced in [Lem 799](#d-qiqth-standardsubspacemodular-borelfc-sub).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-sub"></a>
**Lemma 799** (`borelFC_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1137)</small>

$$
\href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\cdots \,\cdots \,\cdots = \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hf}\,\mathrm{hCf0}\,\mathrm{hCf} - \href{#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,T\,\mathrm{ha}\,\mathrm{hg}\,\mathrm{hCg0}\,\mathrm{hCg}
$$

*Proof.* By [Lem 796](#d-qiqth-standardsubspacemodular-borelfc-add), [Lem 798](#d-qiqth-standardsubspacemodular-borelfc-neg). $\square$

<small>Referenced in [Lem 455](#d-qiqth-deviceopc-sub), [Lem 457](#d-qiqth-deviceopc-slope-normsq).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont"></a>
**Definition 800** (`cfcCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1151)</small>

A definition, built from [Def 692](#d-qiqth-standardsubspacemodular-rvdrc) — see source for the body.

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 801](#d-qiqth-standardsubspacemodular-cfccont-norm-le), [Lem 802](#d-qiqth-standardsubspacemodular-cfccont-one), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Lem 804](#d-qiqth-standardsubspacemodular-cfccont-add), [Lem 805](#d-qiqth-standardsubspacemodular-cfccont-smul), [Lem 806](#d-qiqth-standardsubspacemodular-cfccont-star), [Lem 807](#d-qiqth-standardsubspacemodular-cfccont-coord), [Def 808](#d-qiqth-standardsubspacemodular-cfccont), [Lem 809](#d-qiqth-standardsubspacemodular-cfccont-continuous), [Def 814](#d-qiqth-standardsubspacemodular-cfc), [Lem 815](#d-qiqth-standardsubspacemodular-cfc-one), [Lem 816](#d-qiqth-standardsubspacemodular-cfc-mul), [Lem 817](#d-qiqth-standardsubspacemodular-cfc-add), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul), [Lem 819](#d-qiqth-standardsubspacemodular-cfc-continuous), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-norm-le"></a>
**Lemma 801** (`cfcCont_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1164)</small>

$$
\|\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f\| \le 2 \cdot \|f\|
$$

*Proof.* By [Def 556](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc), [Lem 567](#d-qiqth-spectral-projectionvaluedmeasure-boundedfc-norm-le), [Def 664](#d-qiqth-spectraltheorem-pvm-of-selfadjoint), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 809](#d-qiqth-standardsubspacemodular-cfccont-continuous).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-one"></a>
**Lemma 802** (`cfcCont_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1168)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,1 = 1
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 669](#d-qiqth-spectraltheorem-borelfc-one), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 815](#d-qiqth-standardsubspacemodular-cfc-one).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-mul"></a>
**Lemma 803** (`cfcCont_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1174)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,(f \cdot g) = \href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f \cdot \href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,g
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 816](#d-qiqth-standardsubspacemodular-cfc-mul).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-add"></a>
**Lemma 804** (`cfcCont_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1191)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,(f + g) = \href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f + \href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,g
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 796](#d-qiqth-standardsubspacemodular-borelfc-add). $\square$

<small>Referenced in [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Def 808](#d-qiqth-standardsubspacemodular-cfccont), [Lem 817](#d-qiqth-standardsubspacemodular-cfc-add).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-smul"></a>
**Lemma 805** (`cfcCont_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1205)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,(c \cdot f) = c \cdot \href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 797](#d-qiqth-standardsubspacemodular-borelfc-smul). $\square$

<small>Referenced in [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-star"></a>
**Lemma 806** (`cfcCont_star`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1217)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,({{f}}^{*}) = {{\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,f}}^{*}
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 735](#d-qiqth-standardsubspacemodular-borelfc-adjoint), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-coord"></a>
**Lemma 807** (`cfcCont_coord`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1226)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S\,\{\mathrm{toFun} :=\href{#d-qiqth-standardsubspacemodular-speccoord}{\mathrm{sc}}\,S , \mathrm{continuous\_toFun} :=\cdots \} = \href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Lem 750](#d-qiqth-standardsubspacemodular-speccoord-measurable), [Lem 751](#d-qiqth-standardsubspacemodular-speccoord-norm-le), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc). $\square$

<small>Referenced in [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 442](#d-qiqth-cfccont-sqrttwosub-eq).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont"></a>
**Definition 808** (`cfcContₗ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1233)</small>

A definition, built from [Def 692](#d-qiqth-standardsubspacemodular-rvdrc) — see source for the body.

<small>Referenced in [Lem 809](#d-qiqth-standardsubspacemodular-cfccont-continuous).</small>

<a id="d-qiqth-standardsubspacemodular-cfccont-continuous"></a>
**Lemma 809** (`cfcCont_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1239)</small>

$$
\mathrm{Continuous}\,(\href{#d-qiqth-standardsubspacemodular-cfccont}{\Phi_{c}}\,S)
$$

*Proof.* By [Lem 801](#d-qiqth-standardsubspacemodular-cfccont-norm-le), [Def 808](#d-qiqth-standardsubspacemodular-cfccont). $\square$

<small>Referenced in [Lem 819](#d-qiqth-standardsubspacemodular-cfc-continuous).</small>

<a id="d-qiqth-standardsubspacemodular-covm"></a>
**Definition 810** (`covM`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1249)</small>

A definition — see source for the body.

<small>Referenced in [Lem 811](#d-qiqth-standardsubspacemodular-spectrum-subset-cov), [Def 812](#d-qiqth-standardsubspacemodular-incl), [Def 813](#d-qiqth-standardsubspacemodular-tau), [Def 814](#d-qiqth-standardsubspacemodular-cfc), [Lem 815](#d-qiqth-standardsubspacemodular-cfc-one), [Lem 816](#d-qiqth-standardsubspacemodular-cfc-mul), [Lem 817](#d-qiqth-standardsubspacemodular-cfc-add), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul), [Lem 819](#d-qiqth-standardsubspacemodular-cfc-continuous), [Def 820](#d-qiqth-standardsubspacemodular-coord), [Lem 821](#d-qiqth-standardsubspacemodular-coord-star), [Def 822](#d-qiqth-standardsubspacemodular-tw), [Lem 823](#d-qiqth-standardsubspacemodular-tw-add), [Lem 824](#d-qiqth-standardsubspacemodular-tw-mul), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 826](#d-qiqth-standardsubspacemodular-cfc-sub), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Def 831](#d-qiqth-standardsubspacemodular-h), [Lem 832](#d-qiqth-standardsubspacemodular-tw-h), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-spectrum-subset-cov"></a>
**Lemma 811** (`spectrum_subset_covΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1254)</small>

$$
\mathrm{sp}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S) \subseteq \mathrm{Icc}\,(-\href{#d-qiqth-standardsubspacemodular-covm}{\mathrm{covM}}\,S)\,(2 + \href{#d-qiqth-standardsubspacemodular-covm}{\mathrm{covM}}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Def 812](#d-qiqth-standardsubspacemodular-incl).</small>

<a id="d-qiqth-standardsubspacemodular-incl"></a>
**Definition 812** (`inclΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1262)</small>

A definition, built from [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 810](#d-qiqth-standardsubspacemodular-covm) — see source for the body.

<small>Referenced in [Def 814](#d-qiqth-standardsubspacemodular-cfc), [Lem 815](#d-qiqth-standardsubspacemodular-cfc-one), [Lem 816](#d-qiqth-standardsubspacemodular-cfc-mul), [Lem 817](#d-qiqth-standardsubspacemodular-cfc-add), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul), [Lem 819](#d-qiqth-standardsubspacemodular-cfc-continuous), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-tau"></a>
**Definition 813** (`tauΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1267)</small>

A definition, built from [Def 810](#d-qiqth-standardsubspacemodular-covm) — see source for the body.

<small>Referenced in [Def 822](#d-qiqth-standardsubspacemodular-tw), [Lem 823](#d-qiqth-standardsubspacemodular-tw-add), [Lem 824](#d-qiqth-standardsubspacemodular-tw-mul), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-cfc"></a>
**Definition 814** (`cfcΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1273)</small>

A definition, built from [Def 810](#d-qiqth-standardsubspacemodular-covm) — see source for the body.

<small>Referenced in [Lem 815](#d-qiqth-standardsubspacemodular-cfc-one), [Lem 816](#d-qiqth-standardsubspacemodular-cfc-mul), [Lem 817](#d-qiqth-standardsubspacemodular-cfc-add), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul), [Lem 819](#d-qiqth-standardsubspacemodular-cfc-continuous), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 826](#d-qiqth-standardsubspacemodular-cfc-sub), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-one"></a>
**Lemma 815** (`cfcΩ_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1277)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,1 = 1
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 802](#d-qiqth-standardsubspacemodular-cfccont-one), [Def 812](#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Referenced in [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-mul"></a>
**Lemma 816** (`cfcΩ_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1280)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(f \cdot g) = \href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f \cdot \href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,g
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 803](#d-qiqth-standardsubspacemodular-cfccont-mul), [Def 812](#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Referenced in [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-add"></a>
**Lemma 817** (`cfcΩ_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1284)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(f + g) = \href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f + \href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,g
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 804](#d-qiqth-standardsubspacemodular-cfccont-add), [Def 812](#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Referenced in [Lem 826](#d-qiqth-standardsubspacemodular-cfc-sub), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-smul"></a>
**Lemma 818** (`cfcΩ_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1288)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(c \cdot f) = c \cdot \href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 805](#d-qiqth-standardsubspacemodular-cfccont-smul), [Def 812](#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Referenced in [Lem 826](#d-qiqth-standardsubspacemodular-cfc-sub), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-continuous"></a>
**Lemma 819** (`cfcΩ_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1297)</small>

$$
\mathrm{Continuous}\,(\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S)
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Lem 809](#d-qiqth-standardsubspacemodular-cfccont-continuous), [Def 812](#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Referenced in [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-coord"></a>
**Definition 820** (`coordΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1302)</small>

A definition, built from [Def 810](#d-qiqth-standardsubspacemodular-covm) — see source for the body.

<small>Referenced in [Lem 821](#d-qiqth-standardsubspacemodular-coord-star), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-coord-star"></a>
**Lemma 821** (`coordΩ_star`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1307)</small>

$$
{{\href{#d-qiqth-standardsubspacemodular-coord}{\mathrm{coord}}\,S}}^{*} = \href{#d-qiqth-standardsubspacemodular-coord}{\mathrm{coord}}\,S
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-tw"></a>
**Definition 822** (`twΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1310)</small>

A definition, built from [Def 810](#d-qiqth-standardsubspacemodular-covm) — see source for the body.

<small>Referenced in [Lem 823](#d-qiqth-standardsubspacemodular-tw-add), [Lem 824](#d-qiqth-standardsubspacemodular-tw-mul), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 832](#d-qiqth-standardsubspacemodular-tw-h), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-tw-add"></a>
**Lemma 823** (`twΩ_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1314)</small>

$$
\href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,(f + g) = \href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,f + \href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,g
$$

*Proof.* By [Def 813](#d-qiqth-standardsubspacemodular-tau). $\square$

<small>Referenced in [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-tw-mul"></a>
**Lemma 824** (`twΩ_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1318)</small>

$$
\href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,(f \cdot g) = \href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,f \cdot \href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,g
$$

*Proof.* By [Def 813](#d-qiqth-standardsubspacemodular-tau). $\square$

<small>Referenced in [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-coord"></a>
**Lemma 825** (`cfcΩ_coordΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1322)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(\href{#d-qiqth-standardsubspacemodular-coord}{\mathrm{coord}}\,S) = \href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Def 749](#d-qiqth-standardsubspacemodular-speccoord), [Lem 750](#d-qiqth-standardsubspacemodular-speccoord-measurable), [Lem 751](#d-qiqth-standardsubspacemodular-speccoord-norm-le), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Def 810](#d-qiqth-standardsubspacemodular-covm), [Def 812](#d-qiqth-standardsubspacemodular-incl). $\square$

<small>Referenced in [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-sub"></a>
**Lemma 826** (`cfcΩ_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1327)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(f - g) = \href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f - \href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,g
$$

*Proof.* By [Lem 817](#d-qiqth-standardsubspacemodular-cfc-add), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul). $\square$

<small>Referenced in [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-tw-coord"></a>
**Lemma 827** (`cfcΩ_twΩ_coordΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1331)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(\href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,(\href{#d-qiqth-standardsubspacemodular-coord}{\mathrm{coord}}\,S)) = \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 810](#d-qiqth-standardsubspacemodular-covm), [Lem 815](#d-qiqth-standardsubspacemodular-cfc-one), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 826](#d-qiqth-standardsubspacemodular-cfc-sub). $\square$

<small>Referenced in [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs"></a>
**Lemma 828** (`rvdPmQ_mul_rvdRC_rs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1338)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S) = \mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S) \cdot \href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [Def 674](#d-qiqth-standardsubspacemodular-rvdr), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 724](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr). $\square$

<small>Referenced in [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-intertwine"></a>
**Lemma 829** (`cfcΩ_intertwine`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1348)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,f) = \mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(\href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,f)) \cdot \href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 726](#d-qiqth-standardsubspacemodular-rvdpmq-smul-conj), [Def 813](#d-qiqth-standardsubspacemodular-tau), [Lem 815](#d-qiqth-standardsubspacemodular-cfc-one), [Lem 816](#d-qiqth-standardsubspacemodular-cfc-mul), [Lem 817](#d-qiqth-standardsubspacemodular-cfc-add), [Lem 818](#d-qiqth-standardsubspacemodular-cfc-smul), [Lem 819](#d-qiqth-standardsubspacemodular-cfc-continuous), [Def 820](#d-qiqth-standardsubspacemodular-coord), [Lem 821](#d-qiqth-standardsubspacemodular-coord-star), [Lem 823](#d-qiqth-standardsubspacemodular-tw-add), [Lem 824](#d-qiqth-standardsubspacemodular-tw-mul), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord), [Lem 828](#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs). $\square$

<small>Referenced in [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-modchar-reflect"></a>
**Lemma 830** (`modChar_reflect`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1581)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,(2 - r)) = \href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 832](#d-qiqth-standardsubspacemodular-tw-h).</small>

<a id="d-qiqth-standardsubspacemodular-h"></a>
**Definition 831** (`hΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1597)</small>

A definition, built from [Def 810](#d-qiqth-standardsubspacemodular-covm) — see source for the body.

<small>Referenced in [Lem 832](#d-qiqth-standardsubspacemodular-tw-h), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-tw-h"></a>
**Lemma 832** (`twΩ_hΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1602)</small>

$$
\href{#d-qiqth-standardsubspacemodular-tw}{\mathrm{tw}}\,S\,(\href{#d-qiqth-standardsubspacemodular-h}{\mathrm{h}}\,S\,t) = \href{#d-qiqth-standardsubspacemodular-h}{\mathrm{h}}\,S\,t
$$

*Proof.* By [Def 727](#d-qiqth-standardsubspacemodular-modchar), [Lem 830](#d-qiqth-standardsubspacemodular-modchar-reflect). $\square$

<small>Referenced in [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-cfc-h"></a>
**Lemma 833** (`cfcΩ_hΩ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1613)</small>

$$
\href{#d-qiqth-standardsubspacemodular-cfc}{\mathrm{cfc}}\,S\,(\href{#d-qiqth-standardsubspacemodular-h}{\mathrm{h}}\,S\,t) = \href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t \cdot (\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* By [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Def 727](#d-qiqth-standardsubspacemodular-modchar), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Def 736](#d-qiqth-standardsubspacemodular-modspecfun), [Lem 737](#d-qiqth-standardsubspacemodular-modspecfun-measurable), [Lem 738](#d-qiqth-standardsubspacemodular-modspecfun-norm-le), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [Def 800](#d-qiqth-standardsubspacemodular-cfccont), [Def 810](#d-qiqth-standardsubspacemodular-covm), [Def 812](#d-qiqth-standardsubspacemodular-incl), [Def 813](#d-qiqth-standardsubspacemodular-tau), [Lem 816](#d-qiqth-standardsubspacemodular-cfc-mul), [Def 820](#d-qiqth-standardsubspacemodular-coord), [Def 822](#d-qiqth-standardsubspacemodular-tw), [Lem 825](#d-qiqth-standardsubspacemodular-cfc-coord), [Lem 827](#d-qiqth-standardsubspacemodular-cfc-tw-coord). $\square$

<small>Referenced in [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint"></a>
**Lemma 834** (`rvdRC_mul_rvdTwoSubRC_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1650)</small>

$$
\mathrm{IsSelfAdjoint}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* By [Lem 714](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc), [Lem 739](#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint). $\square$

<small>Referenced in [Lem 842](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective"></a>
**Lemma 835** (`rvdRC_mul_rvdTwoSubRC_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1660)</small>

$$
\mathrm{Injective}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* By [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Lem 700](#d-qiqth-standardsubspacemodular-rvdpmq-injective), [Lem 720](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply). $\square$

<small>Referenced in [Lem 836](#d-qiqth-standardsubspacemodular-rvdrc-injective), [Lem 837](#d-qiqth-standardsubspacemodular-rvdtwosubrc-injective), [Lem 842](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-injective"></a>
**Lemma 836** (`rvdRC_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1667)</small>

$$
\mathrm{Injective}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)
$$

*Proof.* By [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 714](#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc), [Lem 835](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective). $\square$

<small>Referenced in [Lem 840](#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-injective"></a>
**Lemma 837** (`rvdTwoSubRC_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1677)</small>

$$
\mathrm{Injective}\,(\href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Lem 835](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective). $\square$

<small>Referenced in [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k"></a>
**Lemma 838** (`modConj_fixed_of_sqrtR_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1718)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to (\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta = \zeta
$$

*Proof.* By [Def 709](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [Lem 715](#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 722](#d-qiqth-standardsubspacemodular-rvdt-injective), [Lem 786](#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr). $\square$

<small>Referenced in [Lem 427](#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset"></a>
**Lemma 839** (`rvdRC_mul_E_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1733)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot (\href{#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).E\,\{\omega|\omega = c\} = c \cdot (\href{#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).E\,\{\omega|\omega = c\}
$$

*Proof.* By [Lem 569](#d-qiqth-spectral-projectionvaluedmeasure-norm-indicatorone-le), [Def 666](#d-qiqth-spectraltheorem-borelfc), [Lem 668](#d-qiqth-spectraltheorem-borelfc-mul), [Lem 670](#d-qiqth-spectraltheorem-borelfc-const), [Lem 671](#d-qiqth-spectraltheorem-borelfc-indicator), [Lem 734](#d-qiqth-standardsubspacemodular-borelfc-congr), [Def 749](#d-qiqth-standardsubspacemodular-speccoord), [Lem 750](#d-qiqth-standardsubspacemodular-speccoord-measurable), [Lem 751](#d-qiqth-standardsubspacemodular-speccoord-norm-le), [Lem 754](#d-qiqth-standardsubspacemodular-rvdrc-eq-borelfc). $\square$

<small>Referenced in [Lem 840](#d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset), [Lem 841](#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-e-zero-levelset"></a>
**Lemma 840** (`rvdRC_E_zero_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1780)</small>

$$
(\href{#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).E\,\{\omega|\omega = 0\} = 0
$$

*Proof.* By [Lem 836](#d-qiqth-standardsubspacemodular-rvdrc-injective), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset). $\square$

<small>Referenced in [Lem 447](#d-qiqth-rvdspecmeasure-zero-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset"></a>
**Lemma 841** (`rvdRC_E_two_levelSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1794)</small>

$$
(\href{#d-qiqth-spectraltheorem-pvm-of-selfadjoint}{\mathrm{PVM\_of\_selfAdjoint}}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots ).E\,\{\omega|\omega = 2\} = 0
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 837](#d-qiqth-standardsubspacemodular-rvdtwosubrc-injective), [Lem 839](#d-qiqth-standardsubspacemodular-rvdrc-mul-e-levelset). $\square$

<small>Referenced in [Lem 448](#d-qiqth-rvdspecmeasure-two-levelset).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange"></a>
**Lemma 842** (`rvdRC_mul_rvdTwoSubRC_denseRange`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1813)</small>

$$
\mathrm{DenseRange}\,(\mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S \cdot \href{#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S))
$$

*Proof.* By [Lem 758](#d-qiqth-standardsubspacemodular-restrictscalars-star), [Lem 834](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint), [Lem 835](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective). $\square$

<small>Referenced in [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs"></a>
**Lemma 843** (`modUnitary_commute_rvdPmQ_rs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1830)</small>

$$
\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S \cdot \mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t) = \mathrm{res}\,\mathbb{R}\,(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t) \cdot \href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Def 673](#d-qiqth-standardsubspacemodular-projik), [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Lem 704](#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [Lem 721](#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [Def 810](#d-qiqth-standardsubspacemodular-covm), [Def 814](#d-qiqth-standardsubspacemodular-cfc), [Def 822](#d-qiqth-standardsubspacemodular-tw), [Lem 829](#d-qiqth-standardsubspacemodular-cfc-intertwine), [Def 831](#d-qiqth-standardsubspacemodular-h), [Lem 832](#d-qiqth-standardsubspacemodular-tw-h), [Lem 833](#d-qiqth-standardsubspacemodular-cfc-h), [Lem 842](#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-denserange). $\square$

<small>Referenced in [Lem 844](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq"></a>
**Lemma 844** (`modUnitary_commute_rvdPmQ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1851)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,\xi) = (\href{#d-qiqth-standardsubspacemodular-rvdpmq}{\mathrm{rvdPmQ}}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi)
$$

*Proof.* By [Lem 843](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs). $\square$

<small>Referenced in [Lem 845](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-mapsto-k"></a>
**Lemma 845** (`modUnitary_mapsTo_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1858)</small>

$$
\forall \xi\in S.\mathrm{cl}, (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi \in S.\mathrm{cl}
$$

*Proof.* By [Lem 757](#d-qiqth-standardsubspacemodular-modunitary-mapsto-k-of-commute-d), [Lem 844](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq). $\square$

<small>Referenced in [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 289](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 465](#d-qiqth-gfunction-top-edge-real).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-commute-rvdt"></a>
**Lemma 846** (`modUnitary_commute_rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1866)</small>

$$
\mathrm{Commute}\,(\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,(\href{#d-qiqth-standardsubspacemodular-rvdt}{\mathrm{rvdT}}\,S)
$$

*Proof.* By [Def 692](#d-qiqth-standardsubspacemodular-rvdrc), [Def 703](#d-qiqth-standardsubspacemodular-rvdtwosubrc), [Def 708](#d-qiqth-standardsubspacemodular-rvdsqrtr), [Def 709](#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [Lem 755](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdrc). $\square$

<small>Referenced in [Lem 847](#d-qiqth-standardsubspacemodular-modconj-commute-modunitary).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-commute-modunitary"></a>
**Lemma 847** (`modConj_commute_modUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1879)</small>

$$
(\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\eta) = (\href{#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\eta)
$$

*Proof.* By [Def 697](#d-qiqth-standardsubspacemodular-rvdpmq), [Def 716](#d-qiqth-standardsubspacemodular-rvdt), [Lem 765](#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [Lem 767](#d-qiqth-standardsubspacemodular-modconj-rvdt), [Lem 844](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq), [Lem 846](#d-qiqth-standardsubspacemodular-modunitary-commute-rvdt). $\square$

<small>Referenced in [Lem 291](#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 467](#d-qiqth-modconj-devicevecf-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmear"></a>
**Definition 848** (`gaussSmear`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1907)</small>

A definition — see source for the body.

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [Lem 295](#d-qiqth-fock-oneparticlebw-oneparticlebw-complete), [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 413](#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 415](#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 463](#d-qiqth-gfunction-zero), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 850](#d-qiqth-standardsubspacemodular-gausssmear-mem-k), [Lem 851](#d-qiqth-standardsubspacemodular-gausssmear-smul-left), [Def 852](#d-qiqth-standardsubspacemodular-entirevec), [Lem 853](#d-qiqth-standardsubspacemodular-entirevec-sub), [Lem 861](#d-qiqth-standardsubspacemodular-gausssmearc-ofreal), [Lem 866](#d-qiqth-standardsubspacemodular-gausssmearc-zero).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmear-integrable"></a>
**Lemma 849** (`gaussSmear_integrable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1913)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{Integrable}\,(\lambda t \mapsto \exp\,(-n \cdot {t}^{2}) \cdot (V\,t)\,\eta)\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 850](#d-qiqth-standardsubspacemodular-gausssmear-mem-k), [Lem 851](#d-qiqth-standardsubspacemodular-gausssmear-smul-left), [Lem 853](#d-qiqth-standardsubspacemodular-entirevec-sub).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmear-mem-k"></a>
**Lemma 850** (`gaussSmear_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1926)</small>

$$
0 < n \to \forall \{\eta : H\}, (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (t : \mathbb{R}), (V\,t)\,\eta \in S.\mathrm{cl}) \to \href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta \in S.\mathrm{cl}
$$

*Proof.* By [Def 672](#d-qiqth-standardsubspacemodular-projk), [Lem 745](#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [Lem 849](#d-qiqth-standardsubspacemodular-gausssmear-integrable). $\square$

<small>Referenced in [Lem 194](#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmear-smul-left"></a>
**Lemma 851** (`gaussSmear_smul_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1941)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to \forall (s : \mathbb{R}), (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta) = \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot (V\,(s + t))\,\eta
$$

*Proof.* By [Lem 849](#d-qiqth-standardsubspacemodular-gausssmear-integrable). $\square$

<small>Referenced in [Lem 861](#d-qiqth-standardsubspacemodular-gausssmearc-ofreal).</small>

<a id="d-qiqth-standardsubspacemodular-entirevec"></a>
**Definition 852** (`entireVec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1964)</small>

A definition — see source for the body.

<small>Referenced in [Lem 415](#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 853](#d-qiqth-standardsubspacemodular-entirevec-sub), [Lem 854](#d-qiqth-standardsubspacemodular-entirevec-sub-norm-le), [Lem 858](#d-qiqth-standardsubspacemodular-entirevec-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-entirevec-sub"></a>
**Lemma 853** (`entireVec_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1976)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \href{#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta - \eta = \sqrt (n / \pi) \cdot \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot ((V\,t)\,\eta - \eta)
$$

*Proof.* By [Def 848](#d-qiqth-standardsubspacemodular-gausssmear), [Lem 849](#d-qiqth-standardsubspacemodular-gausssmear-integrable). $\square$

<small>Referenced in [Lem 854](#d-qiqth-standardsubspacemodular-entirevec-sub-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-entirevec-sub-norm-le"></a>
**Lemma 854** (`entireVec_sub_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L1998)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \|\href{#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta - \eta\| \le \sqrt (n / \pi) \cdot \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot \|(V\,t)\,\eta - \eta\|
$$

*Proof.* By [Lem 853](#d-qiqth-standardsubspacemodular-entirevec-sub). $\square$

<small>Referenced in [Lem 858](#d-qiqth-standardsubspacemodular-entirevec-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-gauss-mollifier-change-of-var"></a>
**Lemma 855** (`gauss_mollifier_change_of_var`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2014)</small>

$$
0 < n \to \forall (f : \mathbb{R} \to \mathbb{R}), \int (u : \mathbb{R}), \exp\,(-{u}^{2}) \cdot f\,(u / \sqrt n) = \sqrt n \cdot \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot f\,t
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 857](#d-qiqth-standardsubspacemodular-gauss-density-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-gauss-mollifier-integral-tendsto"></a>
**Lemma 856** (`gauss_mollifier_integral_tendsto`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2032)</small>

$$
\mathrm{Continuous}\,f \to (\forall (t : \mathbb{R}), |f\,t| \le M) \to \mathrm{Tendsto}\,(\lambda n \mapsto \int (u : \mathbb{R}), \exp\,(-{u}^{2}) \cdot f\,(u / \sqrt n))\,\mathrm{atTop}\,(\mathrm{nhds}\,(\int (u : \mathbb{R}), \exp\,(-{u}^{2}) \cdot f\,0))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 857](#d-qiqth-standardsubspacemodular-gauss-density-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-gauss-density-tendsto"></a>
**Lemma 857** (`gauss_density_tendsto`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2052)</small>

$$
\mathrm{Continuous}\,f \to (\forall (t : \mathbb{R}), |f\,t| \le M) \to \mathrm{Tendsto}\,(\lambda n \mapsto \sqrt (n / \pi) \cdot \int (t : \mathbb{R}), \exp\,(-n \cdot {t}^{2}) \cdot f\,t)\,\mathrm{atTop}\,(\mathrm{nhds}\,(f\,0))
$$

*Proof.* By [Lem 855](#d-qiqth-standardsubspacemodular-gauss-mollifier-change-of-var), [Lem 856](#d-qiqth-standardsubspacemodular-gauss-mollifier-integral-tendsto). $\square$

<small>Referenced in [Lem 858](#d-qiqth-standardsubspacemodular-entirevec-tendsto).</small>

<a id="d-qiqth-standardsubspacemodular-entirevec-tendsto"></a>
**Lemma 858** (`entireVec_tendsto`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2082)</small>

$$
(\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (V\,0)\,\eta = \eta \to \mathrm{Tendsto}\,(\lambda n \mapsto \href{#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta)\,\mathrm{atTop}\,(\mathrm{nhds}\,\eta)
$$

*Proof.* By [Lem 854](#d-qiqth-standardsubspacemodular-entirevec-sub-norm-le), [Lem 857](#d-qiqth-standardsubspacemodular-gauss-density-tendsto). $\square$

<small>Referenced in [Lem 415](#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc"></a>
**Definition 859** (`gaussSmearC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2115)</small>

A definition — see source for the body.

<small>Referenced in [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 292](#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [Lem 293](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [Lem 294](#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [Lem 412](#d-qiqth-standardsubspacemodular-gconstancy-entire), [Lem 413](#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [Lem 414](#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [Lem 417](#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 461](#d-qiqth-differentiableon-gfunction), [Lem 463](#d-qiqth-gfunction-zero), [Lem 464](#d-qiqth-gfunction-real-eq), [Lem 465](#d-qiqth-gfunction-top-edge-real), [Lem 469](#d-qiqth-gfunction-norm-le), [Lem 473](#d-qiqth-diffcontoncl-gfunction), [Lem 861](#d-qiqth-standardsubspacemodular-gausssmearc-ofreal), [Lem 863](#d-qiqth-standardsubspacemodular-hasderivat-gausssmearc), [Lem 864](#d-qiqth-standardsubspacemodular-differentiable-gausssmearc), [Def 865](#d-qiqth-standardsubspacemodular-corrc), [Lem 866](#d-qiqth-standardsubspacemodular-gausssmearc-zero), [Lem 867](#d-qiqth-standardsubspacemodular-gausssmearc-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc-integrable"></a>
**Lemma 860** (`gaussSmearC_integrable`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2121)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \forall (z : \mathbb{C}), \mathrm{Integrable}\,(\lambda u \mapsto \exp\,(-n \cdot {(u - z)}^{2}) \cdot (V\,u)\,\eta)\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 863](#d-qiqth-standardsubspacemodular-hasderivat-gausssmearc), [Lem 867](#d-qiqth-standardsubspacemodular-gausssmearc-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc-ofreal"></a>
**Lemma 861** (`gaussSmearC_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2143)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to \forall (s : \mathbb{R}), \href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,s = (V\,s)\,(\href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)
$$

*Proof.* By [Lem 851](#d-qiqth-standardsubspacemodular-gausssmear-smul-left). $\square$

<small>Referenced in [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 464](#d-qiqth-gfunction-real-eq).</small>

<a id="d-qiqth-standardsubspacemodular-integrable-abs-add-mul-exp-neg-mul-sq"></a>
**Lemma 862** (`integrable_abs_add_mul_exp_neg_mul_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2166)</small>

$$
0 < b \to \mathrm{Integrable}\,(\lambda u \mapsto (|u| + c) \cdot \exp\,(-b \cdot {u}^{2}))\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 863](#d-qiqth-standardsubspacemodular-hasderivat-gausssmearc).</small>

<a id="d-qiqth-standardsubspacemodular-hasderivat-gausssmearc"></a>
**Lemma 863** (`hasDerivAt_gaussSmearC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2184)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \forall (z_{0} : \mathbb{C}), ({\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta})'({z_{0}})={\int (u : \mathbb{R}), (2 \cdot n \cdot (u - z_{0}) \cdot \exp\,(-n \cdot {(u - z_{0})}^{2})) \cdot (V\,u)\,\eta}
$$

*Proof.* By [Lem 860](#d-qiqth-standardsubspacemodular-gausssmearc-integrable), [Lem 862](#d-qiqth-standardsubspacemodular-integrable-abs-add-mul-exp-neg-mul-sq). $\square$

<small>Referenced in [Lem 864](#d-qiqth-standardsubspacemodular-differentiable-gausssmearc).</small>

<a id="d-qiqth-standardsubspacemodular-differentiable-gausssmearc"></a>
**Lemma 864** (`differentiable_gaussSmearC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2313)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \mathrm{Differentiable}\,\mathbb{C}\,(\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta)
$$

*Proof.* By [Lem 863](#d-qiqth-standardsubspacemodular-hasderivat-gausssmearc). $\square$

<small>Referenced in [Lem 461](#d-qiqth-differentiableon-gfunction), [Lem 473](#d-qiqth-diffcontoncl-gfunction).</small>

<a id="d-qiqth-standardsubspacemodular-corrc"></a>
**Definition 865** (`corrC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2321)</small>

A definition — see source for the body.

<small>Referenced in [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc-zero"></a>
**Lemma 866** (`gaussSmearC_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2343)</small>

$$
\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,0 = \href{#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 463](#d-qiqth-gfunction-zero).</small>

<a id="d-qiqth-standardsubspacemodular-gausssmearc-norm-le"></a>
**Lemma 867** (`gaussSmearC_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2391)</small>

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \forall (z : \mathbb{C}), \|\href{#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z\| \le \exp\,(n \cdot {z.\mathrm{im}}^{2}) \cdot \|\eta\| \cdot \sqrt (\pi / n)
$$

*Proof.* By [Lem 860](#d-qiqth-standardsubspacemodular-gausssmearc-integrable). $\square$

<small>Referenced in [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc"></a>
**Definition 868** (`modCharC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2440)</small>

A definition — see source for the body.

<small>Referenced in [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 451](#d-qiqth-devcharderiv-norm-le-slab), [Lem 452](#d-qiqth-devchar-slope-norm-le), [Lem 869](#d-qiqth-standardsubspacemodular-measurable-modcharc), [Lem 870](#d-qiqth-standardsubspacemodular-modcharc-of-mem), [Lem 871](#d-qiqth-standardsubspacemodular-modcharc-ofreal), [Lem 872](#d-qiqth-standardsubspacemodular-modcharc-add), [Lem 873](#d-qiqth-standardsubspacemodular-hasderivat-modcharc), [Lem 874](#d-qiqth-standardsubspacemodular-modcharc-norm), [Def 875](#d-qiqth-standardsubspacemodular-devchar), [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar), [Lem 877](#d-qiqth-standardsubspacemodular-devchar-ofreal), [Lem 878](#d-qiqth-standardsubspacemodular-modcharc-zero), [Lem 879](#d-qiqth-standardsubspacemodular-devchar-zero), [Lem 880](#d-qiqth-standardsubspacemodular-devchar-neg-half-i), [Lem 881](#d-qiqth-standardsubspacemodular-devchar-norm-le), [Lem 882](#d-qiqth-standardsubspacemodular-devchar-norm-le-icc), [Lem 883](#d-qiqth-standardsubspacemodular-devchar-norm-eq), [Lem 886](#d-qiqth-standardsubspacemodular-hasderivat-devchar), [Lem 887](#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc).</small>

<a id="d-qiqth-standardsubspacemodular-measurable-modcharc"></a>
**Lemma 869** (`measurable_modCharC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2447)</small>

$$
\mathrm{Measurable}\,(\href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-of-mem"></a>
**Lemma 870** (`modCharC_of_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2455)</small>

$$
r \in \mathrm{Ioo}\,0\,2 \to \forall (z : \mathbb{C}), \href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r = \exp\,(i \cdot z \cdot (\log\,((2 - r) / r)))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 872](#d-qiqth-standardsubspacemodular-modcharc-add), [Lem 873](#d-qiqth-standardsubspacemodular-hasderivat-modcharc), [Lem 874](#d-qiqth-standardsubspacemodular-modcharc-norm), [Lem 878](#d-qiqth-standardsubspacemodular-modcharc-zero), [Lem 880](#d-qiqth-standardsubspacemodular-devchar-neg-half-i).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-ofreal"></a>
**Lemma 871** (`modCharC_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2460)</small>

$$
\href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,(t)\,r = \href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 877](#d-qiqth-standardsubspacemodular-devchar-ofreal).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-add"></a>
**Lemma 872** (`modCharC_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2463)</small>

$$
\href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,(z + w)\,r = \href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r \cdot \href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,w\,r
$$

*Proof.* By [Lem 870](#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Referenced in [Lem 450](#d-qiqth-deviceopc-bottomedge-eq).</small>

<a id="d-qiqth-standardsubspacemodular-hasderivat-modcharc"></a>
**Lemma 873** (`hasDerivAt_modCharC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2506)</small>

$$
r \in \mathrm{Ioo}\,0\,2 \to \forall (z : \mathbb{C}), ({\lambda z \mapsto \href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r})'({z})={i \cdot (\log\,((2 - r) / r)) \cdot \href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r}
$$

*Proof.* By [Lem 870](#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Referenced in [Lem 886](#d-qiqth-standardsubspacemodular-hasderivat-devchar).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-norm"></a>
**Lemma 874** (`modCharC_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2539)</small>

$$
r \in \mathrm{Ioo}\,0\,2 \to \forall (z : \mathbb{C}), \|\href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,z\,r\| = \exp\,(-z.\mathrm{im} \cdot \log\,((2 - r) / r))
$$

*Proof.* By [Lem 870](#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Referenced in [Lem 881](#d-qiqth-standardsubspacemodular-devchar-norm-le), [Lem 883](#d-qiqth-standardsubspacemodular-devchar-norm-eq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar"></a>
**Definition 875** (`devChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2594)</small>

A definition — see source for the body.

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [Def 432](#d-qiqth-devspecreal), [Lem 433](#d-qiqth-devspecreal-measurable), [Def 436](#d-qiqth-deviceopc), [Lem 440](#d-qiqth-deviceopc-norm-le), [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 451](#d-qiqth-devcharderiv-norm-le-slab), [Lem 452](#d-qiqth-devchar-slope-norm-le), [Lem 453](#d-qiqth-tendsto-devchar-slope), [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 455](#d-qiqth-deviceopc-sub), [Def 456](#d-qiqth-devicederivopc), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 458](#d-qiqth-hasderivat-devicevecf), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq), [Lem 472](#d-qiqth-devicevecf-continuouson), [Lem 876](#d-qiqth-standardsubspacemodular-measurable-devchar), [Lem 877](#d-qiqth-standardsubspacemodular-devchar-ofreal), [Lem 879](#d-qiqth-standardsubspacemodular-devchar-zero), [Lem 880](#d-qiqth-standardsubspacemodular-devchar-neg-half-i), [Lem 881](#d-qiqth-standardsubspacemodular-devchar-norm-le), [Lem 882](#d-qiqth-standardsubspacemodular-devchar-norm-le-icc), [Lem 883](#d-qiqth-standardsubspacemodular-devchar-norm-eq), [Lem 885](#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le), [Lem 886](#d-qiqth-standardsubspacemodular-hasderivat-devchar), [Lem 887](#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc).</small>

<a id="d-qiqth-standardsubspacemodular-measurable-devchar"></a>
**Lemma 876** (`measurable_devChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2597)</small>

$$
\mathrm{Measurable}\,(\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z)
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 869](#d-qiqth-standardsubspacemodular-measurable-modcharc). $\square$

<small>Referenced in [Lem 433](#d-qiqth-devspecreal-measurable), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 454](#d-qiqth-tendsto-integral-devchar-remainder-sq), [Lem 455](#d-qiqth-deviceopc-sub), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-ofreal"></a>
**Lemma 877** (`devChar_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2602)</small>

$$
\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,(t)\,r = \href{#d-qiqth-standardsubspacemodular-modchar}{\chi_{\mathrm{mod}}}\,t\,r \cdot \sqrt r
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 871](#d-qiqth-standardsubspacemodular-modcharc-ofreal). $\square$

<small>Referenced in [Lem 443](#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-standardsubspacemodular-modcharc-zero"></a>
**Lemma 878** (`modCharC_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2611)</small>

$$
\href{#d-qiqth-standardsubspacemodular-modcharc}{\chi_{\mathrm{mod}}}\,0\,r = 1
$$

*Proof.* By [Lem 870](#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Referenced in [Lem 879](#d-qiqth-standardsubspacemodular-devchar-zero).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-zero"></a>
**Lemma 879** (`devChar_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2617)</small>

$$
\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,0\,r = \sqrt r
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 878](#d-qiqth-standardsubspacemodular-modcharc-zero). $\square$

<small>Referenced in [Lem 441](#d-qiqth-deviceopreal-zero), [Lem 443](#d-qiqth-deviceopreal-eq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-neg-half-i"></a>
**Lemma 880** (`devChar_neg_half_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2623)</small>

$$
r \in \mathrm{Ioo}\,0\,2 \to \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,(-(i / 2))\,r = \sqrt (2 - r)
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 870](#d-qiqth-standardsubspacemodular-modcharc-of-mem). $\square$

<small>Referenced in [Lem 423](#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-norm-le"></a>
**Lemma 881** (`devChar_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2643)</small>

$$
z.\mathrm{im} \le 0 \to -(1/2) \le z.\mathrm{im} \to \forall \{r : \mathbb{R}\}, r \in \mathrm{Ioo}\,0\,2 \to \|\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r\| \le \sqrt 2
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 874](#d-qiqth-standardsubspacemodular-modcharc-norm). $\square$

<small>Referenced in [Lem 882](#d-qiqth-standardsubspacemodular-devchar-norm-le-icc).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-norm-le-icc"></a>
**Lemma 882** (`devChar_norm_le_Icc`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2666)</small>

$$
z.\mathrm{im} \le 0 \to -(1/2) \le z.\mathrm{im} \to \forall \{r : \mathbb{R}\}, r \in \mathrm{Icc}\,0\,2 \to \|\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r\| \le \sqrt 2
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 881](#d-qiqth-standardsubspacemodular-devchar-norm-le). $\square$

<small>Referenced in [Lem 434](#d-qiqth-devspecreal-norm-le), [Lem 450](#d-qiqth-deviceopc-bottomedge-eq), [Lem 455](#d-qiqth-deviceopc-sub), [Lem 457](#d-qiqth-deviceopc-slope-normsq), [Lem 470](#d-qiqth-deviceopc-diff-normsq), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-norm-eq"></a>
**Lemma 883** (`devChar_norm_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2681)</small>

$$
r \in \mathrm{Ioo}\,0\,2 \to \|\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r\| = {(2 - r)}^{(-z.\mathrm{im})} \cdot {r}^{(1/2 + z.\mathrm{im})}
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 874](#d-qiqth-standardsubspacemodular-modcharc-norm). $\square$

<small>Referenced in [Lem 885](#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-rpow-mul-abs-log-le"></a>
**Lemma 884** (`rpow_mul_abs_log_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2698)</small>

$$
0 < x \to x \le 2 \to 0 < \delta \to \delta \le 1 \to {x}^{\delta} \cdot |\log\,x| \le 2 / \delta + \log\,2
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 885](#d-qiqth-standardsubspacemodular-devchar-deriv-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-devchar-deriv-norm-le"></a>
**Lemma 885** (`devChar_deriv_norm_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2740)</small>

$$
0 < \beta_{0} \to \beta_{1} < 1/2 \to z.\mathrm{im} \le -\beta_{0} \to -\beta_{1} \le z.\mathrm{im} \to \forall \{r : \mathbb{R}\}, r \in \mathrm{Ioo}\,0\,2 \to |\log\,((2 - r) / r)| \cdot \|\href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r\| \le \sqrt 2 \cdot (2 / \beta_{0} + \log\,2) + \sqrt 2 \cdot (2 / (1/2 - \beta_{1}) + \log\,2)
$$

*Proof.* By [Lem 883](#d-qiqth-standardsubspacemodular-devchar-norm-eq), [Lem 884](#d-qiqth-standardsubspacemodular-rpow-mul-abs-log-le). $\square$

<small>Referenced in [Lem 451](#d-qiqth-devcharderiv-norm-le-slab), [Lem 452](#d-qiqth-devchar-slope-norm-le).</small>

<a id="d-qiqth-standardsubspacemodular-hasderivat-devchar"></a>
**Lemma 886** (`hasDerivAt_devChar`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2800)</small>

$$
r \in \mathrm{Ioo}\,0\,2 \to \forall (z : \mathbb{C}), ({\lambda z \mapsto \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r})'({z})={i \cdot (\log\,((2 - r) / r)) \cdot \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r}
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 873](#d-qiqth-standardsubspacemodular-hasderivat-modcharc). $\square$

<small>Referenced in [Lem 887](#d-qiqth-standardsubspacemodular-hasderivat-devchar-icc).</small>

<a id="d-qiqth-standardsubspacemodular-hasderivat-devchar-icc"></a>
**Lemma 887** (`hasDerivAt_devChar_Icc`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModularFlow.lean#L2811)</small>

$$
r \in \mathrm{Icc}\,0\,2 \to \forall (z : \mathbb{C}), ({\lambda z \mapsto \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r})'({z})={i \cdot (\log\,((2 - r) / r)) \cdot \href{#d-qiqth-standardsubspacemodular-devchar}{\chi_{\mathrm{dev}}}\,z\,r}
$$

*Proof.* By [Def 868](#d-qiqth-standardsubspacemodular-modcharc), [Lem 886](#d-qiqth-standardsubspacemodular-hasderivat-devchar). $\square$

<small>Referenced in [Lem 452](#d-qiqth-devchar-slope-norm-le), [Lem 453](#d-qiqth-tendsto-devchar-slope), [Lem 471](#d-qiqth-tendsto-integral-devchar-diff-sq).</small>

<a id="sec-qiqth-stripuniqueness"></a>
## QIQTH.StripUniqueness

<a id="d-qiqth-stripuniqueness-kmsstrip"></a>
**Definition 888** (`kmsStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L30)</small>

A definition — see source for the body.

<small>Referenced in [Lem 890](#d-qiqth-stripuniqueness-im-zero-on-strip), [Lem 891](#d-qiqth-stripuniqueness-eqconst-of-im-zero-strip).</small>

<a id="d-qiqth-stripuniqueness-kmsstripopen"></a>
**Definition 889** (`kmsStripOpen`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L33)</small>

A definition — see source for the body.

<small>Referenced in [Lem 890](#d-qiqth-stripuniqueness-im-zero-on-strip), [Lem 891](#d-qiqth-stripuniqueness-eqconst-of-im-zero-strip), [Lem 894](#d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip).</small>

<a id="d-qiqth-stripuniqueness-im-zero-on-strip"></a>
**Lemma 890** (`im_zero_on_strip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L95)</small>

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,g\,\href{#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}} \to (\forall z\in \href{#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}}, \|g\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (g\,z).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 1 \to (g\,z).\mathrm{im} = 0) \to \forall z\in \href{#d-qiqth-stripuniqueness-kmsstrip}{S}, (g\,z).\mathrm{im} = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 891](#d-qiqth-stripuniqueness-eqconst-of-im-zero-strip).</small>

<a id="d-qiqth-stripuniqueness-eqconst-of-im-zero-strip"></a>
**Lemma 891** (`eqConst_of_im_zero_strip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L147)</small>

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,g\,\href{#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}} \to (\forall z\in \href{#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}}, \|g\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (g\,z).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 1 \to (g\,z).\mathrm{im} = 0) \to \exists c, \forall z\in \href{#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}}, g\,z = c
$$

*Proof.* By [Def 888](#d-qiqth-stripuniqueness-kmsstrip), [Lem 890](#d-qiqth-stripuniqueness-im-zero-on-strip). $\square$

<small>Referenced in [Lem 894](#d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip).</small>

<a id="d-qiqth-stripuniqueness-kmshalfstrip"></a>
**Definition 892** (`kmsHalfStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L250)</small>

A definition — see source for the body.

<small>Referenced in [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms).</small>

<a id="d-qiqth-stripuniqueness-kmshalfstripopen"></a>
**Definition 893** (`kmsHalfStripOpen`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L254)</small>

A definition — see source for the body.

<small>Referenced in [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [Lem 429](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [Lem 430](#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [Lem 894](#d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip).</small>

<a id="d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip"></a>
**Lemma 894** (`eqConst_of_im_zero_halfStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L333)</small>

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,g\,\href{#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to (\forall z\in \href{#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}}, \|g\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (g\,z).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (g\,z).\mathrm{im} = 0) \to \exists c, \forall z\in \href{#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}}, g\,z = c
$$

*Proof.* By [Def 889](#d-qiqth-stripuniqueness-kmsstripopen), [Lem 891](#d-qiqth-stripuniqueness-eqconst-of-im-zero-strip). $\square$

<small>Referenced in [Lem 411](#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const).</small>

<a id="d-qiqth-stripuniqueness-negstrip"></a>
**Definition 895** (`negStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L368)</small>

A definition — see source for the body.

<small>Referenced in [Lem 284](#d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline), [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [Lem 897](#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-negstrip), [Lem 898](#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip), [Lem 899](#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip).</small>

<a id="d-qiqth-stripuniqueness-negstripopen"></a>
**Definition 896** (`negStripOpen`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L371)</small>

A definition — see source for the body.

<small>Referenced in [Lem 897](#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-negstrip), [Lem 898](#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip), [Lem 899](#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip).</small>

<a id="d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-negstrip"></a>
**Lemma 897** (`eqZero_of_im_zero_edge_negStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L374)</small>

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{#d-qiqth-stripuniqueness-negstripopen}{S^{-}} \to (\forall z\in \href{#d-qiqth-stripuniqueness-negstrip}{S^{-}}, \|f\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to f\,z = 0) \to \forall z\in \href{#d-qiqth-stripuniqueness-negstrip}{S^{-}}, f\,z = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Referenced in [Lem 898](#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip).</small>

<a id="d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip"></a>
**Lemma 898** (`eqOn_of_im_zero_edge_negStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L431)</small>

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,F\,\href{#d-qiqth-stripuniqueness-negstripopen}{S^{-}} \to \mathrm{DiffContOnCl}\,\mathbb{C}\,G\,\href{#d-qiqth-stripuniqueness-negstripopen}{S^{-}} \to (\forall z\in \href{#d-qiqth-stripuniqueness-negstrip}{S^{-}}, \|F\,z\| \le M) \to (\forall z\in \href{#d-qiqth-stripuniqueness-negstrip}{S^{-}}, \|G\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to F\,z = G\,z) \to \mathrm{EqOn}\,F\,G\,\href{#d-qiqth-stripuniqueness-negstrip}{S^{-}}
$$

*Proof.* By [Lem 897](#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-negstrip). $\square$

<small>Referenced in [Lem 899](#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip).</small>

<a id="d-qiqth-stripuniqueness-real-on-midline-of-conj-flip"></a>
**Lemma 899** (`real_on_midline_of_conj_flip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L443)</small>

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{#d-qiqth-stripuniqueness-negstripopen}{S^{-}} \to (\forall z\in \href{#d-qiqth-stripuniqueness-negstrip}{S^{-}}, \|f\,z\| \le M) \to (\forall (t : \mathbb{R}), f\,(t - i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,t)) \to \forall (t : \mathbb{R}), (f\,(t - i / 2)).\mathrm{im} = 0
$$

*Proof.* By [Lem 898](#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip). $\square$

<small>Referenced in [Lem 284](#d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline), [Lem 287](#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd).</small>

<a id="sec-qiqth-wedgekmstogr"></a>
## QIQTH.WedgeKMSToGR

<a id="d-qiqth-wedgekmstogr-qiqt-gr-from-flux-complete"></a>
**Theorem 900** (`qiqt_gr_from_flux_complete`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/WedgeKMSToGR.lean#L209)</small>

$$
(\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to \forall (T : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}) (\eta \hbar a : \mathbb{R}), \hbar \ne 0 \to \eta \ne 0 \to a = 2 \cdot \pi / (\hbar \cdot \eta) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), T_{{a^{\prime}}{b}}({x}) = T_{{b}{a^{\prime}}}({x})) \to \forall (P \mathrm{Pinv} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to \forall (\mathrm{Sf} \mathrm{KE} A : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R} \to \mathbb{R}) (\mathrm{sd} \mathrm{kd} \mathrm{ad} : \href{#d-qiqth-curvature-point}{M^{{4}}} \to (\mathrm{Fin}\,4 \to \mathbb{R}) \to \mathbb{R}), (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{Sf}\,x\,v})'({0})={\dot{S}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\mathrm{KE}\,x\,v})'({0})={\dot{K}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({A\,x\,v})'({0})={\dot{A}({x},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot \href{#d-qiqth-einsteineos-bl}{({T\,x})({v},{v})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \dot{A}({x},{v}) = ({\lambda i j \mapsto \href{#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})) \to (\forall (f : \href{#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}), (\forall (y : \href{#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot T_{{a^{\prime}}{b}}({y}) = \href{#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\rho : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \wedge \mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot \href{#d-qiqth-curvature-scalarcurv}{R({y})}) \to (\forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\nu : \mathrm{Fin}\,4), \href{#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to \exists \Lambda, \forall (x : \href{#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T_{{\mu}{\nu}}({x}) = \href{#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [Thm 486](#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr). $\square$

<small>Referenced in [Thm 477](#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>
