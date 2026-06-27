---
layout: ../../layouts/Deep.astro
title: QIQTH.RaychaudhuriCongruence
eyebrow: RaychaudhuriCongruence · section of the QIQT-H book
description: QIQTH.RaychaudhuriCongruence — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← Raychaudhuri](/browser/qiqth-raychaudhuri) · [RecordContract →](/browser/qiqth-recordcontract) </small>

<small>RaychaudhuriCongruence · entries 575–578 of 1000</small>

<a id="d-qiqth-curvature-raychaudhuri-setup-of-covconst"></a>
**Lemma 575** (`raychaudhuri_setup_of_covConst`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RaychaudhuriCongruence.lean#L23)</small>

**Stage 1 — the Raychaudhuri congruence setup from one condition.**  A covariantly-constant congruence `V` (`covDerivVec g gi V ≡ 0`) satisfies BOTH the geodesic premise `hWgeo` and the equilibrium premise `hWequil` — trivially, since every covariant derivative term is zero.  This reduces the two labelled premises to the single geometric condition "`V` is covariantly constant."

$$
(\forall (a b : \mathrm{Fin}\,n) (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{a}}{}^{{b}}({y})} = 0) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \wedge \sum_{\mu} \sum_{\nu} \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})} = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`qiqt_gr_freefield_complete_covCong`](/browser/qiqth-qiqtgrcovcong#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete-covcong).</small>

<a id="d-qiqth-curvature-expansion-eq-zero-of-covconst"></a>
**Lemma 576** (`expansion_eq_zero_of_covConst`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RaychaudhuriCongruence.lean#L44)</small>

**Stage 3 — zero expansion for a covariantly-constant congruence.**  The expansion `θ = ∑_μ ∇_μ V^μ` of a covariantly-constant `V` vanishes identically (every `∇_μ V^μ = 0`).

$$
(\forall (a b : \mathrm{Fin}\,n) (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{a}}{}^{{b}}({y})} = 0) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({x})} = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`pd_expansion_zero_of_covConst`](/browser/qiqth-raychaudhuricongruence#d-qiqth-curvature-pd-expansion-zero-of-covconst).</small>

<a id="d-qiqth-curvature-pd-expansion-zero-of-covconst"></a>
**Lemma 577** (`pd_expansion_zero_of_covConst`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RaychaudhuriCongruence.lean#L52)</small>

The coordinate derivative of the (identically-zero) expansion is zero.

$$
(\forall (a b : \mathrm{Fin}\,n) (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{a}}{}^{{b}}({y})} = 0) \to \forall (\nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x}) = 0
$$

*Proof.* By [`pd_const`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const), [`expansion_eq_zero_of_covConst`](/browser/qiqth-raychaudhuricongruence#d-qiqth-curvature-expansion-eq-zero-of-covconst). $\square$

<small>Used by [`area_hasDerivAt_of_covConst`](/browser/qiqth-raychaudhuricongruence#d-qiqth-curvature-area-hasderivat-of-covconst).</small>

<a id="d-qiqth-curvature-area-hasderivat-of-covconst"></a>
**Lemma 578** (`area_hasDerivAt_of_covConst`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RaychaudhuriCongruence.lean#L61)</small>

**Stage 3 — the area-derivative witness `hA` for a covariantly-constant congruence.**  A covariantly- constant congruence has identically-zero expansion, so the Raychaudhuri area-rate `-∑_ν V^ν ∂_ν θ` is `0`, and a constant cross-sectional area satisfies the capstone's `hA` (`HasDerivAt (area) (rate) 0`) — the `θ = 0` case (area preserved along a shear-free, expansion-free congruence).  Discharges `hA` for the flat / pp-wave (∂_v) congruence, the same setting in which `hWgeo`/`hWequil` reduce.  The expanding (θ≠0) curved case needs the geodesic-ODE / area-element machinery Mathlib lacks (the cited frontier, header).

$$
(\forall (a b : \mathrm{Fin}\,n) (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{a}}{}^{{b}}({y})} = 0) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (c : \mathbb{R}), ({\lambda x \mapsto c})'({0})={-\sum_{\nu} V\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x})}
$$

*Proof.* By [`pd_expansion_zero_of_covConst`](/browser/qiqth-raychaudhuricongruence#d-qiqth-curvature-pd-expansion-zero-of-covconst). $\square$

<small>Used by [`qiqt_gr_ppwave_showcase`](/browser/qiqth-qiqtgrshowcase#d-qiqth-wedgekmstogr-qiqt-gr-ppwave-showcase).</small>

---
<small>[← all sections](/browser) · [← Raychaudhuri](/browser/qiqth-raychaudhuri) · [RecordContract →](/browser/qiqth-recordcontract) </small>