---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.OneParticleBW
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.OneParticleBW — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← OneParticle](/browser/qiqth-fock-oneparticle) · [SchwartzDecay →](/browser/qiqth-fock-schwartzdecay) </small>

<small>Fock · entries 286–319 of 1000</small>

<a id="d-qiqth-fock-oneparticlebw-boostunitary-krepl2"></a>
**Lemma 286** (`boostUnitary_KrepL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L66)</small>

**L² boost-covariance of the localization** (GPT-5.5's first Layer-1 brick, the sign check): `boostUnitary a (KrepL2 f) = KrepL2 (boostTest (−a) f)`.  The geometric boost acts on the one-particle wavefunction `Krep f ∈ L²(rapidity)` exactly as the spacetime boost `boostTest (−a)` on the test function.  This is the engine for boost-invariance of the physically-defined wedge subspace (`𝒦 := closure of {KrepL2 f : f real, supp f ⊆ right wedge}`).  Axiom-free; from `Krep_boost` + the flow `θ ↦ θ + (−a) = θ − a`.

$$
(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,(\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,h) = \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-a)\,f))\,h^{\prime}
$$

*Proof.* By [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost), [`flow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow), [`mp`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-mp), [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [`boostFlow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Used by [`inner_boostUnitary_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [`vec_boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-boost), [`boostUnitary_mapsTo_wedgeGenSet`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgegenset).</small>

<a id="d-qiqth-fock-oneparticlebw-coefn-boostunitary"></a>
**Lemma 287** (`coeFn_boostUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L96)</small>

**Pointwise form of the boost action**: `(boostUnitary a ξ)(θ) = ξ(θ − a)` (a.e.).  The rapidity boost is the spatial translation `θ ↦ θ − a` on the one-particle wavefunction.  From `MPFlow.unitary_apply` (the unitary precomposes with the pullback flow `θ ↦ θ + (−a)`).

$$
((\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,\xi) =[\mathrm{volume}] \lambda \theta \mapsto \xi\,(\theta - a)
$$

*Proof.* By [`flow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow), [`mp`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-mp), [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [`boostFlow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Used by [`inner_boostUnitary_toLp`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-inner-boostunitary-tolp), [`boostUnitary_toLp`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-boostunitary-tolp).</small>

<a id="d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd"></a>
**Lemma 288** (`boostUnitary_eq_vadd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L110)</small>

**The boost unitary IS the canonical `Lp` domain-translation** `DomAddAct.mk t +ᵥ ξ`.  `boostUnitary t` is precomposition with `θ ↦ θ + t` (the rapidity-translation flow); Mathlib's `DomAddAct` action is precomposition with `θ ↦ t + θ`.  They agree by `add_comm`, identifying the project's boost group with Mathlib's continuous domain action — the bridge that makes the boost group's *strong continuity* a one-line consequence of Mathlib's `Lp.instContinuousVAddDomAddAct`.

$$
(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,t)\,\xi = \mathrm{mk}\,(-t) +_{v} \xi
$$

*Proof.* By [`flow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow), [`mp`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-mp), [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [`boostFlow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Used by [`continuous_boostUnitary_apply`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-continuous-boostunitary-apply).</small>

<a id="d-qiqth-fock-oneparticlebw-continuous-boostunitary-apply"></a>
**Lemma 289** (`continuous_boostUnitary_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L131)</small>

**Strong continuity of the boost group** (vector level): for every one-particle state `ξ`, the orbit `t ↦ boostUnitary t ξ` is continuous.  This is the genuine strong continuity of the rapidity-translation unitary group — the *first brick of the Stone-generator program* whose later steps would ground the boost-charge derivative `hBoostCharge`.  Derived from Mathlib's continuity of the `Lp` domain action (`Lp.instContinuousVAddDomAddAct`, valid since Lebesgue measure is translation-invariant, locally finite, inner regular) via the identification `boostUnitary_eq_vadd`.  Axiom-free.

$$
\mathrm{Continuous}\,\lambda t \mapsto (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,t)\,\xi
$$

*Proof.* By [`boostUnitary_eq_vadd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd). $\square$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-inner-boostunitary-tolp"></a>
**Lemma 290** (`inner_boostUnitary_toLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L172)</small>

**The boost matrix coefficient as a concrete translation integral.**  For a one-particle state given by a representative `f` (`ξ = f.toLp`), the modular/boost correlation `⟪ξ, boostUnitary s ξ⟫` is the cross-correlation integral `∫ conj(f θ)·f(θ − s) dθ`.  This is the inner-product-to-integral bridge (`L2.inner_def` + `MemLp.coeFn_toLp` + `coeFn_boostUnitary`, the translation pushed through the measure-preserving shift) that turns the abstract boost correlation into an analyzable integral — the setup on which the boost-charge *derivative* (Stone generator → `hBoostCharge`) is computed.  Axiom-free.

$$
\langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,s)\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f\,(\theta - s)
$$

*Proof.* By [`coeFn_boostUnitary`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-coefn-boostunitary). $\square$

<small>Used by [`hasDerivAt_inner_boostUnitary_wedge`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-wedge).</small>

<a id="d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-wedge"></a>
**Lemma 291** (`hasDerivAt_inner_boostUnitary_wedge`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L193)</small>

**The boost-charge derivative (the analytic core of `hBoostCharge`).**  For a one-particle state `ξ = f.toLp` with `f` smooth enough (differentiable with derivative `f'`, with `f`, `|f|²` integrable and `‖f'‖` globally bounded — all satisfied by any Schwartz / compactly-supported-`C¹` `f`), the boost correlation `t ↦ ⟪ξ, boostUnitary(−2π t) ξ⟫` is differentiable at `0` with derivative `2π·∫ conj(f)·f'`.  This is the **rapidity-momentum expectation** `2π⟪ξ, −i∂_θ ξ⟫` — the boost charge — obtained by differentiating the cross-correlation integral under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominating function `2π·B·|f|`). …

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f\,\theta)\,\mathrm{volume} \to \mathrm{AEStronglyMeasurable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta}
$$

*Proof.* By [`inner_boostUnitary_toLp`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-inner-boostunitary-tolp). $\square$

<small>Used by [`hasDerivAt_inner_boostUnitary_imaginary`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary).</small>

<a id="d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary"></a>
**Lemma 292** (`hasDerivAt_inner_boostUnitary_imaginary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L259)</small>

**The boost-charge derivative in its physical `i·(real)` form — `hBoostCharge` grounded.**  The boost correlation derivative is **purely imaginary**: `d/dt ⟪ξ, boostUnitary(−2π t) ξ⟫|₀ = i·(boost energy)`, with boost energy `= (2π·∫ conj(f)·f')·(−i) =` the real rapidity-momentum expectation.  This is exactly the shape of the labelled `hBoostCharge` input — now DERIVED for any smooth wedge state (modulo only the single physical identification `boost energy = (2π/ℏ)·T_kk`, the stress tensor). …

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to \mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f\,\theta)\,\mathrm{volume} \to \mathrm{AEStronglyMeasurable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot (2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta).\mathrm{im}}
$$

*Proof.* By [`boostUnitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-zero-apply), [`hasDerivAt_inner_boostUnitary_wedge`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-wedge). $\square$

<small>Used by [`hasDerivAt_inner_boostUnitary_imaginary_pos`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-hasderivat-inner-boostunitary-imaginary-pos).</small>

<a id="d-qiqth-fock-oneparticlebw-mapsto-closure-span"></a>
**Lemma 293** (`mapsTo_closure_span`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L338)</small>

**Invariance engine** (for the boost-invariance of the wedge standard subspace): a continuous `ℝ`-linear map `L` that maps a set `W` into itself also maps `closure (span ℝ W)` into itself. Applied with `L = boostUnitary a` and `W` = the (boost-closed) wedge generating set, this gives `boostUnitary a (𝒦_W) ⊆ 𝒦_W` — the boost-invariance the KMS-uniqueness route needs.

$$
\mathrm{MapsTo}\,(L)\,W\,W \to \mathrm{MapsTo}\,(L)\,(\overline{{\mathrm{span}\,\mathbb{R}\,W}})\,(\overline{{\mathrm{span}\,\mathbb{R}\,W}})
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`boostUnitary_mapsTo_closure_span`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-closure-span).</small>

<a id="d-qiqth-fock-oneparticlebw-boostunitary-mapsto-closure-span"></a>
**Lemma 294** (`boostUnitary_mapsTo_closure_span`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L355)</small>

**Boost-invariance of a physically-defined wedge subspace.**  If a set `S` of one-particle vectors is closed under the boost (`boostUnitary a` maps `S` into `S` — true for `S` = the `KrepL2` of a boost-closed family of wedge test functions, via `boostUnitary_KrepL2`), then the wedge standard subspace `𝒦_W := closure (span_ℝ S)` is boost-invariant: `boostUnitary a (𝒦_W) ⊆ 𝒦_W`.  This is the invariance the GPT-5-pro KMS-uniqueness route consumes (`V(a)𝒦 = 𝒦`).

$$
\mathrm{MapsTo}\,((\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a))\,S\,S \to \mathrm{MapsTo}\,((\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a))\,(\overline{{\mathrm{span}\,\mathbb{R}\,S}})\,(\overline{{\mathrm{span}\,\mathbb{R}\,S}})
$$

*Proof.* By [`mapsTo_closure_span`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-mapsto-closure-span). $\square$

<small>Used by [`boostUnitary_mapsTo_wedgeSubspace`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgesubspace).</small>

<a id="d-qiqth-fock-oneparticlebw-rightwedge"></a>
**Definition 295** (`rightWedge`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L369)</small>

**The right wedge** `W_R = {z : z¹ > |z⁰|}` in 1+1D Minkowski `V = Fin 2 → ℝ` (index `0` = time, `1` = space), written in light-cone form `z¹ − z⁰ > 0 ∧ z¹ + z⁰ > 0`.

$$
\mathrm{rightWedge} \;:=\; \{z|0 < z\,1 - z\,0 \wedge 0 < z\,1 + z\,0\}
$$

<small>Used by [`lorentzBoost_mapsTo_rightWedge`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-lorentzboost-mapsto-rightwedge), [`support_boostTest_subset`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-support-boosttest-subset), [`wedgeGenSet`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-wedgegenset), [`boostUnitary_mapsTo_wedgeGenSet`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgegenset).</small>

<a id="d-qiqth-fock-oneparticlebw-lorentzboost-mapsto-rightwedge"></a>
**Lemma 296** (`lorentzBoost_mapsTo_rightWedge`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L373)</small>

**The right wedge is boost-invariant**: `lorentzBoost a` maps `W_R` into itself.  In light-cone coordinates `z± = z¹ ± z⁰` the boost acts by the positive scalings `z⁻ ↦ e^{−a}z⁻`, `z⁺ ↦ e^{a}z⁺`, so positivity of both is preserved.  This is why the wedge generating set of test functions is boost-closed, hence `𝒦_W` is boost-invariant.

$$
\mathrm{MapsTo}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a)\,\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-rightwedge}{\mathrm{rightWedge}}\,\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-rightwedge}{\mathrm{rightWedge}}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`support_boostTest_subset`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-support-boosttest-subset).</small>

<a id="d-qiqth-fock-oneparticlebw-lorentzboost-neg-boost"></a>
**Lemma 297** (`lorentzBoost_neg_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L398)</small>

**The boost is invertible**: `lorentzBoost (−a) ∘ lorentzBoost a = id` (`cosh²−sinh²=1`).

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,(-a)\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost}{\mathrm{L}}\,a\,z) = z
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`support_boostTest_subset`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-support-boosttest-subset).</small>

<a id="d-qiqth-fock-oneparticlebw-support-boosttest-subset"></a>
**Lemma 298** (`support_boostTest_subset`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L409)</small>

**Boost preserves wedge support**: if `f` is supported in the right wedge, so is its boost `boostTest a f = f ∘ lorentzBoost a`.  (From `lorentzBoost_mapsTo_rightWedge` + the boost inverse.) This makes the wedge generating set `{KrepL2 f : supp f ⊆ W_R}` boost-closed.

$$
\mathrm{support}\,f \subseteq \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-rightwedge}{\mathrm{rightWedge}} \to \mathrm{support}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,a\,f) \subseteq \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-rightwedge}{\mathrm{rightWedge}}
$$

*Proof.* By [`lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost), [`lorentzBoost_mapsTo_rightWedge`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-lorentzboost-mapsto-rightwedge), [`lorentzBoost_neg_boost`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-lorentzboost-neg-boost). $\square$

<small>Used by [`boostUnitary_mapsTo_wedgeGenSet`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgegenset).</small>

<a id="d-qiqth-fock-oneparticlebw-wedgegenset"></a>
**Definition 299** (`wedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L423)</small>

**The wedge generating set**: the one-particle vectors `KrepL2 f` from *real*, *wedge-supported*, `L²` test functions.  The physical generators of the wedge standard subspace — defined PURELY from wedge test functions (NOT from modular data), per the anti-circularity discipline.

$$
\mathrm{wedgeGenSet}\,m \;:=\; \{\psi|\exists f, \exists (h : \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume}), \mathrm{support}\,f \subseteq \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-rightwedge}{\mathrm{rightWedge}} \wedge (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \wedge \psi = \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,h\}
$$

<small>Used by [`boostUnitary_mapsTo_wedgeGenSet`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgegenset), [`boostUnitary_mapsTo_wedgeSubspace`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgesubspace), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete), [`oneParticle_hFlux_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticle-hflux-complete), [`component_hFlux_of_wedgeKMS_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-component-hflux-of-wedgekms-complete), [`WedgeKMSFlux_complete`](/browser/qiqth-wedgekmstogr#d-qiqth-wedgekmstogr-wedgekmsflux-complete), [`hFlux_of_wedgeKMS_complete`](/browser/qiqth-wedgekmstogr#d-qiqth-wedgekmstogr-hflux-of-wedgekms-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgegenset"></a>
**Lemma 300** (`boostUnitary_mapsTo_wedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L431)</small>

**The wedge generating set is boost-closed**: `boostUnitary a` maps it into itself.  For `ψ = KrepL2 f`, `boostUnitary a ψ = KrepL2(boostTest(−a) f)` (sign lemma), and `boostTest(−a) f` is again real, wedge-supported (`support_boostTest_subset`), and `L²` (translation of an `L²` function).

$$
\mathrm{MapsTo}\,((\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a))\,(\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-wedgegenset}{\mathrm{wedgeGenSet}}\,m)\,(\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-wedgegenset}{\mathrm{wedgeGenSet}}\,m)
$$

*Proof.* By [`V`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-v), [`lorentzBoost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-lorentzboost), [`boostTest`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost), [`boostUnitary_KrepL2`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [`rightWedge`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-rightwedge), [`support_boostTest_subset`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-support-boosttest-subset). $\square$

<small>Used by [`boostUnitary_mapsTo_wedgeSubspace`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgesubspace).</small>

<a id="d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgesubspace"></a>
**Lemma 301** (`boostUnitary_mapsTo_wedgeSubspace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L448)</small>

**The wedge standard subspace `𝒦_W := closure (span_ℝ (wedge generators))` is BOOST-INVARIANT:** `boostUnitary a (𝒦_W) ⊆ 𝒦_W` for every rapidity `a`.  This is the `V(a)𝒦 = 𝒦` the GPT-5-pro KMS-uniqueness route consumes — now PROVED axiom-free for the physically-defined wedge subspace (assembling the sign lemma + invariance engine + wedge geometry).  The remaining inputs of the one-particle BW are the (formalizable) KMS-uniqueness lemma and the single labelled strip/KMS property of `boostUnitary` on these vectors.

$$
\mathrm{MapsTo}\,((\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a))\,(\overline{{\mathrm{span}\,\mathbb{R}\,(\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-wedgegenset}{\mathrm{wedgeGenSet}}\,m)}})\,(\overline{{\mathrm{span}\,\mathbb{R}\,(\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-wedgegenset}{\mathrm{wedgeGenSet}}\,m)}})
$$

*Proof.* By [`boostUnitary_mapsTo_closure_span`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-closure-span), [`boostUnitary_mapsTo_wedgeGenSet`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgegenset). $\square$

<small>Used by [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-stripkmsrvd"></a>
**Definition 302** (`StripKMSrvd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L480)</small>

**The CORRECT one-particle KMS condition — Rieffel–Van Daele (1977), Definition 3.4.**  Faithful to the source (refs/RieffelVanDaele): a strongly-continuous unitary group `V` satisfies the KMS condition w.r.t. the **real subspace** `K` (`= 𝒦`) iff for every `ξ, η ∈ K` there is `f` * **bounded and continuous on the closed strip `{−1 ≤ Im z ≤ 0}`, analytic in the interior** (`DiffContOnCl` on the open strip `{−1 < Im < 0}` + a uniform bound `M`), with boundary values * `f(t)   = ⟪η, V(t) ξ⟫`   (bottom edge `Im = 0`), * `f(t−i) = ⟪V(t) ξ, η⟫`   (top edge `Im = −1`, the plain flip). …

$$
\mathrm{StripKMSrvd}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,V\,K \;:=\; \forall \xi\in K, \forall \eta\in K, \exists f, \mathrm{DiffContOnCl}\,\mathbb{C}\,f\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \wedge (\exists M, \forall (z : \mathbb{C}), \|f\,z\| \le M) \wedge (\forall (t : \mathbb{R}), f\,t = \langle {\eta},{(V\,t)\,\xi}\rangle) \wedge \forall (t : \mathbb{R}), f\,(t - i) = \langle {(V\,t)\,\xi},{\eta}\rangle
$$

<small>Used by [`stripKMSrvd_boostUnitary`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-boostunitary), [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`stripKMSrvd_real_midline`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline), [`stripKMSrvd_halfStripReal`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal), [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`oneParticleBW_of_comparison`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), and 6 more.</small>

<a id="d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline"></a>
**Lemma 303** (`stripKMSrvd_real_midline`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L510)</small>

**From RvD Definition 3.4 to the half-strip reality** (RvD Proposition 3.5 applied to `StripKMSrvd`). The plain-flip top-edge value `f(t − i) = ⟪V_t ξ, η⟫` of `StripKMSrvd` is automatically `conj(f(t))`: by conjugate symmetry `⟪V_t ξ, η⟫ = conj⟪η, V_t ξ⟫`, and `f(t) = ⟪η, V_t ξ⟫` (the corrected RvD Def 3.4 convention, orbit in the linear slot).  So `real_on_midline_of_conj_flip` (RvD Prop 3.5) upgrades the witness to the *half-strip KMS form*: a bounded-holomorphic `f` with real-axis value `f(t) = ⟪V_t ξ, η⟫` **and** `f(t − i/2)` REAL — exactly the reality input RvD Theorem 3.8 consumes (`Δ^{1/2} = J` on the standard subspace).  This discharges the Prop-3.5 step of the `hUniq` proof from the labelled `StripKMSrvd`, axiom-free.

$$
\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,K \to \forall \{\xi \eta : H\}, \xi \in K \to \eta \in K \to \exists f, \mathrm{DiffContOnCl}\,\mathbb{C}\,f\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \wedge (\forall (t : \mathbb{R}), f\,t = \langle {\eta},{(V\,t)\,\xi}\rangle) \wedge \forall (t : \mathbb{R}), (f\,(t - i / 2)).\mathrm{im} = 0
$$

*Proof.* By [`negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstrip), [`real_on_midline_of_conj_flip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip). $\square$

<small>Used by [`stripKMSrvd_halfStripReal`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal).</small>

<a id="d-qiqth-fock-oneparticlebw-halfstripreal"></a>
**Definition 304** (`HalfStripReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L580)</small>

The **half-strip reality form** of the KMS condition (the output of RvD Proposition 3.5): for `ξ, η ∈ K`, a bounded-holomorphic `f` on `{−1 < Im z < 0}` with `f(t) = ⟪V_t ξ, η⟫` and `f(t − i/2)` REAL.  This is the reality input RvD Theorem 3.8 actually consumes; it is PROVABLE from `StripKMSrvd` (`stripKMSrvd_halfStripReal`, via Prop 3.5), so labelling it instead of all of `StripKMS` shrinks the unproven surface to exactly the Theorem-3.8 core.

$$
\mathrm{HalfStripReal}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,V\,K \;:=\; \forall \xi\in K, \forall \eta\in K, \exists f, \mathrm{DiffContOnCl}\,\mathbb{C}\,f\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \wedge (\forall (t : \mathbb{R}), f\,t = \langle {\eta},{(V\,t)\,\xi}\rangle) \wedge \forall (t : \mathbb{R}), (f\,(t - i / 2)).\mathrm{im} = 0
$$

<small>Used by [`stripKMSrvd_halfStripReal`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal), [`oneParticleBW_of_comparison`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal"></a>
**Lemma 305** (`stripKMSrvd_halfStripReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L589)</small>

**`StripKMSrvd` ⟹ `HalfStripReal`** — RvD Proposition 3.5, packaged: the correct full-strip KMS condition yields the half-strip reality form (each pair's witness made real on the mid-line).

$$
\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,K \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-halfstripreal}{\mathrm{HalfStripReal}}\,V\,K
$$

*Proof.* By [`stripKMSrvd_real_midline`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline). $\square$

<small>Used by [`oneParticleBW_of_comparison`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison).</small>

<a id="d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd"></a>
**Lemma 306** (`h1_of_stripKMSrvd`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L595)</small>

**The bottom-edge KMS reality `h1` DISCHARGED from `StripKMSrvd` — RvD Theorem 3.8 g-function complete.** For the orbit input `η ∈ 𝒦` (strongly-continuous contraction, orbit staying in `𝒦`) and `ξ = √Rζ ∈ 𝒦`, the g-function's bottom edge `g(t − i/2) = ⟪J·deviceVecF(t−i/2), gaussSmearC(t−i/2)⟫` is REAL.  Assembly of the whole device g-function argument: the K.M.S. condition (`hKMS`) applied to the pair `(gaussSmear, ξ_t = Δ^{it}ξ)` (both in `𝒦`: `gaussSmear_mem_K`, `modUnitary_mapsTo_K`) gives a bounded-holomorphic `f` with `f(s) = ⟪ξ_t, V_s·gaussSmear⟫` (faithful RvD Def 3.4 convention) and — via the plain conjugate-flip (`real_on_midline_of_conj_flip`, RvD Prop 3.5) — `f(t − i/2)` REAL. …

$$
0 < n \to \forall \{\eta : H\}, (\mathrm{Continuous}\,\lambda s \mapsto (V\,s)\,\eta) \to (\forall (s : \mathbb{R}), \|(V\,s)\,\eta\| \le \|\eta\|) \to (\forall (s u : \mathbb{R}), (V\,s)\,((V\,u)\,\eta) = (V\,(s + u))\,\eta) \to (\forall (s : \mathbb{R}), (V\,s)\,\eta \in S.\mathrm{cl}) \to \forall \{\zeta : H\}, (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,(t - i / 2))).\mathrm{im} = 0
$$

*Proof.* By [`gFunction_bottom_real_of_faithful_kms`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [`modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`modUnitary_mapsTo_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [`gaussSmear`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear), [`gaussSmear_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-mem-k), [`kmsHalfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip), [`kmsHalfStripOpen`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen), [`negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstrip), [`real_on_midline_of_conj_flip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip). $\square$

<small>Used by [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density).</small>

<a id="d-qiqth-fock-oneparticlebw-comparisondatum"></a>
**Definition 307** (`ComparisonDatum`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L641)</small>

The **comparison datum** — the exact OUTPUT of RvD Theorem 3.8's `g`-function: for every `t`, `η ∈ 𝒦`, and `w ⊥ i𝒦` (`projIK w = 0`), `⟪w, V_t η⟫ = ⟪w, Δ^{it} η⟫`.  This is the single relation that the (source-garbled) `g`-pairing / Prop-3.7-device argument produces from the half-strip reality; everything downstream of it — `V_t η = Δ^{it} η` on `𝒦` (`IsSeparating`) and the lift to `Δ^{it} = V_t` (`IsCyclic`) — is the already-proven `modUnitary_eq_of_orbit_compare`.

$$
\mathrm{ComparisonDatum}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,V \;:=\; \forall (t : \mathbb{R}), \forall \eta\in S.\mathrm{cl}, \forall (w : H), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,w = 0 \to \langle {w},{(V\,t)\,\eta}\rangle = \langle {w},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\eta}\rangle
$$

<small>Used by [`oneParticleBW_of_comparison`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison"></a>
**Lemma 308** (`oneParticleBW_of_comparison`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L651)</small>

**Conditional one-particle BW with the TIGHTEST honest labelling.**  Everything provable is now proved: the Proposition-3.5 reduction (`stripKMSrvd_halfStripReal`), the `Δ`-invariance (`modUnitary_mapsTo_K`), and the operator assembly (`modUnitary_eq_of_orbit_compare`: separating ⇒ equal on `𝒦`, cyclic ⇒ equal everywhere).  The SOLE labelled hypothesis `hCompare` is the exact `g`-function output `HalfStripReal ⟹ ComparisonDatum` — the only genuinely source-garbled step of RvD Theorem 3.8.  This is the minimal honest statement of "what remains unproven" on the `hUniq` discharge route.

$$
(\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-halfstripreal}{\mathrm{HalfStripReal}}\,V\,S.\mathrm{cl} \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum}{\mathrm{ComparisonDatum}}\,S\,V) \to (\forall (t : \mathbb{R}), \mathrm{MapsTo}\,(V\,t)\,S.\mathrm{cl}\,S.\mathrm{cl}) \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [`stripKMSrvd_halfStripReal`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd-halfstripreal), [`modUnitary_eq_of_orbit_compare`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`modUnitary_mapsTo_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k). $\square$

<small>Used by [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-gconstancy"></a>
**Definition 309** (`GConstancy`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L677)</small>

The **g-function constancy output** (RvD Theorem 3.8, the analytic conclusion): for `ξ, η ∈ 𝒦`, `⟪V_t η, Δ^{it} J ξ⟫ = ⟪η, J ξ⟫`.  This is exactly what the (analytic) g-function `g(z) = ⟨h(z), J d_z(R) ζ⟩` produces by being constant on the half-strip — `g(t) = ⟨U_t η, JΔ^{it}ξ⟩` (top edge, real), `g(0) = ⟨η, Jξ⟩` — using `Δ^{it}J = JΔ^{it}` (`modConj_commute_modUnitary`).

$$
\mathrm{GConstancy}\,H\,\mathrm{NormedAddCommGroup}\,H\,\mathrm{InnerProductSpace}\,H\,\mathrm{CompleteSpace}\,H\,S\,V \;:=\; \forall (t : \mathbb{R}), \forall \eta\in S.\mathrm{cl}, \forall \xi\in S.\mathrm{cl}, \langle {(V\,t)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

<small>Used by [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy"></a>
**Lemma 310** (`comparisonDatum_of_gConstancy`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L685)</small>

**The g-function constancy output yields `ComparisonDatum`** — the operator-algebra wrapper of RvD Theorem 3.8, reducing the discharge to the *analytic* g-constancy alone.  Given `⟪V_t η, Δ^{it} J ξ⟫ = ⟪η, J ξ⟫` (∀ξ,η∈𝒦): for `w ⊥ i𝒦` set `ξ = Δ^{−it}(J w) ∈ 𝒦` (`J w ∈ 𝒦` since `J𝒦 = (i𝒦)^⊥`, `Δ^{−it}` preserves `𝒦`).  Then `J ξ = Δ^{−it} w` and `Δ^{it} J ξ = w` (`JΔ^{it}=Δ^{it}J` + group law), so g-constancy reads `⟪V_t η, w⟫ = ⟪η, Δ^{−it} w⟫ = ⟪Δ^{it} η, w⟫` (adjoint); conjugating gives `⟪w, V_t η⟫ = ⟪w, Δ^{it} η⟫`.  The `⟪η,Jξ⟫` right-hand side carries the `Δ`-side automatically — no separate `Δ`-version needed.  So the ONLY remaining unproven step is the analytic g-constancy itself.

$$
\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy}{\mathrm{GConstancy}}\,S\,V \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum}{\mathrm{ComparisonDatum}}\,S\,V
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary), [`modUnitary_zero`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-zero), [`modUnitary_add`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-add), [`modUnitary_adjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-adjoint), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj), [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`projK_modConj_eq_self_of_perp_IK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-projk-modconj-eq-self-of-perp-ik), [`modUnitary_mapsTo_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-mapsto-k), [`modConj_commute_modUnitary`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-commute-modunitary). $\square$

<small>Used by [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-gconstancy-of-inputs"></a>
**Lemma 311** (`gConstancy_of_inputs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L711)</small>

**Full `GConstancy` from the two named RvD inputs** (the end-to-end assembly of the device g-function discharge).  Given a strongly-continuous contraction group `V` (`hcont`/`hbd`/`hgrp`/`hV0`), the orbit invariance of `𝒦` (`hKinv`), the **bottom-edge KMS reality** `h1` (the mid-line `Im z = −1/2` reality of the device g-function, supplied by `HalfStripReal`), and the **`√R`-range density in `𝒦`** `hdense` (every `ξ ∈ 𝒦` is a limit of `√R ζ_k ∈ 𝒦`, available since `R` is injective), the `GConstancy` proposition holds. Chains `gConstancy_eta_of_bottom` (η-side, `h1`) → `gConstancy_xi_of_density` (ξ-side, `hdense`). …

$$
(\forall \eta\in S.\mathrm{cl}, \mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (\eta : H) (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (\eta : H) (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (\eta : H), (V\,0)\,\eta = \eta) \to (\forall \eta\in S.\mathrm{cl}, \forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall \eta\in S.\mathrm{cl}, \forall (\zeta : H), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (n : \mathbb{R}), 0 < n \to \forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to (\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)) \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy}{\mathrm{GConstancy}}\,S\,V
$$

*Proof.* By [`gConstancy_eta_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), [`gConstancy_xi_of_density`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-xi-of-density). $\square$

<small>Used by [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs"></a>
**Lemma 312** (`oneParticleBW_of_inputs`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L738)</small>

**One-particle Bisognano–Wichmann via the device g-function, reduced to the two named RvD inputs.** The modular flow IS the candidate flow, `modUnitary S t = V t`, GIVEN: the strongly-continuous contraction group `V` with `𝒦`-invariance (`hInv`), the correct full-strip KMS condition (`hKMS : StripKMSrvd`), and the two RvD Theorem 3.8 inputs that drive the g-function — the **bottom-edge KMS reality** `h1` (mid-line `Im z = −1/2` reality) and the **`√R`-range density in `𝒦`** `hdense`.  `gConstancy_of_inputs` yields the full `GConstancy`, `comparisonDatum_of_gConstancy` the `ComparisonDatum`, and `oneParticleBW_of_comparison` the flow identification. …

$$
(\forall \eta\in S.\mathrm{cl}, \mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (\eta : H) (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (\eta : H) (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (\eta : H), (V\,0)\,\eta = \eta) \to (\forall \eta\in S.\mathrm{cl}, \forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall \eta\in S.\mathrm{cl}, \forall (\zeta : H), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (n : \mathbb{R}), 0 < n \to \forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to (\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)) \to (\forall (t : \mathbb{R}), \mathrm{MapsTo}\,(V\,t)\,S.\mathrm{cl}\,S.\mathrm{cl}) \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [`HalfStripReal`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-halfstripreal), [`oneParticleBW_of_comparison`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs). $\square$

<small>Used by [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density"></a>
**Lemma 313** (`oneParticleBW_of_stripKMSrvd_density`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L768)</small>

**One-particle Bisognano–Wichmann from the KMS condition — `h1` DISCHARGED, only `hdense` named.** `modUnitary S t = V t` for a strongly-continuous contraction group `V` with `𝒦`-invariance (`hInv`) and the correct RvD Def 3.4 KMS condition (`hKMS : StripKMSrvd`), GIVEN only the `√R`-range density `hdense`.  The bottom-edge KMS reality — the last analytic input of RvD Theorem 3.8's device g-function — is no longer a labelled hypothesis: it is derived from `hKMS` via `h1_of_stripKMSrvd` (the complete f-transfer assembly). So the entire `hUniq` discharge now rests on a SINGLE named analytic input, `hdense` (the `√R`-range density in `𝒦`), with the KMS condition supplied as the genuine RvD Def 3.4 hypothesis.

$$
(\forall \eta\in S.\mathrm{cl}, \mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (\eta : H) (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (\eta : H) (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (\eta : H), (V\,0)\,\eta = \eta) \to (\forall \eta\in S.\mathrm{cl}, \forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)) \to (\forall (t : \mathbb{R}), \mathrm{MapsTo}\,(V\,t)\,S.\mathrm{cl}\,S.\mathrm{cl}) \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [`deviceVecF`](/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf), [`modConjBilin`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin), [`gaussSmearC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc). $\square$

<small>Used by [`oneParticleBW_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-complete"></a>
**Lemma 314** (`oneParticleBW_complete`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L798)</small>

**One-particle Bisognano–Wichmann from the KMS condition — the COMPLETE, unconditional discharge.** `modUnitary S t = V t` for a strongly-continuous contraction group `V` with `𝒦`-invariance (`hInv`) and the correct RvD Def 3.4 KMS condition (`hKMS : StripKMSrvd`) — with NO remaining named analytic input.  Both RvD Theorem 3.8 inputs of the device g-function are now theorems: the bottom-edge KMS reality `h1` (via `h1_of_stripKMSrvd`) and the `√R`-range density `hdense` (via `rvdSqrtR_range_dense_in_K`).  This is the full, axiom-free formalization of RvD Theorem 3.8: `Δ^{it}` is the unique strongly-continuous unitary group carrying `𝒦` onto `𝒦` and satisfying the KMS condition — i.e. …

$$
(\forall \eta\in S.\mathrm{cl}, \mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (\eta : H) (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (\eta : H) (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (\eta : H), (V\,0)\,\eta = \eta) \to (\forall \eta\in S.\mathrm{cl}, \forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall (t : \mathbb{R}), \mathrm{MapsTo}\,(V\,t)\,S.\mathrm{cl}\,S.\mathrm{cl}) \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [`rvdSqrtR_range_dense_in_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k). $\square$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete"></a>
**Lemma 315** (`oneParticleBW_wedge_complete`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L859)</small>

**One-particle Bisognano–Wichmann for the WEDGE — KMS-uniqueness DERIVED (no bundled `hUniq`).** `modUnitary S t = boostUnitary(−2π t)` for the wedge standard subspace `𝒦_W`, given ONLY the carrier identity (`hcarrier`), `V = boostUnitary(−2π·)` (`hVboost`), and the genuine RvD Def 3.4 KMS condition `hKMS : StripKMSrvd V 𝒦_W`.  Unlike `oneParticleBW_wedge`, the KMS-uniqueness is no longer a bundled opaque hypothesis but is DERIVED via `oneParticleBW_complete` (the machine-checked RvD Theorem 3.8 discharge), and the labelled KMS predicate is the genuine, non-vacuous `StripKMSrvd` rather than the trivially-satisfiable `StripKMS`. …

$$
S.\mathrm{cl} = \overline{{\mathrm{span}\,\mathbb{R}\,(\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-wedgegenset}{\mathrm{wedgeGenSet}}\,m)}} \to (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,x) \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [`boostUnitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-add-apply), [`boostUnitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-zero-apply), [`continuous_boostUnitary_apply`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-continuous-boostunitary-apply), [`boostUnitary_mapsTo_wedgeSubspace`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-mapsto-wedgesubspace), [`oneParticleBW_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-complete), [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`gaussSmear`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear), [`gaussSmear_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-mem-k). $\square$

<small>Used by [`oneParticle_hFlux_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticle-hflux-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-hasderivat-modularenergy-of-boost"></a>
**Lemma 316** (`hasDerivAt_modularEnergy_of_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L931)</small>

**Modular energy = boost energy (derivative level), via BW.**  Given the one-particle BW `modUnitary S t u = boostUnitary(−2π t) u`, the modular-energy correlation `t ↦ ⟪ξ, Δ^{it} ξ⟫` coincides with the boost-energy correlation `t ↦ ⟪ξ, boostUnitary(−2π t) ξ⟫` as functions of `t`, so their derivatives at `0` agree.  The modular energy `kd = d/dt⟪ξ,Δ^{it}ξ⟫|₀` (the object feeding `hFlux`) therefore equals the boost energy derivative — reducing `hFlux` (modular energy = stress flux) to the standard **boost-charge = stress-flux** identity `δ⟨boost⟩ = ∫λ T_kk`, the one remaining labelled geometric fact.  No unbounded generator needed: the equality is a direct congruence from BW.

$$
(\forall (t : \mathbb{R}) (u : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,u = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,u) \to \forall (\xi : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})) (c : \mathbb{C}), ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,\xi}\rangle})'({0})={c} \to ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi}\rangle})'({0})={c}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modularEnergy_eq_stressFlux`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-modularenergy-eq-stressflux).</small>

<a id="d-qiqth-fock-oneparticlebw-modularenergy-eq-stressflux"></a>
**Lemma 317** (`modularEnergy_eq_stressFlux`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L950)</small>

**One-particle `hFlux`: the modular energy IS `(2π/ℏ)·(stress flux)`** — `hFlux` derived from the BW plus the labelled boost-charge identity.  `hBoostCharge` is the single remaining labelled input on this path: the **boost-charge = stress-flux** identity `δ⟨boost⟩ = (2π/ℏ)·T_kk` (the conserved Killing charge of the boost equals the stress-tensor flux — standard field theory, needs the field stress tensor which the project has not built, so labelled).  Composed with the *proved* `hasDerivAt_modularEnergy_of_boost` (modular energy = boost energy, via BW), it gives the modular energy derivative `= (2π/ℏ)·T_kk` — exactly the `hFlux` of `qiqt_bekenstein_gives_gr` at the one-particle (Hilbert) level. …

$$
(\forall (t : \mathbb{R}) (u : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,u = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,u) \to \forall (\xi : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})) (\hbar T_{kk} : \mathbb{R}), ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,\xi}\rangle})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})} \to ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi}\rangle})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})}
$$

*Proof.* By [`hasDerivAt_modularEnergy_of_boost`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-hasderivat-modularenergy-of-boost). $\square$

<small>Used by [`oneParticle_hFlux_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticle-hflux-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-oneparticle-hflux-complete"></a>
**Lemma 318** (`oneParticle_hFlux_complete`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L1042)</small>

**`oneParticle_hFlux` with KMS-uniqueness DERIVED** — the genuine `StripKMSrvd` replaces the bundled opaque `hUniq`+`StripKMS`.  The modular-energy derivative `t ↦ ⟪ξ, Δ^{it}ξ⟫` equals the boost-charge derivative `i·(2π/ℏ)·T_kk`, with the BW identification `modUnitary = boostUnitary` now derived via `oneParticleBW_wedge_complete` (= `oneParticleBW_complete`, the RvD Theorem 3.8 discharge).

$$
S.\mathrm{cl} = \overline{{\mathrm{span}\,\mathbb{R}\,(\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-wedgegenset}{\mathrm{wedgeGenSet}}\,m)}} \to (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,x) \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (\xi : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})) (\hbar T_{kk} : \mathbb{R}), ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,\xi}\rangle})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})} \to ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi}\rangle})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})}
$$

*Proof.* By [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete), [`modularEnergy_eq_stressFlux`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-modularenergy-eq-stressflux). $\square$

<small>Used by [`component_hFlux_of_wedgeKMS_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-component-hflux-of-wedgekms-complete).</small>

<a id="d-qiqth-fock-oneparticlebw-component-hflux-of-wedgekms-complete"></a>
**Lemma 319** (`component_hFlux_of_wedgeKMS_complete`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticleBW.lean#L1066)</small>

**`component_hFlux_of_wedgeKMS` with KMS-uniqueness DERIVED** — the component-level `hFlux` `kd = (2π/ℏ)·T_kk` resting on the genuine `StripKMSrvd` (not the bundled opaque `hUniq`+vacuous `StripKMS`).  The BW identification is derived via `oneParticleBW_complete` (RvD Theorem 3.8).

$$
S.\mathrm{cl} = \overline{{\mathrm{span}\,\mathbb{R}\,(\href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-wedgegenset}{\mathrm{wedgeGenSet}}\,m)}} \to (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,x) \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,V\,S.\mathrm{cl} \to \forall (\xi : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})) (\hbar \mathrm{kd} T_{kk} : \mathbb{R}), ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(-(2 \cdot \pi \cdot t)))\,\xi}\rangle})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})} \to ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi}\rangle})'({0})={i \cdot \mathrm{kd}} \to \mathrm{kd} = 2 \cdot \pi / \hbar \cdot T_{kk}
$$

*Proof.* By [`oneParticle_hFlux_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticle-hflux-complete). $\square$

<small>Used by [`hFlux_of_wedgeKMS_complete`](/browser/qiqth-wedgekmstogr#d-qiqth-wedgekmstogr-hflux-of-wedgekms-complete).</small>

---
<small>[← all sections](/browser) · [← OneParticle](/browser/qiqth-fock-oneparticle) · [SchwartzDecay →](/browser/qiqth-fock-schwartzdecay) </small>