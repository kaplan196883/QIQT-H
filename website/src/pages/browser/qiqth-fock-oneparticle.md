---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.OneParticle
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.OneParticle — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← Localization](/browser/qiqth-fock-localization) · [OneParticleBW →](/browser/qiqth-fock-oneparticlebw) </small>

<small>Fock · entries 270–285 of 1000</small>

<a id="d-qiqth-fock-oneparticle-mpflow"></a>
**Lemma 270** (`MPFlow`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L48)</small>

A measure-preserving one-parameter flow on `(X, μ)`: a one-parameter group `χ` of `μ`-measure-preserving maps.  The continuum analogue of a one-parameter group of permutations of the (finite) mode set in `FreeFieldTypicality`.

$$
\{X : Type\mathrm{u\_2}\} \to [\mathrm{inst} : \mathrm{MeasurableSpace}\,X] \to \mathrm{Measure}\,X \to Type\mathrm{u\_2}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`mk`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-mk), [`flow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow), [`mp`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-mp), [`flow_zero`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow-zero), [`flow_add`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow-add), [`comp_chain`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-comp-chain), [`unitary`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary), [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply), and 4 more.</small>

<a id="d-qiqth-fock-oneparticle-mpflow-mk"></a>
**Lemma 271** (`mk`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L51)</small>

$$
\{X : Type\mathrm{u\_2}\} \to [\mathrm{inst} : \mathrm{MeasurableSpace}\,X] \to \{\mu : \mathrm{Measure}\,X\} \to (\mathrm{flow} : \mathbb{R} \to X \to X) \to (\forall (t : \mathbb{R}), \mathrm{MeasurePreserving}\,(\mathrm{flow}\,t)\,\mu\,\mu) \to \mathrm{flow}\,0 = \mathrm{id} \to (\forall (s t : \mathbb{R}), \mathrm{flow}\,(s + t) = \mathrm{flow}\,s \circ \mathrm{flow}\,t) \to \href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow}{\mathrm{MPFlow}}\,\mu
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`translationFlow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-translationflow).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-flow"></a>
**Definition 272** (`flow`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L53)</small>

The flow map at time `t`.

$$
\mathrm{flow}\,X\,\mu\,\mathrm{self} \;:=\; \mathrm{self}.1
$$

<small>Used by [`mp`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-mp), [`flow_zero`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow-zero), [`flow_add`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow-add), [`comp_chain`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-comp-chain), [`unitary`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary), [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [`unitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [`unitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), and 3 more.</small>

<a id="d-qiqth-fock-oneparticle-mpflow-mp"></a>
**Lemma 273** (`mp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L55)</small>

Each time-slice preserves `μ`.

$$
\mathrm{MeasurePreserving}\,(\mathrm{self}.\mathrm{flow}\,t)\,\mu\,\mu
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`comp_chain`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-comp-chain), [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [`unitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [`unitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [`boostUnitary_KrepL2`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [`coeFn_boostUnitary`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [`boostUnitary_eq_vadd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-flow-zero"></a>
**Lemma 274** (`flow_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L57)</small>

The flow at time `0` is the identity.

$$
\mathrm{self}.\mathrm{flow}\,0 = \mathrm{id}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`unitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-flow-add"></a>
**Lemma 275** (`flow_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L59)</small>

One-parameter group law.

$$
\mathrm{self}.\mathrm{flow}\,(s + t) = \mathrm{self}.\mathrm{flow}\,s \circ \mathrm{self}.\mathrm{flow}\,t
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`comp_chain`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-comp-chain).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-comp-chain"></a>
**Lemma 276** (`comp_chain`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L63)</small>

Composing twice along the flow chains the times: `ψ ∘ χ_b ∘ χ_a = ψ ∘ χ_{b+a}` at the level of `L²`.

$$
(\mathrm{cmp}\,(\Phi.\mathrm{flow}\,a)\,\cdots )\,((\mathrm{cmp}\,(\Phi.\mathrm{flow}\,b)\,\cdots )\,g) = (\mathrm{cmp}\,(\Phi.\mathrm{flow}\,(b + a))\,\cdots )\,g
$$

*Proof.* By [`flow_add`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow-add). $\square$

<small>Used by [`unitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-unitary"></a>
**Definition 277** (`unitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L73)</small>

**The boost unitary** at flow-time `t`: the unitary `ψ ↦ ψ ∘ χ_{-t}` on `L²(μ)`.  A genuine unitary (surjective linear isometry); unitarity is automatic from measure-preservation.


<small>Used by [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply), [`unitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [`unitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [`boostUnitary`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-unitary-apply"></a>
**Lemma 278** (`unitary_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L85)</small>

The boost unitary acts by precomposition with the inverse-time flow.

$$
(\Phi.\mathrm{U}\,t)\,g = (\mathrm{cmp}\,(\Phi.\mathrm{flow}\,(-t))\,\cdots )\,g
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`unitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [`unitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [`boostUnitary_KrepL2`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [`coeFn_boostUnitary`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [`boostUnitary_eq_vadd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-unitary-add-apply"></a>
**Lemma 279** (`unitary_add_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L92)</small>

**One-parameter group law**: `U(s+t) = U(s) ∘ U(t)`.

$$
(\Phi.\mathrm{U}\,(s + t))\,g = (\Phi.\mathrm{U}\,s)\,((\Phi.\mathrm{U}\,t)\,g)
$$

*Proof.* By [`flow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow), [`mp`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-mp), [`comp_chain`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-comp-chain), [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply). $\square$

<small>Used by [`boostUnitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-add-apply).</small>

<a id="d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply"></a>
**Lemma 280** (`unitary_zero_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L98)</small>

`U(0) = id`.

$$
(\Phi.\mathrm{U}\,0)\,g = g
$$

*Proof.* By [`flow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow), [`mp`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-mp), [`flow_zero`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-flow-zero), [`unitary_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-apply). $\square$

<small>Used by [`boostUnitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-zero-apply).</small>

<a id="d-qiqth-fock-oneparticle-translationflow"></a>
**Definition 281** (`translationFlow`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L106)</small>

**The translation flow** on `(ℝ, volume)`: `χ_t = (· + t)`, measure-preserving since Lebesgue measure is translation-invariant.

$$
\mathrm{translationFlow} \;:=\; \{\mathrm{flow} :=\lambda t x \mapsto x + t , \mathrm{mp} :=\mathrm{\_proof\_1} , \mathrm{flow\_zero} :=\mathrm{\_proof\_2} , \mathrm{flow\_add} :=\mathrm{\_proof\_3}\}
$$

<small>Used by [`boostFlow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostflow).</small>

<a id="d-qiqth-fock-oneparticle-boostflow"></a>
**Definition 282** (`boostFlow`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L114)</small>

**The 1+1D massive Lorentz boost flow.**  In rapidity coordinates `θ` (where `p = m·sinh θ`), the Lorentz-invariant one-particle measure `dΩ_m = dp/2ω_p` is `½·volume` (∝ Lebesgue) and the boost of rapidity `t` is the translation `θ ↦ θ + t`.  So the genuine continuum mass-`m` boost flow IS the translation flow (read in rapidity coordinates).

$$
\mathrm{boostFlow} \;:=\; \href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-translationflow}{\mathrm{translationFlow}}
$$

<small>Used by [`boostUnitary`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary), [`boostUnitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-add-apply), [`boostUnitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-zero-apply), [`boostUnitary_KrepL2`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-krepl2), [`coeFn_boostUnitary`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-coefn-boostunitary), [`boostUnitary_eq_vadd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-eq-vadd).</small>

<a id="d-qiqth-fock-oneparticle-boostunitary"></a>
**Definition 283** (`boostUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L120)</small>

**The 1+1D continuum boost unitary group** on the one-particle space `L²(ℝ) = L²(mass shell, dΩ_m)` (in rapidity coordinates).  This is the genuine continuum replacement for `FreeFieldTypicality`'s finite mode-permutation boost: a one-parameter group of unitaries (`boostUnitary_add_apply`, `boostUnitary_zero_apply`) implementing a real Lorentz symmetry.

$$
U\,t \;:=\; \href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostflow}{\mathrm{boostFlow}}.\mathrm{U}\,t
$$

<small>Used by [`inner_boostUnitary_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [`symm_edge_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-inner), [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`vec_boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-boost), [`boostUnitary_mapsTo_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure), and 35 more.</small>

<a id="d-qiqth-fock-oneparticle-boostunitary-add-apply"></a>
**Lemma 284** (`boostUnitary_add_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L127)</small>

The boost unitaries form a one-parameter group.

$$
(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(s + t))\,g = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,s)\,((\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,t)\,g)
$$

*Proof.* By [`unitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-add-apply), [`boostFlow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete).</small>

<a id="d-qiqth-fock-oneparticle-boostunitary-zero-apply"></a>
**Lemma 285** (`boostUnitary_zero_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/OneParticle.lean#L132)</small>

The boost at rapidity `0` is the identity.

$$
(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,0)\,g = g
$$

*Proof.* By [`unitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-mpflow-unitary-zero-apply), [`boostFlow`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostflow). $\square$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`niceWedgeSeparating_pos_mass`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass), [`hasDerivAt_inner_boostUnitary_imaginary`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete).</small>

---
<small>[← all sections](/browser) · [← Localization](/browser/qiqth-fock-localization) · [OneParticleBW →](/browser/qiqth-fock-oneparticlebw) </small>