---
layout: ../../layouts/Deep.astro
title: QIQTH.DifferentialAreaLaw
eyebrow: DifferentialAreaLaw · section of the QIQT-H book
description: QIQTH.DifferentialAreaLaw — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← Curvature](/browser/qiqth-curvature) · [EffectGleason →](/browser/qiqth-effectgleason) </small>

<small>DifferentialAreaLaw · entries 71–73 of 1000</small>

<a id="d-qiqth-differentialarealaw-deriv-eq-of-le-of-eq"></a>
**Lemma 71** (`deriv_eq_of_le_of_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/DifferentialAreaLaw.lean#L36)</small>

**First-order saturation ⇒ equal first variations.**  If `f ≤ g` on a neighbourhood of `0` and `f 0 = g 0`, then `0` is a local maximum of `f − g`, so the derivatives agree: `f' = g'`.  This is the engine that converts a *bound* saturated at the reference into an *equality of first variations*, without assuming `f = g`.

$$
({f})'({0})={f^{\prime}} \to ({g})'({0})={g^{\prime}} \to (\text{for }t\text{ near }0,\; f\,t \le g\,t) \to f\,0 = g\,0 \to f^{\prime} = g^{\prime}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`differential_area_law`](/browser/qiqth-differentialarealaw#d-qiqth-differentialarealaw-differential-area-law).</small>

<a id="d-qiqth-differentialarealaw-differential-area-law"></a>
**Lemma 72** (`differential_area_law`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/DifferentialAreaLaw.lean#L53)</small>

** THE DIFFERENTIAL AREA LAW, DERIVED.**  Along a one-parameter deformation `t`, with `S` the horizon entropy, `KE` the modular energy `⟨K⟩`, `A` the area, and a constant `η`:

HYPOTHESES (note: NONE asserts `S = ηA` or `δS = ηδA`): * `hbound` — the capacity **bound** `S ≤ η·A` near `0` (QIQT-H's `shannon_le_log_card`); * `hsat`   — **saturation at the reference** `S 0 = η·A 0` (equilibrium, `shannon_uniform_eq_log_card`); * `hfl`    — the **entanglement first law** datum: `KE − S` has a local minimum at `0` (relative entropy `≥ 0`, `= 0` at the reference); * differentiability of `S, KE, A` at `0`.

CONCLUSION: `δS = η δA` **and** `δ⟨K⟩ = η δA` — the differential area law, derived.

$$
({S})'({0})={s^{\prime}} \to ({\mathrm{KE}})'({0})={k^{\prime}} \to ({A})'({0})={a^{\prime}} \to (\text{for }t\text{ near }0,\; S\,t \le \eta \cdot A\,t) \to S\,0 = \eta \cdot A\,0 \to \mathrm{IsLocalMin}\,(\lambda t \mapsto \mathrm{KE}\,t - S\,t)\,0 \to s^{\prime} = \eta \cdot a^{\prime} \wedge k^{\prime} = \eta \cdot a^{\prime}
$$

*Proof.* By [`deriv_eq_of_le_of_eq`](/browser/qiqth-differentialarealaw#d-qiqth-differentialarealaw-deriv-eq-of-le-of-eq). $\square$

<small>Used by [`differential_area_law_of_relEntropy`](/browser/qiqth-differentialarealaw#d-qiqth-differentialarealaw-differential-area-law-of-relentropy).</small>

<a id="d-qiqth-differentialarealaw-differential-area-law-of-relentropy"></a>
**Lemma 73** (`differential_area_law_of_relEntropy`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/DifferentialAreaLaw.lean#L75)</small>

**The differential area law from RELATIVE-ENTROPY POSITIVITY** — grounding the first-law datum `hfl` in QIQT-H's own theorem.  The entanglement first law's premise (`IsLocalMin (KE − S) 0`) is not an extra assumption: it is exactly *relative-entropy non-negativity with equality at the reference*, `D = KE − S ≥ 0` and `D 0 = 0` — which QIQT-H proves as `QuantumEntropy.relEntropy_nonneg` (Klein's inequality) and `relEntropy_self`.  So the inputs reduce to: the capacity bound `S ≤ η·A` (QIQT's `shannon_le_log_card`), saturation at the reference, relative-entropy positivity (Klein), and differentiability — and these DERIVE `δS = η δA` and `δ⟨K⟩ = η δA`.

$$
({S})'({0})={s^{\prime}} \to ({\mathrm{KE}})'({0})={k^{\prime}} \to ({A})'({0})={a^{\prime}} \to (\text{for }t\text{ near }0,\; S\,t \le \eta \cdot A\,t) \to S\,0 = \eta \cdot A\,0 \to (\forall (t : \mathbb{R}), 0 \le \mathrm{KE}\,t - S\,t) \to \mathrm{KE}\,0 - S\,0 = 0 \to s^{\prime} = \eta \cdot a^{\prime} \wedge k^{\prime} = \eta \cdot a^{\prime}
$$

*Proof.* By [`differential_area_law`](/browser/qiqth-differentialarealaw#d-qiqth-differentialarealaw-differential-area-law). $\square$

<small>Used by [`bl_pernull_of_qiqt`](/browser/qiqth-qiqttogr#d-qiqth-qiqttogr-bl-pernull-of-qiqt).</small>

---
<small>[← all sections](/browser) · [← Curvature](/browser/qiqth-curvature) · [EffectGleason →](/browser/qiqth-effectgleason) </small>