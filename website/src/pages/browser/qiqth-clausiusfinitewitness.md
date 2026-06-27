---
layout: ../../layouts/Deep.astro
title: QIQTH.ClausiusFiniteWitness
eyebrow: ClausiusFiniteWitness · section of the QIQT-H book
description: QIQTH.ClausiusFiniteWitness — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← ChristoffelSmooth](/browser/qiqth-christoffelsmooth) · [ClausiusToPernull →](/browser/qiqth-clausiustopernull) </small>

<small>ClausiusFiniteWitness · entries 11–11 of 1000</small>

<a id="d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model"></a>
**Lemma 11** (`clausius_package_from_finite_model`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/ClausiusFiniteWitness.lean#L29)</small>

**The Clausius package from the finite QIQT entropy model.**  Given a finite record set `R`, a deformation-dependent record law `p t` (a probability distribution for every `t`, uniform at the reference `t=0`), and the holographic area-capacity identification `η·Acap = log|R|`, the constructed functionals

`Sf t := Shannon (p t)`,   `KE t := Sf t + KL (p t ‖ p 0)`,   `A t := Acap`

satisfy the four thermodynamic premises of the QIQT→GR area-law derivation: capacity bound, saturation, relative-entropy positivity, and its tightness at the reference.  Each is a direct consequence of the axiom-free finite core (Gibbs/Jensen, uniform saturation, classical Klein).

$$
(\forall (t : \mathbb{R}) (r : R), 0 \le p\,t\,r) \to (\forall (t : \mathbb{R}), \sum_{r} p\,t\,r = 1) \to (p\,0 = \lambda x \mapsto {((\#\,R))}^{-1}) \to \eta \cdot \mathrm{Acap} = \log\,(\#\,R) \to (\text{for }t\text{ near }0,\; \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p\,t})} \le \eta \cdot \mathrm{Acap}) \wedge \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p\,0})} = \eta \cdot \mathrm{Acap} \wedge (\forall (t : \mathbb{R}), 0 \le \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p\,t})} + \href{/browser/qiqth-relentpositivity#d-qiqth-relentpositivity-kl}{D_{\mathrm{KL}}({p\,t}\,\|\,{p\,0})} - \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p\,t})}) \wedge \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p\,0})} + \href{/browser/qiqth-relentpositivity#d-qiqth-relentpositivity-kl}{D_{\mathrm{KL}}({p\,0}\,\|\,{p\,0})} - \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p\,0})} = 0
$$

*Proof.* By [`shannon_le_log_card`](/browser/qiqth-recordcontract#d-qiqth-recordcontract-shannon-le-log-card), [`shannon_uniform_eq_log_card`](/browser/qiqth-recordcontract#d-qiqth-recordcontract-shannon-uniform-eq-log-card), [`KL_classical_nonneg`](/browser/qiqth-relentpositivity#d-qiqth-relentpositivity-kl-classical-nonneg). $\square$

<small>Used by [`qiqt_gr_freefield_thermo`](/browser/qiqth-qiqtgrthermo#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo).</small>

---
<small>[← all sections](/browser) · [← ChristoffelSmooth](/browser/qiqth-christoffelsmooth) · [ClausiusToPernull →](/browser/qiqth-clausiustopernull) </small>