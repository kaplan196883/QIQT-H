---
layout: ../../layouts/Deep.astro
title: QIQTH.RelEntPositivity
eyebrow: RelEntPositivity · section of the QIQT-H book
description: QIQTH.RelEntPositivity — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← RecordContract](/browser/qiqth-recordcontract) · [RicciSymm →](/browser/qiqth-riccisymm) </small>

<small>RelEntPositivity · entries 582–583 of 1000</small>

<a id="d-qiqth-relentpositivity-kl"></a>
**Definition 582** (`KL`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RelEntPositivity.lean#L65)</small>

**Classical KL non-negativity** — the finite-distribution version of Klein's inequality.  Provable from the elementary log inequality `log x ≤ x − 1` (i.e. `−log x ≥ 1 − x`).

For finite probability distributions `p, q : ι → ℝ`: KL(p ‖ q)  :=  Σ_i p_i · log(p_i / q_i)  ≥  0.

We axiomatize at this layer to keep the file small; the proof is `Real.log_le_sub_one_of_pos` applied to each term plus `Finset.sum_nonneg`.

$$
\mathrm{KL}\,\iota\,s\,p\,q \;:=\; \sum_{i s} p\,i \cdot \log\,(p\,i / q\,i)
$$

<small>Used by [`clausius_package_from_finite_model`](/browser/qiqth-clausiusfinitewitness#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model), [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_complete_covCong`](/browser/qiqth-qiqtgrcovcong#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete-covcong), [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave), [`qiqt_gr_ppwave_showcase`](/browser/qiqth-qiqtgrshowcase#d-qiqth-wedgekmstogr-qiqt-gr-ppwave-showcase), [`qiqt_gr_freefield_thermo`](/browser/qiqth-qiqtgrthermo#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), [`KL_classical_nonneg`](/browser/qiqth-relentpositivity#d-qiqth-relentpositivity-kl-classical-nonneg).</small>

<a id="d-qiqth-relentpositivity-kl-classical-nonneg"></a>
**Lemma 583** (`KL_classical_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RelEntPositivity.lean#L78)</small>

**Klein-style inequality for *finite classical* KL — PROVED** (the *full-support* finite Gibbs' inequality: `q` strictly positive on all of `s`, the standard hypothesis; the more general support-degenerate form would instead require only `p_i > 0 → q_i > 0` with the `0·log(0/q)=0` convention). Discharges the former axiom by the elementary log bound `Real.log x ≤ x − 1`: termwise `p_i - q_i ≤ p_i·log(p_i/q_i)`, then sum and use `∑ p = ∑ q = 1`.  This is the finite-classical shadow of Klein / relative-entropy positivity (Open Problem 9 / the information bound behind Open Problem 6); the continuum vN-algebraic `D_nonneg` remains analytic (operator convexity of `−log`, not in Mathlib).

$$
(\forall i\in s, 0 \le p\,i) \to (\forall i\in s, 0 < q\,i) \to \sum_{i s} p\,i = 1 \to \sum_{i s} q\,i = 1 \to 0 \le \href{/browser/qiqth-relentpositivity#d-qiqth-relentpositivity-kl}{D_{\mathrm{KL}}({p}\,\|\,{q})}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`clausius_package_from_finite_model`](/browser/qiqth-clausiusfinitewitness#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model).</small>

---
<small>[← all sections](/browser) · [← RecordContract](/browser/qiqth-recordcontract) · [RicciSymm →](/browser/qiqth-riccisymm) </small>