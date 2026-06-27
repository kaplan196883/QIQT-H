---
layout: ../../layouts/Deep.astro
title: QIQTH.RecordContract
eyebrow: RecordContract · section of the QIQT-H book
description: QIQTH.RecordContract — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← RaychaudhuriCongruence](/browser/qiqth-raychaudhuricongruence) · [RelEntPositivity →](/browser/qiqth-relentpositivity) </small>

<small>RecordContract · entries 579–581 of 1000</small>

<a id="d-qiqth-recordcontract-shannon-eq-sum-negmullog"></a>
**Lemma 579** (`shannon_eq_sum_negMulLog`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RecordContract.lean#L122)</small>

Shannon entropy is a sum of `negMulLog` of the weights.

$$
\href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p})} = \sum_{i s} (p\,i).\mathrm{nml}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`shannon_le_log_card`](/browser/qiqth-recordcontract#d-qiqth-recordcontract-shannon-le-log-card), [`shannon_uniform_eq_log_card`](/browser/qiqth-recordcontract#d-qiqth-recordcontract-shannon-uniform-eq-log-card).</small>

<a id="d-qiqth-recordcontract-shannon-le-log-card"></a>
**Lemma 580** (`shannon_le_log_card`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RecordContract.lean#L128)</small>

**The information bound `H(R) ≤ log|R|` (Gibbs/Jensen), machine-checked.**  For any finite Born record law, the Shannon entropy is at most the log of the record count. This discharges the `hinfo` hypothesis of `area_capacity_bridge` concretely — the only genuinely-mathematical (still textbook) step in the contract.

$$
(\forall (i : \iota), 0 \le p\,i) \to \sum_{i} p\,i = 1 \to \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p})} \le \log\,(\#\,\iota)
$$

*Proof.* By [`shannon_eq_sum_negMulLog`](/browser/qiqth-recordcontract#d-qiqth-recordcontract-shannon-eq-sum-negmullog). $\square$

<small>Used by [`clausius_package_from_finite_model`](/browser/qiqth-clausiusfinitewitness#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model), [`qiqt_gr_ppwave_showcase`](/browser/qiqth-qiqtgrshowcase#d-qiqth-wedgekmstogr-qiqt-gr-ppwave-showcase).</small>

<a id="d-qiqth-recordcontract-shannon-uniform-eq-log-card"></a>
**Lemma 581** (`shannon_uniform_eq_log_card`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RecordContract.lean#L165)</small>

**Capacity saturation `H(R) = log|R|` at the maximally-mixed (equilibrium) record.** The Jensen/Gibbs bound `shannon_le_log_card` is an EQUALITY exactly at the uniform distribution `p i = 1/|R|` — the maximum-entropy state.  There the record's Shannon entropy SATURATES its capacity `log|R|`.  This is the regime where a horizon is in local equilibrium, the state Jacobson assumes when positing the area law.  Machine-checked: `∑_{i} negMulLog(1/n) = n·(1/n)·log n = log n`.

$$
(\href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({\lambda x \mapsto {((\#\,\iota))}^{-1}})}) = \log\,(\#\,\iota)
$$

*Proof.* By [`shannon_eq_sum_negMulLog`](/browser/qiqth-recordcontract#d-qiqth-recordcontract-shannon-eq-sum-negmullog). $\square$

<small>Used by [`clausius_package_from_finite_model`](/browser/qiqth-clausiusfinitewitness#d-qiqth-clausiusfinitewitness-clausius-package-from-finite-model).</small>

---
<small>[← all sections](/browser) · [← RaychaudhuriCongruence](/browser/qiqth-raychaudhuricongruence) · [RelEntPositivity →](/browser/qiqth-relentpositivity) </small>