---
layout: ../../layouts/Deep.astro
title: QIQTH.BornJoinGleason
eyebrow: BornJoinGleason · section of the QIQT-H book
description: QIQTH.BornJoinGleason — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← BornJoin](/browser/qiqth-bornjoin) · [BranchLedger →](/browser/qiqth-branchledger) </small>

<small>BornJoinGleason · entries 4–4 of 1000</small>

<a id="d-qiqth-bornjoingleason-finite-nocollapseborn-fromnoncontextuality"></a>
**Theorem 4** (`finite_noCollapseBorn_fromNoncontextuality`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/BornJoinGleason.lean#L40)</small>

**No-collapse Born representation with the single-trial law DERIVED (not assumed).** Given the prize ensemble PLUS non-contextuality of the single-trial statistics (the law `p` is the value of a non-contextual effect assignment `M` on a measurement `{Pₐ}`), there is a density matrix `ρ` such that: (i) every world has a UNIQUE actual pointer-value history (capacity + selector, no collapse); (ii) the single-trial law is the Born weight `Re tr(ρ Pₐ)` — FORCED by effect-Gleason; (iii) the world-mass of each history is the Born PRODUCT law; (iv) atypical-frequency histories carry vanishing world-mass.  The Born weights are no longer a free parameter — only NON-CONTEXTUALITY + independence (+ the world measure) are assumed.

$$
(\forall (a : \mathrm{Fin}\,m), \href{/browser/qiqth-effectgleason#d-qiqth-effectgleason-iseffect}{\mathrm{IsEffect}}\,(P\,a)) \to (\forall (a : \mathrm{Fin}\,m), M.\mu\,(P\,a) = E.p\,a) \to \forall (k : \mathrm{Fin}\,m) \{\varepsilon : \mathbb{R}\}, 0 < \varepsilon \to 0 < n \to \exists \rho, \rho.\mathrm{PosSemidef} \wedge \rho.\mathrm{trace} = 1 \wedge (\forall (\omega : E.\Omega), \exists !h, \forall (t : \mathrm{Fin}\,n), \exists r\in (E.V\,\omega\,t).\mathrm{config}.\mathrm{active}, (E.V\,\omega\,t).\mathrm{ctx}.\mathrm{valueOf}\,r = h\,t) \wedge (\forall (a : \mathrm{Fin}\,m), E.p\,a = (\rho \cdot P\,a).\mathrm{trace}.\mathrm{re}) \wedge (\forall (h : \mathrm{Fin}\,n \to \mathrm{Fin}\,m), E.P.\mathrm{massSet}\,\{\omega|E.\mathrm{actualHist}\,\omega = h\} = w\,E.p\,h) \wedge E.P.\mathrm{massSet}\,\{\omega|{(n \cdot \varepsilon)}^{2} \le {(\mathrm{count}\,k\,(E.\mathrm{actualHist}\,\omega) - n \cdot E.p\,k)}^{2}\} \le E.p\,k \cdot (1 - E.p\,k) / (n \cdot {\varepsilon}^{2})
$$

*Proof.* Immediate from the definitions. $\square$

---
<small>[← all sections](/browser) · [← BornJoin](/browser/qiqth-bornjoin) · [BranchLedger →](/browser/qiqth-branchledger) </small>