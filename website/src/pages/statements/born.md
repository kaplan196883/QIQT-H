---
layout: ../../layouts/Deep.astro
title: "Born rule"
eyebrow: "Target 1 — the Born rule: reductions and a no-go"
description: "Born rule — QIQT-H headline statements machine-translated from Lean, each with the author's explanation, conclusion and load-bearing hypotheses."
---

<small>[← all targets](/statements) · [← Target 3](/statements/gr) · [Target 2 →](/statements/lorentz)</small>

*Target 1 — the Born rule: reductions and a no-go*

## `finite_noCollapseBorn_fromNoncontextuality`

**No-collapse Born representation with the single-trial law DERIVED (not assumed).** Given the prize ensemble PLUS non-contextuality of the single-trial statistics (the law `p` is the value of a non-contextual effect assignment `M` on a measurement `{Pₐ}`), there is a density matrix `ρ` such that: (i) every world has a UNIQUE actual pointer-value history (capacity + selector, no collapse); (ii) the single-trial law is the Born weight `Re tr(ρ Pₐ)` — FORCED by effect-Gleason; (iii) the world-mass of each history is the Born PRODUCT law; (iv) atypical-frequency histories carry vanishing world-mass.  The Born weights are no longer a free parameter — only NON-CONTEXTUALITY + independence (+ the world measure) are assumed.

`finite_noCollapseBorn_fromNoncontextuality` · *capstone* —  there is $\rho$ such that all of:

1. $\rho.\mathrm{PosSemidef}$
2. $\rho.\mathrm{trace} = 1$
3. $(\forall (\omega : E.\Omega), \exists !h, \forall (t : \mathrm{Fin}\,n), \exists r\in (E.V\,\omega\,t).\mathrm{config}.\mathrm{active}, (E.V\,\omega\,t).\mathrm{ctx}.\mathrm{valueOf}\,r = h\,t)$
4. $(\forall (a : \mathrm{Fin}\,m), E.p\,a = (\rho \cdot P\,a).\mathrm{trace}.\mathrm{re})$
5. $(\forall (h : \mathrm{Fin}\,n \to \mathrm{Fin}\,m), E.P.\mathrm{massSet}\,\{\omega|E.\mathrm{actualHist}\,\omega = h\} = w\,E.p\,h)$
6. $E.P.\mathrm{massSet}\,\{\omega|{(n \cdot \varepsilon)}^{2} \le {(\mathrm{count}\,k\,(E.\mathrm{actualHist}\,\omega) - n \cdot E.p\,k)}^{2}\} \le E.p\,k \cdot (1 - E.p\,k) / (n \cdot {\varepsilon}^{2})$

*assuming*

- `hP` &nbsp; $\href{/browser/qiqth-effectgleason#d-qiqth-effectgleason-iseffect}{\mathrm{IsEffect}}\,(P\,a)$
- `hε` &nbsp; $0 < \varepsilon$
- `hn` &nbsp; $0 < n$

<small>plus 1 routine conditions (1 bridge) — full list in the per-track PDF.</small>

## `finite_effect_gleason`

`finite_effect_gleason` · *spine* —  there is $\rho$ such that all of:

1. $\rho.\mathrm{PosSemidef}$
2. $\rho.\mathrm{trace} = 1$
3. $\forall (E : \mathrm{Mat}\,(\mathrm{Fin}\,d)\,(\mathrm{Fin}\,d)\,\mathbb{C}), \href{/browser/qiqth-effectgleason#d-qiqth-effectgleason-iseffect}{\mathrm{IsEffect}}\,E \to (m.\mu\,E) = (\rho \cdot E).\mathrm{trace}$

## `positive_ray_certain_forces_born`

`positive_ray_certain_forces_born` · *spine* —  we have

$$ w\,E = \mathrm{born}\,\psi\,E $$

*assuming*

- `hψ` &nbsp; ${{\psi}}^{*} \cdot _{v} \psi = 1$
- `hadd` &nbsp; $w\,(A + B) = w\,A + w\,B$
- `hhom` &nbsp; $w\,(c \cdot A) = c \cdot w\,A$
- `hpsd` &nbsp; $\mathrm{NonnegC}\,(w\,(A.\mathrm{conjTranspose} \cdot A))$
- `hone` &nbsp; $w\,1 = 1$

<small>plus 1 routine conditions (1 bridge) — full list in the per-track PDF.</small>

## `continuous_additive_fMeasure_eq_born`

`continuous_additive_fMeasure_eq_born` · *spine* —  we have

$$ \mathrm{fMeasure}\,(f)\,w\,k = w\,k $$

*assuming*

- `hf` &nbsp; $\mathrm{Continuous}\,f$
- `h1` &nbsp; $f\,1 \ne 0$

<small>plus 1 routine conditions (1 setup) — full list in the per-track PDF.</small>

## `decoherent_partition_additive`

`decoherent_partition_additive` · *spine* —  we have

$$ \mathrm{born}\,\psi\,((\sum_{a S} C\,a).\mathrm{conjTranspose} \cdot \sum_{a S} C\,a) = \sum_{a S} \mathrm{born}\,\psi\,((C\,a).\mathrm{conjTranspose} \cdot C\,a) $$

*assuming*

- `hdec` &nbsp; $\mathrm{Decoherent}\,\psi\,C$

## `finite_noCollapseBornRepresentation`

`finite_noCollapseBornRepresentation` · *spine* —  we have all of:

1. $(\forall (\omega : E.\Omega), \exists !h, \forall (t : \mathrm{Fin}\,n), \exists r\in (E.V\,\omega\,t).\mathrm{config}.\mathrm{active}, (E.V\,\omega\,t).\mathrm{ctx}.\mathrm{valueOf}\,r = h\,t)$
2. $(\forall (h : \mathrm{Fin}\,n \to \mathrm{Fin}\,m), E.P.\mathrm{massSet}\,\{\omega|E.\mathrm{actualHist}\,\omega = h\} = w\,E.p\,h)$
3. $E.P.\mathrm{massSet}\,\{\omega|{(n \cdot \varepsilon)}^{2} \le {(\mathrm{count}\,k\,(E.\mathrm{actualHist}\,\omega) - n \cdot E.p\,k)}^{2}\} \le E.p\,k \cdot (1 - E.p\,k) / (n \cdot {\varepsilon}^{2})$

*assuming*

- `hε` &nbsp; $0 < \varepsilon$
- `hn` &nbsp; $0 < n$

## `product_born_measure_unique`

`product_born_measure_unique` · *spine* —  we have

$$ \mu\,S = ((\mathrm{kronN}\,\lambda x \mapsto \rho) \cdot \mathrm{eventEffect}\,E\,S).\mathrm{trace}.\mathrm{re} $$

*assuming*

- `hρ` &nbsp; $\rho.\mathrm{PosSemidef}$
- `hE` &nbsp; $(E\,k).\mathrm{PosSemidef}$
- `hμ0` &nbsp; $\mu\,\emptyset = 0$
- `hμins` &nbsp; $a\notin S \to \mu\,(\mathrm{insert}\,a\,S) = \mu\,\{a\} + \mu\,S$
- `hpt` &nbsp; $\mu\,\{\omega\} = \prod_{t} \mathrm{bornProb}\,\rho\,E\,(\omega\,t)$

## `chebyshev_freq`

`chebyshev_freq` · *spine* —  we have

$$ \sum_{\omega} w\,p\,\omega \le p\,k \cdot (1 - p\,k) / (N \cdot {\varepsilon}^{2}) $$

*assuming*

- `hp` &nbsp; $0 \le p\,i$
- `hp1` &nbsp; $\sum_{i} p\,i = 1$
- `hε` &nbsp; $0 < \varepsilon$
- `hN` &nbsp; $0 < N$

## `qiqth_born_typicality_conditional`

`qiqth_born_typicality_conditional` · *spine* —  we have

$$ \mathrm{expectedIndicator}\,\mathrm{outcome}\,M.\mu\,k = {c\,k}^{2} $$

## `born_distribution_realizable_conditional`

`born_distribution_realizable_conditional` · *nogo* —  there is $\mu$ such that all of:

1. $(\forall (\gamma : \Gamma), 0 \le \mu\,\gamma)$
2. $\sum_{\gamma} \mu\,\gamma = 1$
3. $\forall (k : \mathrm{Outcome}), \mathrm{outcomeMarginal}\,\mathrm{outcome}\,\mu\,k = {c\,k}^{2}$

*assuming*

- `h_surj` &nbsp; $\mathrm{Surjective}\,\mathrm{outcome}$
- `hc_norm` &nbsp; $\sum_{k} {c\,k}^{2} = 1$

## `decoherence_does_not_concentrate`

`decoherence_does_not_concentrate` · *nogo* —  we have all of:

1. $0 < \mathrm{branchWeight}\,c\,0$
2. $0 < \mathrm{branchWeight}\,c\,1$

*assuming*

- `h0` &nbsp; $c\,0 \ne 0$
- `h1` &nbsp; $c\,1 \ne 0$

## `support_preservation_does_not_imply_measure_preservation`

`support_preservation_does_not_imply_measure_preservation` · *nogo* —  there is $T,\ \mu$ such that all of:

1. $\mathrm{Bijective}\,T$
2. $\mathrm{SupportPreserving}\,T$
3. $\neg \mathrm{MeasurePreserving}\,T\,\mu$

## `operational_data_insufficient`

`operational_data_insufficient` · *nogo* —  there is $\mathrm{outcome},\ \nu_{1},\ \nu_{2}$ such that all of:

1. $(\forall (k : \mathrm{Fin}\,2), \mathrm{marginal3to2}\,\nu_{1}\,\mathrm{outcome}\,k = \mathrm{marginal3to2}\,\nu_{2}\,\mathrm{outcome}\,k)$
2. $\nu_{1} \ne \nu_{2}$
