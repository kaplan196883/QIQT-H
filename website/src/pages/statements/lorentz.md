---
layout: ../../layouts/Deep.astro
title: "Lorentz covariance"
eyebrow: "Target 2 — Lorentz covariance of the selection"
description: "Lorentz covariance — QIQT-H headline statements machine-translated from Lean, each with the author's explanation, conclusion and load-bearing hypotheses."
---

<small>[← all targets](/statements) · [← Target 1](/statements/born)</small>

*Target 2 — Lorentz covariance of the selection*

## `upvm_covariant_probability`

`upvm_covariant_probability` · *capstone* —  we have all of:

1. $(\forall (x : P.X\,D), 0 \le \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D\,x)$
2. $.\mathrm{sum}\,(\mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D) = 1$
3. $\forall (x : P.X\,D), \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,((A.\mathrm{act}\,g)\,D)\,((A.\gamma\,g\,D)\,x) = \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D\,x$

## `evaluation_covariance`

`evaluation_covariance` · *spine* —  we have

$$ \mathrm{selector}\,(\mathrm{actSection}\,g\,\lambda)\,(g.\mathrm{act}\,D) = (g.\gamma\,D)\,(\mathrm{selector}\,\lambda\,D) $$

## `group_evaluation_covariance`

`group_evaluation_covariance` · *spine* —  we have

$$ \mathrm{selector}\,(\mathrm{actSection}\,(A.\mathrm{toPoincare}\,g)\,\lambda)\,((A.\mathrm{act}\,g)\,D) = (A.\gamma\,g\,D)\,(\mathrm{selector}\,\lambda\,D) $$

## `freeFieldMeasure_boost_invariant`

`freeFieldMeasure_boost_invariant` · *spine* —  we have

$$ \mathrm{map}\,(\mathrm{diagBoost}\,e)\,(\mathrm{freeFieldMeasure}\,\nu) = \mathrm{freeFieldMeasure}\,\nu $$

*assuming*

- `hν` &nbsp; $\mathrm{map}\,(\mathrm{boostMap}\,e)\,\nu = \nu$

<small>plus 1 routine conditions (1 typeclass) — full list in the per-track PDF.</small>

## `bh_typicalityMeasure_exists`

`bh_typicalityMeasure_exists` · *spine* —  there is $\mu$ such that all of:

1. $\mathrm{IsProbabilityMeasure}\,\mu$
2. $(\mathrm{diagNet}\,\mathrm{hb}\,\mathrm{hp}\,\mathrm{hsum}\,\mathrm{hp1}\,g).\mathrm{toFiniteMarginals}.\mathrm{IsLimit}\,\mu$

*assuming*

- `hb` &nbsp; $\mathrm{Orthonormal}\,\mathbb{C}\,b$
- `hp` &nbsp; $0 \le p\,i$
- `hsum` &nbsp; $\mathrm{Summable}\,p$
- `hp1` &nbsp; $\sum ' (i : \kappa), p\,i = 1$

<small>plus 4 routine conditions (4 typeclass) — full list in the per-track PDF.</small>

## `fock_typicalityMeasure_exists`

`fock_typicalityMeasure_exists` · *spine* —  there is $\mu$ such that all of:

1. $\mathrm{IsProbabilityMeasure}\,\mu$
2. $(\mathrm{fockVacuumNet}\,g).\mathrm{toFiniteMarginals}.\mathrm{IsLimit}\,\mu$

<small>plus 3 routine conditions (3 typeclass) — full list in the per-track PDF.</small>

## `continuum_volume_selects`

`continuum_volume_selects` · *spine* —  we have

$$ \mathrm{vol}\,\{\mathrm{seed}|\mathrm{selects}\,(\mathrm{contWeights}\,S\,\xi\,s)\,\mathrm{seed}\,k\} = {{\mathrm{contWeights}\,S\,\xi\,s\,k}} $$

<small>plus 1 routine conditions (1 typeclass) — full list in the per-track PDF.</small>

## `no_signaling`

`no_signaling` · *spine* —  we have

$$ S.P\,x\,a\,y = S.\mathrm{PAlice}\,x\,a $$

## `bipartite_no_signaling`

`bipartite_no_signaling` · *spine* —  we have

$$ \sum_{b} (\rho \cdot \mathrm{kroneckerMap}\,(\lambda x_{1} x_{2} \mapsto x_{1} \cdot x_{2})\,E\,(F\,b)).\mathrm{trace} = (\rho \cdot \mathrm{kroneckerMap}\,(\lambda x_{1} x_{2} \mapsto x_{1} \cdot x_{2})\,E\,1).\mathrm{trace} $$

*assuming*

- `hF` &nbsp; $\sum_{b} F\,b = 1$

## `no_covariant_selector`

`no_covariant_selector` · *nogo* —  we have

$$ \bot $$

*assuming*

- `equiv` &nbsp; $\sigma\,(\mathrm{actS}\,\Phi) = \mathrm{actH}\,(\sigma\,\Phi)$
- `hΦ` &nbsp; $\mathrm{actS}\,\Phi = \Phi$
- `hno` &nbsp; $\mathrm{actH}\,h \ne h$

## `bool_swap_no_selector`

`bool_swap_no_selector` · *nogo* —  we have

$$ \bot $$

*assuming*

- `equiv` &nbsp; $\sigma\,u = !\sigma\,u$
