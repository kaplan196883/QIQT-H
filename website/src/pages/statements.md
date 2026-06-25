---
layout: ../layouts/Deep.astro
title: Machine-rendered statements
eyebrow: Auto-generated from Lean
description: The QIQT-H theorem statements, machine-translated from the Lean 4 / Mathlib source to readable math — conclusion first, load-bearing hypotheses shown, routine conditions summarized.
---

Each result below is **machine-translated from the Lean&nbsp;4 / Mathlib source** by the project
tool (`lean_track latex`), which walks the *delaborated syntax tree* of every declaration. The
content is **verbatim**; only the presentation is editorial — leading universal quantifiers and
type ascriptions are factored out (free variables are implicitly universally quantified: $x$ ranges
over spacetime points, indices $\mu,\nu$ over $\{0,1,2,3\}$, $v$ over tangent vectors), the
**conclusion leads** in display math, the **load-bearing hypotheses are shown**, and routine
regularity / setup / typeclass conditions are summarized by count (the full assumption surface lives
in each track's PDF). Labels like `hFlux` are the Lean hypothesis names. To explore the full
dependency network — every lemma and definition these results rest on, hyperlinked, with source
links — see the [**theorem browser**](/browser). Regenerate with
`python scripts/lean-track.py latex -c tracks/<id>.toml`.


## GR field equations

*Target 3 — QIQT-H gives the Einstein field equations*

### Einstein field equations for the free field (all geometric inputs discharged)

`qiqt_gr_freefield_complete` · *capstone* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `hcap` &nbsp; $\eta \cdot A({x},{v},{0}) = \log\,(\#\,\iota)$
- `hbound` &nbsp; $({g\,x})({v},{v}) = 0 \to \text{for }t\text{ near }0,\; S({p\,x\,v\,t}) \le \eta \cdot A({x},{v},{t})$

<small>plus 25 routine conditions (17 regularity, 7 setup, 1 typeclass) — full list in the per-track PDF.</small>

### Einstein field equations on an explicit pp-wave spacetime

`qiqt_gr_ppwave_showcase` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g^{\mathrm{pp}}\,H\,x\,\mu\,\nu $$

*assuming*

- `hCH` &nbsp; $({H})\in C^{\infty}$
- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `hcap` &nbsp; $\eta \cdot c = \log\,(\#\,\iota)$
- `hcov` &nbsp; $(\nabla {W\,x\,v})_{{p}}{}^{{q}}({y}) = 0$

<small>plus 14 routine conditions (9 regularity, 4 setup, 1 typeclass) — full list in the per-track PDF.</small>

### `qiqt_gr_freefield_gaussian`

`qiqt_gr_freefield_gaussian` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hWarea` &nbsp; $\dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})$

and

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$

<small>plus 21 routine conditions (14 regularity, 7 setup) — full list in the per-track PDF.</small>

### `qiqt_gr_freefield_thermo`

`qiqt_gr_freefield_thermo` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; S({p\,x\,v\,t}) \le \eta \cdot A({x},{v},{t})$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \partial_{{b}}({\varphi})({x}))}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$

and

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `hcap` &nbsp; $\eta \cdot A({x},{v},{0}) = \log\,(\#\,\iota)$

<small>plus 29 routine conditions (21 regularity, 7 setup, 1 typeclass) — full list in the per-track PDF.</small>

### `qiqt_gr_freefield_geom`

`qiqt_gr_freefield_geom` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \partial_{{b}}({\varphi})({x}))}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$

and

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$

<small>plus 25 routine conditions (18 regularity, 7 setup) — full list in the per-track PDF.</small>

### `qiqt_gr_freefield_nullEnergy`

`qiqt_gr_freefield_nullEnergy` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \partial_{{b}}({\varphi})({x}))}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `hWarea` &nbsp; $\dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})$

and

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$

<small>plus 25 routine conditions (18 regularity, 7 setup) — full list in the per-track PDF.</small>

### `qiqt_gr_freefield_localized'`

`qiqt_gr_freefield_localized'` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `hWarea` &nbsp; $\dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \theta({y})})({x})$

and

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$

<small>plus 25 routine conditions (18 regularity, 7 setup) — full list in the per-track PDF.</small>

### `qiqt_gr_freefield_localized`

`qiqt_gr_freefield_localized` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$

and

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$

<small>plus 21 routine conditions (18 regularity, 3 setup) — full list in the per-track PDF.</small>

### `qiqt_gr_freefield`

`qiqt_gr_freefield` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot ({T({x})})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `hbridge` &nbsp; $({\lambda t \mapsto \mathrm{inner}\,\mathbb{C}\,(\mathrm{toLp}\,(\mathrm{ff}\,x\,v)\,\cdots )\,((\mathrm{modUnitary}\,(\mathrm{niceWedgeStandardSubspace}\,(\mathrm{mw}\,x\,v)\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,(\mathrm{ff}\,x\,v)\,\cdots ))})'({0})={i \cdot (\dot{K}({x},{v}))}$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$

and

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$

<small>plus 21 routine conditions (18 regularity, 3 setup) — full list in the per-track PDF.</small>

### `qiqt_gr_explicit_kg`

`qiqt_gr_explicit_kg` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T({x})\,\mu\,\nu = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$

and

- `hKG` &nbsp; $(\Box {\varphi})({x}) = {m}^{2} \cdot \varphi\,x$
- `hKMS` &nbsp; $\mathrm{WedgeKMSFlux\_complete}\,g\,(\mathrm{kgStress}\,m\,\varphi\,g\,\mathrm{gi})\,\mathrm{kd}\,\hbar$

<small>plus 15 routine conditions (12 regularity, 3 setup) — full list in the per-track PDF.</small>

### `qiqt_gr_from_flux_complete`

`qiqt_gr_from_flux_complete` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T_{{\mu}{\nu}}({x}) = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hflux` &nbsp; $\dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot ({T\,x})({v},{v})$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$

<small>plus 17 routine conditions (14 regularity, 3 setup) — full list in the per-track PDF.</small>

### Einstein field equations from a finite-information bound (Jacobson route)

`qiqt_bekenstein_gives_gr` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T_{{\mu}{\nu}}({x}) = G_{{\mu}{\nu}}({x}) + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ ({g\,x})({v},{v}) = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; S({x},{v},{t}) \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $S({x},{v},{0}) = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - S({x},{v},{t})$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - S({x},{v},{0}) = 0$
- `hFlux` &nbsp; $\dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot ({T\,x})({v},{v})$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto R_{{i}{j}}({x})})({v},{v})$

<small>plus 17 routine conditions (14 regularity, 3 setup) — full list in the per-track PDF.</small>

### `oneParticleBW_niceWedge_unconditional`

`oneParticleBW_niceWedge_unconditional` · *spine* —  we have

$$ \mathrm{modUnitary}\,(\mathrm{niceWedgeStandardSubspace}\,m\,\cdots \,\cdots )\,t = V\,t $$

<small>plus 2 routine conditions (2 regularity) — full list in the per-track PDF.</small>

### `freeField_oneParticle_hFlux`

`freeField_oneParticle_hFlux` · *spine* —  we have

$$ ({\lambda t \mapsto \mathrm{inner}\,\mathbb{C}\,(\mathrm{toLp}\,f\,\mathrm{hf2})\,((\mathrm{modUnitary}\,(\mathrm{niceWedgeStandardSubspace}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2}))})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})} $$

*assuming*

- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im}$

<small>plus 6 routine conditions (6 regularity) — full list in the per-track PDF.</small>

### `freeField_component_hFlux`

`freeField_component_hFlux` · *spine* —  we have

$$ \mathrm{kd} = 2 \cdot \pi / \hbar \cdot T_{kk} $$

*assuming*

- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im}$
- `hbridge` &nbsp; $({\lambda t \mapsto \mathrm{inner}\,\mathbb{C}\,(\mathrm{toLp}\,f\,\mathrm{hf2})\,((\mathrm{modUnitary}\,(\mathrm{niceWedgeStandardSubspace}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2}))})'({0})={i \cdot \mathrm{kd}}$

<small>plus 6 routine conditions (6 regularity) — full list in the per-track PDF.</small>


## Born rule

*Target 1 — the Born rule: reductions and a no-go*

### `finite_noCollapseBorn_fromNoncontextuality`

`finite_noCollapseBorn_fromNoncontextuality` · *capstone* —  there is $\rho$ such that all of:

1. $\rho.\mathrm{PosSemidef}$
2. $\rho.\mathrm{trace} = 1$
3. $(\forall (\omega : E.\Omega), \exists !h, \forall (t : \mathrm{Fin}\,n), \exists r\in (E.V\,\omega\,t).\mathrm{config}.\mathrm{active}, (E.V\,\omega\,t).\mathrm{ctx}.\mathrm{valueOf}\,r = h\,t)$
4. $(\forall (a : \mathrm{Fin}\,m), E.p\,a = (\rho \cdot P\,a).\mathrm{trace}.\mathrm{re})$
5. $(\forall (h : \mathrm{Fin}\,n \to \mathrm{Fin}\,m), E.P.\mathrm{massSet}\,\{\omega|E.\mathrm{actualHist}\,\omega = h\} = w\,E.p\,h)$
6. $E.P.\mathrm{massSet}\,\{\omega|{(n \cdot \varepsilon)}^{2} \le {(\mathrm{count}\,k\,(E.\mathrm{actualHist}\,\omega) - n \cdot E.p\,k)}^{2}\} \le E.p\,k \cdot (1 - E.p\,k) / (n \cdot {\varepsilon}^{2})$

*assuming*

- `hP` &nbsp; $\mathrm{IsEffect}\,(P\,a)$
- `hε` &nbsp; $0 < \varepsilon$
- `hn` &nbsp; $0 < n$

<small>plus 1 routine conditions (1 bridge) — full list in the per-track PDF.</small>

### `finite_effect_gleason`

`finite_effect_gleason` · *spine* —  there is $\rho$ such that all of:

1. $\rho.\mathrm{PosSemidef}$
2. $\rho.\mathrm{trace} = 1$
3. $\forall (E : \mathrm{Mat}\,(\mathrm{Fin}\,d)\,(\mathrm{Fin}\,d)\,\mathbb{C}), \mathrm{IsEffect}\,E \to (m.\mu\,E) = (\rho \cdot E).\mathrm{trace}$

### `positive_ray_certain_forces_born`

`positive_ray_certain_forces_born` · *spine* —  we have

$$ w\,E = \mathrm{born}\,\psi\,E $$

*assuming*

- `hψ` &nbsp; ${{\psi}}^{*} \cdot _{v} \psi = 1$
- `hadd` &nbsp; $w\,(A + B) = w\,A + w\,B$
- `hhom` &nbsp; $w\,(c \cdot A) = c \cdot w\,A$
- `hpsd` &nbsp; $\mathrm{NonnegC}\,(w\,(A.\mathrm{conjTranspose} \cdot A))$
- `hone` &nbsp; $w\,1 = 1$

<small>plus 1 routine conditions (1 bridge) — full list in the per-track PDF.</small>

### `continuous_additive_fMeasure_eq_born`

`continuous_additive_fMeasure_eq_born` · *spine* —  we have

$$ \mathrm{fMeasure}\,(f)\,w\,k = w\,k $$

*assuming*

- `hf` &nbsp; $\mathrm{Continuous}\,f$
- `h1` &nbsp; $f\,1 \ne 0$

<small>plus 1 routine conditions (1 setup) — full list in the per-track PDF.</small>

### `decoherent_partition_additive`

`decoherent_partition_additive` · *spine* —  we have

$$ \mathrm{born}\,\psi\,((\sum_{a S} C\,a).\mathrm{conjTranspose} \cdot \sum_{a S} C\,a) = \sum_{a S} \mathrm{born}\,\psi\,((C\,a).\mathrm{conjTranspose} \cdot C\,a) $$

*assuming*

- `hdec` &nbsp; $\mathrm{Decoherent}\,\psi\,C$

### `finite_noCollapseBornRepresentation`

`finite_noCollapseBornRepresentation` · *spine* —  we have all of:

1. $(\forall (\omega : E.\Omega), \exists !h, \forall (t : \mathrm{Fin}\,n), \exists r\in (E.V\,\omega\,t).\mathrm{config}.\mathrm{active}, (E.V\,\omega\,t).\mathrm{ctx}.\mathrm{valueOf}\,r = h\,t)$
2. $(\forall (h : \mathrm{Fin}\,n \to \mathrm{Fin}\,m), E.P.\mathrm{massSet}\,\{\omega|E.\mathrm{actualHist}\,\omega = h\} = w\,E.p\,h)$
3. $E.P.\mathrm{massSet}\,\{\omega|{(n \cdot \varepsilon)}^{2} \le {(\mathrm{count}\,k\,(E.\mathrm{actualHist}\,\omega) - n \cdot E.p\,k)}^{2}\} \le E.p\,k \cdot (1 - E.p\,k) / (n \cdot {\varepsilon}^{2})$

*assuming*

- `hε` &nbsp; $0 < \varepsilon$
- `hn` &nbsp; $0 < n$

### `product_born_measure_unique`

`product_born_measure_unique` · *spine* —  we have

$$ \mu\,S = ((\mathrm{kronN}\,\lambda x \mapsto \rho) \cdot \mathrm{eventEffect}\,E\,S).\mathrm{trace}.\mathrm{re} $$

*assuming*

- `hρ` &nbsp; $\rho.\mathrm{PosSemidef}$
- `hE` &nbsp; $(E\,k).\mathrm{PosSemidef}$
- `hμ0` &nbsp; $\mu\,\emptyset = 0$
- `hμins` &nbsp; $a\notin S \to \mu\,(\mathrm{insert}\,a\,S) = \mu\,\{a\} + \mu\,S$
- `hpt` &nbsp; $\mu\,\{\omega\} = \prod_{t} \mathrm{bornProb}\,\rho\,E\,(\omega\,t)$

### `chebyshev_freq`

`chebyshev_freq` · *spine* —  we have

$$ \sum_{\omega} w\,p\,\omega \le p\,k \cdot (1 - p\,k) / (N \cdot {\varepsilon}^{2}) $$

*assuming*

- `hp` &nbsp; $0 \le p\,i$
- `hp1` &nbsp; $\sum_{i} p\,i = 1$
- `hε` &nbsp; $0 < \varepsilon$
- `hN` &nbsp; $0 < N$

### `qiqth_born_typicality_conditional`

`qiqth_born_typicality_conditional` · *spine* —  we have

$$ \mathrm{expectedIndicator}\,\mathrm{outcome}\,M.\mu\,k = {c\,k}^{2} $$

### `born_distribution_realizable_conditional`

`born_distribution_realizable_conditional` · *nogo* —  there is $\mu$ such that all of:

1. $(\forall (\gamma : \Gamma), 0 \le \mu\,\gamma)$
2. $\sum_{\gamma} \mu\,\gamma = 1$
3. $\forall (k : \mathrm{Outcome}), \mathrm{outcomeMarginal}\,\mathrm{outcome}\,\mu\,k = {c\,k}^{2}$

*assuming*

- `h_surj` &nbsp; $\mathrm{Surjective}\,\mathrm{outcome}$
- `hc_norm` &nbsp; $\sum_{k} {c\,k}^{2} = 1$

### `decoherence_does_not_concentrate`

`decoherence_does_not_concentrate` · *nogo* —  we have all of:

1. $0 < \mathrm{branchWeight}\,c\,0$
2. $0 < \mathrm{branchWeight}\,c\,1$

*assuming*

- `h0` &nbsp; $c\,0 \ne 0$
- `h1` &nbsp; $c\,1 \ne 0$

### `support_preservation_does_not_imply_measure_preservation`

`support_preservation_does_not_imply_measure_preservation` · *nogo* —  there is $T,\ \mu$ such that all of:

1. $\mathrm{Bijective}\,T$
2. $\mathrm{SupportPreserving}\,T$
3. $\neg \mathrm{MeasurePreserving}\,T\,\mu$

### `operational_data_insufficient`

`operational_data_insufficient` · *nogo* —  there is $\mathrm{outcome},\ \nu_{1},\ \nu_{2}$ such that all of:

1. $(\forall (k : \mathrm{Fin}\,2), \mathrm{marginal3to2}\,\nu_{1}\,\mathrm{outcome}\,k = \mathrm{marginal3to2}\,\nu_{2}\,\mathrm{outcome}\,k)$
2. $\nu_{1} \ne \nu_{2}$


## Lorentz covariance

*Target 2 — Lorentz covariance of the selection*

### `upvm_covariant_probability`

`upvm_covariant_probability` · *capstone* —  we have all of:

1. $(\forall (x : P.X\,D), 0 \le \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D\,x)$
2. $.\mathrm{sum}\,(\mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D) = 1$
3. $\forall (x : P.X\,D), \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,((A.\mathrm{act}\,g)\,D)\,((A.\gamma\,g\,D)\,x) = \mathrm{uborn}\,B.\mathrm{toUniformBornData}\,D\,x$

### `evaluation_covariance`

`evaluation_covariance` · *spine* —  we have

$$ \mathrm{selector}\,(\mathrm{actSection}\,g\,\mathrm{lam})\,(g.\mathrm{act}\,D) = (g.\gamma\,D)\,(\mathrm{selector}\,\mathrm{lam}\,D) $$

### `group_evaluation_covariance`

`group_evaluation_covariance` · *spine* —  we have

$$ \mathrm{selector}\,(\mathrm{actSection}\,(A.\mathrm{toPoincare}\,g)\,\mathrm{lam})\,((A.\mathrm{act}\,g)\,D) = (A.\gamma\,g\,D)\,(\mathrm{selector}\,\mathrm{lam}\,D) $$

### `freeFieldMeasure_boost_invariant`

`freeFieldMeasure_boost_invariant` · *spine* —  we have

$$ \mathrm{map}\,(\mathrm{diagBoost}\,e)\,(\mathrm{freeFieldMeasure}\,\nu) = \mathrm{freeFieldMeasure}\,\nu $$

*assuming*

- `hν` &nbsp; $\mathrm{map}\,(\mathrm{boostMap}\,e)\,\nu = \nu$

<small>plus 1 routine conditions (1 typeclass) — full list in the per-track PDF.</small>

### `bh_typicalityMeasure_exists`

`bh_typicalityMeasure_exists` · *spine* —  there is $\mu$ such that all of:

1. $\mathrm{IsProbabilityMeasure}\,\mu$
2. $(\mathrm{diagNet}\,\mathrm{hb}\,\mathrm{hp}\,\mathrm{hsum}\,\mathrm{hp1}\,g).\mathrm{toFiniteMarginals}.\mathrm{IsLimit}\,\mu$

*assuming*

- `hb` &nbsp; $\mathrm{Orthonormal}\,\mathbb{C}\,b$
- `hp` &nbsp; $0 \le p\,i$
- `hsum` &nbsp; $\mathrm{Summable}\,p$
- `hp1` &nbsp; $\sum ' (i : \kappa), p\,i = 1$

<small>plus 4 routine conditions (4 typeclass) — full list in the per-track PDF.</small>

### `fock_typicalityMeasure_exists`

`fock_typicalityMeasure_exists` · *spine* —  there is $\mu$ such that all of:

1. $\mathrm{IsProbabilityMeasure}\,\mu$
2. $(\mathrm{fockVacuumNet}\,g).\mathrm{toFiniteMarginals}.\mathrm{IsLimit}\,\mu$

<small>plus 3 routine conditions (3 typeclass) — full list in the per-track PDF.</small>

### `continuum_volume_selects`

`continuum_volume_selects` · *spine* —  we have

$$ \mathrm{volume}\,\{\mathrm{seed}|\mathrm{selects}\,(\mathrm{contWeights}\,S\,\xi\,s)\,\mathrm{seed}\,k\} = {{\mathrm{contWeights}\,S\,\xi\,s\,k}} $$

<small>plus 1 routine conditions (1 typeclass) — full list in the per-track PDF.</small>

### `no_signaling`

`no_signaling` · *spine* —  we have

$$ S.P\,x\,a\,y = S.\mathrm{PAlice}\,x\,a $$

### `bipartite_no_signaling`

`bipartite_no_signaling` · *spine* —  we have

$$ \sum_{b} (\rho \cdot \mathrm{kroneckerMap}\,(\lambda x_{1} x_{2} \mapsto x_{1} \cdot x_{2})\,E\,(F\,b)).\mathrm{trace} = (\rho \cdot \mathrm{kroneckerMap}\,(\lambda x_{1} x_{2} \mapsto x_{1} \cdot x_{2})\,E\,1).\mathrm{trace} $$

*assuming*

- `hF` &nbsp; $\sum_{b} F\,b = 1$

### `no_covariant_selector`

`no_covariant_selector` · *nogo* —  we have

$$ \bot $$

*assuming*

- `equiv` &nbsp; $\sigma\,(\mathrm{actS}\,\Phi) = \mathrm{actH}\,(\sigma\,\Phi)$
- `hΦ` &nbsp; $\mathrm{actS}\,\Phi = \Phi$
- `hno` &nbsp; $\mathrm{actH}\,h \ne h$

### `bool_swap_no_selector`

`bool_swap_no_selector` · *nogo* —  we have

$$ \bot $$

*assuming*

- `equiv` &nbsp; $\sigma\,u = !\sigma\,u$
