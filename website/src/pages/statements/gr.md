---
layout: ../../layouts/Deep.astro
title: "GR field equations"
eyebrow: "Target 3 — QIQT-H gives the Einstein field equations"
description: "GR field equations — QIQT-H headline statements machine-translated from Lean, each with the author's explanation, conclusion and load-bearing hypotheses."
---

<small>[← all targets](/statements) · [Target 1 →](/statements/born)</small>

*Target 3 — QIQT-H gives the Einstein field equations*

## Einstein field equations for the free field (all geometric inputs discharged)

**The maximally-discharged free-field QIQT→GR capstone.**  Einstein's equations for the explicit free Klein–Gordon field, with the entropy/heat functionals built from a finite record law (T3-1, discharging `hsat`/`hDnn`/`hD0`) AND the wedge mode built from φ as `↑(∑ₐ vₐ ∂ₐφ)·gaussMode ℏ` (T3-3-C3, discharging `hTkk` and the whole `ff` regularity block), on top of the `hbridge`/`hFocus`/`hWarea`-discharged ladder. Surviving labelled inputs: the dynamical FQ capacity bound `hbound`, the FQ reference identification `hcap`, the realization derivatives `hS`/`hK`/`hA`, the Raychaudhuri congruence setup, geometry scaffolding, and the matter EOM `hKG`.  Axiom-free.

`qiqt_gr_freefield_complete` · *capstone* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$
- `hcap` &nbsp; $\eta \cdot A({x},{v},{0}) = \log\,(\#\,\iota)$
- `hbound` &nbsp; $\href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to \text{for }t\text{ near }0,\; \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p\,x\,v\,t})} \le \eta \cdot A({x},{v},{t})$

<small>plus 25 routine conditions (17 regularity, 7 setup, 1 typeclass) — full list in the per-track PDF.</small>

## Einstein field equations on an explicit pp-wave spacetime

**The instantiated showcase: QIQT→GR for the explicit pp-wave spacetime, floor laid bare.**  The Einstein equations `a·kgStress = G + Λg` with `g = ppMetric H`, with **every geometric and analytic premise discharged** — the pp-wave metric/tetrad (via `qiqt_gr_ppwave`), the area derivative `hA` (via `area_hasDerivAt_of_covConst`, the expansion-free congruence), and the entropy bound `hbound` (via `shannon_le_log_card`, the area = holographic capacity).  The only remaining hypotheses are the irreducible floor: the matter EOM `hKG`, the FQ capacity `hcap` (`η·c = log|R|` = P4), and the localization map `hS`/`hK` (the field-coupled record law whose entropy rate is the stress flux — Gap-2), plus the covariantly-constant congruence and constants. …

`qiqt_gr_ppwave_showcase` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot \href{/browser/qiqth-ppwavemetric#d-qiqth-curvature-ppmetric}{g^{\mathrm{pp}}}\,H\,x\,\mu\,\nu $$

*assuming*

- `hCH` &nbsp; $({H})\in C^{\infty}$
- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$
- `hcap` &nbsp; $\eta \cdot c = \log\,(\#\,\iota)$
- `hcov` &nbsp; $\href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {W\,x\,v})_{{p}}{}^{{q}}({y})} = 0$

<small>plus 14 routine conditions (9 regularity, 4 setup, 1 typeclass) — full list in the per-track PDF.</small>

## `qiqt_gr_freefield_gaussian`

**The free-field QIQT→GR capstone with the localization mode constructed from the field.**  Identical to `qiqt_gr_freefield_nullEnergy`, but the wedge mode `ff` and its derivative `ff'`, all their regularity, and the localization identity `hTkk` are no longer inputs — they are BUILT from `φ`: `ff x v θ := ↑(∑ₐ vₐ ∂ₐφ(x))·gaussMode ℏ θ`.  `hTkk` is discharged by `localized_mode_hTkk` + `gaussMode_calibration`.  Only the Clausius/area physics (`hbound`/`hsat`/`hDnn`/`hD0`/`hK`) and the Raychaudhuri congruence setup (`hWx`/`hWC`/`hWgeo`/`hWequil`/`hWarea`) remain labelled.  Axiom-free.

`qiqt_gr_freefield_gaussian` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hWarea` &nbsp; $\dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x})$

and

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$

<small>plus 21 routine conditions (14 regularity, 7 setup) — full list in the per-track PDF.</small>

## `qiqt_gr_freefield_thermo`

**The THERMODYNAMIC free-field QIQT→GR capstone.**  Einstein's equations for the explicit free Klein–Gordon field, with the entropy/heat functionals CONSTRUCTED from a per-generator finite record law `pp` (a probability distribution for each deformation `t`, uniform at the equilibrium reference), and the saturation + relative-entropy premises (`hsat`/`hDnn`/`hD0`) DISCHARGED internally via `clausius_package_from_finite_model` (the axiom-free finite core: Gibbs/Jensen, uniform saturation, classical Klein). …

`qiqt_gr_freefield_thermo` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \href{/browser/qiqth-branchledger#d-qiqth-branchledger-shannon}{S({p\,x\,v\,t})} \le \eta \cdot A({x},{v},{t})$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({x})})}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$

and

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$
- `hcap` &nbsp; $\eta \cdot A({x},{v},{0}) = \log\,(\#\,\iota)$

<small>plus 29 routine conditions (21 regularity, 7 setup, 1 typeclass) — full list in the per-track PDF.</small>

## `qiqt_gr_freefield_geom`

**Stage 2′ (T3-3, option b): `hWarea` discharged — `ad` defined geometrically.**  Identical to `qiqt_gr_freefield_nullEnergy`, but the area first-variation rate `ad` is no longer an abstract parameter paired with the labelled identity `hWarea`; it is **defined** as the congruence-expansion derivative `ad x v := −∑ᵥ Wˣᵛ ∂ᵥ θ[Wˣᵛ]`, so `hWarea` becomes `rfl`.  `hA` (the area functional's rate) now reads in that explicit geometric form. …

`qiqt_gr_freefield_geom` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({x})})}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$

and

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$

<small>plus 25 routine conditions (18 regularity, 7 setup) — full list in the per-track PDF.</small>

## `qiqt_gr_freefield_nullEnergy`

**Stage 3 (T3-3): `hTkk` in transparent form — the single irreducible localization input.**  Identical to `qiqt_gr_freefield_localized'`, but the one surviving Gap-2 input `hTkk` is stated in its *physically transparent* form via the Stage-0 null-stress identity `BL(kgStress) v = (∑ₐ vₐ ∂ₐφ)²`:

`2π/ℏ · (∑ₐ vₐ ∂ₐφ(x))²  =  (−2π ∫ conj(ff x v)·ff' x v).im`. …

`qiqt_gr_freefield_nullEnergy` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot {(\sum_{b} v\,b \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{b}}({\varphi})({x})})}^{2} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `hWarea` &nbsp; $\dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x})$

and

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$

<small>plus 25 routine conditions (18 regularity, 7 setup) — full list in the per-track PDF.</small>

## `qiqt_gr_freefield_localized'`

**Stage 2 (T3-3): `hFocus` discharged via Raychaudhuri.**  The localized free-field capstone with the focusing identity `hFocus` (`ad = R_kk`) no longer assumed but DERIVED from the machine-checked Raychaudhuri equation (`hFocus_of_raychaudhuri`): per null generator `(x,v)` we supply a smooth geodesic congruence `W x v` through `(x,v)` (`hWx : W x v x = v`), at equilibrium (`hWequil`, the shear–expansion quadratic vanishes — Jacobson's stationary/bifurcation horizon), with the area-vs-expansion identification `hWarea`. The Raychaudhuri *focusing law* `ad = BL(Ric) v` is then proved (no Einstein presupposed); christoffel smoothness is itself discharged (`christoffel_contDiff`). …

`qiqt_gr_freefield_localized'` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot ({\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})}})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `hWarea` &nbsp; $\dot{A}({x},{v}) = -\sum_{\nu} W\,x\,v\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x})$

and

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$

<small>plus 25 routine conditions (18 regularity, 7 setup) — full list in the per-track PDF.</small>

## `qiqt_gr_freefield_localized`

**Stage 1 (T3-3): `hbridge` discharged.**  The free-field QIQT→GR capstone with the heat coefficient FIXED to the boost flux `kd x v := (2π/ℏ)·BL(kgStress) v` and the modular-localization hypothesis `hbridge` DERIVED internally from `freeField_oneParticle_hFlux` (the axiom-free `+2π` one-particle Bisognano–Wichmann machinery) given `hTkk`.  The thermodynamic premise `hK` now reads `HasDerivAt (KE x v) ((2π/ℏ)·T_kk) 0` — the genuine Clausius statement that the heat-functional rate IS the boost-energy flux (correctly kept labelled).  Of the Gap-2 localization map only `hTkk` (Stage 3) and the focusing identity `hFocus` (Stage 2) survive as inputs.  Axiom-free.

`qiqt_gr_freefield_localized` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot ({\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})}})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})$

and

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$

<small>plus 21 routine conditions (18 regularity, 3 setup) — full list in the per-track PDF.</small>

## `qiqt_gr_freefield`

**THE FREE-FIELD QIQT→GR CAPSTONE.**  Einstein's equations for the explicit free Klein–Gordon field, with the wedge-KMS modular flux supplied entirely by the axiom-free `+2π` one-particle Bisognano–Wichmann machinery — NOT a labelled `WedgeKMSFlux_complete` bundle.  Identical to `qiqt_gr_explicit_kg` (geometry `hC`/`hric_symm`/`hreg`, matter `conserv`, and `hT_symm` all discharged internally for `kgStress`), but the modular input is the per-null-generator localization datum `(mw, f, f', …, hTkk, hbridge)` feeding `freeField_kd_conclusion`. …

`qiqt_gr_freefield` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot ({\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})}})({v},{v}) = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{ff}\,x\,v\,\theta) \cdot \mathrm{ff}^{\prime}\,x\,v\,\theta)).\mathrm{im}$
- `hbridge` &nbsp; $({\lambda t \mapsto \langle {\mathrm{toLp}\,(\mathrm{ff}\,x\,v)\,\cdots },{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,(\mathrm{mw}\,x\,v)\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,(\mathrm{ff}\,x\,v)\,\cdots )}\rangle})'({0})={i \cdot (\dot{K}({x},{v}))}$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})$

and

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$

<small>plus 21 routine conditions (18 regularity, 3 setup) — full list in the per-track PDF.</small>

## `qiqt_gr_explicit_kg`

**THE QIQT→GR EINSTEIN EQUATIONS FOR THE EXPLICIT FREE KLEIN–GORDON FIELD, axiom-free.** Specialising the abstract `qiqt_gr_from_wedge_kms_complete` to `T = kgStress` (the concrete KG stress tensor): the matter-conservation input `conserv` is discharged INTERNALLY (`kg_conserv_of_contDiff`, from `ContDiff` smoothness of `φ, g, gi` + the equation of motion `□φ = m²φ`), and the stress-tensor symmetry is proved from metric symmetry. …

`qiqt_gr_explicit_kg` · *spine* —  there is $\Lambda$ such that

$$ a \cdot \href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{T({x})\,\mu\,\nu} = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})$

and

- `hKG` &nbsp; $\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-boxfield}{(\Box {\varphi})({x})} = {m}^{2} \cdot \varphi\,x$
- `hKMS` &nbsp; $\href{/browser/qiqth-wedgekmstogr#d-qiqth-wedgekmstogr-wedgekmsflux-complete}{\mathrm{WedgeKMSFlux\_complete}}\,g\,(\href{/browser/qiqth-kgstressconservation#d-qiqth-curvature-kgstress}{\mathrm{kgStress}}\,m\,\varphi\,g\,\mathrm{gi})\,\mathrm{kd}\,\hbar$

<small>plus 15 routine conditions (12 regularity, 3 setup) — full list in the per-track PDF.</small>

## `qiqt_gr_from_flux_complete`

**THE GOAL THEOREM, taking the per-generator flux EQUATION directly.**  Identical to `qiqt_gr_from_wedge_kms_complete`, but the modular input is the bare conclusion `hflux : kd x v = (2π/ℏ)·BL(T x)v` per null generator — exactly what `qiqt_bekenstein_gives_gr` consumes — instead of the `WedgeKMSFlux_complete` (`−2π`/`wedgeGenSet`) bundle.  This is the convention-agnostic GR entry point: the bundle supplies `hflux` via `hFlux_of_wedgeKMS_complete`, and the free-field `+2π` route supplies it via `freeField_component_hFlux` — both land here.  Axiom-free, no `sorry`.

`qiqt_gr_from_flux_complete` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T_{{\mu}{\nu}}({x}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; \mathrm{Sf}\,x\,v\,t \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $\mathrm{Sf}\,x\,v\,0 = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - \mathrm{Sf}\,x\,v\,t$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - \mathrm{Sf}\,x\,v\,0 = 0$
- `hflux` &nbsp; $\dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({T\,x})({v},{v})}$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})$

<small>plus 17 routine conditions (14 regularity, 3 setup) — full list in the per-track PDF.</small>

## Einstein field equations from a finite-information bound (Jacobson route)

**THE END-TO-END THEOREM — QIQT-H + (cited Bisognano–Wichmann & Raychaudhuri) ⇒ the Einstein field equations.**  Assembles the whole chain into one theorem.  Along each local null generator `(x, v)` (with `v` metric-null), QIQT-H's content — the capacity **bound** `S ≤ η·A` (`shannon_le_log_card`), saturation at the reference (`shannon_uniform_eq_log_card`), and relative-entropy positivity (Klein, `relEntropy_nonneg`) — DERIVES the differential area law / modular relation, which with the two **cited** inputs (`hFlux` = Bisognano–Wichmann boost flux, `hFocus` = Raychaudhuri focusing) gives Jacobson's per-null premise; `jacobson_einstein_equation_of_state` then yields `a·T = G + Λ·g` with genuine Einstein tensor and constant `Λ`. …

`qiqt_bekenstein_gives_gr` · *spine* —  there is $\Lambda$ such that

$$ a \cdot T_{{\mu}{\nu}}({x}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x}) $$

*assuming*

when $ \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 $&nbsp;:

- `hbound` &nbsp; $\text{for }t\text{ near }0,\; S({x},{v},{t}) \le \eta \cdot A({x},{v},{t})$
- `hsat` &nbsp; $S({x},{v},{0}) = \eta \cdot A({x},{v},{0})$
- `hDnn` &nbsp; $\forall (t : \mathbb{R}), 0 \le \mathrm{KE}({x},{v},{t}) - S({x},{v},{t})$
- `hD0` &nbsp; $\mathrm{KE}({x},{v},{0}) - S({x},{v},{0}) = 0$
- `hFlux` &nbsp; $\dot{K}({x},{v}) = 2 \cdot \pi / \hbar \cdot \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({T\,x})({v},{v})}$
- `hFocus` &nbsp; $\dot{A}({x},{v}) = ({\lambda i j \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{i}{j}}({x})}})({v},{v})$

<small>plus 17 routine conditions (14 regularity, 3 setup) — full list in the per-track PDF.</small>

## `oneParticleBW_niceWedge_unconditional`

**THE free-field one-particle Bisognano–Wichmann — FULLY UNCONDITIONAL, axiom-free.** For every mass `m > 0` and every candidate boost representation `V t = boostUnitary(2πt)`, the modular flow of the nice-core wedge standard subspace equals the boost: `modUnitary S t = V t`, with NO Reeh–Schlieder hypotheses whatsoever.  BOTH analytic inputs are now discharged internally and unconditionally: `niceWedgeSeparating_pos_mass` (Pauli–Jordan symplectic non-degeneracy, via the KMS uniqueness argument) and `niceWedgeCyclic_pos_mass` (wedge-totality, via the Wiener–Tauberian theorem). …

`oneParticleBW_niceWedge_unconditional` · *spine* —  we have

$$ \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t = V\,t $$

<small>plus 2 routine conditions (2 regularity) — full list in the per-track PDF.</small>

## `freeField_oneParticle_hFlux`

**The free-field one-particle `hFlux`, FULLY ASSEMBLED in the satisfiable `+2π` convention.**  For any smooth wedge state `ξ = f.toLp` and the nice-wedge standard subspace `S`, the modular-energy derivative is `i·(2π/ℏ)·T_kk`: `HasDerivAt (t ↦ ⟪ξ, modUnitary S t ξ⟫) (i·(2π/ℏ·T_kk)) 0`, with EVERYTHING operator/analytic discharged axiom-free — the Bisognano–Wichmann identification (`oneParticleBW_niceWedge_unconditional`) and the boost-charge derivative (`hasDerivAt_inner_boostUnitary_imaginary_pos`) are both supplied internally.  The ONLY labelled input is the single scalar physics identification `hTkk : (2π/ℏ)·T_kk = (−(2π·∫ conj(f)·f')).im` (the conserved boost Killing charge = stress-tensor flux, in the `+2π` orientation). …

`freeField_oneParticle_hFlux` · *spine* —  we have

$$ ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})} $$

*assuming*

- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im}$

<small>plus 6 routine conditions (6 regularity) — full list in the per-track PDF.</small>

## `freeField_component_hFlux`

**The free-field per-generator flux equation `kd = (2π/ℏ)·T_kk` (the `+2π`/nice-wedge analog of `component_hFlux_of_wedgeKMS_complete`).**  For the nice-wedge standard subspace `S` and smooth wedge state `ξ = f.toLp`, given (i) `hbridge` — that the abstract per-generator modular-energy coefficient `kd` IS the derivative of `t ↦ ⟪ξ, modUnitary S t ξ⟫` — and (ii) `hTkk` — the localization identification of the horizon stress component `T_kk` with the mode's rapidity stress flux — derivative uniqueness pins `kd = (2π/ℏ)·T_kk`. …

`freeField_component_hFlux` · *spine* —  we have

$$ \mathrm{kd} = 2 \cdot \pi / \hbar \cdot T_{kk} $$

*assuming*

- `hTkk` &nbsp; $2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im}$
- `hbridge` &nbsp; $({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot \mathrm{kd}}$

<small>plus 6 routine conditions (6 regularity) — full list in the per-track PDF.</small>
