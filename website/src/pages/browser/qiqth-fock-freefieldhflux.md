---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.FreeFieldHFlux
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.FreeFieldHFlux — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← CyclicWitness](/browser/qiqth-fock-cyclicwitness) · [Localization →](/browser/qiqth-fock-localization) </small>

<small>Fock · entries 231–235 of 1000</small>

<a id="d-qiqth-fock-hasderivat-modularenergy-of-boost-pos"></a>
**Lemma 231** (`hasDerivAt_modularEnergy_of_boost_pos`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L25)</small>

**Modular energy = boost energy, in the `+2π` convention** (sign-flipped copy of `hasDerivAt_modularEnergy_of_boost`).  Given the BW identification `modUnitary S = boostUnitary(+2π·)`, the modular-energy derivative of `ξ` equals its boost-energy derivative.

$$
(\forall (t : \mathbb{R}) (u : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,u = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,u) \to \forall (\xi : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})) (c : \mathbb{C}), ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,\xi}\rangle})'({0})={c} \to ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\xi}\rangle})'({0})={c}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge).</small>

<a id="d-qiqth-fock-freefield-modularenergy-eq-boostcharge"></a>
**Lemma 232** (`freeField_modularEnergy_eq_boostCharge`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L40)</small>

**The free-field modular-energy = stress-flux derivative, BW supplied internally (Phase 2).**  For the nice-wedge standard subspace `S` and ANY mode `ξ`, given the boost-charge derivative `HasDerivAt (t ↦ ⟨ξ, boostUnitary(2πt) ξ⟩) c 0`, the modular-energy derivative `HasDerivAt (t ↦ ⟨ξ, modUnitary S t ξ⟩) c 0` holds — with the Bisognano–Wichmann identification `modUnitary S = boostUnitary(+2π·)` supplied internally and axiom-free by `oneParticleBW_niceWedge_unconditional` (no labelled `hUniq`/`hStrip`, no sign mismatch).

$$
({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,\xi}\rangle})'({0})={c} \to ({\lambda t \mapsto \langle {\xi},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t)\,\xi}\rangle})'({0})={c}
$$

*Proof.* By [`oneParticleBW_niceWedge_unconditional`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [`hasDerivAt_modularEnergy_of_boost_pos`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-hasderivat-modularenergy-of-boost-pos). $\square$

<small>Used by [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux).</small>

<a id="d-qiqth-fock-hasderivat-inner-boostunitary-imaginary-pos"></a>
**Lemma 233** (`hasDerivAt_inner_boostUnitary_imaginary_pos`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L64)</small>

**The `+2π` boost-charge derivative (purely imaginary), by the `t → −t` reflection** of the `−2π` `hasDerivAt_inner_boostUnitary_imaginary`.  Because `⟪ξ, boostUnitary(2πt) ξ⟫ = ⟪ξ, boostUnitary(−2π(−t)) ξ⟫`, the `+2π` correlation is the `−2π` one precomposed with negation, so its derivative is the negative: `d/dt ⟪ξ, boostUnitary(2π t) ξ⟫|₀ = i·((−(2π·∫ conj(f)·f')).im)`.  Reuses the hard dominated-convergence proof of the `−2π` lemma — no re-derivation.  Axiom-free.

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im}}
$$

*Proof.* By [`hasDerivAt_inner_boostUnitary_imaginary`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-hasderivat-inner-boostunitary-imaginary). $\square$

<small>Used by [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux).</small>

<a id="d-qiqth-fock-freefield-oneparticle-hflux"></a>
**Theorem 234** (`freeField_oneParticle_hFlux`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L104)</small>

**The free-field one-particle `hFlux`, FULLY ASSEMBLED in the satisfiable `+2π` convention.**  For any smooth wedge state `ξ = f.toLp` and the nice-wedge standard subspace `S`, the modular-energy derivative is `i·(2π/ℏ)·T_kk`: `HasDerivAt (t ↦ ⟪ξ, modUnitary S t ξ⟫) (i·(2π/ℏ·T_kk)) 0`, with EVERYTHING operator/analytic discharged axiom-free — the Bisognano–Wichmann identification (`oneParticleBW_niceWedge_unconditional`) and the boost-charge derivative (`hasDerivAt_inner_boostUnitary_imaginary_pos`) are both supplied internally.  The ONLY labelled input is the single scalar physics identification `hTkk : (2π/ℏ)·T_kk = (−(2π·∫ conj(f)·f')).im` (the conserved boost Killing charge = stress-tensor flux, in the `+2π` orientation). …

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to \forall (\hbar T_{kk} : \mathbb{R}), 2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im} \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot (2 \cdot \pi / \hbar \cdot T_{kk})}
$$

*Proof.* By [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [`hasDerivAt_inner_boostUnitary_imaginary_pos`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-hasderivat-inner-boostunitary-imaginary-pos), [`boostUnitary`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary). $\square$

<small>Used by [`freeField_component_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-component-hflux), [`qiqt_gr_freefield_localized`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized).</small>

<a id="d-qiqth-fock-freefield-component-hflux"></a>
**Theorem 235** (`freeField_component_hFlux`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/FreeFieldHFlux.lean#L134)</small>

**The free-field per-generator flux equation `kd = (2π/ℏ)·T_kk` (the `+2π`/nice-wedge analog of `component_hFlux_of_wedgeKMS_complete`).**  For the nice-wedge standard subspace `S` and smooth wedge state `ξ = f.toLp`, given (i) `hbridge` — that the abstract per-generator modular-energy coefficient `kd` IS the derivative of `t ↦ ⟪ξ, modUnitary S t ξ⟫` — and (ii) `hTkk` — the localization identification of the horizon stress component `T_kk` with the mode's rapidity stress flux — derivative uniqueness pins `kd = (2π/ℏ)·T_kk`. …

$$
\mathrm{Integrable}\,f\,\mathrm{volume} \to (\forall (x : \mathbb{R}), ({f})'({x})={f^{\prime}\,x}) \to \mathrm{AEStronglyMeasurable}\,f^{\prime}\,\mathrm{volume} \to \forall (B : \mathbb{R}), (\forall (x : \mathbb{R}), \|f^{\prime}\,x\| \le B) \to \forall (\hbar \mathrm{kd} T_{kk} : \mathbb{R}), 2 \cdot \pi / \hbar \cdot T_{kk} = (-(2 \cdot \pi \cdot \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,\theta) \cdot f^{\prime}\,\theta)).\mathrm{im} \to ({\lambda t \mapsto \langle {\mathrm{toLp}\,f\,\mathrm{hf2}},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t)\,(\mathrm{toLp}\,f\,\mathrm{hf2})}\rangle})'({0})={i \cdot \mathrm{kd}} \to \mathrm{kd} = 2 \cdot \pi / \hbar \cdot T_{kk}
$$

*Proof.* By [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux). $\square$

<small>Used by [`freeField_kd_conclusion`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-freefield-kd-conclusion).</small>

---
<small>[← all sections](/browser) · [← CyclicWitness](/browser/qiqth-fock-cyclicwitness) · [Localization →](/browser/qiqth-fock-localization) </small>