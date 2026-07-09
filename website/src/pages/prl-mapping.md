---
layout: ../layouts/Deep.astro
title: "PRL → Lean: the derivation, step by step"
eyebrow: Related work, mapped
description: Every step of Dorau & Much's Physical Review Letters derivation of the semiclassical Einstein equations, mapped to the QIQT-H Lean theorem that formalizes it — for the free field. The mapping itself is a human-audited correspondence; each Lean theorem is machine-checked.
---

In 2026, **Dorau & Much** published *"From Quantum Relative Entropy to the Semiclassical Einstein
Equations"* in **Physical Review Letters** ([arXiv:2510.24491](https://arxiv.org/abs/2510.24491)) — a
pen-and-paper argument ("arguments indicating") that the semiclassical Einstein equations follow from
the Araki–Uhlmann relative entropy of a scalar field across a local Rindler horizon. This page maps
their derivation, equation by equation, onto the QIQT-H Lean 4 theorem that formalizes each step, for
the **free Klein–Gordon field**.

<div class="note" style="border-left-color:var(--st-conditional)">

**Read this first — what this table is and isn't.** Their paper came *first* (arXiv Oct 2025, PRL
2026), before the QIQT-H GR chain was formalized: this is a **formalization** of a published result, and
**no priority is claimed**. Each *Lean theorem* below is machine-checked (axiom-free, standard three).
The **correspondence** between a PRL equation and a Lean theorem is a *human-audited* judgment — the one
thing a proof assistant cannot mechanize (the adequacy question). And both derivations take the
entropy–area relation `S = δA/4` as an input; see the last two rows.

</div>

## The chain

| # | PRL step (Dorau & Much) | QIQT-H Lean theorem | status |
|---|---|---|---|
| Eq. (2) | Free Klein–Gordon field, `(□+m²)Φ = 0`, as the substrate | the free-field one-particle / Fock sector (`Fock/*`) | machine-checked |
| Eq. (3) | Kay–Wald universal scaling-limit two-point function on the horizon | one-particle Fock wedge structure (`Fock/OneParticle*`) | machine-checked |
| Eq. (4) | Modular flow = geometric boost, `Δ_R^{it} = 𝔇_{2πt}` (Summers–Verch / Bisognano–Wichmann) | `oneParticleBW_niceWedge_unconditional` — and, lifted to the whole field algebra, `freeField_secondQuant_BW_unconditional` | machine-checked, **unconditional** |
| Eq. (10) | Araki–Uhlmann formula for coherent states, `S_rel = i·d/dt⟨Ω_φ\|Δ^{it}Ω_φ⟩` | `arakiEntropy_eq_relEntropy` (the coherent-state Araki reduction) | machine-checked |
| Eq. (12) | `S_rel = −2π∫U(∂_Uφ)²` — the Casini–Grillo–Pontello coherent-state entropy | `cgpEntropy_eq_integral_kFn`, `cgpEntropy_nonneg` | machine-checked |
| Eq. (13) | `S_rel = −2π∫U⟨:T_ab:⟩ξ^aξ^b` — relative entropy **=** horizon energy flux `δQ` (the first law) | `modular_casini_bound`, `finiteCorner_firstLaw_boostEnergy` (`ModularEnergyBound`) | machine-checked |
| Eq. (22) | Raychaudhuri equation for the null congruence (`θ = σ = ω = 0` on the horizon) | `raychaudhuri_geodesic`, `raychaudhuri_focusing` | machine-checked |
| Eqs. (20) = (24) | Entropic area variation **=** geometric area variation (`δA ↔ R_ab ξ^aξ^b`) | `differential_area_law` (`DifferentialAreaLaw`) | machine-checked |
| Eqs. (26)–(27) | `α⟨:T_ab:⟩ = R_ab + N g_ab`; conservation `∇^a⟨:T_ab:⟩ = 0 ⟹ N = −R/2 + Λ` | `kg_conserv`, `einsteinTensor_divergence_zero` (twice-contracted Bianchi) | machine-checked |
| Eq. (28) | **The semiclassical Einstein equations**, `R_ab − ½R g_ab + Λ g_ab = α⟨:T_ab:⟩` | `jacobson_einstein_equation_of_state` → the capstone `qiqt_gr_from_wedge_kms` / `qiqt_gr_freefield_complete` (the [claim card](/claim-card)) | machine-checked, **conditional** |

## The one shared input — and where QIQT-H goes further

| | Dorau & Much (PRL) | QIQT-H (Lean) |
|---|---|---|
| Entropy–area relation `S = δA/4` | **bare-assumed** ("under the assumption of the Bekenstein–Hawking entropy-area formula") to fix `α = 8π` | `S = A/4G` **proved** for the induced-area construction (`calibrated_entanglement_cut_area_law`), reducing the input to **one calibration** `log D_e = wEnt_e`, with a machine-checked guard (`codeCap_unbounded_at_fixed_area`) showing that calibration is load-bearing |
| The `1/4` coefficient | assumed (Bekenstein–Hawking) | **re-derived** as a theorem (`sakharov_ratio`, the conical-`4π` / Einstein–Hilbert-`16π` ratio) |
| Numerical value of `G` | not addressed (out of scope) | a named frontier — the relation `G = 1/(N Λ_s²)` is derived, the *number* needs the curved-space Seeley–DeWitt `κ = 1/6` that Mathlib lacks |

<div class="note">

**The honest bottom line.** Both derivations reach the same equations through the same chain, and both
need `S = δA/4` fed in. The PRL assumes it outright; QIQT-H proves the `A/4G` relation for its induced
area and collapses the input to a single, guarded calibration — a stronger position, but that one
calibration is still *carried*, not derived from nothing. So the PRL vindicates the shared **derivation
chain** (relative entropy → modular theory → Jacobson → Einstein), which QIQT-H machine-checks
step for step; it does **not** endorse the finiteness postulate, and the free-field chain is *conditional*
and on a locally-flat horizon (curved higher-order corrections are the shared frontier — their own
closing caveat: "*technically demanding, especially regarding the modular data*").

</div>

[Run the capsule and read your own claim card →](/verify) · [The formalization index →](/formalization)
