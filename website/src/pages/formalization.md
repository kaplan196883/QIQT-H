---
layout: ../layouts/Deep.astro
title: Formalization in Lean 4 / Mathlib
eyebrow: Machine-checked substrate
description: The QIQT-H deductive substrate is machine-verified in Lean 4 / Mathlib — bounded Tomita–Takesaki modular theory and coherent-state Araki relative entropy, with a reproducible build and theorem index.
---

The modular and relative-entropy *calculus* underlying the regional cost functional $\chi_R$ is
machine-verified for the free-field coherent-state sector. The development carries no `sorry` and, as
reported by `#print axioms`, depends only on the standard classical foundations of Lean/Mathlib
(`propext`, `Classical.choice`, `Quot.sound`).

<div class="note"><strong>Scope.</strong> What is verified is the standard borrowed mathematics,
Tomita–Takesaki modular theory and Araki relative entropy in the free-field coherent sector,
<strong>not</strong> the dressed Type&nbsp;II regional framework, the holographic axiom (FQ), the
Macroscopic Definiteness Conjecture, or Born-from-typicality. It strengthens the floor the argument stands
on; it does not close the <a href="/open-problems">open problems</a>.</div>

## The headline result

The coherent-state Araki relative entropy equals the one-particle Casini–Grillo–Pontello entropy, as a
literal machine-checked derivative theorem:

$$
\frac{d}{dt}\Big|_{0}\,\big\langle\Omega,\ \Delta_{W(f)\Omega\,\mid\,\Omega}^{\,it}\,\Omega\big\rangle = -\,i\,S_{\mathrm{CGP}}(f),
$$

so that

$$
S_{\mathrm{Araki}}\big(\omega_{W(f)\Omega}\,\Vert\,\omega_\Omega\big) = S_{\mathrm{CGP}}(f) \ge 0.
$$

## Index of machine-checked results

Toolchain `leanprover/lean4:v4.30.0` · verified in `QIQTH/AxiomAudit.lean`.

### Finite Araki relative entropy

| theorem | statement |
| --- | --- |
| `arakiEntropy_eq_relEntropy` | $S_{\mathrm{Araki}}(\rho\Vert\sigma)=\operatorname{tr}\rho(\log\rho-\log\sigma)$ (Umegaki) |

### Bounded Tomita–Takesaki (standard subspace)

| theorem | statement |
| --- | --- |
| `modConj_rvdRC_modConj` | $JRJ=2-R$ |
| `modConj_rvdT_of_mem_K` | $J(T\xi)=(2-R)\xi$ for $\xi\in\mathcal{K}$ |
| `modUnitary` | $\Delta^{it}$: group law, unitarity, strong continuity |

### One-particle CGP relative entropy

| theorem | statement |
| --- | --- |
| `cgpEntropy` | $S(\xi)=-\!\int\log((2-r)/r)\,d\mu^R_\xi$ |
| `rvdSpec_balance` | the CGP spectral balance |
| `cgpEntropy_nonneg` | $S(\xi)\ge 0$ for localized $\xi\in\mathcal{K}$ |

### Free-field (Fock) modular flow

| theorem | statement |
| --- | --- |
| `secondQuantModFlowH` | $\Gamma(\Delta^{it})$: one-parameter group, vacuum-fixing, strongly continuous on coherent vectors |
| `secondQuantModFlowH_weylH` | $\sigma_t(W(u))=W(\Delta^{it}u)$ |

### Coherent-state relative modular operator and reduction

| theorem | statement |
| --- | --- |
| `relModFlowH` | $\Delta^{it}_{W(f)\Omega\mid\Omega}=W(f)\,\Gamma(\Delta^{it})\,W(f)^{*}$ |
| `connesCocycleH_chain` | $[D\omega_{W(f)\Omega}:D\omega_\Omega]_t=W(f)W(-\Delta^{it}f)$ + chain rule |
| `hasDerivAt_relModFlow_vacuum` | $S_{\mathrm{Araki}}(\omega_{W(f)\Omega}\Vert\omega_\Omega)=S_{\mathrm{CGP}}(f)$ |

### Free-field Born measure & decoherent-histories consistency

A genuine (non-deterministic) Born probability measure on the continuum free field, its Lorentz-covariance,
and the decoherent-histories *consistency* (sum-rule) conditions. Born is the **input** weight
$\mu_\Phi(\alpha)=\lVert C_\alpha\Phi\rVert^2$; these theorems establish that it is a *consistent*,
$\sigma$-additive, covariant probability — not a derivation of Born.

| theorem | statement |
| --- | --- |
| `weylBit_typicalityMeasure_exists` | a $\sigma$-additive Born probability measure $\mu_\infty$ exists (finite-fiber Kolmogorov extension; the finiteness is the capacity bound) |
| `weylBit_typicality_lorentzBoost_invariant` | $\mu_\infty$ is the same in every Lorentz frame (covariant *as a law*) |
| `weak_decoherence_bit` | $\mathrm{Re}\,D(\alpha,\beta)=0$ — weak decoherence / consistency (the Born sum-rule condition), exact |
| `weak_decoherence_context` | the same for every single-bit coarse-graining: the whole projective family is a consistent set |
| `bell_two_bit_strong_decoherence` | for orthogonal records $\langle u,v\rangle=0$, full $D=0$ (incl. the maximally-different Bell pair) |
| `bitOp_vac_expVec_cross_eq` | exact overlap correction $\tfrac12 e^{-\lVert v\rVert^2/2}\sinh\langle v,w\rangle$; vanishes iff $\langle v,w\rangle=0$ |
| `strong_decoherence_needs_orthogonality` | witnessed countermodel: overlapping records are *not* strongly decoherent |
| `offdiagonal_tendsto_zero` | SBS / Quantum-Darwinism: redundancy $N\to\infty$ drives the joint off-diagonal $\to 0$ |
| `realm_unique_of_einselection` | given the einselected pointer family the realm is unique… |
| `capacity_underdetermines_realm` | …but capacity *alone* does not pin it (a no-go: distinct capacity-maximal realms) |

<div class="note"><strong>Terminology (Gell-Mann–Hartle).</strong> <em>Re D = 0</em> is <em>weak</em>
decoherence / consistency (it is what makes the Born weights obey the probability sum rules); full
<em>D = 0</em> is <em>medium</em>, and with orthogonal record states also <em>strong</em>. The Weyl-bit
operators <em>A(u,s) = (I + sW(u))/2</em> are <em>effects</em>, not projectors, so this is a
generalized-measurement history; the projector/Boolean-record content is separate. These are exact algebraic
consistency results for the free/coherent sector — not a proof of macroscopic classicality.</div>

## Reproduce the verification

```bash
~/.elan/bin/lake build QIQTH
~/.elan/bin/lake build QIQTH.AxiomAudit   # emits #print axioms for every theorem
```

Each theorem reports `depends on axioms: [propext, Classical.choice, Quot.sound]`. The full
statement-level index lives in the repository; a companion formalization paper is in preparation.

A note on wording: "no axioms" here means no *project* axioms. `propext`, `Classical.choice`, and
`Quot.sound` are the standard classical foundations every ordinary Mathlib proof uses; we keep them and
add nothing of our own.
