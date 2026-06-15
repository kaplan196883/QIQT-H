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

<div class="note"><strong>Scope.</strong> The verified, axiom-free corpus now covers both the borrowed
mathematics (Tomita–Takesaki modular theory and Araki = CGP relative entropy, free-field coherent sector) and
the program's own results: the covariant σ-additive <em>consistent</em> Born measure on the record net, the
Born-from-typicality reduction (to a state-supervenience premise, with a no-go), and λ's
covariance/contextuality structure. What it does <strong>not</strong> establish: the holographic axiom (FQ),
λ's <em>dynamical</em> law, or the continuum (Type III₁). It does not close the
<a href="/open-problems">open problems</a>. (The original Macroscopic Definiteness Conjecture is
<a href="/open-problems">retired</a> as a category error, not a pending verification target.)</div>

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

### Born from typicality — the symmetry / state-supervenience reduction

The Born weights reduced from typicality to a single state-supervenience premise (with a no-go that *some*
premise is unavoidable). Born is **input**, not derived; these establish what it reduces to.

| theorem | statement |
| --- | --- |
| `RedundancyCompressible.card_redundantCodewords` | $R$ redundant copies of a record are distinguishable in $\lvert X\rvert$ ways, not $\lvert X\rvert^R$ — redundancy is compressible (the category-error core) |
| `RedundancyCompressible.naive_overcounts` | the naive $R\log\lvert X\rvert$ strictly exceeds the true $\log\lvert X\rvert$ |
| `EnvarianceJustification.envariance_swap_invariant` | the system swap, undone by the environment counter-swap, fixes the state **iff** the swapped amplitudes are equal (Zurek envariance, *proved* not assumed) |
| `BornEquiprobable.born_eq_equiprob` | for an equal-amplitude orthonormal fine-graining, the Born weight $=$ the equiprobable branch-count fraction (the amplitude→count bridge) |
| `StateSupervenience.NaturalTypicality.envariance_equiprob` | naturality $+$ a state-fixing symmetry $\Rightarrow$ equal-amplitude outcomes are equiprobable |

### λ's selection schema: covariance & contextuality (OP3b)

| theorem | statement |
| --- | --- |
| `CovariantGluing.no_covariant_selector` | no equivariant $\Phi\mapsto\lambda$ selector when the symmetric state's histories form a nontrivial orbit (the S² obstruction) — so $\lambda$ is a symmetry-breaking *sample* of the covariant law, not a covariant function |
| `ContextualitySafe.contextuality_safe` | a quantum/record correlation $>2$ (Tsirelson) has **no** global value-map — assigning values only to the actual context is forced |
| `Fock.bell_no_signaling_state` | no-signaling is **state-independent**: for *any* (entangled) global state, summing Bob's record outcome leaves Alice's marginal independent of Bob's setting |

### λ's selection schema: the finite Takesaki criterion + modular invariance

The finite (Type I) shadow of λ's kinematic-and-dynamical law. λ is **Type-III-native** — the records it selects
come from a chosen abelian *pointer* subalgebra 𝔄 (which exists already inside a Type III₁ factor), and the
Born weights are the algebraic state value $\omega(P_\alpha)$, needing no trace. These theorems make precise
*which* 𝔄 is consistent, that the decoherence map is the conditional expectation onto it, and that the
selection is stable under the modular dynamics.

| theorem | statement |
| --- | --- |
| `LambdaPointer.modAut_fixes_iff_commute` | **Takesaki criterion**: the modular flow fixes a pointer projection $\sigma(P)=P$ **iff** $[\rho,P]=0$ — i.e. iff the state has no coherence between pointer sectors (exact decoherence selects 𝔄) |
| `LambdaPointer.bornWeights_sum` | the algebraic Born weights $\omega(P_\alpha)=\operatorname{tr}(\rho P_\alpha)$ of a resolution of unity sum to $\operatorname{tr}\rho$ — a genuine probability |
| `LambdaPointer.dephase_preserves_state` | the decoherence map $E(x)=\sum_\alpha P_\alpha x P_\alpha$ is the unital, $\omega$-preserving **conditional expectation** onto 𝔄 (exactly when the criterion holds) |
| `LambdaPointer.dephase_sigmaDiag_commute` | **modular-invariance, $\forall t$**: $E$ commutes with the real-time modular flow $\sigma_t(x)=\rho^{it}x\rho^{-it}$ — a consistency fact (the modular flow is *not* physical time, so this is not physical no-recoherence) |
| `LambdaPointer.dephase_sigmaDiag_commute_diagonal` | in the einselected (density-eigenbasis) pointer basis the modular-invariance is **unconditional** for all $t$ |
| `LambdaPointer.modAut_fixes_pointer` / `bornWeight_modAut_invariant` | each selected record is a **fixed point** of the flow, and the Born weights are **constants of the modular motion** |
| `SelectionEvent.selects_exists_unique` | the **selection event**: an inverse-CDF selector from an actuality seed $s\in[0,1)$ picks **exactly one** record per seed (totality + uniqueness — single-world consistency) |
| `SelectionEvent.volume_selects` | the uniform seed measure of record $k$ equals its Born weight $p_k$ — the *single-shot* seed measure of record $k$ = its Born weight $p_k$ (the seed is λ; an across-run *frequency* needs the separate LLN; the selector is order-dependent, not equivariant, as the no-covariant-selector result requires) |

### λ's selection schema in the continuum (free-field / standard-subspace sector)

The finite schema above, lifted onto the **genuine continuum modular flow** $\Delta^{it}$ (the Rieffel–Van Daele
bounded `modUnitary` of a standard subspace) — axiom-free. The local algebra's Type III₁-ness (Buchholz–Wichmann)
is cited; the residual walls are the Haagerup natural-cone existence in Mathlib and the interacting case.

| theorem | statement |
| --- | --- |
| `ContinuumLambda.modAutOp_add` / `_mul` / `_star` | the modular automorphism $\sigma_t=\mathrm{Ad}(\Delta^{it})$ is a one-parameter group of unital $\star$-automorphisms |
| `ContinuumLambda.modAutOp_fixes_iff_commute` | **continuum Takesaki criterion**: $\sigma_t(A)=A \Leftrightarrow A$ commutes with $\Delta^{it}$ |
| `ContinuumLambda.dephaseOp_specProj_commute` | **continuum modular-invariance**: the decoherence map commutes with $\sigma_t$ for **every $t$** (unconditional for spectral pointer projections) — a consistency fact, *not* physical persistence (modular flow ≠ physical time) |
| `NaturalConeBorn.bornWeights_sum` | the **Type-independent algebraic Born rule**: the scalar spectral measure of a finite pointer partition sums to $\lVert\xi\rVert^2$ (a genuine probability, no trace) |
| `ContinuumSelection.continuum_selects_exists_unique` | the **Type-blind selection event**: exactly one record per actuality seed, driven by the continuum Born weights |
| `ContinuumSelection.continuum_volume_selects` | the uniform seed measure of record $k$ equals its continuum Born weight — the *single-shot* seed measure = its continuum Born weight (across-run frequency needs the separate LLN) |

And the **whole schema lifted to the second-quantized free field**: $\Gamma(\Delta^{it})$ as a unitary one-parameter
group of bounded operators on the Fock Hilbert space, with the field-level automorphism, modular-invariance, Born rule
(on the genuine Fock vacuum state) and selection event.

| theorem | statement |
| --- | --- |
| `secondQuantModCLM_unitary` | $\Gamma(\Delta^{it})$ is **unitary** on the Fock Hilbert space ($\Gamma^\star=\Gamma(-t)$) — the free-field modular unitary group |
| `dephaseFock_modAutFock_commute` | **field-level modular-invariance**: the decoherence map commutes with $\sigma_t=\mathrm{Ad}(\Gamma(\Delta^{it}))$ for every $t$ (a consistency fact, not physical persistence) |
| `vacuumState_povm_sum` / `vacuumState_weylBit_sum` | **field-level Born rule**: vacuum-state weights of a POVM are a probability; the Weyl-bit record gives $(1\pm e^{-\lVert u\rVert^2/2})/2$ |
| `field_selects_exists_unique` / `field_volume_selects` | the **free-field selection event**: exactly one Weyl-bit record per actuality seed, single-shot seed-measure = the Fock-vacuum-state Born weight |

<div class="note"><strong>What these add (and don't).</strong> They pin down λ's <em>selection schema</em>, not a
law: Born reduces to state-supervenience (not capacity, not a counting rule); the covariance + contextuality
structure is verified (covariant measure, no covariant point-selector; no global value-map; state-independent
no-signaling — operationally weaker than Bell local causality); the Takesaki criterion fixes which record
context is consistent; and the dephasing map is <em>modular-invariant</em>. That last is a consistency fact,
<strong>not</strong> physical persistence — the modular flow is not the physical Hamiltonian evolution. The
inverse-CDF selection is a sampling representation (single-shot seed-measure = Born weight), <em>not</em> a
mechanism or an across-run frequency. So the single outcome is λ's by stipulation; the holographic bound is the
finite record <em>stage</em> only; and the scheme is operationally equivalent to standard QM. The honest
residual: the seed's <em>origin</em> (a primitive), an across-run <em>frequency</em> theorem, a <em>global
decoherent-history</em> selector, and the continuum walls (Haagerup natural-cone existence; interacting case).</div>

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
