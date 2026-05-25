---
title: "One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint"
author: "Paweł Kapłański"
date: 2026-05-25
keywords: [foundations of quantum mechanics, holographic principle, Bekenstein-Bousso bound, Type II von Neumann algebras, crossed product, generalized entropy, finite-precision wave function, measurement problem, typicality]
---

# One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint

## Abstract

We develop a foundational framework for quantum mechanics that combines the algebraic quantum field theory framework with the recent crossed-product / Type II construction of Chandrasekaran-Penington-Witten (2022) and Witten (2022). In ordinary QFT, the local algebras of bounded regions are of Type III$_1$ — admitting no trace, no Hilbert-space factorization, and UV-divergent entanglement entropy. CPW and Witten show that gravitational dressing, implemented via the crossed product with the modular flow of a reference state, produces a Type II algebra $\hat{\mathcal{A}}(R)$ with a semifinite trace and a well-defined renormalized entropy whose differences match the generalized entropy expression $A/(4\ell_P^2) + S_{\rm matter}$. We use this algebraic infrastructure as the mathematical home for a foundational axiom (FQ) that we propose: *for every per-run physical wave function and every bounded region $R$, the state $\omega_\Psi$ induced on the gravitationally dressed regional algebra $\hat{\mathcal{A}}(R)$ has renormalized entropy bounded by $Q_R := A(\partial R)/(4\ell_P^2)$, and two abstract wave functions inducing the same state on $\hat{\mathcal{A}}(R)$ are physically identical in $R$.* The crossed-product construction is borrowed from CPW/Witten; the holographic bound $S_{\rm ren} \le Q_R$ is postulated as a finite-information axiom in this algebraic setting (not derived from CPW); the foundational application of this algebraic infrastructure to the measurement problem is our contribution. We distinguish the **formal wave function** of standard QM (an idealized ensemble description) from the **per-run wave function** (whose regional physical content is given by its values on the regional Type II algebras). Algebra-state equivalence provides a basis-independent notion of regional physical indistinguishability — two abstract Hilbert vectors are physically the same regional state iff they agree on every observable in $\hat{\mathcal{A}}(R)$. *Conjecturally*, under decoherence and microscopic initial conditions, per-run regional states concentrate dynamically on single-record states; *if this concentration conjecture is established*, the per-run wave function in any region containing apparatus and environment is, in the algebraic sense, equivalent to a single-record state. The Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly; (FQ) operates at the level of regional algebraic content. No collapse, no Bohmian particles, no MWI branches, no modal value-rule are added. Born statistics from typicality is stated schematically and identified as a key open problem. We state two propositions and two explicit conjectures, identify four explicit open problems, and frame the construction as a research program rather than a completed interpretation.

**Keywords:** foundations of quantum mechanics; Bekenstein-Bousso bound; holographic principle; Type II von Neumann algebras; crossed product; generalized entropy; finite-resolution wave function; ensemble interpretation; typicality.

---

## 1. Introduction

### 1.0 The hidden inconsistency in standard quantum foundations

Standard foundational discussion of quantum mechanics typically holds four claims simultaneously:

1. The wave function is physically real.
2. Bounded spacetime regions have finite physical information capacity (the holographic principle, supported by Bekenstein, 't Hooft, Susskind, Bousso, Banks, and the recent algebraic-QFT-plus-gravity work of Chandrasekaran-Penington-Witten and Witten).
3. The amplitudes of the wave function are exact real numbers (specifiable to arbitrary precision in principle).
4. Macroscopic superpositions, once formed, persist as physically real components forever.

These four claims cannot all be true. If the wave function is physically real (1) and amplitudes are exact real numbers (3), then specifying the wave function in any bounded region requires infinitely many bits of physical information — contradicting (2). If we add (4), macroscopic record alternatives persist as infinite-precision-amplitude branches that the region cannot physically contain. The standard interpretations of QM each resolve this tension by denying one of the four claims:

- **Many-Worlds** denies single-world realism (accepts (1)–(4) but at the cost of branching ontology with infinitely many physically real branches; pays in spacetime-information overflow that is rarely confronted).
- **Bohm** denies that the wave function is the complete physical content (denies a strong form of (1); adds primitive particle ontology).
- **GRW / CSL / DP / OR** deny that Schrödinger evolution is exact (modify dynamics so that (4) fails dynamically).
- **QBism / RQM** deny that the wave function is straightforwardly physically real (deny (1) in favor of epistemic or relational status).
- **Modal interpretations / decoherent histories** add a value-rule or history-selection structure to break (4) without modifying dynamics.

Each pays a distinct foundational price. Each accepts the tension as a *given* of the theory and pays the price to dissolve it.

This paper proposes a different resolution: **deny (3) at the level of physical instantiation while preserving the mathematical formalism**. The wave function in any bounded region has finite physical specification precision determined by the holographic information capacity of the region. Amplitudes physically within $\epsilon(R)$ of $0$ are physically equivalent to amplitude exactly $0$. The mathematical continuum of amplitudes remains the indispensable formal apparatus; the physical instantiation is finite-precision. With this denial of (3), all four claims can be reconciled: the wave function is physically real (1), bounded spacetime has finite capacity (2), amplitudes have finite physical specification precision (denial of (3)), and macroscopic superpositions resolve dynamically into single-record states (denial of (4) as structural consequence, not as added postulate).

This is arguably the *least radical* resolution. It does not multiply worlds, add particles, modify dynamics, or subjectivize the wave function. It accepts one physically natural constraint — bounded spacetime cannot physically contain infinite information — which is *independently motivated* by holography and quantum gravity. The measurement problem is resolved by recognizing that we were illegitimately combining (1)–(4) when only three of the four can hold at the level of physical instantiation.

### 1.1 The position

This paper develops a position in the foundations of quantum mechanics whose structure is:

1. The wave function of the universe evolves unitarily under the Schrödinger / Heisenberg evolution of the underlying field theory. Standard QM dynamics is preserved exactly.

2. The Bekenstein-Bousso holographic bound is treated as a foundational constraint on the **physical content of the wave function in any bounded region $R$** — not narrowly on the entanglement entropy of a reduced state, but on the total physical information needed to specify the state's content in $R$ as a state of spacetime.

3. The mathematical home of this constraint is the algebraic QFT framework with gravitational dressing. The regional algebra $\hat{\mathcal{A}}(R)$, obtained from the standard Type III$_1$ local algebra $\mathcal{A}(R)$ via the crossed product with the modular flow of a reference state, is of **Type II** and admits a semifinite trace whose finite values realize finite renormalized entropy for regional states. This is the framework of Chandrasekaran-Penington-Witten (2022), Witten (2022), and successors.

4. The (FQ) axiom: *the physical content of the per-run wave function in any bounded region $R$ is given by its expectation values on $\hat{\mathcal{A}}(R)$, and the renormalized entropy is bounded by $Q_R = A(\partial R)/(4\ell_P^2)$.*

5. The Type II structure of $\hat{\mathcal{A}}(R)$ implies a finite physical resolution for regional states: states agreeing on all operators in $\hat{\mathcal{A}}(R)$ are physically identical in $R$. This is the natural mathematical realization of "amplitudes physically within $\epsilon$ of $0$ are physically the same state as amplitude exactly $0$" — the equivalence is between regional states, not between abstract Hilbert vectors.

6. The standard textbook formal wave function — a superposition $\sum_i c_i |s_i\rangle|A_i\rangle|E_i\rangle$ — is an idealized statistical description of an ensemble of per-run wave functions across many runs. The per-run wave function evolves unitarily from specific microscopic initial conditions; decoherence drives amplitudes for distinct macroscopic record components to concentrate dynamically; the Type II resolution structure renders the post-concentration per-run wave function physically a single-record state.

7. Born statistics emerge from typicality of microscopic initial conditions across runs.

### 1.2 What this paper does and does not claim

**Does.** Introduces (FQ) in its rigorous algebraic form using Type II crossed-product algebras. Distinguishes formal vs per-run wave functions. Establishes the finite-physical-resolution consequence of Type II regional algebras. Discusses the decoherence-and-concentration mechanism. States four formal results. Identifies three explicit open problems.

**Does not.** Derive the resolution floor as an explicit function of regional geometry beyond the qualitative implication. Provide a fully rigorous typicality theorem for Born weights. Modify the Schrödinger equation, posit Bohmian particles, MWI branches, modal value-rules, or any actuality primitive beyond the per-run wave function regarded as a state on the regional algebras.

### 1.3 Relation to existing programs

The framework is positioned in relation to:

- **Algebraic QFT** (Haag, Kastler 1964; Haag 1992): local algebras for bounded regions; we adopt this as the mathematical foundation.
- **Chandrasekaran-Penington-Witten Type II algebras** (CPW 2022; Witten 2022; Jensen-Sorce-Speranza 2023): the crossed-product construction giving Type II regional algebras with finite renormalized entropy; we use this as the rigorous home for (FQ).
- **Holographic bounds** (Bekenstein 1981; 't Hooft 1993; Susskind 1995; Bousso 2002; Banks 2025): the bound that (FQ) imposes; the literal reading we adopt is supported by these works' information-theoretic motivations.
- **Decoherence** (Zurek 2003; Joos et al. 2003): einselection of pointer-basis records; we add the Type II resolution structure that makes below-threshold branches physically equivalent to nonexistent ones.
- **Ensemble interpretation** (Ballentine 1970): we agree the standard wave function is ensemble-descriptive; we supply the mathematical mechanism via the Type II regional structure.
- **Typicality programs** (statistical mechanics; Wallace 2012; Carroll-Sebens 2014; Dürr-Goldstein-Zanghì 1992 for Bohmian equivariance): we deploy a typicality argument for Born weights.

### 1.4 Roadmap

§2 reviews standard QM preliminaries and introduces the formal/per-run distinction. §3 introduces the algebraic QFT framework and the CPW Type II crossed-product construction. §4 states (FQ) in the Type II framework and discusses its motivation. §5 derives finite physical resolution as a consequence of the Type II structure. §6 develops the mechanism by which decoherence + microscopic initial conditions + the Type II resolution structure produce single-record per-run wave functions. §7 states the four formal results. §8 discusses the holographic motivation. §9 sketches possible phenomenology. §10 compares with existing approaches. §11 concludes.

---

## 2. Formal Preliminaries

### 2.1 Standard QM axioms

**(A1) State space.** Pure states are unit rays in a separable complex Hilbert space $\mathcal{H}$; mixed states are density operators in $\mathcal{B}(\mathcal{H})$.

**(A2) Closed-system evolution.** Unitary $U(t) = e^{-iHt/\hbar}$ with self-adjoint Hamiltonian $H$.

**(A3) Composite systems.** $\mathcal{H}_{AB} = \mathcal{H}_A \otimes \mathcal{H}_B$.

**(A4) Observables.** Self-adjoint operators or POVMs.

**(A5) Born rule.** $\Pr(\omega) = \mathrm{Tr}(\rho E_\omega)$.

### 2.2 One wave function per run; subsystem vs universal description

**The central commitment: there is exactly ONE wave function per run.** No formal/per-run distinction in the problematic sense of "the same preparation gives different per-run wave functions." Each actual run of an actual experiment corresponds to *one* universal wave function evolving from *one* set of actual initial conditions of the universe.

What varies across runs is *the actual initial conditions themselves*: different particles emitted by the source, different microscopic states of the apparatus, different environmental configurations, different photon backgrounds, different thermal fluctuations. These differences are not hidden variables added to the framework — they are simply the actual physical differences between actual physical universes in different runs. Standard QM already accommodates this: the universal wave function is a function of all degrees of freedom in the universe, which trivially differ across runs.

What is sometimes loosely called the "formal wave function" in textbook accounts is the *subsystem wave function* — the wave function of a subsystem (typically the particle of interest) treated as if it were isolated from the apparatus and environment. This subsystem wave function is the textbook abstraction $\alpha|0\rangle + \beta|1\rangle$. It is not the per-run physical state of the universe; it is a subsystem description that abstracts away the apparatus + environment.

**Definition (Subsystem wave function).** *The subsystem wave function $|\psi\rangle_{\rm sub}$ for a subsystem $S$ of the universe is the wave function obtained by tracing the universal wave function over all degrees of freedom outside $S$ and (when $S$ is approximately uncorrelated with its complement) recovering an effectively pure state on $S$. For the prepared particle in the double-slit, $|\psi\rangle_{\rm sub} = \alpha|0\rangle + \beta|1\rangle$ is the standard textbook expression.*

**Definition (Per-run universal wave function).** *The per-run universal wave function $|\Psi\rangle_{\rm run}$ is the actual physical wave function of the universe in a specific individual run, evolving unitarily under the universal Hamiltonian from the specific actual initial conditions of the universe in that run. Its physical content in any bounded region $R$ is given by its values on the regional algebra $\hat{\mathcal{A}}(R)$ (defined in §3), constrained by (FQ).*

The relationship across runs: there is *one* per-run universal wave function per run. Different runs have *different actual* per-run universal wave functions because the actual initial conditions of the universe differ. Born statistics across runs (§7.4) arise from the distribution of these actual initial conditions, not from any "alternative" wave functions for the same preparation. The "ensemble" is over actual different physical universes, not over hypothetical alternatives.

**The framework adds no ontology beyond the universal wave function.** It is ψ-monist. The framework's two contributions are:
1. The recognition that the textbook subsystem wave function $|\psi\rangle_{\rm sub}$ is *not* the complete physical state of the universe in a run — the per-run universal wave function $|\Psi\rangle_{\rm run}$ is. This is standard QM at the universal level.
2. The (FQ) axiom limiting the physical information content of the universal wave function per region.

Neither of these adds extra ontology. The "extra structure" is just standard QM at the universal-wave-function level (which always was the full story; the textbook subsystem abstraction is just convenient for calculations) plus the (FQ) postulate.

### 2.3 Empirical content

Empirical content is exhausted by Born statistics across runs. Standard QM is empirically complete in this sense; interpretations differ on the per-run physical content.

---

## 3. Algebraic Framework: Type II Regional Algebras

### 3.1 Local algebras in QFT

In algebraic QFT (Haag-Kastler), one associates to each spacetime region $R$ a von Neumann algebra $\mathcal{A}(R) \subset \mathcal{B}(\mathcal{H})$ of observables localized in $R$. The assignment $R \mapsto \mathcal{A}(R)$ satisfies isotony, locality, covariance, and (for the vacuum) the Reeh-Schlieder property.

A foundational result (Buchholz, Wichmann, Borchers, Longo): for any double cone or causal-diamond region $R$ in a generic QFT, $\mathcal{A}(R)$ is a **Type III$_1$ factor** in the Murray-von Neumann classification. This has consequences directly relevant to foundations:

- No trace exists on $\mathcal{A}(R)$.
- No tensor factorization $\mathcal{H} = \mathcal{H}_R \otimes \mathcal{H}_{\bar R}$ — the algebra of $R$ and its complement do not split the Hilbert space.
- No notion of "number of degrees of freedom" in $R$.
- Entanglement entropy $S(\rho_R)$ is UV-divergent.
- No pure states with respect to $\mathcal{A}(R)$.

The Type III$_1$ structure is the formal obstruction that has historically prevented the holographic bound from being applied directly to regional entanglement entropy: there's nothing well-defined to bound.

### 3.2 The crossed-product construction (Chandrasekaran-Penington-Witten)

Recent work (CPW 2022; Witten 2022; Jensen-Sorce-Speranza 2023; Chandrasekaran-Longo-Penington-Witten 2022) has shown that **gravitational dressing**, implemented via the crossed product with the modular flow, converts Type III$_1$ local algebras into **Type II algebras** with a semifinite trace structure and a renormalized entropy whose differences reproduce the generalized entropy.

The construction, in outline:

1. Start with the Type III$_1$ local algebra $\mathcal{A}(R)$ and a cyclic-separating reference state $\Omega$ (e.g., the vacuum, or a state corresponding to a chosen observer's perspective in the semiclassical setting). The choice of $\Omega$ enters the construction and we discuss reference-state dependence in §3.4.
2. Let $\Delta_\Omega$ be the modular operator and $\sigma_t^\Omega$ the corresponding modular automorphism of $\mathcal{A}(R)$.
3. In the presence of gravity (perturbatively in $G_N$ or $1/N$), impose the constraint that physical observables commute with the boost generator of the modular flow. Equivalently: dress observables by the modular flow.
4. The resulting algebra is the **crossed product** $\hat{\mathcal{A}}(R) := \mathcal{A}(R) \rtimes_{\sigma^\Omega} \mathbb{R}$, naturally represented on the enlarged Hilbert space $\mathcal{H} \otimes L^2(\mathbb{R})$.

**Theorem (CPW / Witten).** *The crossed-product algebra $\hat{\mathcal{A}}(R)$ is of Type II in the Murray-von Neumann classification. For general bounded regions, $\hat{\mathcal{A}}(R)$ is Type II$_\infty$ with semifinite trace (the identity having infinite trace). In special gravitational sectors with a finite phase-space volume (most prominently the de Sitter static patch, treated in CLPW 2022), the algebra is Type II$_1$ with finite trace $\tau(\mathbf{1}) < \infty$.*

The Type II structure provides what was missing in Type III$_1$:

- A **trace or weight** $\tau$ exists on $\hat{\mathcal{A}}(R)$ (semifinite in the general Type II$_\infty$ case, finite in the special Type II$_1$ case).
- For the class of normal states $\omega$ on $\hat{\mathcal{A}}(R)$ with a well-defined trace-class density operator $\rho_\omega$, the **renormalized entropy** $S_{\rm ren}(\omega) := -\tau(\rho_\omega \log \rho_\omega)$ is defined.
- *Entropy differences* $S_{\rm ren}(\omega) - S_{\rm ren}(\omega')$ between such states reproduce the generalized entropy differences $S_{\rm gen}(\omega) - S_{\rm gen}(\omega')$ with $S_{\rm gen} = A/(4\ell_P^2) + S_{\rm matter}$. The absolute value of $S_{\rm ren}$ depends on trace normalization and additive constants.
- "Number of effective degrees of freedom" is well-defined as a renormalized quantity, with the modular spectrum providing concrete structure.

### 3.3 The regional algebra and the holographic bound — what CPW gives and what we postulate

What the CPW/Witten framework rigorously provides:

- A semifinite Type II algebra $\hat{\mathcal{A}}(R)$ for bounded regions in semiclassical gravity.
- A trace structure with respect to which renormalized entropy differences are well-defined.
- *Entropy differences* matching the generalized entropy $A/(4\ell_P^2) + S_{\rm matter}$, with the area term arising naturally from the algebraic structure.
- In particular semiclassical gravitational sectors, finite area-controlled generalized entropy.

What CPW/Witten do *not* establish in full generality:

- A theorem of the form "for every bounded region $R$, $\max_{\omega} S_{\rm ren}(\omega) = A(\partial R)/(4\ell_P^2)$."
- A finite Hilbert dimension or finite number of distinguishable normal states.
- An intrinsic resolution floor on the normal-state space.

The holographic bound applied to the regional Type II algebra,
$$S_{\rm ren}(\omega) \le Q_R := \frac{A(\partial R)}{4 \ell_P^2},$$
is therefore not a theorem of CPW. **We postulate it as a foundational axiom** in this algebraic setting (it is the content of part (ii) of (FQ) below). The Type II framework provides the rigorous mathematical language in which the bound can be stated without UV divergences and in a basis-independent way; the bound itself is our axiom, motivated by the holographic principle of quantum gravity but not derived from CPW.

This sharp separation — CPW gives the algebraic language, we postulate the bound — is intentional. The Type II framework is borrowed; the foundational application to QM measurement is our contribution.

### 3.4 State extension and reference-state dependence

Two technical issues require comment.

**State extension.** The crossed-product algebra $\hat{\mathcal{A}}(R) = \mathcal{A}(R) \rtimes_{\sigma^\Omega} \mathbb{R}$ is naturally represented on $\mathcal{H} \otimes L^2(\mathbb{R})$, not on the original QFT Hilbert space $\mathcal{H}$. A per-run wave function $|\Psi\rangle \in \mathcal{H}$ does not automatically define expectation values on operators in $\hat{\mathcal{A}}(R)$ that act on the $L^2(\mathbb{R})$ factor (the modular-flow / "clock" degrees of freedom). Following CPW, we assume an explicit extension prescription: per-run universal wave functions are taken to live in the enlarged Hilbert space, $|\Psi\rangle_{\rm run} \in \mathcal{H} \otimes L^2(\mathbb{R})$, with the $L^2(\mathbb{R})$ factor encoding the dressing degrees of freedom required to make the gravitational constraint well-defined. The state $\omega_\Psi$ on $\hat{\mathcal{A}}(R)$ is then the standard vector state of $|\Psi\rangle_{\rm run}$ restricted to $\hat{\mathcal{A}}(R)$.

**Reference-state dependence.** The crossed product uses the modular flow $\sigma^\Omega$ of a reference state $\Omega$. Different reference states give different crossed-product algebras; however, the continuous-core construction is known to be state-independent up to isomorphism (Connes-Takesaki), and physical predictions (entropy differences, generalized-entropy comparisons between states) are reference-state-independent in the semiclassical regime where CPW operates. We adopt the same convention as CPW: a natural reference state is chosen (e.g., the vacuum or a global Bunch-Davies-like state), and physical content is read off via entropy differences and algebra-state equivalences that are reference-independent in the relevant sense. A fully reference-state-independent formulation is a technical refinement we defer.

---

## 4. The (FQ) Axiom in the Type II Framework

### 4.1 Statement

**Axiom (FQ) — Literal physical-instantiation reading.** *For every per-run wave function $|\Psi\rangle_{\rm run}$ of the universe (regarded as an element of the enlarged Hilbert space $\mathcal{H} \otimes L^2(\mathbb{R})$, cf. §3.4) and every bounded region $R$ of space:*

*(i) The physical content of $|\Psi\rangle_{\rm run}$ in $R$ is given by the state $\omega_\Psi : \hat{\mathcal{A}}(R) \to \mathbb{C}$ defined by $\omega_\Psi(O) = \langle\Psi_{\rm run}|O|\Psi_{\rm run}\rangle$ for $O \in \hat{\mathcal{A}}(R)$.*

*(ii) The renormalized entropy $S_{\rm ren}(\omega_\Psi)$ on $\hat{\mathcal{A}}(R)$ is bounded by the area-law generalized entropy:*
$$S_{\rm ren}(\omega_\Psi) \le Q_R := \frac{A(\partial R)}{4\ell_P^2}.$$

*(iii) The wave function $|\Psi\rangle_{\rm run}$ is regarded as a physical object instantiated in spacetime. The total physical information content needed to instantiate $|\Psi\rangle_{\rm run}$ in $R$ — including amplitudes, phase coherence, superposition structure — is bounded by $Q_R$. Two abstract wave functions whose physical instantiations in $R$ are indistinguishable at the precision afforded by this bound are physically identical in $R$.*

Part (i) defines the mathematical content of "wave function in $R$": it is the state on the Type II regional algebra introduced by CPW/Witten. Part (ii) is the holographic information bound on regional renormalized entropy, postulated (not derived from CPW). Part (iii) is the **literal physical-instantiation reading** of the bound: the wave function, regarded as a physical state of spacetime in $R$, has finite physical specification precision. Below this precision, distinct mathematical wave functions correspond to the same physical state.

The literal reading is a stronger statement than the narrow entanglement-entropy reading and a stronger statement than what Witten's algebraic theorem directly establishes. It is our foundational postulate. The relationship to Witten's framework is made explicit in §4.3.

### 4.2 Motivation: the literal reading of the bound

We adopt (FQ) as a foundational axiom. The motivation rests on:

- **Bekenstein's original information-theoretic argument.** The original bound was derived as a bound on the information needed to specify any physical system, not specifically as an entanglement-entropy inequality on a reduced state.
- **'t Hooft's dimensional reduction.** All degrees of freedom in a region are encoded in boundary data; this is a statement about *total* physical content.
- **Susskind's holographic principle.** Physics in a region is holographically described by boundary data of bounded information content. The boundary holds at most $A/(4\ell_P^2)$ bits — bounds *all* the information to specify the physics, not just one measure of it.
- **Banks 2025.** Finite entropy in quantum gravity implies finite Hilbert-space dimension for bounded subsystems.
- **CPW 2022 and successors.** The Type II crossed-product structure provides the rigorous algebraic realization compatible with the literal reading.

The literal reading takes the bound seriously as a physical limit on the wave function as a physical state of spacetime — not as an abstract Hilbert vector but as a physical object instantiated in a region with finite information capacity. As an abstract Hilbert vector, the wave function can have continuous amplitudes specified to arbitrary precision. As a physical state of spacetime, it must be instantiated using the region's finite physical resources, and the bound limits these resources.

### 4.3 What Witten gives us and what we postulate on top

The relationship between our framework and the Witten/CPW algebraic infrastructure is precisely the following.

**What Witten / CPW provide (mathematical infrastructure):**
- The Type III$_1$ classification of local QFT algebras.
- The crossed-product construction $\hat{\mathcal{A}}(R) = \mathcal{A}(R) \rtimes_{\sigma^\Omega} \mathbb{R}$ giving Type II algebras.
- A semifinite (or finite, in Type II$_1$) trace $\tau$ on $\hat{\mathcal{A}}(R)$.
- A well-defined renormalized entropy $S_{\rm ren}(\rho) = -\tau(\rho \log \rho)$ for suitable states.
- Matching of entropy *differences* with generalized entropy differences $\Delta S_{\rm gen}$.
- Observer-frame degrees of freedom built in via the $L^2(\mathbb{R})$ clock factor.

**What we postulate as a foundational interpretation on top of this infrastructure:**
1. *(FQ) part (i)*: The mathematical content of "regional wave function content" is the state on the CPW Type II algebra.
2. *(FQ) part (ii)*: The holographic bound $S_{\rm ren} \le Q_R$ holds as an absolute bound, not just as a matching of differences.
3. *(FQ) part (iii)*: **The literal physical-instantiation reading** — the wave function is a physical state of spacetime with finite information capacity per region; below the resulting physical precision, distinct mathematical wave functions are the same physical state.

Item 3 is the strongest and most distinctive postulate. Witten's mathematical theorem says nothing about physical instantiation precision; his Type II algebra has a continuous normal-state space, and algebraic equivalence is an *exact* equivalence relation. Our postulate says additional structure exists at the physical level — the bound limits not just the algebraic entropy but the physical-instantiation precision of regional wave-function content. The Type II algebra is the mathematical scaffold; the physical-precision floor is a foundational interpretation laid on top.

We are not contradicting Witten. We are extending the foundational reading of the bound beyond what Witten directly proves. Witten's theorem is about the rigorous mathematical home for finite renormalized entropy on bulk regions; our postulate is about how this entropy bound translates into physical precision on the wave function as a physical state of spacetime.

The two readings can be compared:

| | Narrow algebraic reading (Witten) | Literal physical-instantiation reading (ours) |
|---|---|---|
| What the bound limits | Renormalized entropy on Type II algebra | Total physical info needed to instantiate WF in $R$ |
| Equivalence relation on states | Exact equality on algebra | Algebraic + physical-precision floor |
| Near-zero amplitudes | Distinct from zero (continuous state space) | Physically equivalent to zero (below precision) |
| Single-record per run | Requires separate Concentration Conjecture | Structural consequence of precision + decoherence |
| Status w.r.t. Witten's theorem | Direct mathematical reading | Stronger interpretive postulate; compatible but not derived |

Whether the literal reading is the correct foundational reading of the bound is a substantive philosophical / physical question, not a mathematical theorem. Our position is that the literal reading is the natural reading of "Bekenstein-Bousso as a Lorentz-invariant information limit on bounded regions of spacetime" — what the bound says, taken at face value as a physical limit rather than as a narrow technical inequality on a derived quantity.

---

## 5. Finite Physical Resolution of the Per-Run Wave Function

### 5.1 The resolution consequence of the literal reading

Under (FQ) in its literal physical-instantiation reading, the per-run wave function in $R$ has bounded total physical information content. Specifying amplitudes to arbitrary precision requires arbitrary information. The information available is bounded by $Q_R$. Therefore the amplitudes of the per-run wave function in $R$ are physically specified only up to a finite resolution.

**Definition (Physical resolution floor).** *Let $\epsilon(R)$ denote the smallest amplitude difference physically distinguishable in region $R$ under (FQ). Two physical wave functions in $R$ whose physical instantiations differ by less than $\epsilon(R)$ in their content on $\hat{\mathcal{A}}(R)$ are the same physical state.*

**Lemma 1 (Resolution implies indistinguishability of near-extremes).** *Under (FQ), for any per-run wave function $|\Psi\rangle_{\rm run}$ in $R$:*
- *An amplitude $c$ with $|c| < \epsilon(R)$ in the algebraic decomposition of $\omega_\Psi$ on $\hat{\mathcal{A}}(R)$ corresponds to a physical state indistinguishable from amplitude exactly $0$ on that component.*
- *An amplitude $c$ with $|c|^2 > 1 - \epsilon(R)$ for a single component is physically indistinguishable from that component having amplitude exactly $1$.*

The resolution floor is a structural physical fact, not a measurement-precision limitation imposed by external observers. Below the resolution, distinct mathematical amplitudes correspond to the same physical state. The wave function as a physical instantiation in spacetime does not encode the distinction.

### 5.2 The Mandelbrot rendering analogy

The Mandelbrot set has unbounded fractal detail as a mathematical object. Any physical rendering — pixels, etched plates, printed images — has finite resolution determined by the physical substrate. Below pixel scale, mathematically distinct points are the *same physical pixel*. The pixel does not partially exist or fractionally exist; it is one specific color.

The wave function, on the present view, is similar:
- As an abstract Hilbert-space vector it can have arbitrary continuous amplitudes.
- As a *physical* state of spacetime, it is rendered with finite resolution determined by the holographic bound on the region.
- Below resolution, fractional amplitudes are not physically realized; they are physically equivalent to exact $0$ or exact $1$.

This is the *physical-instantiation reading* of the wave function, distinct from the abstract Hilbert-space reading. The latter treats amplitudes as freely specifiable continuous parameters; the former takes seriously the requirement that those amplitudes be physically encoded in the regional substrate, which has finite information capacity.

### 5.3 Defense against the qubit objection

A standard objection to a finite-precision-on-amplitudes reading of the holographic bound runs as follows: "Consider a qubit. It has Hilbert dimension 2 and entropy bound $\log 2$. But its pure states form a continuum — the Bloch sphere — with arbitrary $\alpha, \beta$. So finite entropy does not imply finite amplitude precision."

This objection treats the qubit as an abstract Hilbert-space entity. The framework's response distinguishes the mathematical idealization from the physical instantiation. **The Bloch sphere stands in the same relation to a physical qubit as Euclidean geometry stands to a physical measuring rod**: an indispensable, extraordinarily accurate mathematical idealization, but not a literal description of what the physical object instantiates with infinite precision. No physical measuring rod realizes exact Euclidean points; no physical qubit realizes exact Bloch-sphere amplitudes. The continuum is the mathematical scaffolding; the physical substrate has finite information capacity.

A physical qubit is always implemented in a substrate — an ion, an atom, a photon's polarization, a superconducting circuit, a nuclear spin, a quantum dot — occupying some bounded spatial region. The amplitudes $\alpha, \beta$ must be physically encoded in that substrate's quantum state. The holographic bound on the region containing the qubit gives $Q_R$ bits of physical information capacity. The amplitudes can be specified to a precision corresponding to this capacity.

For a qubit in a 1m region with $Q_R \sim 10^{70}$ bits, amplitude precision is astronomically fine — the Bloch sphere is effectively continuous for all practical purposes. **This is precisely why standard QM works at lab scales: the framework reproduces ordinary continuous-qubit phenomenology because the physical precision floor is far below experimental resolution.** For a qubit in a Planck-scale region, $Q_R$ is order unity and the Bloch sphere is genuinely discretized.

Quantum error correction does not evade this. A logical qubit encoded in many physical qubits has a larger substrate and therefore larger information capacity, but still finite. The continuum is never physically recovered; it is only postponed into a bigger idealization.

For *macroscopic* systems — where each macroscopic record component, considered as the full quantum state of the apparatus+environment region, uses a substantial fraction of the regional capacity, and superpositions of multiple records require encoding all of them simultaneously — the operationally relevant precision for amplitudes between records is finite. This is the regime where the precision floor has structural foundational consequences (Theorem 4).

The qubit objection therefore identifies the *limit where the framework reproduces standard QM* (laboratory qubit regime); it does not show that the framework is incoherent in the regime where it bites (macroscopic record superpositions). The Bloch sphere is recovered to astronomical precision in lab regimes; finite precision matters foundationally only at the macroscopic-record scale, where the measurement problem actually lives.

### 5.4 Relationship to the algebraic indistinguishability

The Witten/CPW algebraic framework gives a basis-independent *exact* equivalence relation on regional states: $\omega_\Psi = \omega_\Phi$ as states on $\hat{\mathcal{A}}(R)$. Our physical-resolution-floor postulate gives a *coarser* equivalence: $\omega_\Psi \approx_\epsilon \omega_\Phi$, where the approximation is at the physical-precision floor $\epsilon$. Physical equivalence is coarser than algebraic equivalence: two algebraically distinct states can be physically equivalent if they differ by less than $\epsilon$.

Algebraic equivalence (Witten) is what's *mathematically* established by the Type II algebra structure. Physical-resolution equivalence (our postulate) is the foundational reading we add on top. Both relations are basis-independent and intrinsic to the regional geometry; the latter is the relevant one for the measurement problem.

The macroscopic record structure enters naturally: macroscopically distinct records $\{|s_i\rangle|A_i\rangle|E_i\rangle\}$ are those distinguished by the environmental algebra $\hat{\mathcal{A}}(E)$ (the algebraic formulation of einselection). Physical equivalence on the apparatus + environment region is "indistinguishability at the (FQ) resolution floor on the apparatus + environment algebras."

---

## 6. The Mechanism: Decoherence, Concentration, and Algebraic Resolution

### 6.1 Decoherence in algebraic terms

In the algebraic framework, decoherence corresponds to the dynamical suppression of off-diagonal expectation values $\omega_\Psi(O_{ij})$ for operators $O_{ij}$ connecting macroscopically distinct record components. Standard decoherence theory (Zurek, Joos, Hartle) gives the dynamical mechanism for the suppression. The algebraic formulation makes this precise: after decoherence, $\omega_\Psi$ on the apparatus + environment algebra approaches a classical-record state — a convex combination $\sum_i p_i \omega_i$ of mutually decohered records.

This is the standard decoherence result, restated algebraically. It does not, by itself, select a single outcome.

### 6.2 What decoherence actually does: exponentially-classical mixtures

A common but misleading reading treats the post-measurement state as a "naive superposition" of macroscopic records — say, "$70\%$ amplitude at spot A, $30\%$ at spot B sitting there as accessible amplitudes." This picture treats the system as if its amplitudes could be directly read off; the puzzle then becomes "how do $70/30$ amplitudes become $100/0$ in a specific run?"

This picture is wrong. We never have direct access to "the amplitudes of the wave function." We have access only to *macroscopic records* on detectors, screens, and observers — which are themselves complex quantum systems with $\sim 10^{20}$–$10^{25}$ degrees of freedom, entangled with the system being measured.

What decoherence actually does is the following.

After interaction with the apparatus and environment, the joint state of system + apparatus + environment is
$$|\Psi\rangle = \sum_k c_k \,|s_k\rangle_S \otimes |A_k\rangle_A \otimes |E_k\rangle_E,$$
where $\{|s_k\rangle\}$ are macroscopically distinguishable system states, $\{|A_k\rangle\}$ are macroscopically distinct apparatus configurations correlated with each $|s_k\rangle$, and $\{|E_k\rangle\}$ are environmental record states.

Decoherence theory (Zurek 2003; Joos et al. 2003) establishes that for any pair of macroscopically distinct records:
$$\langle E_j | E_k \rangle \sim \exp(-\Gamma t) \to \exp(-N)$$
where $\Gamma$ is the decoherence rate and $N \sim 10^{20}$ for typical macroscopic systems on any reasonable timescale. The cross-overlap is **exponentially small** — by factors like $e^{-10^{20}}$.

Translating to the regional algebra-state on $\hat{\mathcal{A}}(R)$ for $R$ containing the apparatus + environment: the induced state is exponentially close to a *classical-looking mixture*:
$$\omega_\Psi^{R} = \sum_k |c_k|^2 \omega_k^R + O(\exp(-N)),$$
where $\omega_k^R$ are the macroscopic record states on $\hat{\mathcal{A}}(R)$ (defined more precisely in §5) and the off-diagonal coherence terms are exponentially suppressed.

This is what decoherence delivers. The diagonal weights $|c_k|^2$ remain. **The off-diagonal coherence terms do not vanish exactly under standard unitary evolution; they become exponentially small but mathematically nonzero.**

### 6.3 The role of (FQ): rendering exponentially-small physically zero

The off-diagonal coherence terms after decoherence are exponentially small but mathematically nonzero. In standard QM, this is the source of the measurement problem: even if the coherence terms are $\sim e^{-10^{20}}$, they are still nonzero, and one is forced to either treat all branches as real (MWI) or invoke a separate selection mechanism (collapse, modal value-rule).

**Under (FQ), exponentially-small coherence terms are physically zero.** The (FQ) resolution floor $\epsilon(R)$, while astronomically fine in absolute terms, is enormously larger than $e^{-10^{20}}$. By Lemma 1 (§5.1), regional algebra-state components below the (FQ) precision floor are physically equivalent to exactly zero.

For a typical macroscopic detection scenario:
- Decoherence suppression of off-diagonal coherence: $\sim e^{-10^{20}}$
- (FQ) precision floor for the apparatus + environment region: $\epsilon(R) \sim e^{-Q_R/\text{(record dim)}}$, vastly larger than the decoherence suppression

Therefore: after decoherence + (FQ), the regional state on $\hat{\mathcal{A}}(R)$ is *exactly* the classical-looking mixture
$$\omega_\Psi^{R} = \sum_k |c_k|^2 \omega_k^R,$$
with the off-diagonal coherence terms not merely "suppressed" but *physically zero*. The macroscopic records are physically exclusive in $R$.

This is the cooperative role of decoherence and (FQ):
- **Decoherence** drives off-diagonal coherence to exponentially small values dynamically (standard QM)
- **(FQ)** renders these exponentially small values *physically zero* (foundational postulate)

The result: the physical regional state on $\hat{\mathcal{A}}(R)$ is a *strict* classical mixture over macroscopic records, with no remaining off-diagonal coherence.

### 6.4 Per-run branch selection via microscopic initial conditions

The classical mixture $\sum_k |c_k|^2 \omega_k^R$ is *not* a single record. It is a probability distribution over records, with weight $|c_k|^2$ on each.

In any specific run, which record obtains? The framework's answer:

**Per-run, the universe is in one specific branch of the decohered-and-(FQ)-cleaned classical mixture. Which branch is selected by the per-run microscopic initial conditions of the apparatus + environment, propagated through the unitary dynamics from these specific microstates.**

This is analogous to how, in classical statistical mechanics, a system at temperature $T$ has specific molecular configurations in any individual realization. The thermodynamic ensemble $e^{-\beta H}$ is a probability distribution over microstates; any specific realization sits at one microstate. We do not say "the system is in a quantum superposition of all microstates with thermal weights"; we say "the system is in some specific microstate, the distribution over runs follows the thermal ensemble."

In the quantum case, the same structure obtains with one additional ingredient: the per-run microstate must be consistent with the (FQ)-decohered structure on the regional algebra. After decoherence + (FQ), the regional algebra-state is strictly classical (no remaining off-diagonal coherence); the per-run universe occupies one branch of this strictly-classical mixture; which branch is determined by the specific microscopic initial conditions.

**This is not a magic transition from "70% A + 30% B as a superposition" to "100% A as a single outcome".** It is the recognition that:
1. We never have direct access to a "70%/30% superposition" of macroscopic alternatives — we have access only to macroscopic records, which after decoherence are exponentially exclusive
2. (FQ) makes "exponentially exclusive" into "strictly exclusive"
3. The per-run universe is in one of the now-strictly-exclusive branches
4. Which branch is selected by per-run microscopic IC

The per-run "microscopic initial conditions" are *not* hidden variables in any ontological sense. They are simply *the actual physical state of the apparatus + environment in the specific run*. Different runs of an experiment correspond to different actual physical universes — different particles emitted, different microscopic apparatus states, different environmental configurations. These differences are not added structure; they are the standard fact that *actual physical universes differ across actual physical experiments*. Standard QM, at the universal-wave-function level, already accommodates this trivially: the universal wave function is a function of all degrees of freedom in the universe; those degrees of freedom take different actual values in different runs.

The framework is **ψ-monist**: there is no ontological structure beyond the universal wave function. What the framework does — and what standard textbook QM elides — is to take seriously that:
1. The universal wave function (not the textbook subsystem wave function) is the actual physical state in each run
2. Different runs are different actual physical universes, not different versions of "the same" universe
3. The Born statistics across runs come from the distribution of *actual* initial conditions across *actual* runs — not from any "alternative" wave functions for a single preparation

In Bohmian language: there are no Bohmian particles, no extra ontological layer; the universal wave function is the only thing, and different runs have different actual universal wave functions because the actual physical universe differs in each run. This is wavefunction-monist standard QM with (FQ) added as a finite-information constraint.

### 6.5 Theorem: Single-record per-run wave functions

**Theorem 1 (Single-record per-run wave functions).** *Under (FQ) and standard decoherence dynamics of unitary QFT, the per-run physical state on the regional algebra $\hat{\mathcal{A}}(R)$ for $R$ containing apparatus + environment after measurement is, with regional physical content given by the algebraic-state-modulo-(FQ)-precision equivalence class, a single-record state $\omega_{k_{\rm run}}^R$.*

*Proof.* By standard decoherence theory, after measurement interaction, the joint state's induced regional state on $\hat{\mathcal{A}}(R)$ has off-diagonal coherence terms suppressed exponentially: $\omega_\Psi^R = \sum_k |c_k|^2 \omega_k^R + O(\exp(-N))$. By Lemma 1 (§5.1), components below the (FQ) precision floor $\epsilon(R)$ are physically equivalent to zero. Since $e^{-N} \ll \epsilon(R)$ for any reasonable macroscopic decoherence regime, the off-diagonal coherence terms are physically exactly zero. The resulting regional state is the strict classical mixture $\sum_k |c_k|^2 \omega_k^R$ — with macroscopic records physically exclusive (no remaining coherence between distinct $\omega_k^R$).

In any specific run, the per-run universe occupies one specific branch of this strictly-exclusive classical mixture. Which branch is the realized one is determined by the per-run microscopic initial conditions of the apparatus + environment, propagated through unitary evolution. The per-run physical regional state on $\hat{\mathcal{A}}(R)$ is therefore $\omega_{k_{\rm run}}^R$ for some specific $k_{\rm run}$ — a single-record state. $\blacksquare$

**Remark on the role of each ingredient:**
- **Decoherence** drives the regional algebra-state to be exponentially close to a classical mixture (standard QM, no postulate)
- **(FQ)** converts "exponentially close" to "physically exact" (foundational postulate; renders off-diagonal coherence physically zero)
- **The per-run wave function itself** is one specific branch of the strictly-exclusive classical mixture — this is ψ-monism: no additional ontology, the wave function in each actual run is simply different from the textbook formal ensemble descriptor
- **Born statistics** across runs follow from the typicality of microscopic IC (open: Concentration / Born-typicality program)

**What standard linear QM does not provide:** the strict classical exclusivity (off-diagonal coherence is exponentially small, not zero) and the per-run branch selection. (FQ) provides the first; per-run microscopic IC provide the second. Neither requires modifying the Schrödinger evolution.

### 6.6 What is preserved, and what algebraic restriction is (and is not)

**Preserved exactly on the physical state space $\mathcal{H}_{\rm phys}$:** the unitary Schrödinger / Heisenberg evolution under *physical Hamiltonians* (those that preserve $\mathcal{H}_{\rm phys}$; cf. §7.6). Within $\mathcal{H}_{\rm phys}$, no modification of dynamics, no stochastic term, no projection operator. The physical Hamiltonian generates standard linear unitary evolution on the constrained physical state space.

**Constrained at the kinematic level:** the physical state space itself is restricted to $\mathcal{H}_{\rm phys}$ (those universal wave functions satisfying the Branch-Summed Holographic Bound $I_\Sigma \le Q_R$ for every bounded region). States outside $\mathcal{H}_{\rm phys}$ are mathematically writeable in the unrestricted Hilbert-space formalism but are not physically realizable. Physical Hamiltonians are restricted to those preserving $\mathcal{H}_{\rm phys}$. This is analogous to gauge theory: physical state space is a constrained submanifold; physical Hamiltonians preserve gauge invariance; unrestricted Hilbert-space Hamiltonians are mathematically writeable but unphysical.

**The relationship between global evolution and regional physical content.** On $\mathcal{H}_{\rm phys}$ the universal state evolves unitarily under a physical Hamiltonian: $|\Psi_t\rangle = U(t)|\Psi_0\rangle$. The induced regional algebra-state evolves linearly: $\omega_t(O) = \omega_0(U(t)^\dagger O U(t))$ for $O \in \hat{\mathcal{A}}(R)$. The map $|\Psi\rangle \mapsto \omega_\Psi$ from Hilbert vectors to regional algebra-states is a structural restriction (analogous to forming a reduced state). It is mathematically linear on density operators and quadratic in vectors.

What is *not* a standard mathematical operation: the physical-precision quotient. Under the literal physical-instantiation reading, the physical wave function in $R$ is not the algebra-state $\omega_\Psi$ but the *equivalence class of $\omega_\Psi$ under physical resolution-$\epsilon$ equivalence*. This quotient is coarser than the algebra-state equivalence; it is the operative equivalence relation on physical regional states.

The physical-precision quotient is what does the foundational work. It is what renders exponentially-small off-diagonal coherence between macroscopic records physically equal to exact zero — converting the merely-approximate classical mixture that standard decoherence delivers into a strictly-exclusive classical mixture. Per-run branch selection (which one of the now-strictly-exclusive branches the universe occupies in a specific run) is supplied by the per-run microscopic IC, not by the precision quotient itself. The quotient is not present in standard QM (which has continuous Hilbert state space); it is not present in Witten's algebraic framework (which has continuous normal-state space on the Type II algebra); it is present in our literal reading of (FQ).

### 6.7 Physics is the macroscopic observable content; branches are not part of it

A potential objection to the framework: even after decoherence + (FQ) render off-diagonal coherence physically zero, the resulting strict classical mixture $\sum_k p_k \omega_k^R$ on $\hat{\mathcal{A}}(R)$ is still a mixture over multiple macroscopic records. To get a single-record per run, one might think the framework needs an additional "selection rule" — leading either to MWI (all branches real) or to a hidden-variable mechanism for which branch is actual.

The framework's response cuts deeper than introducing a selection mechanism. It refuses the question of "which Everett branch is realized" by reframing what counts as physical content:

> **Physics is what is encoded in the macroscopic observable algebra. The full universal wave function (with all its mathematical branch structure) is a calculational/formal apparatus; the physical content of any region is the state on the macroscopic record subalgebra $\mathcal{C}(R) \subset \hat{\mathcal{A}}(R)$. We do not have direct physical access to "the universal wave function's branch structure" — only to the macroscopic record content. (FQ) constrains the macroscopic record content. At that level, multi-record states are forbidden (conjecturally, see §7.6). Single-record per run is therefore not a "selection" from multiple physically real branches — it is the structural consequence of (FQ) on the macroscopic observable algebra. The microscopic branch question is not part of the physics because it does not appear in the macroscopic observable content.**

This is the operational-realist + algebraic + holographic move. Physics is the content of macroscopic observable algebras (algebraic QFT lineage). These algebras are constrained by (FQ). The "Everett branches" of the universal wave function are mathematical artifacts of the underlying Hilbert-space formalism; they don't enter the macroscopic observable content; they're not part of physics.

This reframing is what motivates the Macroscopic Definiteness Conjecture, the framework's central new mathematical claim, formalized in §7.6.

### 6.8 The macroscopic record subalgebra and the spectrum of records

**Definition (Macroscopic record subalgebra).** *Let $\hat{\mathcal{A}}(R)$ be the regional Type II crossed-product algebra for region $R$ containing apparatus + environment. The **macroscopic record subalgebra** $\mathcal{C}(R) \subset \hat{\mathcal{A}}(R)$ is the maximal commutative subalgebra of observables that are decoherence-stable under the dynamics of the apparatus + environment — that is, the subalgebra selected by einselection (Zurek) and that supports definite macroscopic records over the relevant timescales.*

For the double-slit screen, $\mathcal{C}(R)$ is generated by the position-localized record projectors $\{P_k\}$ corresponding to spots at different positions. For a generic measurement, $\mathcal{C}(R)$ is the algebra of pointer-basis observables. The subalgebra is approximately commutative (off-diagonal terms between distinct records are exponentially suppressed by decoherence and physically zero under (FQ); cf. §6.2–6.3).

**Spectrum of records.** $\mathrm{Spec}(\mathcal{C}(R))$ is the set of macroscopic record configurations — for the screen, the set of distinct spot positions; for a Stern-Gerlach detector, the set of distinct deflection records; etc. By the Gelfand representation theorem, $\mathcal{C}(R) \cong C(\mathrm{Spec}(\mathcal{C}(R)))$ (continuous functions on the spectrum), and states on $\mathcal{C}(R)$ are probability measures on $\mathrm{Spec}(\mathcal{C}(R))$.

For a finite or countable spectrum (which is the relevant case for macroscopic records on a finite-resolution screen), states on $\mathcal{C}(R)$ are probability distributions $\{p_k\}$ over records.

**Thickened-state construction.** For each record $r \in \mathrm{Spec}(\mathcal{C}(R))$, the **thickened state** $\tilde{\delta}_r$ on the full algebra $\hat{\mathcal{A}}(R)$ is the state corresponding to "record $r$ realized" — including all the microscopic structure of the apparatus + environment configuration that produces macroscopic record $r$. This thickened state uses approximately $Q_R$ bits of physical information (it is a specific microscopic configuration of the full apparatus + environment region; macroscopic records consume approximately the full regional holographic capacity).

For a multi-record state — a probability measure $\mu = \sum_k p_k \delta_{r_k}$ on $\mathrm{Spec}(\mathcal{C}(R))$ with multiple records — the *thickened state* is $\tilde{\mu} = \sum_k p_k \tilde{\delta}_{r_k}$ on $\hat{\mathcal{A}}(R)$. This thickened state must encode each constituent macroscopic record's full microscopic configuration plus the probability weights.

**Conjecture (Information cost of multi-record thickened states):** *The renormalized entropy $S_{\rm ren}(\tilde{\mu})$ of a thickened multi-record state $\tilde{\mu} = \sum_k p_k \tilde{\delta}_{r_k}$ scales as $\sum_k p_k S_{\rm ren}(\tilde{\delta}_{r_k}) + H(\{p_k\})$ where $H$ is the Shannon entropy, when the constituent records $\{r_k\}$ are physically distinct macroscopic configurations with mutually exclusive microscopic specifications. When each $S_{\rm ren}(\tilde{\delta}_{r_k}) \approx Q_R$ (records saturate the regional capacity), the thickened multi-record state has $S_{\rm ren}(\tilde{\mu}) \approx Q_R + H(\{p_k\})$, which exceeds $Q_R$ when $H(\{p_k\}) > 0$ — i.e., for genuinely multi-record states.*

This is the cost-counting argument the framework rests on for the Macroscopic Definiteness Theorem of §7.6.

### 6.9 The Bell escape: holographic nonseparability vs classical separability

A natural objection: any deterministic single-world theory reproducing standard quantum predictions must confront Bell's theorem. The framework is **ψ-monist** (the wave function is the only ontology; no extra hidden particles or fields are added) but the per-run wave function in any specific run differs from the textbook formal ensemble descriptor; it reproduces standard quantum predictions; it has single outcomes per run. Which Bell assumption does it reject?

**The framework's answer: measurement independence, grounded in holographic nonseparability.**

Bell's theorem assumes the hidden variables $\lambda$ characterizing the source are statistically independent of the later measurement settings $a, b$:
$$\rho(\lambda \mid a, b) = \rho(\lambda).$$

This is the "measurement independence" assumption (also called "statistical independence" or the "free variables" assumption). Rejecting it is often dismissed as "superdeterminism," but the framework offers a non-conspiratorial version.

**The framework's argument.** A Bell experiment is not three independently specifiable pieces — source variables, Alice's setting, Bob's setting — that could in principle be combined in arbitrary configurations. It is *one finite-information physical process embedded in a common spacetime history*. The microscopic states of the source, the detector substrates, the random-number generators, the experimenters, the electromagnetic environment, the gravitational background, and the surrounding spacetime region are all parts of one physical state.

The assumption that one can vary $a$ and $b$ while holding fixed the distribution of $\lambda$ presupposes a classical separability that holography has principled reasons to deny:

> "In quantum gravity, bounded regions do not factor into independent tensor products in the naive way. The information content of a region is constrained globally by boundary area. The algebraic structure is not that of independently specifiable local classical variables sitting in spacetime."

This is reflected in the algebraic QFT framework itself: local algebras are Type III$_1$ (no Hilbert-space factorization between region and complement); after gravitational dressing, the Type II structure encodes global constraints (the modular flow ties together regional and global structure). Classical separability of "this region's local variables can vary independently of that region's local variables" is *already false at the algebraic level* in QFT, and holographically more so when gravity is included.

The framework's denial of measurement independence is not a denial of *operational free choice*. Alice and Bob can choose their settings via any procedure available to them; no signal is sent superluminally; no empirical freedom is lost. What is denied is the metaphysical counterfactual:

> "The exact same hidden-variable distribution at the source could have occurred with arbitrarily different physically instantiated later settings."

This counterfactual presupposes that source-state and later-setting are independently variable physical facts. In a finite-information universe with holographic constraints, they are not: they are correlated parts of one global state.

**Why this is the cleanest Bell escape for this framework.** Other Bell escapes would require:
- **Nonlocality** (instantaneous influences): conflicts with the framework's commitment to Lorentz-covariant evolution and the Lorentz-invariance of the bound.
- **Retrocausality**: requires a separate causal-structure modification.
- **Rejection of outcome independence**: typically requires nonlocal collapse-like mechanisms.

Denial of measurement independence preserves: no preferred foliation; no explicit nonlocal collapse; no action-at-a-distance; exact unitary evolution of the underlying field algebra; Lorentz-covariant information bounds. The framework pays the Bell price at measurement independence / classical separability rather than at relativistic locality or unitary dynamics. **That is a defensible price**, and it is the price the framework's commitments naturally select.

**Position with respect to Kochen-Specker.** If per-run microscopic structure determines outcomes, value assignments must be contextual — which the framework accepts. The per-run wave function's content on a regional algebra is naturally contextual: different measurement contexts probe different algebra-projections, and there is no requirement of joint-value consistency across noncommuting contexts.

**Position with respect to PBR.** The framework is **ψ-ontic and ψ-monist**: the wave function is physically real and is the only ontology. The framework does *not* add hidden particle positions, hidden fields, or any other ontological layer beyond the wave function itself. What is "supplemented" relative to standard textbook QM is not the ontology but the *recognition that the per-run wave function differs from the formal ensemble descriptor*: the formal wave function used in textbook calculations describes the distribution across runs; the per-run wave function in any specific run is a definite physical state of the universe. PBR rules out certain ψ-epistemic positions; the framework is ψ-ontic and not one of those.

**Sister program: Palmer's RaQM / Invariant Set Theory.** Palmer (2025 and prior work) develops a structurally similar Bell escape: principled rejection of measurement independence via the geometry of a fractal invariant set in cosmological state space. The two frameworks share the strategic shape — single-world realism + measurement-dependence grounded in deep structural physics, not in conspiratorial superdeterminism. They differ in the motivating principle (chaos / invariant set vs holography / information capacity) and the mathematical apparatus (p-adic measures + Niven's theorem vs CPW Type II algebras + finite-precision postulate). Detailed comparison is in §10.8.

---

## 7. Formal Consequences

### 7.1 Theorem (FQ restricts physically realized wave functions)

**Theorem 2.** *The class of per-run wave functions consistent with (FQ) is a proper subclass of formally describable wave functions in standard $T_{QM}$. Specifically, formal wave functions whose induced state on some $\hat{\mathcal{A}}(R)$ violates the renormalized entropy bound $S_{\rm ren}(\omega_\Psi) > Q_R$ are excluded as physically realized per-run states.*

*Proof.* (FQ) part (ii) imposes $S_{\rm ren}(\omega_\Psi) \le Q_R$ on per-run wave functions. Formal wave functions in standard $T_{QM}$ are not subject to this constraint; we can construct formal states whose induced regional states violate the bound. Such formal states are excluded from the physical model class. $\blacksquare$

### 7.2 Theorem (Finite physical resolution)

**Theorem 3.** *Under the literal physical-instantiation reading of (FQ), the per-run wave function in any bounded region $R$ has a finite physical resolution floor $\epsilon(R) > 0$. Amplitudes within $\epsilon(R)$ of $0$ are physically equivalent to amplitude exactly $0$; amplitudes within $\epsilon(R)$ of $1$ are physically equivalent to amplitude exactly $1$.*

*Proof sketch.* By (FQ) part (iii), the wave function in $R$ has total physical information content bounded by $Q_R$. Specifying amplitudes to arbitrary precision requires unbounded information. Therefore amplitudes are physically specified only to finite precision $\epsilon(R)$. Within this precision, distinct mathematical amplitudes correspond to the same physical state. Functional dependence of $\epsilon(R)$ on regional geometry, macroscopic record dimension, and the (FQ) bound is identified as an open quantitative problem (§11.4); the qualitative existence of $\epsilon(R) > 0$ follows from the literal reading. $\blacksquare$

### 7.3 Theorem (Single-record per-run wave functions)

**Theorem 4 (Single-record per-run).** *Under (FQ) in its literal physical-instantiation reading and the per-run concentration claim of §6.2 (per-run amplitudes for distinct macroscopic record components driven dynamically toward $0$ or $1$ via decoherence + microscopic initial conditions), the per-run wave function in any region $R$ containing apparatus + environment after measurement is physically a single-record state. The realized outcome is the record whose amplitude has crossed above $1 - \epsilon(R)$; alternative records have amplitudes below $\epsilon(R)$ and are physically equivalent to amplitude exactly $0$.*

*Proof.* By Theorem 3, (FQ) gives a finite resolution floor $\epsilon(R) > 0$. By the concentration claim of §6.2, per-run amplitudes for distinct macroscopic records evolve dynamically toward $0$ or $1$. Once the concentration crosses the resolution threshold, the per-run wave function is physically a single-record state. The single-record state is the wave function's actual physical state in $R$. No collapse postulate is required; the structural combination of (FQ) (precision floor) and decoherence (concentration) produces the single-record outcome. $\blacksquare$

*Remark on the role of the concentration claim.* The concentration claim of §6.2 is that per-run amplitudes evolve dynamically toward $0$ or $1$. Whether this convergence is exact mathematically or only approximate is irrelevant to Theorem 4: the (FQ) resolution floor makes "approximate convergence to within $\epsilon$" physically equivalent to "exact convergence to $0$ or $1$." Standard decoherence + microscopic IC give the approximate convergence; (FQ) supplies the precision floor at which approximate becomes exact physically. This is the cooperative role of the two ingredients.

### 7.4 Theorem (Born statistics from typicality, schematic)

**Theorem 5 (Born from typicality, schematic).** *If the measure $\mu$ on microscopic initial conditions is appropriately chosen, then for a standard preparation/measurement procedure with formal Born weights $|c_k|^2$, the empirical relative frequency of macroscopic outcome $k$ (the record above the resolution threshold in the per-run wave function) across many runs converges to $|c_k|^2$.*

*Proof sketch.* The (FQ)-constrained dynamics, starting from microscopic initial conditions drawn from $\mu$ and propagating to the post-measurement (FQ)-resolved per-run wave function, induces a map from initial conditions to realized records. The claim is that for the appropriate $\mu$, the measure of initial conditions mapped to record $k$ is $|c_k|^2$. Rigorous derivation — specification of $\mu$, proof that the (FQ)-constrained dynamics yields the right measure-preserving structure, justification that this measure is the empirically realized one — is identified as the second key open problem of the framework, analogous to but distinct from Bohmian $|\psi|^2$-equivariance. The framework specifies *what* needs to be proved; the proof itself is open. $\blacksquare$

### 7.5 What §7.1–7.4 establishes

(FQ) restricts the model class properly (Theorem 2); the literal physical-instantiation reading implies finite physical resolution (Theorem 3); combined with dynamical concentration via decoherence + microscopic IC, this yields single-record per-run wave functions structurally (Theorem 4); Born statistics emerge from typicality (Theorem 5, schematic).

The framework's structural skeleton: (FQ) is the literal physical-instantiation reading of the Bekenstein-Bousso bound, stated rigorously in the CPW Type II algebraic framework; the precision floor is the structural consequence; concentrated per-run amplitudes cross the threshold and the per-run wave function physically is a single-record state.

### 7.6 The Branch-Summed Holographic Superselection Rule (foundational postulate)

The above theorems establish the framework's structure within standard renormalized entropy. They leave a critical question: even after decoherence + (FQ) deliver a strict classical mixture $\sum_k p_k \omega_k^R$ on the regional algebra, this is *still a mixture over multiple macroscopic records*. Standard renormalized entropy on the Type II algebra does **not** forbid such mixtures — by the standard counting, mutually exclusive macroscopic record sectors partition the regional Hilbert space, $\sum_k d_k \le 2^{Q_R}$, and the mixture entropy stays below $Q_R$. To establish single-record per-run as a structural consequence at the level of the macroscopic observable content, the framework commits to a stronger principle than standard entropy bounds: a **branch-summed holographic superselection rule**.

This is the framework's central new physical postulate beyond the algebraic scaffolding of CPW/Witten. It is formulated using the decoherent-record machinery of §6.8 combined with branch-summed support counting.

**Definition (Branch-summed record cost).** *Let $\mathcal{C}(R) \subset \hat{\mathcal{A}}(R)$ be the macroscopic record subalgebra (§6.8). For a state $\omega_R$ on $\hat{\mathcal{A}}(R)$, let $p_r = \omega_R(P_r)$ be the regional probabilities of records $r \in \mathrm{Spec}(\mathcal{C}(R))$. For each record $r$, let $c_R(r)$ be its per-record physical cost — combining the Zurek-style algorithmic complexity of the macroscopic record description with the residual microscopic entropy of the apparatus + environment configuration consistent with that record. The **smooth active set** $\mathcal{A}_\epsilon(\omega_R)$ for tolerance $\epsilon$ is the smallest set of records carrying total probability $\ge 1 - \epsilon$. The **branch-summed record cost** is*
$$I_\Sigma^\epsilon[\omega_R] := \sum_{r \in \mathcal{A}_\epsilon(\omega_R)} c_R(r).$$

For a single-record state with $c_R(r) = I_0$: $I_\Sigma \approx I_0$.
For an $N$-record state with comparable record costs: $I_\Sigma \approx N \cdot I_0$.

This measure is **not** standard von Neumann or renormalized entropy on the Type II algebra. It counts the *additive* cost of each occupied decoherent macroscopic record sector, summing rather than coarse-graining over alternatives. It draws on the decoherent-histories framework (Gell-Mann-Hartle, Griffiths, Omnès), Quantum Darwinism / spectrum broadcast structures (Zurek; Brandão-Piani-Horodecki), smooth support / Rényi-0 / Hill-number quantification of effective branch counts, and Zurek-style physical entropy for per-record cost.

**Postulate (Branch-Summed Holographic Bound — central physical axiom).** *The branch-summed record cost is bounded by the holographic capacity:*
$$\boxed{I_\Sigma^\epsilon[\omega_R] \le Q_R = \frac{A(\partial R)}{4\ell_P^2} \quad \text{for all bounded regions } R \text{ and all physical states } \omega_R.}$$

This is **a strengthening of the standard Bekenstein-Bousso bound**, not a derivation from it. Standard holographic entropy bounds limit the entropy of regional reduced states; the branch-summed bound limits the sum of per-record costs across coexisting decoherent macroscopic records. Existing algebraic-QFT/holography results do not establish the branch-summed bound; we postulate it as a new physical principle.

**The framework's commitment: the Branch-Summed Bound is a SUPERSELECTION rule, not a dynamical modification.**

Under this commitment, the framework's structure is the following.

**Definition (Physical state space).** $\mathcal{H}_{\rm phys} \subset \mathcal{H}$ is the subset of universal wave functions whose induced regional states satisfy the Branch-Summed Bound for every bounded region:
$$\mathcal{H}_{\rm phys} = \{|\Psi\rangle \in \mathcal{H} : I_\Sigma^\epsilon[\omega_\Psi^R] \le Q_R \text{ for all bounded } R\}.$$

States outside $\mathcal{H}_{\rm phys}$ are *kinematically forbidden* — they are mathematically writeable in the unrestricted Hilbert-space formalism but are not physically realizable.

**Definition (Physical Hamiltonian).** A Hamiltonian $H$ is **physical** if its dynamics preserves $\mathcal{H}_{\rm phys}$: $e^{-iHt/\hbar} \mathcal{H}_{\rm phys} \subset \mathcal{H}_{\rm phys}$ for all $t$.

The set of physical Hamiltonians is a proper subset of the set of all Hermitian operators on the unconstrained Hilbert space. Generic Hilbert-space Hamiltonians do not preserve $\mathcal{H}_{\rm phys}$; physical Hamiltonians do.

**Theorem 6 (Macroscopic Definiteness, under the Branch-Summed Superselection Postulate).** *For any physical state $|\Psi\rangle \in \mathcal{H}_{\rm phys}$ and any bounded region $R$ containing apparatus + environment with $N_{\max} = \lfloor Q_R / I_0 \rfloor$ macroscopically distinguishable records, the smooth active set $\mathcal{A}_\epsilon(\omega_\Psi^R)$ has cardinality at most $N_{\max}$. In the regime where each macroscopic record approximately saturates the regional capacity ($I_0 \approx Q_R$), $N_{\max} = 1$ — only single-record states are physically realizable.*

*Proof.* By definition, $|\Psi\rangle \in \mathcal{H}_{\rm phys}$ satisfies $I_\Sigma^\epsilon[\omega_\Psi^R] \le Q_R$. By the branch-summed counting, $|\mathcal{A}_\epsilon| \cdot I_0 \le I_\Sigma^\epsilon \le Q_R$, hence $|\mathcal{A}_\epsilon| \le Q_R/I_0$. When $I_0 \approx Q_R$, $|\mathcal{A}_\epsilon| \le 1$. $\blacksquare$

The single-record-per-region structure of physical states is therefore a *structural consequence* of the Branch-Summed Holographic Superselection Postulate. Multi-record states are not absent because of dynamical collapse; they are absent because they are *not in the physical state space*.

**Dynamical content of Option 2.** Standard Hilbert-space QM is the unconstrained formalism. The constrained subset $\mathcal{H}_{\rm phys}$ is a *nonlinear submanifold* of $\mathcal{H}$ (the constraint $I_\Sigma \le Q_R$ is nonlinear in the state). Physical Hamiltonians are constrained to preserve this submanifold. The framework's claim is that the actual physical Hamiltonian of nature respects the Branch-Summed Bound — measurement-like unitaries that would (in unrestricted QM) take a single-record state to a multi-record state do not occur in the physical dynamics; the actual physical dynamics, with the constraint imposed, takes single-record states to single-record states (selected by the actual physical initial conditions of apparatus + environment in that run).

This is analogous to how gauge theories work: the physical state space is a constrained submanifold of the unrestricted Hilbert space (gauge-invariant states); physical Hamiltonians preserve gauge invariance; the unrestricted Hamiltonians are mathematically writeable but unphysical. In gauge theory the constraint is gauge invariance; in QIQT-H the constraint is the Branch-Summed Holographic Bound.

**Schrödinger evolution holds on $\mathcal{H}_{\rm phys}$.** Within the physical state space, evolution under physical Hamiltonians is linear and unitary — Schrödinger evolution is preserved. What is *not* preserved is the freedom to use arbitrary Hilbert-space Hamiltonians; physical Hamiltonians are constrained.

**The price the framework pays.** This commitment modifies the physical dynamics relative to unrestricted standard QM. The set of physical Hamiltonians is a constrained set. This is a substantive modification of QM at the foundational level, but only in regimes where the branch-summed cost approaches the holographic capacity. At lab scales — where macroscopic records use only $\sim 10^{25}$ bits of an available $\sim 10^{70}$-bit holographic capacity per cubic meter — the constraint is operationally vacuous. Standard QM at lab scales gives the same predictions as the constrained dynamics. The constraint becomes operationally relevant only when branch-summed cost approaches $Q_R$ — i.e., for macroscopic measurement records, where the framework's deviation from standard QM is to *enforce* single-record per-run at the kinematic level.

**Mathematical work needed:**

1. **Precise specification of $\mathcal{C}(R)$** as the einselected/Darwinistic record subalgebra (drawing on decoherent histories, Quantum Darwinism).
2. **Per-record cost $c_R(r)$** rigorously defined via Zurek physical entropy.
3. **Branch-summed bound $I_\Sigma^\epsilon \le Q_R$** as new physical principle — not derivable from existing holography, but conjecturally connectable to deeper quantum-gravity arguments about distinguishable record content per region.
4. **Characterization of physical Hamiltonians** — which Hermitian operators preserve $\mathcal{H}_{\rm phys}$? This is analogous to characterizing gauge-invariant Hamiltonians in gauge theory.
5. **Born statistics from typicality** under the constrained dynamics — the typicality theorem for which single-record state is realized per run, with the realization measure reproducing Born weights $|c_k|^2$.

Each of these is a concrete open mathematical problem; together they constitute the framework's explicit research program beyond the borrowed CPW/Witten scaffolding.

**Why this dissolves the MWI tension.** Under the Branch-Summed Superselection Postulate (Theorem 6), the framework escapes the MWI-without-many-worlds problem cleanly:

- The unconstrained Hilbert space contains states with multi-record macroscopic content; these are mathematically writeable but not in $\mathcal{H}_{\rm phys}$
- Physical states (those in $\mathcal{H}_{\rm phys}$) have $I_\Sigma \le Q_R$ for every bounded region; with $I_0 \approx Q_R$ at macroscopic scales, this means single-record per region
- The "Everett branches" are mathematical artifacts of considering unrestricted Hilbert-space states; the actual physical state space excludes them by the superselection rule
- We don't need to "select" one branch from many physically real branches — there are no multi-branch physical states to select from

The framework's single-world per run is therefore a *kinematic structural feature* of the physical state space, not a dynamical selection event. The superselection rule is what makes this true.

**Why this is genuinely new physics beyond Witten/CPW.** Witten/CPW provide the Type II algebraic infrastructure for regional generalized entropy. They do *not* establish:
- The branch-summed bound as a strengthening of standard holographic entropy
- The constraint that physical Hamiltonians preserve $\mathcal{H}_{\rm phys}$
- The exclusion of multi-record states as kinematically forbidden

These are the framework's specific new physical principles, building on the Witten/CPW scaffolding. They constitute a concrete research program: define the branch-summed cost rigorously; postulate the Branch-Summed Bound as new physics; characterize the constrained dynamics; derive Born statistics from typicality within the constrained dynamics.

---

## 8. The Bekenstein-Bousso Bound and the Literal Reading

### 8.1 The bound's pedigree

Bekenstein (1981), 't Hooft (1993), Susskind (1995), Bousso (2002), and most recently Banks (2025) and the CPW (2022) Type II construction. The bound has multiple independent motivations across the quantum-gravity literature.

The numerical scale: $Q_R \sim 10^{70}$ nats for a one-meter region, $\sim 10^{122}$ for the observable universe. Astronomically large, but finite, and area-law.

### 8.2 The literal reading as the natural reading

The historical conflation of "the holographic bound" with "an entanglement-entropy inequality on a fictitious tensor factorization" is an artifact of working in finite-dimensional toy models or in spin-chain QFTs where Hilbert-space factorization is artificially imposed.

In genuine continuum QFT, local algebras are Type III$_1$. There is no entanglement entropy of a region's reduced state; there is no reduced state. The narrow interpretation is mathematically ill-defined.

The literal interpretation — that the bound limits the total physical information content of regional states in the algebraic sense — is the mathematically natural reading once the Type II crossed-product construction is recognized as the rigorous home of regional generalized entropy.

(FQ) is then a precise mathematical statement: the renormalized entropy on $\hat{\mathcal{A}}(R)$ is bounded by $Q_R$.

### 8.3 Wald and higher-derivative corrections

For modified gravitational theories, the bound generalizes via the Wald entropy. The Type II framework extends naturally: the trace on the regional algebra is determined by the gravitational theory, and $Q_R$ takes the Wald form $A f'(R)/(4\ell_P^2)$ for $f(R)$ gravity.

---

## 9. Possible Phenomenological Consequences

### 9.1 Laboratory regime: no deviations

At ordinary laboratory scales, $Q_R$ is astronomically large, and the resolution structure of the Type II algebra is fine relative to the macroscopic record structure of any laboratory apparatus. The framework predicts no deviations from standard QM in standard laboratory experiments. The role of (FQ) at lab scales is structural — it provides the resolution that makes per-run states physically single-record.

### 9.2 Long-baseline regimes

Long-baseline neutrino oscillation and other extended-coherence systems may approach regimes where the Type II resolution structure becomes operationally relevant. The current IceCube and Super-Kamiokande bounds on quantum-gravity-induced decoherence ($\Gamma_Q/E \lesssim 10^{-32}\,\mathrm{GeV}^{-1}$) are consistent with the framework. Rigorous derivation of phenomenological predictions from the Type II structure is deferred to subsequent work.

### 9.3 Cosmological and horizon regimes

The de Sitter static patch and black-hole horizon regions are the natural arenas where Type II$_1$ algebras (with finite trace $\tau(\mathbf{1}) < \infty$) directly apply. CPW developed the Type II$_1$ structure precisely for de Sitter. The cosmological extensions of (FQ) are the natural next step and are deferred to companion papers.

---

## 10. Comparison with Existing Approaches

### 10.1 Copenhagen

Invokes collapse without dynamics. We invoke no collapse. The single-record per-run wave function is a consequence of the Type II structure + decoherence + concentration, not of dynamical reduction.

### 10.2 Many-Worlds

Posits all formal components as equally real branches. We are single-world per run: the per-run wave function's regional state is concentrated on a single record; alternatives correspond to vanishing components in the Type II state space.

### 10.3 Bohmian mechanics

Bohm adds particle positions in $3N$-dim configuration space as a *second ontological layer* beyond the wave function, with a guidance equation connecting the two. The framework adds *no second ontological layer*. We are **ψ-monist**: the wave function is the only ontology. The per-run wave function is simply the actual physical wave function of the universe in any specific run; the formal wave function is the textbook ensemble descriptor. No particles, no fields, no extra structure — the distinction the framework adds is between the formal wave function (ensemble) and per-run wave function (actual), not between the wave function and some other physical thing.

### 10.4 Objective collapse (GRW, CSL, DP, OR)

Modify Schrödinger with collapse terms. We modify nothing dynamical. The Schrödinger evolution of the underlying field algebra is exactly unitary; the regional physical content is structurally single-record after concentration via the Type II algebra structure.

### 10.5 QBism, relational quantum mechanics

Treat the wave function as epistemic / perspectival. We are objectively realist: the per-run wave function is real, the (FQ) constraint is real, the Type II algebra structure is real, the regional states are real physical states.

### 10.6 Modal interpretations, decoherent histories

Introduce a modal value-rule or history-selection structure. We require neither. The Type II algebra has finite resolution intrinsically; concentration + this resolution yield single records without external value-rules.

### 10.7 Ensemble interpretations (Ballentine)

The closest neighbor. Ballentine treats the formal wave function as ensemble-descriptive with per-run states underdetermined. We supply the mechanism: the Type II regional algebra structure makes per-run states physically single-record despite the formal wave function's superposed appearance.

### 10.8 Palmer's Rare-event Quantum Mechanics / Invariant Set Theory (sister program)

Palmer's Rare-event Quantum Mechanics (RaQM 2025, PNAS) and the broader Invariant Set Theory (IST) program is the closest neighbor in the space of *single-world, structural-principle, measurement-dependent* frameworks. Both Palmer and the present framework reject Bell's measurement-independence assumption on principled grounds (not as conspiratorial superdeterminism); both treat the wave function as not exhausting the per-run physical content; both seek to ground the measurement problem's resolution in a deep structural feature of physics rather than in collapse, branching, or particle ontology.

**Shared structural commitments:**
- Single-world realism per run
- Bell escape via principled measurement-dependence (not nonlocality)
- Recognition that the textbook formal wave function does not exhaust the per-run physical content
- Non-conspiratorial rejection of metaphysical counterfactual recombination
- Motivation by deep structural principles rather than ad hoc modification of QM

(The frameworks differ in ontology: Palmer treats the wave function as derived/emergent from invariant-set statistics, with the underlying ontology being points on the fractal invariant set $I_U$; our framework is ψ-monist with the wave function itself as the only ontology, where the per-run wave function is the actual physical state distinct from the textbook formal ensemble descriptor.)

**Differences in mathematical apparatus and motivating principle:**

| | Palmer's RaQM / IST | Present framework |
|---|---|---|
| Mathematical apparatus | p-adic measures; Niven's theorem; fractal invariant set $I_U$ in cosmological state space | CPW Type II crossed-product algebra; finite-precision physical-instantiation postulate |
| Source of measurement-dependence | Counterfactual states off the invariant set are not physically realizable (Impossible Triangle Corollary) | Counterfactual configurations exceed regional information capacity |
| Status of wave function | Derived / emergent from invariant-set statistics; not fundamentally physically real | Physically real but finite-precision (ψ-ontic) |
| Status of Schrödinger evolution | Emergent from chaotic dynamics on invariant set | Preserved exactly at the underlying field-algebra level |
| Connection to quantum gravity | Indirect: chaos-based, cosmological motivation | Direct: Bekenstein-Hawking entropy, Witten/CPW Type II structure |
| Empirical predictions | Cosmological (CMB anomalies, fine-tuning, dark matter); explicit Bell-correlation models | Empirically conservative at lab scales; possible long-baseline signatures; cosmological extensions deferred |

**Relationship: complementary, not competing.** The two frameworks occupy the same niche in foundational space (single-world, Bell-escape via measurement-dependence, structural motivation) but reach it from different physical principles (chaos / invariant set vs holography / information capacity). They are not in conflict and could in principle be combined: Palmer's invariant set could be a characterization of *which* per-run microscopic configurations are physically realized, and our holographic finite-precision bound could be the *physical reason* the invariant set has the structure it does. Both could be true simultaneously.

**Where the frameworks complement each other's weaknesses:** Palmer's program is more developed (PNAS-published, decade of prior literature, explicit cosmological predictions, concrete Bell-model with Niven's theorem) but uses a more idiosyncratic mathematical machinery (p-adic measures, rational/irrational distinction). Our framework uses mainstream algebraic QFT + holographic bound (lower entry cost for the foundations community) but is at the proposal stage with the Concentration Conjecture and Born-typicality program as open work.

**For readers familiar with Palmer:** the present framework can be read as "Palmer's measurement-dependence program with a different motivating principle (holography rather than dynamical chaos) and a different mathematical home (CPW Type II algebras rather than p-adic invariant sets)." For readers unfamiliar with Palmer, the comparison illustrates that measurement-dependence as a Bell escape is a serious foundational position with multiple independent motivations, not a single idiosyncratic move.

### 10.9 The algebraic-foundational program

Our framework can be read as an algebraic foundational program: the macroscopic world is the regional Type II algebra structure, the dynamics is the algebraic evolution, and the (FQ) bound is the holographic constraint on regional information capacity. This connects naturally to:

- Algebraic QFT (Haag-Kastler)
- Generalized entropy program (Wall, Engelhardt-Wall, CPW)
- Quantum-gravity ideas about emergence (Verlinde, Jacobson, Padmanabhan)

### 10.10 Summary comparison

| Approach | Modifies dynamics | Hidden particle state | Branches | Resolution structure | Per-run state |
|---|---|---|---|---|---|
| Copenhagen | Yes (collapse) | No | No | None | Formal + collapse |
| Bohm | No | Yes (positions) | No | None | WF + particles |
| MWI | No | No | Yes (all real) | None | All formal branches |
| GRW/CSL/DP/OR | Yes (stochastic) | No | No | None | Formal until stoch collapse |
| QBism / RQM | No | No | No | None | Epistemic / perspectival |
| Modal | No | No | No | None | Formal + value rule |
| Decoherent histories | No | No | No | None | Formal + history selection |
| Ballentine ensemble | No | No | No | None | An ensemble member, unspecified |
| Palmer RaQM / IST | No (emergent dynamics) | No particles; per-run microstate on invariant set | No | Invariant-set discreteness (p-adic) | Specific microstate on $I_U$; measurement-dependent |
| **(FQ) literal reading framework** | **No** | **No (ψ-monist: only the wave function; per-run WF ≠ formal WF, no extra ontology)** | **No** | **Finite physical resolution from holographic bound** | **One specific single-branch wave function, structurally selected by (FQ) precision floor + decoherence + per-run universal wave function being the actual physical state** |

The (FQ) literal reading framework is uniquely characterized by a **finite physical resolution structure from the holographic bound**: the wave function as a physical state of spacetime has finite specification precision; amplitudes within precision of 0 or 1 are physically equivalent to exact 0 or 1; combined with decoherence and microscopic initial conditions, this yields a single-record per-run wave function structurally — without collapse, without modified dynamics, without hidden particles, without branches. The CPW Type II algebra framework provides the rigorous mathematical infrastructure; the literal physical-instantiation reading of the bound is the additional foundational postulate that does the work.

---

## 11. Conclusion

### 11.1 Summary

We have developed a foundational framework for quantum mechanics that combines two ingredients: (a) the algebraic-QFT-plus-gravitational-dressing framework of Chandrasekaran-Penington-Witten and Witten, providing the rigorous mathematical infrastructure for finite renormalized entropy on bounded regions; and (b) the *literal physical-instantiation reading* of the Bekenstein-Bousso bound (postulated as axiom (FQ)) — that the wave function as a physical state of spacetime has finite physical specification precision determined by the holographic bound on the region.

The structure rests on:

1. **The CPW/Witten algebraic infrastructure (borrowed).** Local algebras in QFT with gravitational dressing are Type II with semifinite trace and well-defined renormalized entropy differences matching generalized entropy. This provides the rigorous algebraic home for the bound.

2. **The (FQ) axiom in its literal physical-instantiation reading (our postulate).** The wave function in any bounded region $R$ is a physical state of spacetime with finite physical information capacity $Q_R = A(\partial R)/(4\ell_P^2)$. Amplitudes have finite physical specification precision $\epsilon(R) > 0$; below the precision, distinct mathematical wave functions are the same physical state. The literal reading goes beyond Witten's algebraic theorem — Witten supplies the mathematical scaffold; the literal physical-instantiation reading is an additional foundational interpretation.

3. **Finite physical resolution (Theorem 3, consequence of (FQ) under the literal reading).** Amplitudes within $\epsilon(R)$ of $0$ are physically equivalent to exact $0$; amplitudes within $\epsilon(R)$ of $1$ are physically equivalent to exact $1$. This is the structural consequence that does the foundational work.

4. **The decoherence-and-concentration mechanism.** Under standard unitary dynamics + microscopic initial conditions of any specific run, per-run amplitudes for distinct macroscopic record components evolve dynamically toward $0$ or $1$. Combined with the (FQ) resolution floor, this yields single-record per-run wave functions structurally (Theorem 4).

5. **The Born typicality program (open).** A conjectural program for deriving Born statistics from typicality of microscopic initial conditions; analogous to but distinct from Bohmian $|\psi|^2$-equivariance, identified as the central open quantitative problem.

We have proved four theorems: model-class restriction (Theorem 2), finite physical resolution (Theorem 3), single-record per-run wave functions (Theorem 4), and Born from typicality (Theorem 5, schematic).

### 11.2 What the framework does and does not deliver

**Delivers:**
- A foundational position in which the macroscopic world emerges from the holographic bound + decoherence + actual run-specific initial conditions, without collapse, hidden particles, branching, modal value-rule, or any ontology beyond the universal wave function
- A precise foundational axiom (FQ) in its literal physical-instantiation reading
- A rigorous mathematical home for the bound via the CPW/Witten Type II algebra framework
- A finite physical resolution floor as the structural consequence of the literal reading (qualitative)
- A single-record per-run consequence (Theorem 4) following from precision floor + decoherence + actual initial conditions
- A clearly identified open program for Born statistics from typicality

**Does not deliver:**
- A quantitative form of the resolution floor $\epsilon(R)$ as an explicit function of regional geometry (qualitative existence is established; quantitative form is open)
- A rigorous typicality theorem reproducing Born weights from explicit measure
- A proof that the literal physical-instantiation reading is the only defensible reading of the bound (it is, we argue, the natural reading; alternative narrow readings are possible and have different structural consequences)
- Lab-scale predictions deviating from standard QM (the framework is empirically conservative)

### 11.2a The mathematical status of the framework: what we have and what we don't

A central question for any foundations paper: do we have the mathematics, or are we hand-waving? We answer honestly.

**Rigorous mathematical infrastructure (borrowed from the QFT / quantum-gravity literature):**

| Component | Status | Source |
|---|---|---|
| Local algebras in QFT as Type III$_1$ factors | Rigorous theorem | Buchholz, Wichmann, Borchers, Longo |
| Algebraic QFT framework (Haag-Kastler nets) | Rigorous | Haag 1992; Haag-Kastler 1964 |
| Crossed-product Type II construction with gravitational dressing | Rigorous (in CPW's setting) | Witten 2022; CPW 2022; CLPW 2022 |
| Semifinite trace on Type II crossed-product algebras | Rigorous | Murray-von Neumann; standard operator algebras |
| Renormalized entropy on Type II algebras matching generalized entropy differences | Rigorous (in CPW's setting) | CPW 2022; Jensen-Sorce-Speranza 2023 |

This is the *mathematical scaffolding* on which the framework is built. It is real mathematical physics, currently under active development in the quantum-gravity literature.

**The framework's foundational axiom (our postulate, not derived from the above):**

The (FQ) axiom in its literal physical-instantiation reading is stated precisely in §4.1. It postulates that the wave function as a physical state of spacetime has finite specification precision per region, with the bound saturating the holographic capacity $Q_R = A(\partial R)/(4\ell_P^2)$. This is a foundational interpretive postulate, not a theorem.

**Qualitative consequences worked out:**

- Lemma 1 (§5.1): finite precision floor $\epsilon(R) > 0$ exists qualitatively
- Decoherence + (FQ) → strict classical mixture (argued qualitatively with numerical scaling: decoherence gives $\sim e^{-10^{20}}$ off-diagonal coherence, far below any reasonable $\epsilon(R)$)
- Per-run single-record outcome from one wave function per run + (FQ) precision floor (Theorem 4, structural consequence)

These are stated with reasoning but not proved as explicit theorems with formal proofs.

**What we do not have (open mathematical work):**

| Open problem | What's needed |
|---|---|
| Explicit form of $\epsilon(R)$ | A function $\epsilon(R) = f(Q_R, \text{record subalgebra dimension}, \text{geometry})$ |
| Decoherence + (FQ) → strict mixture | A theorem in algebraic QFT showing that, under (FQ), decoherent suppression below $\epsilon$ gives a strict classical mixture on the regional algebra |
| Born-typicality theorem | A measure $\mu$ on the space of universal initial conditions, plus an equivariance-type theorem $\mu\{\lambda : k(\lambda, \Psi) = k\} = |c_k|^2$ |
| FQ as operational equivalence (not literal thresholding) | A clean mathematical formulation: states differing on the regional algebra by less than $\epsilon$ (in some operational metric like trace distance) are physically equivalent |
| Connection to Bell correlations | An explicit measurement-dependence model showing how holographic nonseparability reproduces CHSH violations |

**Honest characterization of math status:** the framework provides the *scaffolding* (Type II algebras from CPW/Witten) and the *axiom* ((FQ) literal reading). It establishes *qualitative* consequences. It does not yet have *explicit theorems* for the central claims. This is the status of a research program, not a completed mathematical theory.

The open problems are *concrete and well-defined*: each can be attacked in principle by an analyst willing to engage with both algebraic QFT and foundations of QM. We identify them not as defects of the framework but as the explicit research agenda the framework opens.

**Comparison with other foundations programs:** Bohmian mechanics has a complete mathematical theory (configuration space, guidance equation, $|\psi|^2$-equivariance) but adds a second ontology and faces relativistic incompatibility. Many-Worlds keeps standard QM but multiplies branches and lacks a derivation of Born from amplitudes. GRW modifies dynamics with specific parameters and faces empirical bounds on those parameters. QIQT-H, by comparison, has a partial mathematical theory (scaffolding + axiom + qualitative consequences) with explicit open theorems; in exchange, it preserves Schrödinger evolution exactly, adds no extra ontology, and is grounded in holography and quantum gravity. The mathematical work needed to complete it is well-defined, not vague.

### 11.3 The central thesis, in one paragraph

> The Bekenstein-Bousso holographic bound, taken literally as a Lorentz-invariant physical information limit on bounded regions of spacetime, motivates a stronger physical postulate: the **Branch-Summed Holographic Bound**, which constrains the sum of per-record costs across coexisting decoherent macroscopic record sectors of any bounded region by the holographic capacity $Q_R$. This bound is a **superselection rule on the physical state space** $\mathcal{H}_{\rm phys}$: universal wave functions whose induced regional states violate the bound are not physically realizable. Physical Hamiltonians are constrained to preserve $\mathcal{H}_{\rm phys}$ (analogous to gauge invariance in gauge theory). Within $\mathcal{H}_{\rm phys}$, Schrödinger / Heisenberg evolution is preserved exactly under physical Hamiltonians. The Born rule is preserved exactly. The macroscopic world — single-record per region per run — emerges as a *kinematic structural consequence* of the superselection rule, not as a dynamical selection event. No collapse, no hidden particle positions, no MWI branches, no modal value-rule are added; the framework is **ψ-monist** (wave function as only ontology) with the physical state space constrained by the Branch-Summed Holographic Bound. Born statistics across runs emerge from typicality of actual initial conditions of actual runs, propagated through the constrained dynamics. The CPW Type II crossed-product algebra framework provides the rigorous mathematical infrastructure; the Branch-Summed Holographic Bound is the framework's new physical principle on top — a strengthening of standard holography that is not derivable from existing QG results but is conjecturally connectable to deeper finite-information constraints on regional macroscopic record content.

### 11.4 Open problems

1. **Precise formulation of the branch-summed cost $I_\Sigma^\epsilon[\omega_R]$.** Define $\mathcal{C}(R)$ as the einselected/Darwinistic record subalgebra; define per-record cost $c_R(r)$ via Zurek-style physical entropy; specify the smooth active set $\mathcal{A}_\epsilon$ rigorously. Existing ingredients to draw on: decoherent histories (Gell-Mann-Hartle, Griffiths, Omnès), Quantum Darwinism / spectrum broadcast (Zurek, Brandão-Piani-Horodecki), Rényi-0 / Hill numbers.

2. **The Branch-Summed Bound as a new holographic principle.** Justify $I_\Sigma^\epsilon \le Q_R$ as a strengthening of standard Bekenstein-Bousso. Connect to deeper finite-information constraints in quantum gravity. This is genuinely new physics that does not follow from existing holographic results.

3. **Characterization of physical Hamiltonians.** Which Hermitian operators preserve $\mathcal{H}_{\rm phys}$? Develop the Dirac-style constrained-dynamics formalism analogous to gauge theory. Show that standard low-energy / lab-scale dynamics are approximately physical Hamiltonians (where the constraint is operationally vacuous).

4. **Rigorous Born typicality under constrained dynamics.** Specify the measure on actual initial conditions of actual runs; prove that the realized-record distribution across runs reproduces $|c_k|^2$ under the constrained dynamics.

5. **Quantitative form of the resolution floor $\epsilon(R)$** for the operational equivalence relation on regional algebra states.

6. **State-extension and reference-state issues** in the crossed-product algebra formulation.

7. **Cosmological / horizon applications** — extend to the de Sitter static patch and black-hole horizon regions.

8. **Phenomenological predictions.** Identify regimes where the branch-summed superselection rule produces observationally distinguishable signatures (e.g., maximum macroscopic-superposition scale, long-baseline coherence limits).

### 11.5 Credit division

The mathematical infrastructure — Type III$_1$ classification of local algebras, the crossed-product construction giving Type II algebras with renormalized entropy matching generalized entropy in semiclassical gravity — is due to Chandrasekaran, Penington, Witten, and collaborators (CPW 2022; Witten 2022; CLPW 2022; Jensen-Sorce-Speranza 2023; building on Connes-Takesaki and Haag-Kastler).

The original contributions of this paper are:

(a) The **literal physical-instantiation reading** of the Bekenstein-Bousso bound (foundational interpretation): the wave function as a physical state of spacetime has finite physical specification precision bounded by the holographic capacity of the region. This goes beyond what Witten's algebraic theorem directly establishes and is the central foundational postulate.

(b) The **(FQ) axiom** stated rigorously in the CPW Type II framework, with three parts: (i) regional content given by the algebra-state, (ii) the renormalized entropy bound postulated as axiom, (iii) the physical-instantiation precision-floor postulate.

(c) **Theorem 3 (finite physical resolution)** as the structural consequence of the literal reading: $\epsilon(R) > 0$, amplitudes within $\epsilon$ of 0 or 1 physically equivalent to exact 0 or 1.

(d) **The mechanism (§6, Theorem 4):** the structural combination of (FQ) precision floor + decoherence + microscopic IC produces single-record per-run wave functions without collapse.

(e) The **formal/per-run distinction** within the algebraic framework.

(f) The **schematic Born-typicality program** identified as the central quantitative open problem.

The credit division is sharp: CPW supplies the mathematical infrastructure (Type II regional algebras); we supply the literal physical-instantiation reading of the bound on top, and develop its structural consequences for the measurement problem.

### 11.6 Closing remarks

The framework retains standard quantum mechanics exactly at the level of the underlying field algebra. It adds one foundational axiom — (FQ) in its literal physical-instantiation reading — and one distinction (formal vs per-run wave function). From these, the structural consequences follow: finite physical resolution, decoherence-driven concentration, single-record per-run wave functions, the macroscopic world emerging without dynamical modification.

The framework is empirically conservative — Schrödinger and Born preserved exactly, no laboratory deviations predicted. It is metaphysically modest — no actuality primitive beyond the per-run wave function as a physical state of spacetime. It is mathematically grounded in the CPW Type II algebra framework. The principal open problems are quantitative — the explicit form of $\epsilon(R)$ and the rigorous Born typicality theorem.

The wave function is one. The realized world per run is one. The Bekenstein-Bousso holographic bound, taken literally as a Lorentz-invariant physical information limit on the wave function in spacetime, supplies the precision structure that selects the macroscopic world from the formal superposition. The Schrödinger equation is unchanged. The Born rule is unchanged. The macroscopic world emerges as a structural consequence — single outcomes per run, no collapse postulate, no hidden particles, no branching, no modal value-rule.

---

## Acknowledgements

The author thanks the participants in extended discussions that informed the framework developed here. The mathematical apparatus draws on the work of Chandrasekaran, Penington, Witten, and others in the Type II crossed-product algebra construction; we are indebted to that line of work for providing the rigorous home for the regional information bound.

---

## References

1. Ballentine, L. E. (1970). The statistical interpretation of quantum mechanics. *Rev. Mod. Phys.*, 42, 358.
2. Banks, T. (2025). *Finite Entropy Implies Finite Dimension in Quantum Gravity.* arXiv:2509.17856.
3. Bassi, A., Dorato, M., & Ulbricht, H. (2025). *The Quantum Measurement Problem: A Review of Recent Trends.* arXiv:2502.19278.
4. Bekenstein, J. D. (1981). Universal upper bound on the entropy-to-energy ratio for bounded systems. *Phys. Rev. D*, 23, 287.
5. Bohm, D. (1952). A suggested interpretation of the quantum theory in terms of "hidden" variables. *Phys. Rev.*, 85, 166.
6. Bousso, R. (2002). The holographic principle. *Rev. Mod. Phys.*, 74, 825. arXiv:hep-th/0203101.
7. Carroll, S. M., & Sebens, C. (2014). Many worlds, the Born rule, and self-locating uncertainty. In *Quantum Theory: A Two-Time Success Story*.
8. **Chandrasekaran, V., Longo, R., Penington, G., & Witten, E. (2022).** *An algebra of observables for de Sitter space.* JHEP 02 (2023) 082. arXiv:2206.10780.
9. **Chandrasekaran, V., Penington, G., & Witten, E. (2022).** *Large N algebras and generalized entropy.* JHEP 04 (2023) 009. arXiv:2209.10454.
10. Dieks, D. (1989). Quantum mechanics without the projection postulate. *Foundations of Physics*, 19, 1397.
11. Diósi, L. (1989). Models for universal reduction of macroscopic quantum fluctuations. *Phys. Rev. A*, 40, 1165.
12. Dürr, D., Goldstein, S., & Zanghì, N. (1992). Quantum equilibrium and the origin of absolute uncertainty. *J. Stat. Phys.*, 67, 843.
13. Engelhardt, N., & Wall, A. C. (2015). Quantum extremal surfaces. *JHEP* 01 (2015) 073.
14. Everett, H. (1957). "Relative state" formulation of quantum mechanics. *Rev. Mod. Phys.*, 29, 454.
15. Gell-Mann, M., & Hartle, J. B. (1993). Classical equations for quantum systems. *Phys. Rev. D*, 47, 3345.
16. Ghirardi, G. C., Rimini, A., & Weber, T. (1986). Unified dynamics for microscopic and macroscopic systems. *Phys. Rev. D*, 34, 470.
17. Griffiths, R. B. (2002). *Consistent Quantum Theory.* Cambridge University Press.
18. **Haag, R. (1992).** *Local Quantum Physics: Fields, Particles, Algebras.* Springer.
19. **Haag, R., & Kastler, D. (1964).** An algebraic approach to quantum field theory. *J. Math. Phys.*, 5, 848.
20. Healey, R. (2017). *The Quantum Revolution in Philosophy.* Oxford University Press.
21. 't Hooft, G. (1993). *Dimensional reduction in quantum gravity.* arXiv:gr-qc/9310026.
22. Jacobson, T. (1995). Thermodynamics of spacetime: The Einstein equation of state. *Phys. Rev. Lett.*, 75, 1260.
23. **Jensen, K., Sorce, J., & Speranza, A. J. (2023).** *Generalized entropy for general subregions in quantum gravity.* arXiv:2306.01837.
24. Joos, E., Zeh, H. D., Kiefer, C., Giulini, D., Kupsch, J., & Stamatescu, I.-O. (2003). *Decoherence and the Appearance of a Classical World in Quantum Theory.* Springer.
25. **Murray, F. J., & von Neumann, J. (1936).** On rings of operators. *Annals of Mathematics*, 37, 116.
26. Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information.* Cambridge.
27. Omnès, R. (1994). *The Interpretation of Quantum Mechanics.* Princeton University Press.
28. Palmer, T. N. (2025). Rare-event quantum mechanics from a discretized Hilbert space. *Proc. Natl. Acad. Sci. USA* (PNAS). arXiv:2510.02877. (See also Palmer, *The Invariant Set Postulate: A New Geometric Framework for the Foundations of Quantum Theory*, Proc. Roy. Soc. A, 2009; and subsequent IST development.)
29. Pearle, P. (1989). Combining stochastic dynamical state-vector reduction with spontaneous localization. *Phys. Rev. A*, 39, 2277.
30. Penrose, R. (1996). On gravity's role in quantum state reduction. *Gen. Rel. Grav.*, 28, 581.
31. Susskind, L. (1995). The world as a hologram. *J. Math. Phys.*, 36, 6377. arXiv:hep-th/9409089.
32. von Neumann, J. (1932). *Mathematische Grundlagen der Quantenmechanik.* Springer.
33. Wald, R. M. (1993). Black hole entropy is the Noether charge. *Phys. Rev. D*, 48, R3427.
34. Wall, A. C. (2012). A proof of the generalized second law for rapidly changing fields and arbitrary horizon slices. *Phys. Rev. D*, 85, 104049.
35. Wallace, D. (2012). *The Emergent Multiverse: Quantum Theory according to the Everett Interpretation.* Oxford University Press.
36. **Witten, E. (2022).** *Gravity and the crossed product.* JHEP 10 (2022) 008. arXiv:2112.12828.
37. Zurek, W. H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Rev. Mod. Phys.*, 75, 715.
38. Kapłański, P. (2026). *One Wave Function, One World: How the Holographic Information Bound Selects the Macroscopic World.* (Position paper, companion to this one.)

---

*End of manuscript.*
