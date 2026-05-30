---
title: "One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint"
author: "Paweł Kapłański"
date: 2026-05-25
keywords: [foundations of quantum mechanics, holographic principle, Bekenstein-Bousso bound, Type II von Neumann algebras, crossed product, generalized entropy, finite-precision wave function, measurement problem, typicality]
---

# One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint

## Abstract

We develop a foundational framework for quantum mechanics that combines the algebraic quantum field theory framework with the recent crossed-product / Type II construction of Chandrasekaran-Penington-Witten (2022) and Witten (2022). In ordinary QFT, the local algebras of bounded regions are of Type III$_1$, admitting no trace, no Hilbert-space factorization, and UV-divergent entanglement entropy. CPW and Witten show that gravitational dressing, implemented via the crossed product with the modular flow of a reference state, produces a Type II algebra $\hat{\mathcal{A}}(R)$ with a semifinite trace and a well-defined renormalized entropy whose differences match the generalized entropy expression $A/(4\ell_P^2) + S_{\rm matter}$. We use this algebraic infrastructure as the mathematical home for a foundational axiom (FQ) that we propose: *for every per-run physical wave function and every bounded region $R$, the state $\omega_\Psi$ induced on the gravitationally dressed regional algebra $\hat{\mathcal{A}}(R)$ has renormalized entropy bounded by $Q_R := A(\partial R)/(4\ell_P^2)$, and two abstract wave functions inducing the same state on $\hat{\mathcal{A}}(R)$ are physically identical in $R$.* The crossed-product construction is borrowed from CPW/Witten; the holographic bound $S_{\rm ren} \le Q_R$ is postulated as a finite-information axiom in this algebraic setting (not derived from CPW); the foundational application of this algebraic infrastructure to the measurement problem is our contribution. We distinguish the **formal wave function** of standard QM (an idealized ensemble description) from the **per-run wave function** (whose regional physical content is given by its values on the regional Type II algebras). Algebra-state equivalence provides a basis-independent notion of regional physical indistinguishability, two abstract Hilbert vectors are physically the same regional state iff they agree on every observable in $\hat{\mathcal{A}}(R)$. *Conjecturally*, under decoherence and microscopic initial conditions, per-run regional states concentrate dynamically on single-record states; *if this concentration conjecture is established*, the per-run wave function in any region containing apparatus and environment is, in the algebraic sense, equivalent to a single-record state. The Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly; (FQ) operates at the level of regional algebraic content. No collapse, no Bohmian particles, no MWI branches, no modal value-rule are added. Born statistics from typicality is stated schematically and identified as a key open problem. We state two propositions and two explicit conjectures, identify four explicit open problems, and frame the construction as a research program rather than a completed interpretation.

**Keywords:** foundations of quantum mechanics; Bekenstein-Bousso bound; holographic principle; Type II von Neumann algebras; crossed product; generalized entropy; finite-resolution wave function; ensemble interpretation; typicality.

**Formal verification.** The deductive core of this framework — Theorems 3, 6, 7, Lemma 1, Donald's identity, the no-signaling chain, the Bell/CHSH inequality (with rigorous singlet construction reaching $2\sqrt{2}$), seven structural audits (independence of (H2) from (H1) plus its sharp reference-weight reformulation; unitary decoherence does not imply concentration; the modular-local entropy bound is distinct from the CPW renormalized entropy; branch-summed cost is not a holographic consequence; literal-finite (FQ) admissibility gives trivial dynamics; compression-locality leakage and the local-projection constraint on (FQ); $\mu$-selection is load-bearing for Born statistics; support preservation $\neq$ Born equivariance), and three sub-theorems for the Canonical IC Measure Principle (typicality Mackey-Gleason; operational data insufficient; FQ-equivariance uniqueness) — is machine-verified in Lean 4 with Mathlib. A subsequent **A1+A2+A4+A6 strengthening pass** further: (i) proves the *finite marginal-locality step* of the Canonical IC Measure Principle as a theorem holding for **any** IC measure — with no equivariance assumption (`MarginalLocality.pushforward_marginal_local`) — so locality is no longer an *independent* Born-selection sub-axiom, though the reduction remains conditional on a named, explicit Hilbert→set-level locality bridge axiom (`set_level_locality_from_unitary_dilation`); (ii) proves the permutation-symmetry collapse component of Goldstein-Struyve sub-lemma 1c under its necessary hypothesis (`step1c_collapse_of_perm_symmetric`) together with the foundational matrix-conjugation identities $P_\sigma \cdot E_{ij} \cdot P_\sigma^* = E_{\sigma(i),\sigma(j)}$ and $D(z)\cdot E_{ij}\cdot D(z)^* = (z_i\,\overline{z_j})\,E_{ij}$ — while the *full* Goldstein-Struyve Schur classification remains a single named interface axiom; (iii) proves a single-trial Chebyshev frequency-concentration bound and the variance-addition (independence) lemma for Bernoulli trials (`BornConcentration.lean`), with the $N$-fold product-measure scaling still resting on the LLN interface axiom; and (iv) packages the three remaining Born sub-axioms with their independence countermodels in a unified minimality table (`BornMinimalityTable.lean`). Consolidation: the `FQEquivarianceUniqueness` module was rewritten to route through the concrete `GoldsteinStruyveFinDim` proof (eliminating 12 redundant abstract axioms), and the five Goldstein-Struyve Step-1 sub-axioms (three of which were *literally false as stated* and all of which were unused) were deleted — reducing the project axiom total from 57 to 40 and leaving `canonical_ic_measure_principle` dependent on exactly two project-specific axioms (Schur classification + tensor multiplicativity). The theorems introduced by the strengthening pass themselves depend only on the standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`; the *end-to-end* Born pipeline still rests on the named interface axioms (Mackey-Gleason / Radon-Nikodym, Schur classification, tensor multiplicativity, the LLN scaling, and the locality bridge), which the complete axiom audit in `lean/mathlib/QIQTH/AxiomAudit.lean` enumerates explicitly. See `lean/mathlib/QIQTH/` in the project repository.

---

## 1. Introduction

### 1.0 The hidden inconsistency in standard quantum foundations

Standard foundational discussion of quantum mechanics typically holds four claims simultaneously:

1. The wave function is physically real.
2. Bounded spacetime regions have finite physical information capacity (the holographic principle, supported by Bekenstein, 't Hooft, Susskind, Bousso, Banks, and the recent algebraic-QFT-plus-gravity work of Chandrasekaran-Penington-Witten and Witten).
3. The amplitudes of the wave function are exact real numbers (specifiable to arbitrary precision in principle).
4. Macroscopic superpositions, once formed, persist as physically real components forever.

These four claims cannot all be true. If the wave function is physically real (1) and amplitudes are exact real numbers (3), then specifying the wave function in any bounded region requires infinitely many bits of physical information, contradicting (2). If we add (4), macroscopic record alternatives persist as infinite-precision-amplitude branches that the region cannot physically contain. The standard interpretations of QM each resolve this tension by denying one of the four claims:

- **Many-Worlds** denies single-world realism (accepts (1)–(4) but at the cost of branching ontology with infinitely many physically real branches; pays in spacetime-information overflow that is rarely confronted).
- **Bohm** denies that the wave function is the complete physical content (denies a strong form of (1); adds primitive particle ontology).
- **GRW / CSL / DP / OR** deny that Schrödinger evolution is exact (modify dynamics so that (4) fails dynamically).
- **QBism / RQM** deny that the wave function is straightforwardly physically real (deny (1) in favor of epistemic or relational status).
- **Modal interpretations / decoherent histories** add a value-rule or history-selection structure to break (4) without modifying dynamics.

Each pays a distinct foundational price. Each accepts the tension as a *given* of the theory and pays the price to dissolve it.

This paper proposes a different resolution: **deny (3) at the level of physical instantiation while preserving the mathematical formalism**. The wave function in any bounded region has finite physical specification precision determined by the holographic information capacity of the region. Amplitudes physically within $\epsilon(R)$ of $0$ are physically equivalent to amplitude exactly $0$. The mathematical continuum of amplitudes remains the indispensable formal apparatus; the physical instantiation is finite-precision. With this denial of (3), all four claims can be reconciled: the wave function is physically real (1), bounded spacetime has finite capacity (2), amplitudes have finite physical specification precision (denial of (3)), and macroscopic superpositions resolve dynamically into single-record states (denial of (4) as structural consequence, not as added postulate).

This is arguably the *least radical* resolution. It does not multiply worlds, add particles, modify dynamics, or subjectivize the wave function. It accepts one physically natural constraint, bounded spacetime cannot physically contain infinite information, which is *independently motivated* by holography and quantum gravity. The measurement problem is resolved by recognizing that we were illegitimately combining (1)–(4) when only three of the four can hold at the level of physical instantiation.

### 1.1 The position

This paper develops a position in the foundations of quantum mechanics whose structure is:

1. The wave function of the universe evolves unitarily under the Schrödinger / Heisenberg evolution of the underlying field theory. Standard QM dynamics is preserved exactly.

2. The Bekenstein-Bousso holographic bound is treated as a foundational constraint on the **physical content of the wave function in any bounded region $R$**, not narrowly on the entanglement entropy of a reduced state, but on the total physical information needed to specify the state's content in $R$ as a state of spacetime.

3. The mathematical home of this constraint is the algebraic QFT framework with gravitational dressing. The regional algebra $\hat{\mathcal{A}}(R)$, obtained from the standard Type III$_1$ local algebra $\mathcal{A}(R)$ via the crossed product with the modular flow of a reference state, is of **Type II** and admits a semifinite trace whose finite values realize finite renormalized entropy for regional states. This is the framework of Chandrasekaran-Penington-Witten (2022), Witten (2022), and successors.

4. The (FQ) axiom: *the physical content of the per-run wave function in any bounded region $R$ is given by its expectation values on $\hat{\mathcal{A}}(R)$, and the renormalized entropy is bounded by $Q_R = A(\partial R)/(4\ell_P^2)$.*

5. The Type II structure of $\hat{\mathcal{A}}(R)$ implies a finite physical resolution for regional states: states agreeing on all operators in $\hat{\mathcal{A}}(R)$ are physically identical in $R$. This is the natural mathematical realization of "amplitudes physically within $\epsilon$ of $0$ are physically the same state as amplitude exactly $0$", the equivalence is between regional states, not between abstract Hilbert vectors.

6. The standard textbook formal wave function, a superposition $\sum_i c_i |s_i\rangle|A_i\rangle|E_i\rangle$, is an idealized statistical description of an ensemble of per-run wave functions across many runs. The per-run wave function evolves unitarily from specific microscopic initial conditions; decoherence drives amplitudes for distinct macroscopic record components to concentrate dynamically; the Type II resolution structure renders the post-concentration per-run wave function physically a single-record state.

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

What varies across runs is *the actual initial conditions themselves*: different particles emitted by the source, different microscopic states of the apparatus, different environmental configurations, different photon backgrounds, different thermal fluctuations. These differences are not hidden variables added to the framework, they are simply the actual physical differences between actual physical universes in different runs. Standard QM already accommodates this: the universal wave function is a function of all degrees of freedom in the universe, which trivially differ across runs.

What is sometimes loosely called the "formal wave function" in textbook accounts is the *subsystem wave function*, the wave function of a subsystem (typically the particle of interest) treated as if it were isolated from the apparatus and environment. This subsystem wave function is the textbook abstraction $\alpha|0\rangle + \beta|1\rangle$. It is not the per-run physical state of the universe; it is a subsystem description that abstracts away the apparatus + environment.

**Definition (Subsystem wave function).** *The subsystem wave function $|\psi\rangle_{\rm sub}$ for a subsystem $S$ of the universe is the wave function obtained by tracing the universal wave function over all degrees of freedom outside $S$ and (when $S$ is approximately uncorrelated with its complement) recovering an effectively pure state on $S$. For the prepared particle in the double-slit, $|\psi\rangle_{\rm sub} = \alpha|0\rangle + \beta|1\rangle$ is the standard textbook expression.*

**Definition (Per-run universal wave function).** *The per-run universal wave function $|\Psi\rangle_{\rm run}$ is the actual physical wave function of the universe in a specific individual run, evolving unitarily under the universal Hamiltonian from the specific actual initial conditions of the universe in that run. Its physical content in any bounded region $R$ is given by its values on the regional algebra $\hat{\mathcal{A}}(R)$ (defined in §3), constrained by (FQ).*

The relationship across runs: there is *one* per-run universal wave function per run. Different runs have *different actual* per-run universal wave functions because the actual initial conditions of the universe differ. Born statistics across runs (§7.4) arise from the distribution of these actual initial conditions, not from any "alternative" wave functions for the same preparation. The "ensemble" is over actual different physical universes, not over hypothetical alternatives.

**The framework adds no ontology beyond the universal wave function.** It is ψ-monist. The framework's two contributions are:
1. The recognition that the textbook subsystem wave function $|\psi\rangle_{\rm sub}$ is *not* the complete physical state of the universe in a run, the per-run universal wave function $|\Psi\rangle_{\rm run}$ is. This is standard QM at the universal level.
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
- No tensor factorization $\mathcal{H} = \mathcal{H}_R \otimes \mathcal{H}_{\bar R}$, the algebra of $R$ and its complement do not split the Hilbert space.
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

### 3.3 The regional algebra and the holographic bound, what CPW gives and what we postulate

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

This sharp separation, CPW gives the algebraic language, we postulate the bound, is intentional. The Type II framework is borrowed; the foundational application to QM measurement is our contribution.

### 3.4 State extension and reference-state dependence

Two technical issues require comment.

**State extension.** The crossed-product algebra $\hat{\mathcal{A}}(R) = \mathcal{A}(R) \rtimes_{\sigma^\Omega} \mathbb{R}$ is naturally represented on $\mathcal{H} \otimes L^2(\mathbb{R})$, not on the original QFT Hilbert space $\mathcal{H}$. A per-run wave function $|\Psi\rangle \in \mathcal{H}$ does not automatically define expectation values on operators in $\hat{\mathcal{A}}(R)$ that act on the $L^2(\mathbb{R})$ factor (the modular-flow / "clock" degrees of freedom). Following CPW, we assume an explicit extension prescription: per-run universal wave functions are taken to live in the enlarged Hilbert space, $|\Psi\rangle_{\rm run} \in \mathcal{H} \otimes L^2(\mathbb{R})$, with the $L^2(\mathbb{R})$ factor encoding the dressing degrees of freedom required to make the gravitational constraint well-defined. The state $\omega_\Psi$ on $\hat{\mathcal{A}}(R)$ is then the standard vector state of $|\Psi\rangle_{\rm run}$ restricted to $\hat{\mathcal{A}}(R)$.

**Reference-state dependence.** The crossed product uses the modular flow $\sigma^\Omega$ of a reference state $\Omega$. Different reference states give different crossed-product algebras; however, the continuous-core construction is known to be state-independent up to isomorphism (Connes-Takesaki), and physical predictions (entropy differences, generalized-entropy comparisons between states) are reference-state-independent in the semiclassical regime where CPW operates. We adopt the same convention as CPW: a natural reference state is chosen (e.g., the vacuum or a global Bunch-Davies-like state), and physical content is read off via entropy differences and algebra-state equivalences that are reference-independent in the relevant sense. A fully reference-state-independent formulation is a technical refinement we defer.

---

## 4. The (FQ) Axiom in the Type II Framework

### 4.1 Statement

**Axiom (FQ), Literal physical-instantiation reading.** *For every per-run wave function $|\Psi\rangle_{\rm run}$ of the universe (regarded as an element of the enlarged Hilbert space $\mathcal{H} \otimes L^2(\mathbb{R})$, cf. §3.4) and every bounded region $R$ of space:*

**Local von Neumann net and normality.** Work in the GNS representation $(\mathcal{H}_\sigma, \pi_\sigma, \Omega_\sigma)$ of the reference state $\sigma$ (§7.6). For each bounded region $R$, let

$$
\mathcal{M}(R) := \pi_\sigma(\mathcal{A}_{\rm loc}(R))''
$$

be the local von Neumann algebra. The hatted algebra $\hat{\mathcal{A}}(R)$ denotes the corresponding semifinite Type II crossed-product / core algebra, represented in the standard crossed-product representation induced by $\mathcal{M}(R)$ and $\sigma_R$. (If no crossed-product refinement is being used, set $\hat{\mathcal{A}}(R) = \mathcal{M}(R)$.) The net is assumed isotonic and local: $R' \subset R \Rightarrow \hat{\mathcal{A}}(R') \subset \hat{\mathcal{A}}(R)$, and $R_1 \perp R_2 \Rightarrow [\hat{\mathcal{A}}(R_1), \hat{\mathcal{A}}(R_2)] = 0$.

*(i) **Local normality.** The physical content of $|\Psi\rangle_{\rm run}$ in $R$ is given by the regional restriction $\omega_\Psi|_R$. This restriction must be a normal state on $\hat{\mathcal{A}}(R)$, equivalently, a positive unital $\sigma$-weakly continuous linear functional, $\omega_\Psi|_R \in \hat{\mathcal{A}}(R)_*^+$ with $\|\omega_\Psi|_R\| = 1$.*

*(ii) **Finite holographic modular budget.** Define the regional information functional as the Araki relative entropy with respect to the canonical sector reference state $\sigma_R$ (§7.6):*
$$
\chi_R(\omega_\Psi|_R) \;:=\; S^{\hat{\mathcal{A}}(R)}_{\rm Araki}(\omega_\Psi|_R \,\|\, \sigma_R).
$$
*The (FQ) postulate (ii) is the modular-local bound:*
$$
\chi_R(\omega_\Psi|_R) \;\le\; Q_R \;\equiv\; C(R) \;:=\; \frac{A(\partial R)}{4\ell_P^2}.
$$

*(The symbols $Q_R$ and $C(R)$ are used interchangeably throughout for the regional holographic capacity. We retain both because $Q_R$ emphasizes "information capacity" while $C(R)$ emphasizes "modular-cost ceiling"; the underlying quantity is identical.)*

*Notational caveat: we will also write this functional as $S_{\rm ren}(\omega_\Psi)$ for emphasis on "modular-local information content", and (FQ)(ii) then reads $S_{\rm ren}(\omega_\Psi) \le Q_R$. This $S_{\rm ren}$ is **not** the same functional as the CPW/Witten "renormalized entropy" of the state on the Type II crossed-product algebra — they are distinct functionals related by the modular identity*
$$
\chi_R(\omega) \;=\; \Delta_\omega \langle K_R^\sigma \rangle - \Delta_\omega S_R^{\rm CPW}
$$
*where $K_R^\sigma$ is the modular Hamiltonian of $\sigma_R$ and $S_R^{\rm CPW}$ is the CPW renormalized entropy. **The (FQ) bound is on the relative-entropy functional $\chi_R$, not on the CPW renormalized entropy.** The two functionals can disagree substantially (a state may satisfy one bound and violate the other; see the formal verification module `lean/mathlib/QIQTH/EntropyBridge.lean` for a classical counterexample making this concrete).*

*(iii) The wave function $|\Psi\rangle_{\rm run}$ is regarded as a physical object instantiated in spacetime. The total physical information content needed to instantiate $|\Psi\rangle_{\rm run}$ in $R$, including amplitudes, phase coherence, superposition structure, is bounded by $Q_R$. Two abstract wave functions whose physical instantiations in $R$ are indistinguishable at the precision afforded by this bound are physically identical in $R$.*

Part (i) defines the mathematical content of "wave function in $R$": it is the state on the Type II regional algebra introduced by CPW/Witten. Part (ii) is the holographic information bound on regional renormalized entropy, postulated (not derived from CPW). Part (iii) is the **literal physical-instantiation reading** of the bound: the wave function, regarded as a physical state of spacetime in $R$, has finite physical specification precision. Below this precision, distinct mathematical wave functions correspond to the same physical state.

The literal reading is a stronger statement than the narrow entanglement-entropy reading and a stronger statement than what Witten's algebraic theorem directly establishes. It is our foundational postulate. The relationship to Witten's framework is made explicit in §4.3.

**Important: (FQ) is a modular-local kinematic constraint, not a single global budget.** Each bounded region $R$ has its own capacity $Q_R$ set by *its* boundary area; the bound is imposed independently for each $R$ as a constraint on the algebra-state pair $(\hat{\mathcal{A}}(R), \omega_\Psi|_R)$. There is no single shared information budget over all spacetime, and no joint-region cutoff is applied to the spacelike-combined algebra $\hat{\mathcal{A}}(D_A) \vee \hat{\mathcal{A}}(D_B)$.

**Spacelike combination by meet of local predicates.** For spacelike-separated regions $D_A, D_B$:

$$
\mathrm{Adm}(D_A \cup D_B) \;=\; \mathrm{Adm}(D_A) \wedge \mathrm{Adm}(D_B).
$$

That is: a state is admissible on the spacelike pair iff its restriction to *each* local algebra is admissible. The joint algebra $\hat{\mathcal{A}}(D_A) \vee \hat{\mathcal{A}}(D_B)$ may remain vacuum-entangled and Type III non-factorizing, the admissibility predicate imposes nothing on the joint structure beyond the two local restrictions. The framework's admissibility is therefore a **local subfunctor** of the AQFT state functor.

This modular-local formulation makes no-signaling a *theorem*, not an extra axiom: it follows automatically from AQFT microcausality (§7.7 below). The naive alternative, imposing the bound on the joint spacelike algebra as well, would produce operational signaling, because the vacuum is not a product state across spacelike-separated boundaries.

### 4.2 Motivation: the literal reading of the bound

We adopt (FQ) as a foundational axiom. The motivation rests on:

- **Bekenstein's original information-theoretic argument.** The original bound was derived as a bound on the information needed to specify any physical system, not specifically as an entanglement-entropy inequality on a reduced state.
- **'t Hooft's dimensional reduction.** All degrees of freedom in a region are encoded in boundary data; this is a statement about *total* physical content.
- **Susskind's holographic principle.** Physics in a region is holographically described by boundary data of bounded information content. The boundary holds at most $A/(4\ell_P^2)$ bits, bounds *all* the information to specify the physics, not just one measure of it.
- **Banks 2025.** Finite entropy in quantum gravity implies finite Hilbert-space dimension for bounded subsystems.
- **CPW 2022 and successors.** The Type II crossed-product structure provides the rigorous algebraic realization compatible with the literal reading.

The literal reading takes the bound seriously as a physical limit on the wave function as a physical state of spacetime, not as an abstract Hilbert vector but as a physical object instantiated in a region with finite information capacity. As an abstract Hilbert vector, the wave function can have continuous amplitudes specified to arbitrary precision. As a physical state of spacetime, it must be instantiated using the region's finite physical resources, and the bound limits these resources.

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
3. *(FQ) part (iii)*: **The literal physical-instantiation reading**, the wave function is a physical state of spacetime with finite information capacity per region; below the resulting physical precision, distinct mathematical wave functions are the same physical state.

Item 3 is the strongest and most distinctive postulate. Witten's mathematical theorem says nothing about physical instantiation precision; his Type II algebra has a continuous normal-state space, and algebraic equivalence is an *exact* equivalence relation. Our postulate says additional structure exists at the physical level, the bound limits not just the algebraic entropy but the physical-instantiation precision of regional wave-function content. The Type II algebra is the mathematical scaffold; the physical-precision floor is a foundational interpretation laid on top.

We are not contradicting Witten. We are extending the foundational reading of the bound beyond what Witten directly proves. Witten's theorem is about the rigorous mathematical home for finite renormalized entropy on bulk regions; our postulate is about how this entropy bound translates into physical precision on the wave function as a physical state of spacetime.

The two readings can be compared:

| | Narrow algebraic reading (Witten) | Literal physical-instantiation reading (ours) |
|---|---|---|
| What the bound limits | Renormalized entropy on Type II algebra | Total physical info needed to instantiate WF in $R$ |
| Equivalence relation on states | Exact equality on algebra | Algebraic + physical-precision floor |
| Near-zero amplitudes | Distinct from zero (continuous state space) | Physically equivalent to zero (below precision) |
| Single-record per run | Requires separate Concentration Conjecture | Structural consequence of precision + decoherence |
| Status w.r.t. Witten's theorem | Direct mathematical reading | Stronger interpretive postulate; compatible but not derived |

Whether the literal reading is the correct foundational reading of the bound is a substantive philosophical / physical question, not a mathematical theorem. Our position is that the literal reading is the natural reading of "Bekenstein-Bousso as a Lorentz-invariant information limit on bounded regions of spacetime", what the bound says, taken at face value as a physical limit rather than as a narrow technical inequality on a derived quantity.

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

The Mandelbrot set has unbounded fractal detail as a mathematical object. Any physical rendering, pixels, etched plates, printed images, has finite resolution determined by the physical substrate. Below pixel scale, mathematically distinct points are the *same physical pixel*. The pixel does not partially exist or fractionally exist; it is one specific color.

The wave function, on the present view, is similar:
- As an abstract Hilbert-space vector it can have arbitrary continuous amplitudes.
- As a *physical* state of spacetime, it is rendered with finite resolution determined by the holographic bound on the region.
- Below resolution, fractional amplitudes are not physically realized; they are physically equivalent to exact $0$ or exact $1$.

This is the *physical-instantiation reading* of the wave function, distinct from the abstract Hilbert-space reading. The latter treats amplitudes as freely specifiable continuous parameters; the former takes seriously the requirement that those amplitudes be physically encoded in the regional substrate, which has finite information capacity.

### 5.3 Defense against the qubit objection

A standard objection to a finite-precision-on-amplitudes reading of the holographic bound runs as follows: "Consider a qubit. It has Hilbert dimension 2 and entropy bound $\log 2$. But its pure states form a continuum, the Bloch sphere, with arbitrary $\alpha, \beta$. So finite entropy does not imply finite amplitude precision."

This objection treats the qubit as an abstract Hilbert-space entity. The framework's response distinguishes the mathematical idealization from the physical instantiation. **The Bloch sphere stands in the same relation to a physical qubit as Euclidean geometry stands to a physical measuring rod**: an indispensable, extraordinarily accurate mathematical idealization, but not a literal description of what the physical object instantiates with infinite precision. No physical measuring rod realizes exact Euclidean points; no physical qubit realizes exact Bloch-sphere amplitudes. The continuum is the mathematical scaffolding; the physical substrate has finite information capacity.

A physical qubit is always implemented in a substrate, an ion, an atom, a photon's polarization, a superconducting circuit, a nuclear spin, a quantum dot, occupying some bounded spatial region. The amplitudes $\alpha, \beta$ must be physically encoded in that substrate's quantum state. The holographic bound on the region containing the qubit gives $Q_R$ bits of physical information capacity. The amplitudes can be specified to a precision corresponding to this capacity.

For a qubit in a 1m region with $Q_R \sim 10^{70}$ bits, amplitude precision is astronomically fine, the Bloch sphere is effectively continuous for all practical purposes. **This is precisely why standard QM works at lab scales: the framework reproduces ordinary continuous-qubit phenomenology because the physical precision floor is far below experimental resolution.** For a qubit in a Planck-scale region, $Q_R$ is order unity and the Bloch sphere is genuinely discretized.

Quantum error correction does not evade this. A logical qubit encoded in many physical qubits has a larger substrate and therefore larger information capacity, but still finite. The continuum is never physically recovered; it is only postponed into a bigger idealization.

For *macroscopic* systems, where each macroscopic record component, considered as the full quantum state of the apparatus+environment region, uses a substantial fraction of the regional capacity, and superpositions of multiple records require encoding all of them simultaneously, the operationally relevant precision for amplitudes between records is finite. This is the regime where the precision floor has structural foundational consequences (Theorem 4).

The qubit objection therefore identifies the *limit where the framework reproduces standard QM* (laboratory qubit regime); it does not show that the framework is incoherent in the regime where it bites (macroscopic record superpositions). The Bloch sphere is recovered to astronomical precision in lab regimes; finite precision matters foundationally only at the macroscopic-record scale, where the measurement problem actually lives.

### 5.4 Relationship to the algebraic indistinguishability

The Witten/CPW algebraic framework gives a basis-independent *exact* equivalence relation on regional states: $\omega_\Psi = \omega_\Phi$ as states on $\hat{\mathcal{A}}(R)$. Our physical-resolution-floor postulate gives a *coarser* equivalence: $\omega_\Psi \approx_\epsilon \omega_\Phi$, where the approximation is at the physical-precision floor $\epsilon$. Physical equivalence is coarser than algebraic equivalence: two algebraically distinct states can be physically equivalent if they differ by less than $\epsilon$.

Algebraic equivalence (Witten) is what's *mathematically* established by the Type II algebra structure. Physical-resolution equivalence (our postulate) is the foundational reading we add on top. Both relations are basis-independent and intrinsic to the regional geometry; the latter is the relevant one for the measurement problem.

The macroscopic record structure enters naturally: macroscopically distinct records $\{|s_i\rangle|A_i\rangle|E_i\rangle\}$ are those distinguished by the environmental algebra $\hat{\mathcal{A}}(E)$ (the algebraic formulation of einselection). Physical equivalence on the apparatus + environment region is "indistinguishability at the (FQ) resolution floor on the apparatus + environment algebras."

---

## 6. The Mechanism: Decoherence, Concentration, and Algebraic Resolution

### 6.1 Decoherence in algebraic terms

In the algebraic framework, decoherence corresponds to the dynamical suppression of off-diagonal expectation values $\omega_\Psi(O_{ij})$ for operators $O_{ij}$ connecting macroscopically distinct record components. Standard decoherence theory (Zurek, Joos, Hartle) gives the dynamical mechanism for the suppression. The algebraic formulation makes this precise: after decoherence, $\omega_\Psi$ on the apparatus + environment algebra approaches a classical-record state, a convex combination $\sum_i p_i \omega_i$ of mutually decohered records.

This is the standard decoherence result, restated algebraically. It does not, by itself, select a single outcome.

### 6.2 What decoherence actually does: exponentially-classical mixtures

A common but misleading reading treats the post-measurement state as a "naive superposition" of macroscopic records, say, "$70\%$ amplitude at spot A, $30\%$ at spot B sitting there as accessible amplitudes." This picture treats the system as if its amplitudes could be directly read off; the puzzle then becomes "how do $70/30$ amplitudes become $100/0$ in a specific run?"

This picture is wrong. We never have direct access to "the amplitudes of the wave function." We have access only to *macroscopic records* on detectors, screens, and observers, which are themselves complex quantum systems with $\sim 10^{20}$–$10^{25}$ degrees of freedom, entangled with the system being measured.

What decoherence actually does is the following.

After interaction with the apparatus and environment, the joint state of system + apparatus + environment is
$$|\Psi\rangle = \sum_k c_k \,|s_k\rangle_S \otimes |A_k\rangle_A \otimes |E_k\rangle_E,$$
where $\{|s_k\rangle\}$ are macroscopically distinguishable system states, $\{|A_k\rangle\}$ are macroscopically distinct apparatus configurations correlated with each $|s_k\rangle$, and $\{|E_k\rangle\}$ are environmental record states.

Decoherence theory (Zurek 2003; Joos et al. 2003) establishes that for any pair of macroscopically distinct records:
$$\langle E_j | E_k \rangle \sim \exp(-\Gamma t) \to \exp(-N)$$
where $\Gamma$ is the decoherence rate and $N \sim 10^{20}$ for typical macroscopic systems on any reasonable timescale. The cross-overlap is **exponentially small**, by factors like $e^{-10^{20}}$.

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

The classical mixture $\sum_k |c_k|^2 \omega_k^R$ is *not* a single record. It is a weighted list of records carrying the Born weights $|c_k|^2$ — weights that the framework reads as the *empirical frequency pattern across runs* (§7.4), not as a fundamental per-run probability (QIQT-H has no fundamental probabilities).

In any specific run, which record obtains? The framework's answer:

**Per-run, the universe is in one specific branch of the decohered-and-(FQ)-cleaned classical mixture. Which branch is selected by the per-run microscopic initial conditions of the apparatus + environment, propagated through the unitary dynamics from these specific microstates.**

This is analogous to how, in classical statistical mechanics, a system at temperature $T$ has specific molecular configurations in any individual realization. The thermodynamic ensemble $e^{-\beta H}$ is a probability distribution over microstates; any specific realization sits at one microstate. We do not say "the system is in a quantum superposition of all microstates with thermal weights"; we say "the system is in some specific microstate, the distribution over runs follows the thermal ensemble."

In the quantum case, the same structure obtains with one additional ingredient: the per-run microstate must be consistent with the (FQ)-decohered structure on the regional algebra. After decoherence + (FQ), the regional algebra-state is strictly classical (no remaining off-diagonal coherence); the per-run universe occupies one branch of this strictly-classical mixture; which branch is determined by the specific microscopic initial conditions.

**This is not a magic transition from "70% A + 30% B as a superposition" to "100% A as a single outcome".** It is the recognition that:
1. We never have direct access to a "70%/30% superposition" of macroscopic alternatives, we have access only to macroscopic records, which after decoherence are exponentially exclusive
2. (FQ) makes "exponentially exclusive" into "strictly exclusive"
3. The per-run universe is in one of the now-strictly-exclusive branches
4. Which branch is selected by per-run microscopic IC

The per-run "microscopic initial conditions" are *not* hidden variables in any ontological sense. They are simply *the actual physical state of the apparatus + environment in the specific run*. Different runs of an experiment correspond to different actual physical universes, different particles emitted, different microscopic apparatus states, different environmental configurations. These differences are not added structure; they are the standard fact that *actual physical universes differ across actual physical experiments*. Standard QM, at the universal-wave-function level, already accommodates this trivially: the universal wave function is a function of all degrees of freedom in the universe; those degrees of freedom take different actual values in different runs.

The framework is **ψ-monist**: there is no ontological structure beyond the universal wave function. What the framework does, and what standard textbook QM elides, is to take seriously that:
1. The universal wave function (not the textbook subsystem wave function) is the actual physical state in each run
2. Different runs are different actual physical universes, not different versions of "the same" universe
3. The Born statistics across runs come from the distribution of *actual* initial conditions across *actual* runs, not from any "alternative" wave functions for a single preparation

In Bohmian language: there are no Bohmian particles, no extra ontological layer; the universal wave function is the only thing, and different runs have different actual universal wave functions because the actual physical universe differs in each run. This is wavefunction-monist standard QM with (FQ) added as a finite-information constraint.

### 6.5 Theorem: Single-record per-run wave functions

**Theorem 1 (Single-record per-run wave functions).** *Under (FQ) and standard decoherence dynamics of unitary QFT, the per-run physical state on the regional algebra $\hat{\mathcal{A}}(R)$ for $R$ containing apparatus + environment after measurement is, with regional physical content given by the algebraic-state-modulo-(FQ)-precision equivalence class, a single-record state $\omega_{k_{\rm run}}^R$.*

*Proof.* By standard decoherence theory, after measurement interaction, the joint state's induced regional state on $\hat{\mathcal{A}}(R)$ has off-diagonal coherence terms suppressed exponentially: $\omega_\Psi^R = \sum_k |c_k|^2 \omega_k^R + O(\exp(-N))$. By Lemma 1 (§5.1), components below the (FQ) precision floor $\epsilon(R)$ are physically equivalent to zero. Since $e^{-N} \ll \epsilon(R)$ for any reasonable macroscopic decoherence regime, the off-diagonal coherence terms are physically exactly zero. The resulting regional state is the strict classical mixture $\sum_k |c_k|^2 \omega_k^R$, with macroscopic records physically exclusive (no remaining coherence between distinct $\omega_k^R$).

In any specific run, the per-run universe occupies one specific branch of this strictly-exclusive classical mixture. Which branch is the realized one is determined by the per-run microscopic initial conditions of the apparatus + environment, propagated through unitary evolution. The per-run physical regional state on $\hat{\mathcal{A}}(R)$ is therefore $\omega_{k_{\rm run}}^R$ for some specific $k_{\rm run}$, a single-record state. $\blacksquare$

**Remark on the role of each ingredient:**
- **Decoherence** drives the regional algebra-state to be exponentially close to a classical mixture (standard QM, no postulate)
- **(FQ)** converts "exponentially close" to "physically exact" (foundational postulate; renders off-diagonal coherence physically zero)
- **The per-run wave function itself** is one specific branch of the strictly-exclusive classical mixture, this is ψ-monism: no additional ontology, the wave function in each actual run is simply different from the textbook formal ensemble descriptor
- **Born statistics** across runs follow from the typicality of microscopic IC (open: Concentration / Born-typicality program)

**What standard linear QM does not provide:** the strict classical exclusivity (off-diagonal coherence is exponentially small, not zero) and the per-run branch selection. (FQ) provides the first; per-run microscopic IC provide the second. Neither requires modifying the Schrödinger evolution.

### 6.6 What is preserved, and what algebraic restriction is (and is not)

**Preserved exactly on the physical state space $\mathcal{H}_{\rm phys}$:** the unitary Schrödinger / Heisenberg evolution under *physical Hamiltonians* (those that preserve $\mathcal{H}_{\rm phys}$; cf. §7.6). Within $\mathcal{H}_{\rm phys}$, no modification of dynamics, no stochastic term, no projection operator. The physical Hamiltonian generates standard linear unitary evolution on the constrained physical state space.

**Constrained at the kinematic level:** the physical state space itself is restricted to $\mathcal{H}_{\rm phys}$ (those universal wave functions satisfying the Branch-Summed Holographic Bound $I_\Sigma \le Q_R$ for every bounded region). States outside $\mathcal{H}_{\rm phys}$ are mathematically writeable in the unrestricted Hilbert-space formalism but are not physically realizable. Physical Hamiltonians are restricted to those preserving $\mathcal{H}_{\rm phys}$. This is analogous to gauge theory: physical state space is a constrained submanifold; physical Hamiltonians preserve gauge invariance; unrestricted Hilbert-space Hamiltonians are mathematically writeable but unphysical.

**The relationship between global evolution and regional physical content.** On $\mathcal{H}_{\rm phys}$ the universal state evolves unitarily under a physical Hamiltonian: $|\Psi_t\rangle = U(t)|\Psi_0\rangle$. The induced regional algebra-state evolves linearly: $\omega_t(O) = \omega_0(U(t)^\dagger O U(t))$ for $O \in \hat{\mathcal{A}}(R)$. The map $|\Psi\rangle \mapsto \omega_\Psi$ from Hilbert vectors to regional algebra-states is a structural restriction (analogous to forming a reduced state). It is mathematically linear on density operators and quadratic in vectors.

What is *not* a standard mathematical operation: the physical-precision quotient. Under the literal physical-instantiation reading, the physical wave function in $R$ is not the algebra-state $\omega_\Psi$ but the *equivalence class of $\omega_\Psi$ under physical resolution-$\epsilon$ equivalence*. This quotient is coarser than the algebra-state equivalence; it is the operative equivalence relation on physical regional states.

The physical-precision quotient is what does the foundational work. It is what renders exponentially-small off-diagonal coherence between macroscopic records physically equal to exact zero, converting the merely-approximate classical mixture that standard decoherence delivers into a strictly-exclusive classical mixture. Per-run branch selection (which one of the now-strictly-exclusive branches the universe occupies in a specific run) is supplied by the per-run microscopic IC, not by the precision quotient itself. The quotient is not present in standard QM (which has continuous Hilbert state space); it is not present in Witten's algebraic framework (which has continuous normal-state space on the Type II algebra); it is present in our literal reading of (FQ).

### 6.7 Physics is the macroscopic observable content; branches are not part of it

A potential objection to the framework: even after decoherence + (FQ) render off-diagonal coherence physically zero, the resulting strict classical mixture $\sum_k p_k \omega_k^R$ on $\hat{\mathcal{A}}(R)$ is still a mixture over multiple macroscopic records. To get a single-record per run, one might think the framework needs an additional "selection rule", leading either to MWI (all branches real) or to a hidden-variable mechanism for which branch is actual.

The framework's response cuts deeper than introducing a selection mechanism. It refuses the question of "which Everett branch is realized" by reframing what counts as physical content:

> **Physics is what is encoded in the macroscopic observable algebra. The full universal wave function (with all its mathematical branch structure) is a calculational/formal apparatus; the physical content of any region is the state on the macroscopic record subalgebra $\mathcal{C}(R) \subset \hat{\mathcal{A}}(R)$. We do not have direct physical access to "the universal wave function's branch structure", only to the macroscopic record content. (FQ) constrains the macroscopic record content. At that level, multi-record states are forbidden (conjecturally, see §7.6). Single-record per run is therefore not a "selection" from multiple physically real branches, it is the structural consequence of (FQ) on the macroscopic observable algebra. The microscopic branch question is not part of the physics because it does not appear in the macroscopic observable content.**

This is the operational-realist + algebraic + holographic move. Physics is the content of macroscopic observable algebras (algebraic QFT lineage). These algebras are constrained by (FQ). The "Everett branches" of the universal wave function are mathematical artifacts of the underlying Hilbert-space formalism; they don't enter the macroscopic observable content; they're not part of physics.

This reframing is what motivates the Macroscopic Definiteness Conjecture, the framework's central new mathematical claim, formalized in §7.6.

### 6.8 The macroscopic record subalgebra and the spectrum of records

**Definition (Macroscopic record subalgebra).** *Let $\hat{\mathcal{A}}(R)$ be the regional Type II crossed-product algebra for region $R$ containing apparatus + environment. The **macroscopic record subalgebra** $\mathcal{C}(R) \subset \hat{\mathcal{A}}(R)$ is the maximal commutative subalgebra of observables that are decoherence-stable under the dynamics of the apparatus + environment, that is, the subalgebra selected by einselection (Zurek) and that supports definite macroscopic records over the relevant timescales.*

For the double-slit screen, $\mathcal{C}(R)$ is generated by the position-localized record projectors $\{P_k\}$ corresponding to spots at different positions. For a generic measurement, $\mathcal{C}(R)$ is the algebra of pointer-basis observables. The subalgebra is approximately commutative (off-diagonal terms between distinct records are exponentially suppressed by decoherence and physically zero under (FQ); cf. §6.2–6.3).

**Spectrum of records.** $\mathrm{Spec}(\mathcal{C}(R))$ is the set of macroscopic record configurations, for the screen, the set of distinct spot positions; for a Stern-Gerlach detector, the set of distinct deflection records; etc. By the Gelfand representation theorem, $\mathcal{C}(R) \cong C(\mathrm{Spec}(\mathcal{C}(R)))$ (continuous functions on the spectrum), and states on $\mathcal{C}(R)$ are probability measures on $\mathrm{Spec}(\mathcal{C}(R))$.

For a finite or countable spectrum (which is the relevant case for macroscopic records on a finite-resolution screen), states on $\mathcal{C}(R)$ are probability distributions $\{p_k\}$ over records.

**Thickened-state construction.** For each record $r \in \mathrm{Spec}(\mathcal{C}(R))$, the **thickened state** $\tilde{\delta}_r$ on the full algebra $\hat{\mathcal{A}}(R)$ is the state corresponding to "record $r$ realized", including all the microscopic structure of the apparatus + environment configuration that produces macroscopic record $r$. This thickened state uses approximately $Q_R$ bits of physical information (it is a specific microscopic configuration of the full apparatus + environment region; macroscopic records consume approximately the full regional holographic capacity).

For a multi-record state, a probability measure $\mu = \sum_k p_k \delta_{r_k}$ on $\mathrm{Spec}(\mathcal{C}(R))$ with multiple records, the *thickened state* is $\tilde{\mu} = \sum_k p_k \tilde{\delta}_{r_k}$ on $\hat{\mathcal{A}}(R)$. This thickened state must encode each constituent macroscopic record's full microscopic configuration plus the probability weights.

**Conjecture (Information cost of multi-record thickened states):** *The renormalized entropy $S_{\rm ren}(\tilde{\mu})$ of a thickened multi-record state $\tilde{\mu} = \sum_k p_k \tilde{\delta}_{r_k}$ scales as $\sum_k p_k S_{\rm ren}(\tilde{\delta}_{r_k}) + H(\{p_k\})$ where $H$ is the Shannon entropy, when the constituent records $\{r_k\}$ are physically distinct macroscopic configurations with mutually exclusive microscopic specifications. When each $S_{\rm ren}(\tilde{\delta}_{r_k}) \approx Q_R$ (records saturate the regional capacity), the thickened multi-record state has $S_{\rm ren}(\tilde{\mu}) \approx Q_R + H(\{p_k\})$, which exceeds $Q_R$ when $H(\{p_k\}) > 0$, i.e., for genuinely multi-record states.*

This is the cost-counting argument the framework rests on for the Macroscopic Definiteness Theorem of §7.6.

### 6.9 The Bell escape: holographic nonseparability vs classical separability

A natural objection: any deterministic single-world theory reproducing standard quantum predictions must confront Bell's theorem. The framework is **ψ-monist** (the wave function is the only ontology; no extra hidden particles or fields are added) but the per-run wave function in any specific run differs from the textbook formal ensemble descriptor; it reproduces standard quantum predictions; it has single outcomes per run. Which Bell assumption does it reject?

**The framework's answer: measurement independence, grounded in holographic nonseparability.**

Bell's theorem assumes the hidden variables $\lambda$ characterizing the source are statistically independent of the later measurement settings $a, b$:
$$\rho(\lambda \mid a, b) = \rho(\lambda).$$

This is the "measurement independence" assumption (also called "statistical independence" or the "free variables" assumption). Rejecting it is often dismissed as "superdeterminism," but the framework offers a non-conspiratorial version.

**The framework's argument.** A Bell experiment is not three independently specifiable pieces, source variables, Alice's setting, Bob's setting, that could in principle be combined in arbitrary configurations. It is *one finite-information physical process embedded in a common spacetime history*. The microscopic states of the source, the detector substrates, the random-number generators, the experimenters, the electromagnetic environment, the gravitational background, and the surrounding spacetime region are all parts of one physical state.

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

**Position with respect to Kochen-Specker.** If per-run microscopic structure determines outcomes, value assignments must be contextual, which the framework accepts. The per-run wave function's content on a regional algebra is naturally contextual: different measurement contexts probe different algebra-projections, and there is no requirement of joint-value consistency across noncommuting contexts.

**Position with respect to PBR.** The framework is **ψ-ontic and ψ-monist**: the wave function is physically real and is the only ontology. The framework does *not* add hidden particle positions, hidden fields, or any other ontological layer beyond the wave function itself. What is "supplemented" relative to standard textbook QM is not the ontology but the *recognition that the per-run wave function differs from the formal ensemble descriptor*: the formal wave function used in textbook calculations describes the distribution across runs; the per-run wave function in any specific run is a definite physical state of the universe. PBR rules out certain ψ-epistemic positions; the framework is ψ-ontic and not one of those.

**Sister program: Palmer's RaQM / Invariant Set Theory.** Palmer (2025 and prior work) develops a structurally similar Bell escape: principled rejection of measurement independence via the geometry of a fractal invariant set in cosmological state space. The two frameworks share the strategic shape, single-world realism + measurement-dependence grounded in deep structural physics, not in conspiratorial superdeterminism. They differ in the motivating principle (chaos / invariant set vs holography / information capacity) and the mathematical apparatus (p-adic measures + Niven's theorem vs CPW Type II algebras + finite-precision postulate). Detailed comparison is in §10.8.

### 6.10 Tunneling: standard dynamics, record-level reading

Quantum tunneling is a useful test of what QIQT-H does and does not modify. The under-barrier amplitude is real physical content of the formal field state, and **all tunneling amplitudes and rates are exactly those of standard quantum theory** — coherent tunneling (ammonia inversion, Josephson oscillation, double-well coherent oscillation), WKB barrier penetration, $\alpha$-decay and fusion rates, instanton / vacuum-decay amplitudes, and Quantum Zeno / anti-Zeno effects are all unchanged, because (FQ) does not modify the Schrödinger evolution of the underlying field algebra.

**The information limit constrains how the wave function *resides*; it does not trim it.** This point must be stated carefully, because QIQT-H is ψ-monist and deterministic: there are **no fundamental probabilities** in the theory — only the wave function and its unitary evolution. The holographic / (FQ) bound is a constraint on the *physical specification capacity* of a region — on how much amplitude/phase structure the wave function can be instantiated with in $R$ — not a dynamical rule that sets small amplitudes to zero. Concretely:

- The under-barrier evanescent tail is **genuine wave-function content** and stays so. (FQ) never deletes it, never truncates it to zero, and never alters its unitary evolution. The Schrödinger equation runs untouched.
- (FQ) does *not* act pointwise on $\psi$ in the forbidden region. The pointwise value $\psi(x)$ is not even a well-defined physical target for a floor: it is basis-, normalization-, and coarse-graining-dependent, and in the continuum it is dimensionful. The bound is a statement about the regional algebra-state's information content, not about individual amplitudes.
- There is therefore **no kinematic cutoff on tunneling amplitudes**. Any reading on which "a tunneling amplitude below $\varepsilon(R)$ is excluded" is mistaken — it would both presuppose probabilities the theory does not have and misread (FQ) as an amplitude-trimming operation rather than a capacity constraint. A fixed pointwise floor would also be ill-defined (a transition amplitude over a time slice scales with the arbitrary slice duration) and would wrongly freeze ordinary decay.

What (FQ) *does* constrain is the regional **record structure**: distinct, decohered, macroscopically distinguishable records cannot be co-instantiated in $R$ beyond its finite capacity $Q_R$. This is where the framework's content enters — not in the coherent tunneling amplitude, but in how a tunneling *outcome* can reside as a definite regional record.

The correct statement is therefore: QIQT-H leaves the tunneling wave function and its evolution exactly as in standard quantum theory, and differs only in what it says about the **regional record once decoherence has occurred** (the particle is found, or not, on the far side). Per run, the deterministic evolution of the full wave function — together with the finite regional capacity, which cannot hold a co-resident superposition of macroscopically distinct records — leaves a single record physically instantiated in $R$. The textbook Born numbers $|\psi|^2$ are recovered as the *empirical frequency pattern* of records across many runs (the typicality reading of §7.4, §11.4), never as a fundamental per-run probability. This is the same mechanism as for any other measurement (§6); tunneling is not a special case. **Standard dynamics (barrier penetration, unchanged); QIQT-H reading of the regional record only — and even there, by capacity constraint, not by amplitude trimming.**

**Horizon tunneling (Hawking radiation).** The Parikh-Wilczek (1999) tunneling derivation of Hawking emission expresses the rate in terms of the change in Bekenstein-Hawking entropy $S_{\rm BH} = A/(4\ell_P^2)$ — exactly the holographic capacity that QIQT-H reads as the finite information content of the horizon region (in bits, $Q_{\rm hor} = S_{\rm BH}/\ln 2 = A/(4\ell_P^2 \ln 2)$). This is a clean conceptual alignment — the same quantity governs lab-scale per-run wave functions and the horizon's information budget — but it is a *reinterpretation*, not a new prediction: QIQT-H does not by itself modify or re-derive the Parikh-Wilczek emission rate.

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

*Remark on decoherence as the load-bearing ingredient.* A machine-verified audit (`lean/mathlib/QIQTH/NoConcentration.lean`) confirms that linear unitary measurement-decoherence **alone** cannot produce single-record concentration: branch weights $|c_k|^2$ are conserved by unitarity, not concentrated toward $0$ or $1$. The equal-superposition input $\psi = (|0\rangle + |1\rangle)/\sqrt{2}$ leaves post-measurement weights exactly $(1/2, 1/2)$, never $(1, 0)$ or $(0, 1)$. The audit's value is forcing the right reading of how a single record arises. It does **not** arise by any modification of the dynamics: QIQT-H is ψ-monist and the global wave function evolves by the **exact unitary** Schrödinger / Heisenberg dynamics of the underlying field algebra, with (FQ) trimming no amplitude and adding no non-linear or stochastic term. Instead the two genuinely non-standard ingredients are: (a) the (FQ) **resolution-equivalence on regional physical states** (§5.1, Lemma 1) — a statement about how the wave function can *reside* in a region of finite capacity, individuating two regional algebra-states that differ below $\epsilon(R)$ as the *same* physical state, so that a decohered regional state is the *same physical state* as a strict classical mixture (no off-diagonal content survives at the level of regional physical individuation); and (b) **microscopic-IC selection** — which single resident record the actual per-run universe carries is fixed by its specific microscopic initial conditions, propagated through the same unitary evolution. Neither ingredient modifies the dynamics: (a) is a constraint on regional *residence/individuation*, not a dynamical operation on amplitudes, and (b) is just the standard fact that distinct runs are distinct actual universes. The earlier "concentration of amplitudes toward $0$ or $1$" language should be read in this light — it is the regional *record* that is single (by capacity + IC), not the global amplitudes that are dynamically pushed to extremes.

### 7.4 Theorem (Conditional Born typicality)

**Reframing.** QIQT-H has no fundamental probabilities. The framework is deterministic per run: microscopic initial conditions of that run determine which macroscopic record is realized. "Born" in QIQT-H refers to the *empirical frequency pattern* across many runs — a statistical regularity that must emerge from the IC distribution, not a primitive probability assignment. Accordingly Theorem 5 is best understood not in the probability-axiomatic mode of Gleason's theorem, but in the **typicality** mode of Bohmian Dürr-Goldstein-Zanghì equivariance (adapted to QIQT-H's no-particle, no-branching ontology).

**Theorem 5 (Conditional Born typicality).** *Let $\rho$ be a preparation state, $\Omega_\rho$ the QIQT-H microscopic-IC space, and $O_M : \Omega_\rho \to \mathrm{Outcomes}(M)$ the deterministic outcome map for a measurement protocol $M$. Suppose:*

*(i) **Canonicality.** There exists a measure $\mu_\rho$ on $\Omega_\rho$ defined from QIQT-H primitives (not fitted per measurement).*

*(ii) **Born pushforward.** $(O_M)_* \mu_\rho(i) = \mathrm{tr}(\rho E_i)$ for every allowed outcome effect $E_i$ in the measurement protocol $M$.*

*(iii) **Equivariance / stationarity.** $\mu_\rho$ is preserved (up to allowed parameter-dependence on $\rho$) by the (FQ)-restricted physical Hamiltonian.*

*(iv) **Repeated-trial typicality.** Repeated trials of the prepare-measure procedure are represented by a $\mu_\rho$-typical iid (or stationary-ergodic) process on $\Omega_\rho$.*

*Then for $\mu_\rho$-typical microscopic-IC sequences, the empirical relative frequency of macroscopic outcome $k$ across many runs converges to the Born weight $\mathrm{tr}(\rho E_k)$ (= $|c_k|^2$ for pure states with $\rho = |\psi\rangle\langle\psi|$ and projective measurements).* $\blacksquare$

**Status of the four hypotheses.** Hypotheses (ii) and (iv) are standard: (ii) is what defines $\mu_\rho$ as "the Born measure" for $\rho$; (iv) is a routine LLN/ergodicity input. Hypotheses (i) and (iii) — *canonicality* and *equivariance* — are the **framework's load-bearing open commitments**. They are not delivered by FQ + AQFT + holography alone; see machine-verified audits below.

The conditional shape of Theorem 5 is now formalized in `lean/mathlib/QIQTH/BornTypicality.lean` (theorem `qiqth_born_typicality_conditional`). The deterministic core (mean per-run frequency equals the outcome marginal) is rigorously proved; the LLN step is taken as a standard probability black box at the interface layer.

**Important — QIQT-H does not derive the Born measure.** It identifies the exact canonical-measure / equivariance principle required for Born frequencies, and reduces the Born problem to that principle. This is the typicality-paradigm analog of Bohmian $|\psi|^2$-equivariance, adapted for QIQT-H's no-particle ontology.

**Audit remark — universal realizability (the negative companion).** A machine-verified audit (`lean/mathlib/QIQTH/NoBornFromNothing.lean`) establishes that for **any** target outcome distribution $p$ (not just $|c_k|^2$) and any surjective outcome map from the IC space, there exists a measure $\mu_p$ whose outcome-marginal equals $p$. Construction: choose a section of the outcome map and place mass $p_k$ on $s(k)$. Hence the framework's structural axioms (FQ, microcausality, Donald, holographic bound) do *not* select Born over any other distribution. Hypothesis (i) of Theorem 5 is therefore *genuinely independent* of the other QIQT-H postulates — it must be added as a separate principle, not derived.

**Audit remark — support preservation $\neq$ Born equivariance.** A second machine-verified audit (`lean/mathlib/QIQTH/EquivarianceGap.lean`) establishes that the framework's "(FQ)-restricted physical Hamiltonian preserves $\mathcal{H}_{\rm phys}$" statement is *support preservation*, strictly weaker than the measure-preservation hypothesis (iii) of Theorem 5. Concrete counterexample: a bijection on a 2-point space preserves the support trivially yet shuffles a non-uniform measure. Hypothesis (iii) is therefore a *genuine additional commitment* beyond the framework's current postulates.

**Candidate principles for hypothesis (i).** Three candidate physical mechanisms could supply the Canonical IC Measure Principle:

*(α) **Canonical tracial typicality from CPW Type II structure.** The crossed-product Type II algebra $\hat{\mathcal{A}}(R)$ carries a canonical normal semifinite trace $\tau_R$ (unique up to scale). If $\tau_R$ induces, via the natural identification of IC space with the algebra's state space, a canonical measure $\mu_\rho^{\tau}$ satisfying (i)–(iv), this is the most QIQT-H-native route. (Currently the leading candidate.)*

*(β) **Symmetric equiprobability** on a natural decomposition of $\Omega_\rho$ into record-fibers, with Born weights emerging from fiber-volume ratios. This route requires a structural principle making the decomposition canonical and the fiber volumes well-defined.*

*(γ) **Holographic / modular construction** from the canonical sector reference state $\sigma_R$ (vacuum on Minkowski, KMS on stationary thermal, Bunch-Davies on de Sitter, etc.) via a modular-theoretic construction yielding $\mu_\rho$. Physically attractive but currently the least mathematically developed of the three.*

None of (α), (β), (γ) is derivable from FQ + AQFT + holography alone; each is a candidate **additional postulate** the framework would need to adopt. The framework presently leaves the choice open; Open Problem 1 (§11.4) sharpens the canonical-measure problem with explicit sub-conditions.

*Remark on Gleason.* Gleason's theorem derives the Born rule from probability-axiomatic constraints (noncontextuality + orthogonal additivity) on a projection lattice. It is *not* the appropriate primary derivation for QIQT-H, which is deterministic per run and has no primitive probability assignment. Gleason functions as a consistency check on the *target* empirical frequencies (Born is the unique probability rule consistent with the noncontextuality axioms), but cannot select the microscopic IC measure $\mu_\rho$ — many distinct $\mu_\rho$ push forward to the same Born outcome distribution. Closing the gap requires the typicality argument above, not Gleason.

### 7.5 What §7.1–7.4 establishes

(FQ) restricts the model class properly (Theorem 2); the literal physical-instantiation reading implies finite physical resolution (Theorem 3); combined with dynamical concentration via decoherence + microscopic IC, this yields single-record per-run wave functions structurally (Theorem 4); Born statistics emerge from typicality (Theorem 5, schematic).

The framework's structural skeleton: (FQ) is the literal physical-instantiation reading of the Bekenstein-Bousso bound, stated rigorously in the CPW Type II algebraic framework; the precision floor is the structural consequence; concentrated per-run amplitudes cross the threshold and the per-run wave function physically is a single-record state.

### 7.6 The Modular-Local Holographic Superselection Rule (foundational postulate)

**Reference state sector.** Fix once and for all a faithful locally normal reference state $\sigma$ on the quasilocal algebra, and choose the hatted local algebras coherently with this reference sector. In the Minkowski-vacuum sector $\sigma$ is the vacuum state; on stationary thermal backgrounds it is the geometrically preferred KMS state; and on de Sitter / cosmological backgrounds it is the Bunch–Davies, Hartle–Hawking, or other specified invariant reference state. For every bounded diamond $R$, write

$$
\sigma_R := \sigma|_{\hat{\mathcal{A}}(R)}.
$$

The family $\{\sigma_R\}$ is required to be **restriction-compatible**: whenever $R' \subset R$, isotony gives $\hat{\mathcal{A}}(R') \subset \hat{\mathcal{A}}(R)$, and

$$
\sigma_{R'} = \sigma_R |_{\hat{\mathcal{A}}(R')}.
$$

All relative entropies and modular Hamiltonians below are taken with respect to this $\sigma_R$. The notation $\Omega_R$, when it appears in vacuum-sector examples, denotes only the GNS vector representative of $\sigma_R$, not a second reference state.

The entropy quantity denoted $S_{\rm ren}$ in §4.1(ii) is the modular-local information functional used here:

$$
S_{\rm ren}(R; \omega) \;\equiv\; \chi_R(\omega_R) \;:=\; S^{\hat{\mathcal{A}}(R)}_{\rm Araki}(\omega_R \,\|\, \sigma_R).
$$

When the Type II crossed-product representation supplies a canonical trace and a modular Hamiltonian $K_R^\sigma$, this is equivalently written as

$$
\chi_R(\omega_R) \;=\; \Delta_\omega \langle K_R^\sigma \rangle - \Delta_\omega S_R.
$$

The holographic condition (FQ)(ii) is precisely the modular-local capacity bound $\chi_R(\omega_R) \le C(R)$.

The above theorems establish the framework's structure within standard renormalized entropy. They leave a critical question: even after decoherence + (FQ) deliver a strict classical mixture $\sum_k p_k \omega_k^R$ on the regional algebra, this is *still a mixture over multiple macroscopic records*. The modular-local capacity bound controls the record-entropy / effective support of this mixture: for $k$ equiprobable records of per-record cost $I_0$, one typically has $\chi_R \simeq I_0 + \log k$, so raw cardinality is not excluded without additional branch-summed assumptions. To establish single-record per-run as a structural consequence at the level of the macroscopic observable content, the framework commits to a stronger principle than standard entropy bounds: a **modular-local holographic superselection rule**.

This is the framework's central new physical postulate beyond the algebraic scaffolding of CPW/Witten. It is formulated *intrinsically* on the algebra-state pair via Araki / Type II core relative entropy, with no joint-region cutoff applied to spacelike-combined algebras.

**Definition (Regional information functional, restated).** *The regional information functional $\chi_R$ is the Araki relative entropy on $\hat{\mathcal{A}}(R)$ with respect to the fixed reference $\sigma_R$ defined above. Equivalently, in the Type II crossed-product core with canonical semifinite trace $\tau_R$ and Haagerup densities $h_{\omega, R}$, $h_{\sigma, R}$:*
$$
\chi_R(\omega) \;=\; \tau_R\!\left[ h_{\omega, R} \left( \log h_{\omega, R} - \log h_{\sigma, R} \right) \right] + \text{counterterms},
$$
*finite by the CPW/Witten construction (no UV divergence; no density-matrix assumption).*

**Postulate (Modular-Local Holographic Bound, central physical axiom).** *The regional information functional is bounded by the holographic capacity, region by region:*
$$
\boxed{\chi_R(\omega) \;\le\; C(R) \;=\; \frac{A(\partial R)}{4\ell_P^2} \quad \text{for every bounded region } R \text{ and every physical state } \omega.}
$$

*For spacelike-separated regions $D_A, D_B$, admissibility combines as the meet of local predicates:*
$$
\mathrm{Adm}(D_A \cup D_B) \;=\; \mathrm{Adm}(D_A) \wedge \mathrm{Adm}(D_B).
$$

*No bound is imposed on the joint spacelike algebra $\hat{\mathcal{A}}(D_A) \vee \hat{\mathcal{A}}(D_B)$ beyond what the local restrictions already require.*

This is a **strengthening of the standard Bekenstein-Bousso bound**, not a derivation from it. Standard holographic entropy bounds limit the renormalized entropy of regional reduced states; the modular-local bound limits the *relative* entropy with respect to a reference state, intrinsically defined via Araki/Connes machinery in Type III local QFT.

**Branch-summed cost as derived approximation.** When $\omega_R$ is a strict classical mixture $\bar\omega_R = \sum_k p_k \omega_{k,R}$ over decoherent macroscopic records (as after decoherence + (FQ) at lab scale, §6.2–6.3), Donald's identity for Araki relative entropy gives
$$
\chi_R(\bar\omega_R) \;=\; \sum_k p_k \, c_R(r_k) - I_{\rm Hol}^R,
$$
where $c_R(r_k) = \chi_R(\omega_{k,R})$ is the per-record cost (relative entropy of branch $k$ to the reference $\sigma_R$) and $I_{\rm Hol}^R = \sum_k p_k S_{\rm Araki}(\omega_{k,R} \| \bar\omega_R)$ is the Holevo information of the mixture. In the strict distinguishable-record limit, $I_{\rm Hol}^R \approx H(\{p_k\})$. Effective branch multiplicity is thus controlled by the Holevo term that reappears in Theorem 6, not by an independent spacelike joint cutoff. **The earlier "branch-summed cost" $I_\Sigma^\epsilon$ is a derived classical-mixture approximation in this sense, useful for operational calibration (the $I_0$ parameter, Schrödinger-cat scale, exclusion curves) but not the fundamental statement of the bound.**

This formulation matters for two reasons:

1. **Type III compatibility.** $\chi_R$ is defined directly in Type III via Araki; it does not require selecting a record subalgebra or smoothing parameter to be fundamentally defined. Branch counting is a coarse-graining of $\chi_R$ in the classical-mixture limit, not a new entropy concept.

2. **No-signaling becomes a theorem.** Because $\chi_R$ depends only on the algebra-state pair $(\hat{\mathcal{A}}(R), \omega_R)$ and not on any joint-region structure, and because the admissibility predicate for spacelike-separated regions is the meet of local predicates, no-signaling follows automatically from AQFT microcausality. See §7.7.

**The framework's commitment: the modular-local capacity bound is a superselection/admissibility rule, not a dynamical collapse rule and not a universal branch-summed cardinality postulate.**

Under this commitment, the framework's structure is the following.

**Definition (Stagewise causal admissibility).** *Fix a global time function with Cauchy slices $\{\Sigma_t\}$. Let $\{\mathcal{F}_t\}$ be the classical filtration generated by outcome records whose localization diamonds lie in $J^-(\Sigma_t)$. For a branch/history $h \in \mathcal{F}_t$, let $\mathcal{O}_t(h)$ be the set of record diamonds realized on that branch up to time $t$.*

*A bounded diamond $R$ is **causally instantiated** at stage $(t, h)$ if $R \Subset J^-(\Sigma_t)$ and either:*
*(a) **Conditioned case** ($Y \ne \varnothing$): there exists a finite nonempty set $Y \subset \mathcal{O}_t(h)$ of records whose alternatives are being jointly constrained in $R$, with $R \Subset \bigcap_{O \in Y} J^+(O)$. This is the joint-record-comparison case where $R$ sits causally downstream of all records in $Y$.*
*(b) **Unconditioned local case** ($Y = \varnothing$): $R$ has no past records constraining it. This case gives the ordinary local capacity constraint on $R$ alone, in force whenever $R$ has been physically instantiated (i.e., it is a finite causal diamond contained in $J^-(\Sigma_t)$ at the current stage).*
*Denote the resulting collection of instantiated regions by $\mathfrak{R}_t(h)$.*

*The **stagewise physical state space** is*
$$
\mathcal{S}_{\rm phys}(t, h) \;:=\; \left\{ \omega_t^h : (\omega_t^h)_R \in \hat{\mathcal{A}}(R)_*^+,\; \|(\omega_t^h)_R\| = 1,\; \chi_R((\omega_t^h)_R) \le C(R) \text{ for all } R \in \mathfrak{R}_t(h) \right\}.
$$

*A **physical process** is an adapted family $h \mapsto \omega_t^h$ such that $\omega_t^h \in \mathcal{S}_{\rm phys}(t, h)$ for every stage $t$ and $\mathcal{F}_t$-almost every branch $h$.*

*The unqualified notation $\mathcal{S}_{\rm phys}$ denotes this stagewise family unless a terminal completed-history limit is explicitly specified. Future joint-diamond constraints are therefore imposed only when the relevant region has become causally instantiated; they do not retroactively delete branches that were admissible at earlier stages.*

*If a universal Hilbert-space representation is used, let $\pi(|\Psi\rangle) = \omega_\Psi$ be the induced algebraic state. Then $\mathcal{H}_{\rm phys}$ denotes the set of $|\Psi\rangle$ whose induced stagewise family $(\omega_\Psi)_t^h$ satisfies the stagewise condition above, modulo the equivalence $|\Psi\rangle \sim |\Phi\rangle \iff \omega_\Psi|_R = \omega_\Phi|_R$ for every $R$. This is a set of physical equivalence classes, not a linear subspace of $\mathcal{H}$.* States outside $\mathcal{S}_{\rm phys}$ are *kinematically forbidden*, they are mathematically writeable in the unrestricted formalism but are not physically realizable.

**Definition (Physical dynamics and instruments).** *A deterministic evolution is represented in the Heisenberg picture by a normal unital completely positive map $\alpha_t: \hat{\mathcal{A}} \to \hat{\mathcal{A}}$; for closed reversible dynamics, $\alpha_t$ is an automorphism. It is **physical** iff*
$$
\alpha_{t*}(\mathcal{S}_{\rm phys}) \subseteq \mathcal{S}_{\rm phys}, \qquad (\alpha_{t*}\omega)(A) := \omega(\alpha_t(A)).
$$

*A Hamiltonian is physical only insofar as its induced automorphism group satisfies this condition.*

*A measurement instrument $\mathcal{I} = \{\mathcal{I}_a\}_a$ is **physical** iff $\sum_a \mathcal{I}_a$ is unital and, for every $\omega \in \mathcal{S}_{\rm phys}$:*
*(i) the non-selective state $\omega \circ (\sum_a \mathcal{I}_a)$ lies in $\mathcal{S}_{\rm phys}$; and*
*(ii) **branchwise**: for each outcome $a$, the corresponding durable classical record is localized in a bounded diamond $O_a$. Whenever $p_a = \omega(\mathcal{I}_a(\mathbf{1})) > 0$, the normalized conditional state*
$$
\omega_a(B) := \frac{\omega(\mathcal{I}_a(B))}{p_a}
$$
*must satisfy the admissibility bound on every bounded diamond $R \Subset J^+(O_a)$:*
$$
(\omega_a)_R \in \hat{\mathcal{A}}(R)_*^+, \qquad \chi_R((\omega_a)_R) \le C(R).
$$
*At finite process stage $t$, this condition is imposed only for those $R \Subset J^+(O_a) \cap J^-(\Sigma_t)$ that lie in the instantiated collection $\mathfrak{R}_t(a)$. Conditional feed-forward operations must satisfy the same condition on each branch.*

The set of physical dynamics is a proper subset of the set of all normal unital CP maps on $\hat{\mathcal{A}}$. Generic Hilbert-space Hamiltonians do not induce physical dynamics; physical dynamics do.

**Axiom (Causal application of admissibility).** *Modular-local admissibility is imposed on the state of a region when that region is physically instantiated in the causal order. If earlier alternatives are separately admissible in their respective past algebras, a later joint diamond $D^+$ constrains only the state restricted to $\hat{\mathcal{A}}(D^+)$ after the relevant systems enter $D^+$. Failure of $\chi_{D^+} \le C(D^+)$ makes the proposed future joint state or transition inadmissible; it does **not** retroactively delete previously admissible past branches.*

**Theorem 6 (Effective Macroscopic Definiteness via Donald's identity, conditional form).** *Throughout this theorem, $\chi_R(\varphi) := S_{\rm Araki}^{\hat{\mathcal{A}}(R)}(\varphi \| \sigma_R)$ denotes Araki relative entropy to the **fixed** regional reference state $\sigma_R$ of §7.6, and all states are normal on $\hat{\mathcal{A}}(R)$.*

*Let $\omega \in \mathcal{S}_{\rm phys}$ and let $R$ contain a decohered macroscopic record algebra with mutually exclusive record predicates $\{P_k\}_{k \in \mathcal{A}_\epsilon}$ forming the $\epsilon$-smoothed active set, with $|\mathcal{A}_\epsilon| < \infty$ (finite effective support). Let $p_k = \omega_R(P_k)$, $q := \sum_{k \in \mathcal{A}_\epsilon} p_k > 0$, $\tilde p_k := p_k/q$. Let $\omega_{k,R}$ be the conditional regional state of branch $k$, $\bar\omega_R := \sum_k \tilde p_k \, \omega_{k,R}$, and*
$$
I_{\rm Hol}^R \;:=\; \sum_{k \in \mathcal{A}_\epsilon} \tilde p_k \, S^{\hat{\mathcal{A}}(R)}_{\rm Araki}(\omega_{k,R} \,\|\, \bar\omega_R), \qquad H_\epsilon \;:=\; -\sum_k \tilde p_k \log \tilde p_k.
$$

*The exact **Donald's identity** holds for Araki relative entropy:*
$$
\sum_{k \in \mathcal{A}_\epsilon} \tilde p_k \, \chi_R(\omega_{k,R}) \;=\; \chi_R(\bar\omega_R) + I_{\rm Hol}^R. \tag{$\star$}
$$

*Assume:*
*(H1) **Branchwise admissibility.** Each active branch satisfies $\chi_R(\omega_{k,R}) \le C(R)$.*
*(H2) **Record-instantiation cost** (independent framework postulate). The mean regional state has cost $\chi_R(\bar\omega_R) \ge I_0 - \eta_0$, where $I_0$ is the per-record cost parameter and $\eta_0 \ge 0$ a tolerance.*
*(H3) **Operational distinguishability.** There exists a normal measurement instrument on $\hat{\mathcal{A}}(R)$ decoding the active record index $K \in \mathcal{A}_\epsilon$ with average error probability $P_e$. Standard information theory gives $H_\epsilon = I(K;Y) + H(K \mid Y)$ where $Y$ is the decoded outcome. The Holevo bound yields $I(K;Y) \le I_{\rm Hol}^R$, and Fano's inequality gives $H(K \mid Y) \le h_2(P_e) + P_e \log(|\mathcal{A}_\epsilon| - 1) =: \eta_{\rm def}$. Hence $H_\epsilon \le I_{\rm Hol}^R + \eta_{\rm def}$.*

*Then Donald's identity $(\star)$ together with (H1) and (H2) gives*
$$
I_{\rm Hol}^R \;=\; \sum_k \tilde p_k \chi_R(\omega_{k,R}) - \chi_R(\bar\omega_R) \;\le\; C(R) - I_0 + \eta_0.
$$
*(Since $I_{\rm Hol}^R \ge 0$, this is informative only when $C(R) - I_0 + \eta_0 \ge 0$. If $C(R) < I_0 - \eta_0$, the hypotheses (H1) and (H2) are jointly unsatisfiable, the region cannot support even a single record at its specified cost, so no admissible record-bearing state on $R$ exists.)*

*and with (H3),*
$$
\boxed{H_\epsilon \;\le\; C(R) - I_0 + \eta_0 + \eta_{\rm def}, \qquad N^{(\epsilon)}_{\rm eff} := \exp H_\epsilon \;\le\; \exp(C(R) - I_0 + \eta_0 + \eta_{\rm def}).}
$$
*Here $\eta_{\rm def} = h_2(P_e) + P_e \log(|\mathcal{A}_\epsilon| - 1)$ is the explicit Fano residual.*

*Moreover, for every $0 < \delta < 1$, there exists $T_\delta \subseteq \mathcal{A}_\epsilon$ with normalized active probability $\ge 1 - \delta$ and*
$$
|T_\delta| \;\le\; \exp\!\left(\frac{C(R) - I_0 + \eta_0 + \eta_{\rm def}}{\delta}\right).
$$

*If the leakage sector $\mathcal{A}_\epsilon^c$ is retained, the theorem bounds only the conditional active entropy $H_\epsilon$. The full unnormalized entropy decomposes as $H(p) = h_2(q) + q H_\epsilon + (1-q) H(p \mid \mathcal{A}_\epsilon^c)$, so an additional finite-support or entropy assumption on the leakage sector is required to bound $H(p)$ itself.*

*At **exact** saturation $I_0 = C(R)$ and $\eta_0 = \eta_{\rm def} = 0$, one obtains $H_\epsilon = 0$: a single record has normalized active probability one. For **finite** tolerances, the conclusion weakens to $H_\epsilon \le \eta_0 + \eta_{\rm def}$, one record dominates with probability $\ge 1 - O(\eta_0 + \eta_{\rm def})$. For approximate saturation, the conclusion is **effective / probability-weighted** rather than a raw cardinality bound.*

*Proof.* Donald's identity $(\star)$ is a standard property of Araki relative entropy on a von Neumann algebra (Donald 1986; cf. Ohya-Petz 1993, Thm 5.21). Under (H1), the LHS of $(\star)$ is bounded by $C(R)$. Under (H2), the term $\chi_R(\bar\omega_R)$ in the RHS of $(\star)$ is at least $I_0 - \eta_0$. Rearranging gives the bound on $I_{\rm Hol}^R$. Applying (H3) gives the bound on $H_\epsilon$. The smoothed support bound follows by Markov's inequality on $-\log \tilde p_k$, and $\tilde p_{\max} \ge e^{-H_\epsilon}$ gives the saturation conclusion. $\blacksquare$

**Status of the assumptions.** (H1) is a direct consequence of $\omega \in \mathcal{S}_{\rm phys}$ provided each $\omega_{k,R}$ inherits admissibility, natural under the branchwise instrument condition of §7.6. (H3), operational distinguishability, is the formal expression of macroscopic record decodability, established under decoherence + Quantum Darwinism for the macroscopic-record subalgebra (§6.4–6.7). (H2) is the *independent framework postulate*: it asserts that physical instantiation of a macroscopic record on $R$ requires modular cost $\ge I_0$. This is *not* a theorem of standard AQFT or holography; it is the framework's central commitment, calibrated empirically against the observed quantum-to-classical transition scale.

**Sharpening of (H2) — reference-weight form.** A machine-verified audit (see `lean/mathlib/QIQTH/H1H2Audit.lean` in the project repository) confirms that (H2) is genuinely independent of (H1), Donald's identity, Klein positivity, and DPI: a classical KL countermodel with $\sigma=(1/2,1/2)$ and $\rho=\delta_0$ satisfies all the structural hypotheses but violates (H2) with $I_0=1$. The same audit also yields the following sharp structural reformulation of (H2). For a perfect-record state on event $E_{\rm record}$,
$$\chi_R(\bar\omega_R) \ge I_0 - \eta_0 \quad \Longleftrightarrow \quad \sigma_R(E_{\rm record}) \le e^{-(I_0 - \eta_0)}.$$
Equivalently: (H2) is the assertion that **macroscopic record sectors occupy exponentially small reference-weight** under the canonical sector reference state $\sigma_R$. This identifies the load-bearing physical content of (H2): not the positivity of relative entropy (which Klein already provides), but a reference-weight bound on pointer sectors that a future first-principles derivation must obtain from modular/holographic structure on macroscopic records.

**Conditional modular estimate of Born-weight deviations.** Let $\mu$ be the Born measure over conditional record states $r \mapsto \omega_r$, and define the inadmissible set
$$
F_R := \{r : \chi_R(\omega_r) > C(R)\}, \qquad \delta_R := \mu(F_R).
$$
Since $\chi_R \ge 0$, Markov's inequality gives
$$
\delta_R \;\le\; \frac{\mathbb{E}_\mu[\chi_R(\omega_r)]}{C(R)}.
$$

The conversion of $\chi_R$ into a stress-energy estimate is *not* assumed for a generic QFT ball. It is used only when the reference modular Hamiltonian is known geometrically, or when $R$ is compared to such a region by monotonicity of relative entropy.

*Wedge case (Bisognano-Wichmann).* In the Minkowski-vacuum sector, i.e., with $\sigma_R$ taken to be the vacuum / geometric-modular reference state corresponding to a Rindler wedge $W \supset R$, the Bisognano-Wichmann theorem gives, for states normal to the vacuum representation and in the domain of the boost / modular Hamiltonian, the *exact first-moment expression*
$$
\Delta\langle K_W^\sigma\rangle \;=\; \frac{2\pi}{\hbar c} \int_W x^1 \, \Delta\langle T_{00}\rangle(x) \, d^{d-1}x.
$$
*(This formula is specific to the vacuum / geometric-wedge modular setting; for arbitrary $\sigma_R$ no such universal local form is available.)*
The simplified estimate $\Delta\langle K_W^\sigma\rangle \le 2\pi L E_W/(\hbar c)$ requires: (i) finite renormalized energy; (ii) finite first moment; (iii) the excitation has support effectively in $0 \le x^1 \le L$ (split / smeared localization to avoid UV pathologies of sharp localization); (iv) nonnegative renormalized energy density / positive energy measure in that region. If these conditions fail, use the exact first-moment expression rather than the $L E_W$ bound.

By monotonicity of Araki relative entropy under restriction,
$$
\chi_R(\omega_R) \;\le\; \chi_W(\omega_W) \;=\; \Delta\langle K_W^\sigma\rangle - \Delta S_W.
$$
Hence $\chi_R(\omega_R) \le 2\pi L E_W/(\hbar c) + s_W$ provided the entropy shift satisfies $\Delta S_W \ge -s_W$. The commonly used estimate $\chi_R(\omega_R) \le 2\pi L E_W/(\hbar c)$ requires the additional hypothesis $\Delta S_W \ge 0$ along with (i)–(iv) above.

*CFT-vacuum ball case.* For a ball $B_L$ in a CFT vacuum, the conformal modular Hamiltonian gives
$$
K_{B_L}^\sigma \;=\; \frac{2\pi}{\hbar c} \int_{|x| < L} \frac{L^2 - |x|^2}{2L} T_{00}(x) \, d^{d-1}x,
$$
and the same conclusion holds, with the corresponding entropy-shift qualification.

*Generic QFT ball.* For a non-conformal QFT ball, no universal local formula for $K_R^\sigma$ is assumed; the bound is obtained only by enclosing-wedge monotonicity as above.

Under these hypotheses, the Born-deviation estimate reads
$$
\delta_R \;\lesssim\; \frac{2\pi L \, \mathbb{E}_\mu[E_R]/(\hbar c) + s_R}{A(\partial R)/(4\ell_P^2)}.
$$
If $s_R$ is negligible, $A(\partial R) \simeq 4\pi L^2$, $L \simeq 1\,\mathrm{m}$, and $E_R \simeq 1\,\mathrm{kg}\,c^2$, this gives the **conditional** order-of-magnitude estimate
$$
\delta_R \;\sim\; 10^{-27}.
$$
This number is therefore **not a generic QFT consequence**; it is a wedge / CFT-ball modular-energy estimate with the stated entropy-shift hypothesis. The deviation theorem (§7.4) then implies that Born probabilities under modular-local admissibility deviate from standard Born probabilities by at most $\delta_R$ on bounded observables, operationally invisible at lab scale, conditional on the hypotheses above.

The single-record-per-region structure of physical states is therefore a *structural consequence* of the modular-local capacity bound. **Effective form (Theorem 6, the precise statement).** Multi-record states are not absent because of dynamical collapse; under approximate saturation $I_0 \approx C(R)$ they are *exponentially suppressed* on the normalized active distribution (effective multiplicity $N^{(\epsilon)}_{\rm eff} = \exp H_\epsilon \le \exp(C(R) - I_0 + \eta_0 + \eta_{\rm def})$), and at exact saturation $I_0 = C(R), \eta_0 = \eta_{\rm def} = 0$ they are *kinematically forbidden* (single record with active probability one). The strong-language passages below ("not in the physical state space", "$N_{\max} \approx Q_R/I_0$") are to be read in the exact-saturation limit; the precise effective form for finite tolerances is Theorem 6.

**Dynamical content of Option 2.** Standard Hilbert-space QM is the unconstrained formalism. The constrained subset $\mathcal{H}_{\rm phys}$ is a *nonlinear submanifold* of $\mathcal{H}$ (the constraint $I_\Sigma \le Q_R$ is nonlinear in the state). Physical Hamiltonians are constrained to preserve this submanifold. The framework's claim is that the actual physical Hamiltonian of nature respects the Branch-Summed Bound, measurement-like unitaries that would (in unrestricted QM) take a single-record state to a multi-record state do not occur in the physical dynamics; the actual physical dynamics, with the constraint imposed, takes single-record states to single-record states (selected by the actual physical initial conditions of apparatus + environment in that run).

**Response to the linear measurement obstruction.** A standard objection: "By linearity, $U(\alpha|0\rangle + \beta|1\rangle)|A_{\rm ready}\rangle = \alpha|A_0\rangle + \beta|A_1\rangle$, exactly the forbidden multi-record state."

This objection assumes that the unrestricted-Hilbert-space wave function $\alpha|A_0\rangle + \beta|A_1\rangle$ is the physically primary object, the actual physical state that we have direct access to. The framework denies this. **We do not have direct physical access to unrestricted-Hilbert-space states; we have access only to the physical observable content of bounded regions, the state on the macroscopic record subalgebra $\mathcal{C}(R)$, with the (FQ) precision floor.**

The screen is a complex quantum system with $\sim 10^{20}$–$10^{25}$ degrees of freedom that becomes entangled with the particle during detection. Decoherence between distinct macroscopic record states $|A_0\rangle$ and $|A_1\rangle$ produces environmental cross-overlaps $\langle E_0 | E_1 \rangle \sim e^{-10^{20}}$ on physically realistic timescales (§6.2). Under (FQ), these exponentially-small off-diagonal coherence terms are *physically zero* (§6.3).

So at the level of physical observable content, which is what physics is about, the formal $\alpha|A_0\rangle + \beta|A_1\rangle$ structure decoheres to a classical-looking expression, and the residual coherence is rendered physically zero by (FQ). The physical state on the macroscopic observable algebra is a strict classical mixture over records. The framework's superselection rule then says: even this strict classical mixture (with $H(\{p_k\}) > 0$ when $|c_k|^2$ are both non-negligible) violates the Branch-Summed Bound when the records' costs approach $Q_R/I_0$. So this state isn't a *physical* state either.

What actually happens in a specific run, under the constrained physical Hamiltonian acting on the actual initial conditions of that run (specific microscopic state of screen + environment), is that the per-run evolution stays within $\mathcal{H}_{\rm phys}$ throughout, the actual physical Hamiltonian does not produce multi-record states from physically allowed initial conditions. The linear-Hilbert-space-formalism argument $U(\alpha|0\rangle + \beta|1\rangle) \to \alpha|A_0\rangle + \beta|A_1\rangle$ describes what an *unconstrained* unitary would do; the *physical* Hamiltonian, constrained to preserve $\mathcal{H}_{\rm phys}$, takes the per-run initial state (with specific actual microscopic IC) to a per-run final state (with a specific actual macroscopic record). Different runs with different actual initial conditions produce different actual records; across many runs, Born statistics emerge from typicality.

The "linear measurement obstruction" thus disappears once one recognizes that (a) physical observable content, not unrestricted Hilbert-space wave functions, is what we have physical access to; (b) decoherence + (FQ) make the off-diagonal coherence physically zero at the observable level; (c) the constraint on physical Hamiltonians (preserving $\mathcal{H}_{\rm phys}$) eliminates the multi-record final state from physical dynamics.

**The per-record cost $I_0$ as an experimental parameter.** The framework's central physical postulate, the Branch-Summed Holographic Bound $I_\Sigma^\epsilon[\omega_R] \le Q_R$, combines two quantities:
- $Q_R = A(\partial R)/(4\ell_P^2)$: the **regional holographic capacity**, a geometric quantity determined by the boundary area in Planck units. Set by quantum gravity; not a free parameter.
- $c_R(r) \approx I_0$: the **per-record physical cost**, the information cost of specifying a macroscopic record's full microscopic configuration. This is an **experimental parameter** of the theory.

The number of coexisting macroscopic records allowed per region is $N_{\max} \approx Q_R/I_0$. The empirically observed boundary at which macroscopic superpositions cease to occur (the quantum-to-classical transition scale) corresponds to the scale at which $N \cdot I_0$ approaches $Q_R$ for the relevant macroscopic record cost $I_0$.

**This is directly analogous to GRW's parameter structure.** GRW has a collapse rate $\lambda$ that is a free parameter calibrated empirically: small enough that microscopic quantum coherence is preserved, large enough that macroscopic superpositions decohere on observed timescales. QIQT-H has $I_0$ playing an analogous role: small enough that microscopic records (atoms, qubits, small molecules) have $N \cdot I_0 \ll Q_R$ and standard QM behavior is recovered, large enough that macroscopic records have $N \cdot I_0$ approaching $Q_R$ so the superselection enforces single-record per run.

Unlike GRW, where $\lambda$ is ad hoc, in QIQT-H $I_0$ has a **physical interpretation**: the information cost of specifying a macroscopic record's full microscopic configuration in the regional Type II algebra. This is in principle calculable from microphysics (Zurek physical entropy, decoherent-history weights, Quantum Darwinist redundancy), though current best estimates give $I_0 \sim 10^{25}$ bits for typical macroscopic records, far below $Q_R \sim 10^{70}$ for a 1m region.

The framework's empirical content includes the prediction: **the per-record cost $I_0$ must be calibrated such that $N \cdot I_0$ approaches $Q_R$ at the observed quantum-to-classical transition scale.** If standard Zurek entropy gives $I_0 \sim 10^{25}$ bits and laboratory macroscopic records are still well below the regional capacity, then the framework predicts the observable quantum-to-classical boundary involves macroscopic records whose cost is much larger than naive Zurek estimates, including all entangled environmental degrees of freedom out to the relevant decoherence horizon. The framework's specific prediction is that this calibration converges to a definite value of $I_0$ for macroscopic record types, and this value is testable against the observed scale at which Schrödinger-cat-like experiments fail.

The two-parameter structure of the theory:
| Parameter | Origin | Status |
|---|---|---|
| $Q_R = A(\partial R)/(4\ell_P^2)$ | Holographic principle of quantum gravity | Geometric; not adjustable |
| $I_0 = c_R(r)$ for typical macroscopic records | Per-record physical cost in regional Type II algebra | Experimental; calibrated empirically |

The single-outcome enforcement threshold occurs at $N \cdot I_0 \approx Q_R$. Below this threshold (microscopic regime, $N \cdot I_0 \ll Q_R$): constraint vacuous, standard QM behavior. Above this threshold (macroscopic regime): constraint enforces single-record per run.

This is analogous to how gauge theories work: the physical state space is a constrained submanifold of the unrestricted Hilbert space (gauge-invariant states); physical Hamiltonians preserve gauge invariance; the unrestricted Hamiltonians are mathematically writeable but unphysical. In gauge theory the constraint is gauge invariance; in QIQT-H the constraint is the Branch-Summed Holographic Bound.

**Schrödinger evolution holds on $\mathcal{H}_{\rm phys}$.** Within the physical state space, evolution under physical Hamiltonians is linear and unitary, Schrödinger evolution is preserved. What is *not* preserved is the freedom to use arbitrary Hilbert-space Hamiltonians; physical Hamiltonians are constrained.

**The price the framework pays.** This commitment modifies the physical dynamics relative to unrestricted standard QM. The set of physical Hamiltonians is a constrained set. This is a substantive modification of QM at the foundational level, but only in regimes where the branch-summed cost approaches the holographic capacity. At lab scales, where macroscopic records use only $\sim 10^{25}$ bits of an available $\sim 10^{70}$-bit holographic capacity per cubic meter, the constraint is operationally vacuous. Standard QM at lab scales gives the same predictions as the constrained dynamics. The constraint becomes operationally relevant only when branch-summed cost approaches $Q_R$, i.e., for macroscopic measurement records, where the framework's deviation from standard QM is to *enforce* single-record per-run at the kinematic level.

**Mathematical work needed:**

1. **Precise specification of $\mathcal{C}(R)$** as the einselected/Darwinistic record subalgebra (drawing on decoherent histories, Quantum Darwinism).
2. **Per-record cost $c_R(r)$** rigorously defined via Zurek physical entropy.
3. **Branch-summed bound $I_\Sigma^\epsilon \le Q_R$** as new physical principle, not derivable from existing holography, but conjecturally connectable to deeper quantum-gravity arguments about distinguishable record content per region.
4. **Characterization of physical Hamiltonians**, which Hermitian operators preserve $\mathcal{H}_{\rm phys}$? This is analogous to characterizing gauge-invariant Hamiltonians in gauge theory.
5. **Born statistics from typicality** under the constrained dynamics, the typicality theorem for which single-record state is realized per run, with the realization measure reproducing Born weights $|c_k|^2$.

Each of these is a concrete open mathematical problem; together they constitute the framework's explicit research program beyond the borrowed CPW/Witten scaffolding.

**Why this dissolves the MWI tension.** Under the Branch-Summed Superselection Postulate (Theorem 6), the framework escapes the MWI-without-many-worlds problem cleanly:

- The unconstrained Hilbert space contains states with multi-record macroscopic content; these are mathematically writeable but not in $\mathcal{H}_{\rm phys}$
- Physical states (those in $\mathcal{H}_{\rm phys}$) have $I_\Sigma \le Q_R$ for every bounded region; with $I_0 \approx Q_R$ at macroscopic scales, this means single-record per region
- The "Everett branches" are mathematical artifacts of considering unrestricted Hilbert-space states; the actual physical state space excludes them by the superselection rule
- We don't need to "select" one branch from many physically real branches, there are no multi-branch physical states to select from

The framework's single-world per run is therefore a *kinematic structural feature* of the physical state space, not a dynamical selection event. The superselection rule is what makes this true.

**Why this is genuinely new physics beyond Witten/CPW.** Witten/CPW provide the Type II algebraic infrastructure for regional generalized entropy. They do *not* establish:
- The branch-summed bound as a strengthening of standard holographic entropy
- The constraint that physical Hamiltonians preserve $\mathcal{H}_{\rm phys}$
- The exclusion of multi-record states as kinematically forbidden

These are the framework's specific new physical principles, building on the Witten/CPW scaffolding. They constitute a concrete research program: define the branch-summed cost rigorously; postulate the Branch-Summed Bound as new physics; characterize the constrained dynamics; derive Born statistics from typicality within the constrained dynamics.

### 7.7 Theorem (No-signaling from modular-local admissibility)

**Non-selective-instrument convention.** All operations used in the no-signaling argument below are deterministic *non-selective* channels, i.e., instruments enter only through their sum $\mathcal{I} = \sum_a \mathcal{I}_a$. Selective conditional states $\omega_a$ are admissibility-checked branchwise (cf. §7.6 Definition (Physical instruments)), but **postselection on the outcome label $a$ is not an operation available for spacelike signaling**; it becomes operational only once the outcome record is classically available in the common future. Without this restriction, even ordinary Born probabilities can be made to "signal" by postselecting on rare outcomes; with it, no-signaling reduces cleanly to algebraic commutation.

**Theorem 7 (No-signaling).** *Let $D_A, D_B$ be spacelike-separated causally complete regions with $[\hat{\mathcal{A}}(D_A), \hat{\mathcal{A}}(D_B)] = 0$. Let $\{\Phi_a^x\}$ be a normal CP instrument localized in $\hat{\mathcal{A}}(D_A)$ with setting $x$ and outcomes $a$, and let $\{\Psi_b^y\}$ be similarly localized in $\hat{\mathcal{A}}(D_B)$. Under the Modular-Local Holographic Superselection Rule (§7.6) and the non-selective-instrument convention above, Alice's marginal probability is independent of Bob's setting:*
$$
P_{\rm QIQT}(a \mid x, y) \;=\; P_{\rm QIQT}(a \mid x).
$$

*Proof.* Bob's nonselective channel is $\Psi^y = \sum_b \Psi_b^y$, localized in $\hat{\mathcal{A}}(D_B)$ by construction. By locality of this deterministic channel (i.e., $\Psi^{y*}$ is implemented by operators in $\hat{\mathcal{A}}(D_B)$, equivalently it acts trivially on $\hat{\mathcal{A}}(D_B)'$) together with microcausality $[\hat{\mathcal{A}}(D_A), \hat{\mathcal{A}}(D_B)] = 0$, the Heisenberg dual $\Psi^{y*}$ acts as the identity on Alice's algebra:
$$
\Psi^{y*}(X) \;=\; X \qquad \forall X \in \hat{\mathcal{A}}(D_A).
$$

Alice's outcome effect is $E_a^x = \Phi_a^{x*}(\mathbf{1}) \in \hat{\mathcal{A}}(D_A)$. Therefore:
$$
P_{\rm QIQT}(a \mid x, y) \;=\; \omega\!\left(\Psi^{y*}(E_a^x)\right) \;=\; \omega(E_a^x),
$$
which is manifestly independent of $y$.

The admissibility predicate does not alter this conclusion, because (§7.6) admissibility on spacelike-separated regions is the *meet of local predicates*: $\mathrm{Adm}(D_A \cup D_B) = \mathrm{Adm}(D_A) \wedge \mathrm{Adm}(D_B)$. Alice's local admissibility predicate $\mathrm{Adm}(D_A)$ depends only on $\omega|_{\hat{\mathcal{A}}(D_A)}$, which Bob's nonselective operation does not affect. Hence Alice's branch admissibility cannot depend on $y$. $\blacksquare$

**Remarks.**

1. The proof uses *only* microcausality $[\hat{\mathcal{A}}(D_A), \hat{\mathcal{A}}(D_B)] = 0$, which is the bedrock of relativistic AQFT. It does *not* assume tensor factorization $\mathcal{A}(D_A \cup D_B) \cong \mathcal{A}(D_A) \,\bar\otimes\, \mathcal{A}(D_B)$, which Type III local QFT generally lacks because of vacuum boundary entanglement.

2. The key structural feature is that the admissibility predicate is a **local subfunctor** of the AQFT state functor: $\mathrm{Adm}(D) \subseteq \mathrm{States}_{\rm normal}(\hat{\mathcal{A}}(D))$ is defined entirely from data on $\hat{\mathcal{A}}(D)$, with no joint-region cutoff. Imposing a hard cutoff on the joint relative entropy $S_{\hat{\mathcal{A}}(D_A) \vee \hat{\mathcal{A}}(D_B)}(\omega \| \Omega)$ would *not* satisfy the modular-local form and would re-introduce signaling, because the vacuum is not a product state across spacelike boundaries (the difference between joint and additive relative entropies is precisely the mutual-information / boundary-entanglement contribution).

3. **Joint causal diamonds containing record-comparison events** ($D_{AB}$ containing both Alice's and Bob's records, encountered when records meet in a common future) carry their own capacity $C(D_{AB})$ and their own modular-local admissibility predicate $\mathrm{Adm}(D_{AB})$, which constrains the *single* algebra-state pair $(\hat{\mathcal{A}}(D_{AB}), \omega|_{D_{AB}})$. No additional cross-coupling is imposed. The admissibility of the joint record is the relative entropy of the joint state on the joint algebra, not a sum of separate Alice-cost plus Bob-cost.

4. **Operational rule on instruments**, not on branches: a physical instrument $\{\Phi_a^x\}$ must be branchwise admissibility-preserving, if $\omega \in \mathrm{Adm}(D)$, then for every nonzero branch $a$ the post-outcome state $\omega \circ \Phi_a^* / \omega(\Phi_a^*(\mathbf{1}))$ must also be in $\mathrm{Adm}(D)$. Inadmissible outcomes are not produced because the dynamics that would produce them is not a physical operation, *not* because branches are postselected away after the fact. This preserves the superselection (kinematic-exclusion) flavor of the framework.

This theorem retires the earlier no-signaling concern arising from joint-comparison-diamond admissibility. An explicit Bell-style counter-example with hard joint-diamond cutoff and asymmetric record costs motivated the modular-local reformulation; the meet-of-local-predicates structure resolves it.

---

## 8. The Bekenstein-Bousso Bound and the Literal Reading

### 8.1 The bound's pedigree

Bekenstein (1981), 't Hooft (1993), Susskind (1995), Bousso (2002), and most recently Banks (2025) and the CPW (2022) Type II construction. The bound has multiple independent motivations across the quantum-gravity literature.

The numerical scale: $Q_R \sim 10^{70}$ nats for a one-meter region, $\sim 10^{122}$ for the observable universe. Astronomically large, but finite, and area-law.

### 8.2 The literal reading as the natural reading

The historical conflation of "the holographic bound" with "an entanglement-entropy inequality on a fictitious tensor factorization" is an artifact of working in finite-dimensional toy models or in spin-chain QFTs where Hilbert-space factorization is artificially imposed.

In genuine continuum QFT, local algebras are Type III$_1$. There is no entanglement entropy of a region's reduced state; there is no reduced state. The narrow interpretation is mathematically ill-defined.

The literal interpretation, that the bound limits the total physical information content of regional states in the algebraic sense, is the mathematically natural reading once the Type II crossed-product construction is recognized as the rigorous home of regional generalized entropy.

(FQ) is then a precise mathematical statement: the renormalized entropy on $\hat{\mathcal{A}}(R)$ is bounded by $Q_R$.

### 8.3 Wald and higher-derivative corrections

For modified gravitational theories, the bound generalizes via the Wald entropy. The Type II framework extends naturally: the trace on the regional algebra is determined by the gravitational theory, and $Q_R$ takes the Wald form $A f'(R)/(4\ell_P^2)$ for $f(R)$ gravity.

---

## 9. Possible Phenomenological Consequences

### 9.1 Laboratory regime: no deviations

At ordinary laboratory scales, $Q_R$ is astronomically large, and the resolution structure of the Type II algebra is fine relative to the macroscopic record structure of any laboratory apparatus. The framework predicts no deviations from standard QM in standard laboratory experiments. The role of (FQ) at lab scales is structural, it provides the resolution that makes per-run states physically single-record.

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

Bohm adds particle positions in $3N$-dim configuration space as a *second ontological layer* beyond the wave function, with a guidance equation connecting the two. The framework adds *no second ontological layer*. We are **ψ-monist**: the wave function is the only ontology. The per-run wave function is simply the actual physical wave function of the universe in any specific run; the formal wave function is the textbook ensemble descriptor. No particles, no fields, no extra structure, the distinction the framework adds is between the formal wave function (ensemble) and per-run wave function (actual), not between the wave function and some other physical thing.

### 10.4 Objective collapse (GRW, CSL, DP, OR)

Modify Schrödinger with collapse terms. We modify nothing dynamical. The Schrödinger evolution of the underlying field algebra is exactly unitary; the regional physical content is structurally single-record after concentration via the Type II algebra structure.

### 10.5 QBism, relational quantum mechanics

Treat the wave function as epistemic / perspectival. We are objectively realist: the per-run wave function is real, the (FQ) constraint is real, the Type II algebra structure is real, the regional states are real physical states.

### 10.6 Modal interpretations, decoherent histories

Introduce a modal value-rule or history-selection structure. We require neither. The Type II algebra has finite resolution intrinsically; concentration + this resolution yield single records without external value-rules.

### 10.7 Ensemble interpretations (Ballentine)

The closest neighbor. Ballentine treats the formal wave function as ensemble-descriptive with per-run states underdetermined. We supply the mechanism: the Type II regional algebra structure makes per-run states physically single-record despite the formal wave function's superposed appearance.

### 10.8 Palmer's Rational Quantum Mechanics / Invariant Set Theory (sister program)

Palmer's Rational Quantum Mechanics (RaQM 2025, PNAS) and the broader Invariant Set Theory (IST) program is the closest neighbor in the space of *single-world, structural-principle, measurement-dependent* frameworks. Both Palmer and the present framework reject Bell's measurement-independence assumption on principled grounds (not as conspiratorial superdeterminism); both treat the wave function as not exhausting the per-run physical content; both seek to ground the measurement problem's resolution in a deep structural feature of physics rather than in collapse, branching, or particle ontology.

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

The (FQ) literal reading framework is uniquely characterized by a **finite physical resolution structure from the holographic bound**: the wave function as a physical state of spacetime has finite specification precision; amplitudes within precision of 0 or 1 are physically equivalent to exact 0 or 1; combined with decoherence and microscopic initial conditions, this yields a single-record per-run wave function structurally, without collapse, without modified dynamics, without hidden particles, without branches. The CPW Type II algebra framework provides the rigorous mathematical infrastructure; the literal physical-instantiation reading of the bound is the additional foundational postulate that does the work.

---

## 11. Conclusion

### 11.1 Summary

We have developed a foundational framework for quantum mechanics that combines two ingredients: (a) the algebraic-QFT-plus-gravitational-dressing framework of Chandrasekaran-Penington-Witten and Witten, providing the rigorous mathematical infrastructure for finite renormalized entropy on bounded regions; and (b) the *literal physical-instantiation reading* of the Bekenstein-Bousso bound (postulated as axiom (FQ)), that the wave function as a physical state of spacetime has finite physical specification precision determined by the holographic bound on the region.

The structure rests on:

1. **The CPW/Witten algebraic infrastructure (borrowed).** Local algebras in QFT with gravitational dressing are Type II with semifinite trace and well-defined renormalized entropy differences matching generalized entropy. This provides the rigorous algebraic home for the bound.

2. **The (FQ) axiom in its literal physical-instantiation reading (our postulate).** The wave function in any bounded region $R$ is a physical state of spacetime with finite physical information capacity $Q_R = A(\partial R)/(4\ell_P^2)$. Amplitudes have finite physical specification precision $\epsilon(R) > 0$; below the precision, distinct mathematical wave functions are the same physical state. The literal reading goes beyond Witten's algebraic theorem, Witten supplies the mathematical scaffold; the literal physical-instantiation reading is an additional foundational interpretation.

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

> The Bekenstein-Bousso holographic bound, taken literally as a Lorentz-invariant physical information limit on bounded regions of spacetime, motivates a stronger physical postulate: the **Branch-Summed Holographic Bound**, which constrains the sum of per-record costs across coexisting decoherent macroscopic record sectors of any bounded region by the holographic capacity $Q_R$. This bound is a **superselection rule on the physical state space** $\mathcal{H}_{\rm phys}$: universal wave functions whose induced regional states violate the bound are not physically realizable. Physical Hamiltonians are constrained to preserve $\mathcal{H}_{\rm phys}$ (analogous to gauge invariance in gauge theory). Within $\mathcal{H}_{\rm phys}$, Schrödinger / Heisenberg evolution is preserved exactly under physical Hamiltonians. The Born rule is preserved exactly. The macroscopic world, single-record per region per run, emerges as a *kinematic structural consequence* of the superselection rule, not as a dynamical selection event. No collapse, no hidden particle positions, no MWI branches, no modal value-rule are added; the framework is **ψ-monist** (wave function as only ontology) with the physical state space constrained by the Branch-Summed Holographic Bound. Born statistics across runs emerge from typicality of actual initial conditions of actual runs, propagated through the constrained dynamics. The CPW Type II crossed-product algebra framework provides the rigorous mathematical infrastructure; the Branch-Summed Holographic Bound is the framework's new physical principle on top, a strengthening of standard holography that is not derivable from existing QG results but is conjecturally connectable to deeper finite-information constraints on regional macroscopic record content.

### 11.4 Open problems

The Lean audit work (see `lean/mathlib/QIQTH/` and the formal-verification footnote in the abstract) has sharpened the boundary between what the framework derives from FQ + AQFT + holography and what remains as load-bearing additional commitments. The open problems are reorganized here to reflect that sharpened boundary, with the Born / canonical-measure problem promoted to first position as the most central remaining commitment.

**Open Problem 1 — Canonical IC Measure Principle (the central Born/typicality problem).**

This problem decomposes naturally into six layers, each requiring different kinds of work. The decomposition is based on a closing audit (`lean/mathlib/QIQTH/AxiomAudit.lean` + GPT-5.5-pro consultation) that distinguishes what is mathematically derivable from what is genuinely open physics from what is irreducible empirical calibration.

**Goal.** Specify, for each preparation state $\rho$, a measure $\mu_\rho$ on the QIQT-H microscopic-IC space $\Omega_\rho$ (alternatively: a typicality structure on the FQ-restricted physical Hilbert space) satisfying:
   (a) **Canonicality** — defined from QIQT-H primitives, not fitted per measurement;
   (b) **Born pushforward** — $(O_M)_* \mu_\rho(i) = \mathrm{tr}(\rho E_i)$ for every allowed measurement protocol $M$ with effects $\{E_i\}$;
   (c) **Equivariance / stationarity** — preserved by the (FQ)-restricted physical Hamiltonian;
   (d) **Repeated-trial typicality** — supports iid / exchangeable / stationary-ergodic frequency theorems;
   (e) **Measurement-setting independence** — $\mu_\rho$ does not depend on the measurement context (unless the theory explicitly accepts contextual / measurement-dependent typicality);
   (f) **Uniqueness / stability** — robust under coarse-graining and equivalent IC descriptions.

Machine-verified audits flag the difficulty: `NoBornFromNothing.lean` (any distribution realizable; the structural axioms do not pick out Born), `EquivarianceGap.lean` (support preservation $\neq$ Born equivariance), `OperationalNoGo.lean` (operational frequency data alone insufficient). The independence package `BornMinimalityTable.lean` re-exports these three countermodels and shows that the locality premise is *not* an independent Born-selection sub-axiom — its marginal-level content is a theorem holding for any measure (`MarginalLocality.pushforward_marginal_local`), modulo a named Hilbert→set-level bridge axiom (§11.4.5). Relative to the current finite formal decomposition, the Canonical IC Measure Principle's irreducible Born-selection content is three named sub-axioms (canonical measure, equivariance, operational sufficiency), each provably necessary by concrete finite countermodel — alongside the two acknowledged operator-algebra interface axioms (Schur classification, tensor multiplicativity) that the Born representation itself rests on.

#### 11.4.1 Formal Born representation theorem (Mackey-Gleason + noncommutative Radon-Nikodym)

**The mathematical core.** For a normal probability measure on the projection lattice of a von Neumann algebra without Type $I_2$ summand, Mackey-Gleason (Bunce-Wright 1990s, extending classical Gleason 1957) gives a unique normal state extension. Combined with the noncommutative Radon-Nikodym theorem (Sakai 1971; Takesaki vol. II), this yields the trace-density form
$$\mu_\rho(P) = \tau(D_\rho \cdot P)$$
on semifinite vN algebras with faithful normal trace $\tau$.

**Caveats to be explicit about:**
- **No bare qubit Gleason**: classical Gleason has a $d=2$ exception. The fix is Busch's POVM-Gleason theorem (2003) extending the result to all effects (Busch, Caves-Fuchs-Manne-Renes 2004).
- Normality / σ-additivity vs finite additivity assumptions.
- Complex Hilbert spaces (real/quaternionic variants require separate treatment).
- Factor vs non-factor center (superselection sectors).
- PVM-only vs POVM/effect-level Born rule.
- Exclusion of singular states.

**Lean status:** Sub-theorem A (`TypicalityMackeyGleason.lean`) packages the Mackey-Gleason + noncommutative Radon-Nikodym implication as a conditional theorem. The interface axioms are well-defined Mathlib-formalization tasks (multi-week for the full vN-algebraic version; tractable in finite dimensions).

#### 11.4.2 Existence and canonicality in finite factors (Type $II_1$)

**Standard mathematical existence (NOT open).** For a finite Type II factor $M$ with faithful normal tracial state $\tau$, the construction
$$\mu_\rho(p) = \tau(\rho \cdot p), \quad \rho \in L^1(M, \tau)_+, \quad \tau(\rho) = 1$$
yields a normal probability measure on the projection lattice $\mathrm{Proj}(M)$. Positivity, normalization, orthogonal additivity, normality, and unitary covariance are all standard theorems. **In a $II_1$ factor, the trace $\tau$ is the unique normal state invariant under all inner unitaries** — so canonicality under unitary invariance is *not* an open problem; it is a consequence of factor structure.

**What remains open in $II_1$:** none of the *mathematical* existence; only the (genuinely open) question of canonical *physical selection* — what makes a particular $\rho$ correspond to a particular preparation. That is the empirical calibration step (§11.4.4 below).

**Lean status:** This is a Lean formalization gap, *not* an open math problem. The construction can be formalised directly given the requisite vN-algebra infrastructure in Mathlib.

#### 11.4.3 Infinite trace and Type $II_\infty$ — a sharp obstruction

**The obstruction.** For a Type $II_\infty$ factor with semifinite trace $\tau$, the trace satisfies $\tau(1) = \infty$. Therefore the trace itself is a *weight*, not a probability state. There is **no normalized normal state on a $II_\infty$ factor invariant under all unitaries**.

Concretely: one cannot define a "canonical uniform" probability measure $\mu(p) = \tau(p)$ in $II_\infty$; the candidate is not normalizable.

**Options for the QIQT-H Type II setting:**
1. Choose a density $\rho$: $\mu_\rho(p) = \tau(\rho \cdot p)$ with $\rho \in L^1(M, \tau)_+$ and $\tau(\rho) = 1$. The measure exists; canonicality requires an additional principle to select $\rho$ for a given physical preparation.
2. Restrict to a finite corner $eMe$ with $\tau(e) < \infty$: recovers the $II_1$ analysis above on the corner.
3. Use semifinite *typicality weight* rather than probability measure — appropriate if the framework adopts a non-probability typicality reading.
4. Provide additional physical selection principles (canonical sector reference state, modular structure, holographic origin).

**Lean status:** Sub-theorem A's interface (Mackey-Gleason + RN) applies to $II_\infty$; the obstruction is *physical canonicality*, not formal existence of $\mu_\rho$.

#### 11.4.3a Type III caveat (AQFT local algebras)

**A non-trivial caveat.** AQFT local algebras of bounded regions are typically Type $III_1$, not Type II (Buchholz, Borchers, Longo; see foundations paper §3). The QIQT-H framework uses the CPW Type II crossed-product construction (CPW 2022, Witten 2022) precisely to *escape* Type III to a well-defined entropy structure. But:

- **There is no trace-density picture in Type III.** Normal states still give projection probabilities $\phi(p)$, but the formula $\phi(p) = \tau(\rho \cdot p)$ has no analog in Type III (no trace).
- The relationship between the underlying Type III local algebras and the crossed-product Type II algebras is mediated by the modular flow of the canonical sector reference state $\sigma_R$.
- The Born representation problem in Type III is structurally different and requires either passing through the Type II crossed product or using Connes' spatial derivative / Haagerup's $L^p$-space construction.

**Open:** make explicit how the Type II crossed-product trace-density picture relates to the underlying Type III local-algebra structure — particularly whether the canonical IC measure $\mu_\rho$ on the Type II core has a natural Type III pullback.

#### 11.4.4 Operational calibration — split into derivable and irreducible parts

**Splitting the calibration step.** The "measurement-calibration" step (often informally called "the Born content bridge") is actually two parts:

- **(4a) Mathematical restriction (derivable).** If $A \cong M_d(\mathbb{C})$ is a finite-dimensional measurement subalgebra of a Type II factor and $\phi$ is a normal state, then $\phi|_A(a) = \mathrm{tr}_d(\rho_A \cdot a)$ for a unique ordinary $d \times d$ density matrix $\rho_A$. If the embedding is trace-preserving, the Type II trace restricts to the normalized matrix trace on $A$. *This is standard mathematics.*

- **(4b) Empirical calibration (irreducible).** The identifications:
  - this detector $\leftrightarrow$ this projection / effect;
  - this preparation $\leftrightarrow$ this density;
  - this pointer event $\leftrightarrow$ this subalgebra;
  - this finite-dimensional operational model $\leftrightarrow$ the right model of the actual lab.
  
  Operational reconstructions (Hardy 2001; Chiribella-D'Ariano-Perinotti 2011; Masanes-Müller 2011; Brukner-Zeilinger) derive the Born pairing from operational axioms — but the axioms themselves are physical/empirical inputs. *Calibration is not eliminated; it is relocated.*

**The irreducible part is small but real.** Any deterministic theory needs (4b). It is the analog of the bridge from Liouville measure to thermodynamic ensembles in classical statistical mechanics.

**POVMs and instruments.** Modern operational treatments use POVMs (effects) rather than PVMs (projections). For sequential measurements and state update, Davies-Lewis / Ozawa instruments are the appropriate framework. The QIQT-H paper should include POVM formulations in §7.6 and §7.7 to avoid the bare-qubit Gleason exception.

#### 11.4.5 Dynamics, equivariance, and locality

The conditional Born typicality theorem (`BornTypicality.lean`) requires three additional physical inputs:

- **Equivariance theorem.** If $\rho_t = U_t \rho_0 U_t^*$ under FQ-restricted unitary dynamics, then $\mu_{\rho_t}(p) = \mu_{\rho_0}(U_t^* p U_t)$. For QFT-style Hamiltonians, this requires careful treatment of domain / self-adjointness issues. The `EquivarianceGap.lean` audit establishes that support preservation (the framework's current claim) is strictly weaker than measure preservation.

- **Projection locality.** Need precise assumptions on the local algebraic structure: tensor product factorisation (or its absence in Type III), commuting local algebras (microcausality), split property, finite corners. The `CompressionLocality.lean` audit isolates the compression-locality leakage identity and identifies when the FQ projection preserves microcausality at the restricted level. *Post A1 strengthening* (`MarginalLocality.pushforward_marginal_local`): given set-level locality of Bob's dynamics ($r\circ T = r$), the Alice-marginal is invariant for **any** IC measure — with no equivariance assumption — so locality of the marginal is a theorem, not a separate Born-selection postulate. This reduction is, however, *conditional* on a named Hilbert→set-level locality bridge axiom (`set_level_locality_from_unitary_dilation`, a standard Heisenberg↔Schrödinger correspondence): locality has been relocated into that explicit bridge, not eliminated. Subject to that caveat, locality is no longer counted among the independent Born-selection sub-axioms of the Canonical IC Measure Principle.

- **Empirical frequency bridge.** If μ is interpreted as typicality (rather than primitive probability), one needs a DGZ-style step from typical initial configurations to observed frequencies. The `BornTypicality.lean` module formalizes this conditionally via standard finite LLN.

#### 11.4.6 Typicality vs probability

**The conceptual framing.** QIQT-H is fully deterministic; the "measure" $\mu_\rho$ is a *typicality structure* on the microscopic-IC space (à la Dürr-Goldstein-Zanghì 1992 in Bohmian mechanics), not a primitive probability assignment. The candidate routes for canonicality (§7.4 α/β/γ) are typicality principles, not probability axioms.

**Caveats and references:**
- **Frequency concentration (PROVED, single-trial + independence step).** The Lean module `BornConcentration.lean` proves Chebyshev's tail bound on finite probability spaces ($\Pr(|X-\mu| \ge \varepsilon) \le \mathrm{Var}/\varepsilon^2$), computes the Bernoulli variance ($p(1-p)$), proves the variance-addition (independence) lemma `variance_add_of_product` (variance of a sum of independent variables equals the sum of variances), and combines these to give the single-trial concentration inequality and the two-trial Bernoulli variance $2p(1-p)$. *What is proved:* the single-trial Chebyshev bound and the reusable variance-addition lemma the $N$-fold induction would iterate. *What remains axiomatic:* the full $N$-trial product-measure scaling $\Pr(|\mathrm{freq}_N - p| \ge \varepsilon) \le p(1-p)/(N\varepsilon^2)$ rests on the LLN interface axiom in `BornTypicality.lean`. Accordingly the framework's frequency statement ("Born *frequencies*", not merely "Born *means*") is established up to that single named scaling axiom — for which the per-trial variance and the independence step are now both in hand.
- **Goldstein-Struyve uniqueness** (J. Stat. Phys. 128, 1197, 2007): in Bohmian mechanics, $|\psi|^2$ is the unique local equivariant typicality density. The adaptation to QIQT-H's Type II + (FQ) setting is precisely the multi-week mathematical task of Sub-theorem C.
- **Valentini nonequilibrium** (1991, 2002; Valentini-Westman 2005): there exist non-Born typicality measures whose dynamics relaxes (or fails to relax) to equilibrium. This is the principled objection to "canonical = equivariant" — equivariance is necessary but may not be sufficient without an additional relaxation argument.
- **Noncontextuality** in this deterministic-with-typicality setting refers to the equilibrium probability assignment to quantum effects (Spekkens 2005 generalised noncontextuality), *not* to noncontextual pre-existing values (which Kochen-Specker rules out in $d \ge 3$).

#### 11.4.7 Independence / minimality of the remaining sub-axioms

Per GPT-5.5-pro's sixth audit, the honest Born claim is not "Born is derived from holography alone" — `NoBornFromNothing` refutes that — but rather:

> *Born is the unique admissible measure given a NAMED minimal set of additional postulates, and each postulate is INDEPENDENT — dropping any one yields a finite countermodel where Born fails.*

The independence package `BornMinimalityTable.lean` makes this explicit. Relative to the current finite formal decomposition, the Canonical IC Measure Principle has three irreducible Born-selection sub-axioms, each with a concrete finite countermodel witnessing its necessity (with the locality premise reducible, modulo the named bridge axiom of §11.4.5):

| Tag | Premise | Minimality witness (Lean module) | Countermodel size |
|---|---|---|---|
| P1 | Canonical IC measure (some structurally-distinguished $\mu$ is selected) | `NoBornFromNothing.any_anti_born_realizable` | $\Gamma$ arbitrary finite |
| P2 | Measure equivariance under FQ-restricted dynamics | `EquivarianceGap.support_preservation_does_not_imply_…` | $\mathrm{Fin}\,2$ swap |
| P3 | Operational sufficiency (click-statistics determine IC marginal) | `OperationalNoGo.operational_data_insufficient` | $\mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ |
| P4 | Locality of Alice's marginal under Bob's local dynamics | **REDUCIBLE** — proved as a theorem holding for *any* measure (`MarginalLocality.pushforward_marginal_local`), conditional on the named Hilbert→set-level bridge axiom (§11.4.5) | (not an independent Born-selection axiom) |

This converts the standing concern "you still assume X" into a sharper audit conclusion: X is *necessary*. Relative to the current finite formal decomposition, the irreducible Born-selection premise set is $\{P1, P2, P3\}$ (down from four, once the marginal-locality step is theoremized modulo its bridge axiom); each premise has a finite-dimensional countermodel; and Born follows uniquely when all three hold together with the two acknowledged interface axioms (Schur classification, tensor multiplicativity) and the operator-algebraic Mackey-Gleason / Radon-Nikodym input. This is the strongest honest statement available without resolving Sub-theorems A and C as theorems-in-Mathlib; it is a *minimality relative to this decomposition*, not a proof that no coarser axiom set could suffice.

#### Combined: what is and is not open

| Layer | Item | Status |
|---|---|---|
| 11.4.1 | Mackey-Gleason + RN representation theorem | Standard math; Mathlib formalisation gap (multi-week) |
| 11.4.2 | Existence in finite Type II ($II_1$) | Standard math; Lean formalisation gap (constructive) |
| 11.4.3 | Canonical normalised probability state on $II_\infty$ | **Sharply obstructed**; requires density or finite corner or additional principle |
| 11.4.3a | Type III ↔ Type II crossed-product correspondence for IC measure | Open; mathematically non-trivial |
| 11.4.4a | Type II → finite-dim restriction (math) | Standard math |
| 11.4.4b | Empirical lab-to-formalism calibration | Irreducible empirical bridge (no derivation in any framework eliminates it) |
| 11.4.5 | Equivariance theorem under FQ-restricted Hamiltonian | Open; requires concrete FQ-Hamiltonian + self-adjointness analysis |
| 11.4.6 | Justification of typicality framing (Goldstein-Struyve adaptation; Valentini relaxation) | Open; multi-year research direction |
| 11.4.6 | Born **frequency** concentration (single-trial Chebyshev) | **PROVED** in `BornConcentration.born_chebyshev_single_trial`; $N$-trial scaling at LLN axiom interface |
| 11.4.7 | Independence/minimality of P1, P2, P3 by finite countermodel | **PROVED** in `BornMinimalityTable.lean` |
| 11.4.7 | Reducibility of locality (P4): marginal-locality step proved for *any* measure | **PROVED** in `MarginalLocality.pushforward_marginal_local`; reduction conditional on the named Hilbert→set bridge axiom |

**Bottom line.** The Canonical IC Measure Principle is **not** a monolithic mystery. The hard parts are: the $II_\infty$ canonicality obstruction (11.4.3); the Type III correspondence (11.4.3a); the equivariance theorem for FQ-restricted dynamics (11.4.5); and the typicality justification (11.4.6). The mathematical core (11.4.1, 11.4.2, 11.4.4a) is standard given operator-algebra infrastructure; the empirical calibration (11.4.4b) is irreducible. **After the A1+A2+A4+A6 strengthening pass:** the marginal-locality step is theoremized (for *any* measure, no equivariance assumed) so locality is no longer an independent Born-selection sub-axiom — modulo a named Hilbert→set-level bridge axiom into which the locality content is relocated, not eliminated; relative to the current decomposition the irreducible Born-selection set has three named members (P1/P2/P3), each provably necessary by concrete finite countermodel; and single-trial Born frequency concentration plus the variance-addition (independence) lemma are proved, with the $N$-trial scaling to full frequency convergence still resting on the named product-measure LLN axiom. These are minimality and reduction results *relative to this formal decomposition*, not claims that the underlying operator-algebra interface axioms (Schur classification, tensor multiplicativity, Mackey-Gleason/Radon-Nikodym) have been discharged.

**Open Problem 2 — Reference-weight bound (sharpened H2).**
The record-instantiation-cost postulate (H2 in Theorem 6) is *equivalent* to the reference-weight bound $\sigma_R(E_{\rm record}) \le \exp(-(I_0 - \eta_0))$ on macroscopic pointer sectors (see §7.6 Sharpening of (H2); formalized in `lean/mathlib/QIQTH/H1H2Audit.lean`). Derive this reference-weight bound from modular / holographic first principles, as a strengthening of standard Bekenstein-Bousso. Donald's identity + Klein positivity + DPI alone are insufficient. This is genuinely new physics; progress here feeds directly into Open Problem 3.

**Open Problem 3 — Concentration Conjecture.**
Per-run amplitudes for distinct macroscopic record components evolve dynamically toward 0 or 1 under decoherence + microscopic IC + FQ. Currently argued qualitatively with numerical scaling; not yet a formal theorem. A machine-verified audit (`NoConcentration.lean`) confirms that *linear unitary decoherence alone* cannot produce concentration; the framework's position requires (FQ) literal truncation + microscopic-IC selection to jointly do the work. Make this mechanism a theorem.

**Open Problem 4 — Quantitative form of $\epsilon(R)$.**
The (FQ)(iii) resolution floor satisfies $\epsilon(R) > 0$ (Theorem 3; formalized in `Resolution.lean`). Derive an explicit functional form $\epsilon(R) = f(\text{geometry}, Q_R, \text{macroscopic record dimension})$ tying the framework to numerical predictions. Downstream of Open Problems 2 and 3.

**Open Problem 5 — Empirical calibration of $I_0$.**
The per-record physical cost $I_0$ is a phenomenological parameter, analogous to GRW's collapse rate $\lambda$. Current best estimates (Zurek physical entropy for typical macroscopic records) give $I_0 \sim 10^{25}$ bits. The framework's prediction: a definite calibrated value of $I_0$ such that the saturation condition $I_0 \approx C(R)$ matches the observed quantum-to-classical transition. Downstream of Open Problem 4.

---

**Algebraic / mathematical-physics infrastructure:**

6. **Operational distinguishability axiomatization (H3).** Make precise, under decoherence + Quantum Darwinism, when the macroscopic-record subalgebra admits a normal measurement instrument decoding the record index with small error, so that the Fano-type bound $H_\epsilon \le I_{\rm Hol}^R + \eta_{\rm def}$ holds. Existing ingredients: spectrum broadcast structure (Zurek, Brandão-Piani-Horodecki), redundancy plateaus, decoherent-histories medium-decoherence conditions.

7. **Stagewise adapted process and refinement compatibility.** Construct rigorously the stagewise process $h \mapsto \omega_t^h$ of §7.6, including: existence under Cauchy-slice refinement; compatibility of $\mathfrak{R}_t(h)$ with the AQFT net's isotony; conditions under which the adapted family extends to a completed-history limit.

8. **Functorial / isotonic crossed-product local nets.** Establish the functorial structure $D \mapsto \hat{\mathcal{A}}(D)$ as a covariant net of Type II crossed-product algebras with normal embeddings under inclusion. Needed for the modular-local bound to behave consistently under region refinement / coarse-graining.

9. **Modular-Hamiltonian estimates beyond wedges and CFT balls.** Generalize the wedge / CFT-ball modular-Hamiltonian estimate to broader classes of regions, either via tighter enclosing-wedge monotonicity arguments or new geometric forms of $K_R^\sigma$. Without this the conditional $\delta_R \sim 10^{-27}$ estimate cannot be extended to generic laboratory geometries.

10. **State-extension and reference-state issues** in the crossed-product algebra formulation: extension of states across causal-diamond boundaries, choice of $\sigma_R$ in cosmological / non-stationary backgrounds.

11. **Locality of the (FQ)-restricted dynamics.** The (FQ) projection onto $\mathcal{H}_{\rm phys}$ must commute with the local algebras' observables for Theorem 7's no-signaling argument to apply to the *restricted* (physical) theory rather than only the ambient (unrestricted) theory. The compression-locality leakage identity (formalized in `CompressionLocality.lean`) isolates this implicit constraint. Construct concrete (FQ) projections satisfying it; characterize the class of admissible projections.

**Empirical / phenomenological:**

12. **Concrete measurement-apparatus models realizing finite $\chi_R$ budgets.** Build explicit toy models (Stern-Gerlach, interferometer, optomechanical) where $\chi_R$ for the apparatus-record state is computable and the saturation regime can be approached. Without these the framework's content cannot be confronted with experiment.

13. **Phenomenological predictions.** With $I_0$ calibrated, the framework predicts: maximum macroscopic-superposition scale (testable against Schrödinger-cat experiments with progressively larger systems); long-baseline coherence limits; specific signatures distinguishing the framework from GRW-style stochastic collapse (the framework predicts kinematic exclusion, not stochastic events).

14. **Cosmological / horizon applications**, extend to the de Sitter static patch and black-hole horizon regions, where $C(R)$ becomes finite and saturation may be physically relevant.

---

**Strategic note.** Of the central open problems, the audit work suggests two bottleneck chains:

  • **Foundations bottleneck:** Open Problem 1 (canonical $\mu$-selection / equivariance). Now decomposed into three sub-theorems A, B, C (see above), with the A1+A2+A4+A6 strengthening pass further narrowing the load-bearing content. Two of the three sub-theorems are direct applications of existing operator-algebra machinery (Mackey-Gleason + noncommutative Radon-Nikodym); the third requires adapting the Goldstein-Struyve 2007 uniqueness theorem from Bohmian dynamics to QIQT-H's Type II / (FQ) setting. Concrete progress: the permutation-symmetry collapse component of Goldstein-Struyve Step 1 sub-lemma 1c is **PROVED** under its necessary hypothesis (`step1c_collapse_of_perm_symmetric`) along with the foundational matrix-conjugation identities (`permutation_conj_matrixUnit`, `diagonalU_conj_matrixUnit`), while the full Schur classification remains a single named interface axiom; the marginal-locality step is **PROVED** as a theorem holding for any measure (`MarginalLocality.pushforward_marginal_local`), reducing locality to a named Hilbert→set-level bridge axiom rather than eliminating it; single-trial Chebyshev frequency concentration and the variance-addition (independence) lemma are **PROVED** (`BornConcentration`), with the $N$-trial scaling still on the LLN axiom; and the duplicate axiomatization of Goldstein-Struyve sub-steps in `FQEquivarianceUniqueness` is **CONSOLIDATED** to route through the concrete `GoldsteinStruyveFinDim` proof (`canonical_ic_measure_principle` now depends on exactly two project-specific axioms, down from nine), with the five false/unused Step-1 placeholder sub-axioms deleted (project axiom total 57 → 40). Progress on the remaining load-bearing axioms transforms the Born section from conditional to substantive, and is the most pressing problem for foundations-of-QM defensibility.

  • **Quantitative-emergence bottleneck:** Open Problem 2 (reference-weight bound) $\Rightarrow$ Open Problem 3 (Concentration) $\Rightarrow$ Open Problem 4 ($\epsilon(R)$) $\Rightarrow$ Open Problem 5 ($I_0$ calibration). Progress on Open Problem 2 unlocks the quantitative QIQT-H pipeline.

These are the two genuinely open research directions left after the Lean audit work has clarified the deductive boundary. The remaining items (6–14) are infrastructure and phenomenology that follow once the bottlenecks are addressed.

### 11.4a Claim-to-Lean theorem matrix

The following table maps each major paper claim to its Lean theorem, with explicit status. Status labels:

  • **U** — unconditional (no project-specific axioms; depends only on standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`).
  • **C** — conditional on a standard external theorem (Mathlib-citable; axiomatized at clean interface in the project).
  • **P** — programmatic interface axiom (specific framework or AQFT-level axiom; concrete Lean discharge is a multi-day to multi-week task).
  • **N** — negative audit / counterexample (proves a *non*-derivation).

| Paper claim | Lean theorem | Status | Notes |
|---|---|---|---|
| Theorem 3 (resolution floor) | `Resolution.eps_pos` | U | $\varepsilon(R) > 0$ from finite $Q_R$ |
| Lemma 1 (near-extreme indistinguishability) | `Resolution.lemma1_zero` | U | Discrete-bin formalization |
| Theorem 6 (effective definiteness) | `Theorem6.effective_definiteness` | U | Donald-bound chain |
| Theorem 6 inner step | `Theorem6.BranchData.holevo_le_capacity` | U | $I_{\rm Hol}^R \le C(R)$ from $\chi_R \le C(R)$ and Klein |
| Theorem 7 (no-signaling) | `Theorem7.Setup.no_signaling` | U | From microcausality + locality |
| Donald's identity | `Donald.donald_identity` | C | Conditional on 3 cross-entropy axioms (A1, A2, A3) |
| Microcausality ⇒ locality (unitary) | `UnitarityLocality.locality_of_conjugation` | U | StarRing argument |
| Microcausality ⇒ locality (Kraus) | `KrausLocality.kraus_channel_aliceFixing` | U | Generalization to CPTP channels |
| Bell/CHSH inequality (LHV bound) | `Bell.LHVModel.chsh_le_two` | U | Finite probability + ±1 algebra |
| Tsirelson saturation by singlet | `Tsirelson.singlet_chsh_abs_gt_two` | U | Explicit 4D real construction; attains $2\sqrt{2}$ exactly (does *not* prove the universal upper bound) |
| (H1) ⇏ (H2) | `H1H2Audit.H1_does_not_imply_H2` | N | Classical KL countermodel |
| (H2) ⇔ reference-weight bound | `H1H2Audit.H2_iff_reference_weight` | U | Sharp structural reformulation |
| Decoherence ⇏ concentration | `NoConcentration.audit_conclusion` | N | Linear unitary preserves branch weights |
| $S_{\rm ren}$ (paper) $\neq$ $S_{\rm ren}^{\rm CPW}$ | `EntropyBridge.fq_ambiguity_counterexample` | N | Classical KL counterexample distinguishing the two |
| Branch-summed cost > Shannon possible | `BranchLedger.branchSummed_not_bounded_by_Shannon` | N | Binary uniform witness |
| FQ-literal finite ⇒ trivial dynamics | `FQDynamicsNoGo.finite_admissible_flow_fixed` | U | Continuous flow on finite T2 space (only — not arbitrary finite-info dynamics) |
| Compression-locality leakage identity | `CompressionLocality.compressed_commutator_with_commute` | U | Pure ring algebra |
| Any $p$ realizable (no Born from nothing) | `NoBornFromNothing.exists_probability_realizing` | N | Concrete section-based construction |
| Support preservation $\neq$ Born equivariance | `EquivarianceGap.support_preservation_does_not_imply_measure_preservation` | N | Concrete `Fin 2` counterexample |
| Born typicality (mean form) | `BornTypicality.born_mean_conditional` | U | Conditional on canonical $\mu_\rho$ with Born marginal |
| Operational data ⇏ unique IC measure | `OperationalNoGo.operational_data_insufficient` | N | Concrete `Fin 3` witness |
| Sub-thm A (Typicality Mackey-Gleason) | `TypicalityMackeyGleason.qiqth_typicality_mackey_gleason` | C | Conditional on Mackey-Gleason + noncommutative Radon-Nikodym (standard operator-algebra theorems, axiomatized) |
| Sub-thm C (FQ-equivariance uniqueness) | `FQEquivarianceUniqueness.canonical_ic_measure_principle` | P | **Post-consolidation:** depends on exactly 2 project axioms (`GoldsteinStruyveFinDim.step1_schur_classification` + `step3_tensor_multiplicativity`), down from 9 (12 redundant abstract axioms eliminated) |
| GS Step 2 (normalization) | `GoldsteinStruyveFinDim.step2_normalization` | U | Concrete `Matrix.trace` computation |
| GS Step 4 (non-degeneracy) | `GoldsteinStruyveFinDim.step4_nondegeneracy` | U | Direct case analysis |
| GS Step 3 algebraic core | `GoldsteinStruyveStep3.step3_algebraic_core` | U | Polynomial identity via `ring` |
| GS Step 3 Kronecker bridge | `GoldsteinStruyveKronecker.step3_kronecker_bridge` | U | Concrete `d = 2` witness with E₁₁ ⊗ E₁₁ |
| GS Step 1 (Schur classification) | `GoldsteinStruyveStep1.step1_via_sub_lemmas` | P | Delegates to the single top-level interface axiom `GoldsteinStruyveFinDim.step1_schur_classification`. The five former placeholder sub-axioms (1a–1e) — three of them literally false as stated, all unused — have been **deleted**; the proved foundation lemmas `permutation_conj_matrixUnit`, `diagonalU_conj_matrixUnit`, and `step1c_collapse_of_perm_symmetric` are its concrete building blocks |
| GS Step 1c (coefficient unification, partial) | `GoldsteinStruyveStep1.step1c_collapse_of_perm_symmetric` | U | **NEW (A2):** the *permutation-symmetry collapse component* of Step 1c, proved via `Equiv.swap` transitivity under its necessary permutation-symmetry hypothesis. The prior bare-coefficient axiom (no hypothesis) was literally false and has been **deleted**. The *full* Schur classification (Step 1) remains the single named interface axiom |
| Permutation conjugation of matrix units | `GoldsteinStruyveStep1.permutation_conj_matrixUnit` | U | **NEW (A2):** $P_\sigma \cdot E_{ij} \cdot P_\sigma^* = E_{\sigma(i),\sigma(j)}$ via direct matrix-entry computation |
| Diagonal-unitary conjugation of matrix units | `GoldsteinStruyveStep1.diagonalU_conj_matrixUnit` | U | **NEW (A2):** $D(z)\cdot E_{ij}\cdot D(z)^* = (z_i\,\overline{z_j})\,E_{ij}$, self-contained diagonal parameterization (no `Complex.exp`) |
| Combined GS finite-dim theorem | `GoldsteinStruyveFinDim.goldstein_struyve_findim` | P | Proved by composition; inherits Step 1 + Step 3 axioms |
| Marginal locality (pure pushforward) | `MarginalLocality.pushforward_marginal_local` | U | **NEW (A1):** $r\circ T = r \Rightarrow r_*(T_*\mu) = r_*\mu$ for **any** $\mu$ — no equivariance assumption; reindexing argument |
| Marginal locality (equivariant corollary) | `MarginalLocality.alice_marginal_unchanged_by_bob_dynamics` | U | **NEW (A1):** thin corollary of the pure version; discharges the *marginal-locality step* (not the Hilbert→set bridge, which stays a named axiom) |
| Chebyshev tail bound on finite probability space | `BornConcentration.chebyshev_tail_bound` | U | **NEW (A4):** abstract Chebyshev via variance-dominates-restriction |
| Bernoulli variance $p(1-p)$ | `BornConcentration.bernoulli_variance` | U | **NEW (A4):** direct two-term sum computation |
| Variance addition (independence) | `BornConcentration.variance_add_of_product` | U | **NEW (A4):** $\mathrm{Var}(X_1+X_2)=\mathrm{Var}\,X_1+\mathrm{Var}\,X_2$ on a product measure — the reusable lemma the $N$-fold LLN induction would iterate |
| Two-trial Bernoulli variance $2p(1-p)$ | `BornConcentration.two_trial_bernoulli_variance` | U | **NEW (A4):** concrete instance of variance-addition |
| Born single-trial frequency concentration | `BornConcentration.born_chebyshev_single_trial` | U | **NEW (A4):** single-trial bound; the $N$-trial scaling to full "Born frequencies" still rests on the LLN interface axiom |
| Minimality witnesses for P1, P2, P3 | `BornMinimalityTable.{P1, P2, P3}_…_necessary` | N + U | **NEW (A6):** unified independence package showing each Born sub-axiom is necessary by concrete finite countermodel (minimality *relative to the current decomposition*) |
| Locality (P4) is reducible | `BornMinimalityTable.P4_locality_reducible_to_equivariance` | U | **NEW (A6):** marginal-locality theoremized (modulo the named bridge axiom); not an independent Born-selection sub-axiom |

**No-signaling clarification.** All "no-signaling" results in this paper are about *nonselective* CPTP instruments — the unconditional marginal probability after Bob's measurement, marginalized over outcomes (equivalently, the trace-preserving sum over Kraus operators). Selective post-measurement conditional states can change remotely once Bob's outcome is known; this is not "signaling" because the conditional update requires classical communication.

**Tsirelson clarification.** The Lean module `QIQTH.Tsirelson` proves *attainability* of the value $2\sqrt{2}$ by an explicit singlet-state construction in 4-dimensional real Euclidean space (which is the achievability content of Tsirelson's theorem). The *upper bound* statement that CHSH $\le 2\sqrt{2}$ for *every* quantum state and *every* measurement choice — the full Tsirelson theorem — requires operator-norm machinery on C\*-algebras and is *not* proved in this formalization. The framework relies on the standard Tsirelson upper bound as a cited result.

**Markov suppression clarification.** The `CapacityPacking` module formalizes only the *Markov-style* multi-record suppression (polynomial tail in the modular slack), explicitly *not* exponential suppression. Where the paper says "exponentially suppressed", the reference is to *decoherence-driven* exponential suppression of off-diagonal coherence (which is genuinely exponential, e.g., $e^{-10^{20}}$ for macroscopic environment dimensions), not to Markov-style multi-record suppression from the entropy bound alone.

### 11.5 Credit division

The mathematical infrastructure, Type III$_1$ classification of local algebras, the crossed-product construction giving Type II algebras with renormalized entropy matching generalized entropy in semiclassical gravity, is due to Chandrasekaran, Penington, Witten, and collaborators (CPW 2022; Witten 2022; CLPW 2022; Jensen-Sorce-Speranza 2023; building on Connes-Takesaki and Haag-Kastler).

The original contributions of this paper are:

(a) The **literal physical-instantiation reading** of the Bekenstein-Bousso bound (foundational interpretation): the wave function as a physical state of spacetime has finite physical specification precision bounded by the holographic capacity of the region. This goes beyond what Witten's algebraic theorem directly establishes and is the central foundational postulate.

(b) The **(FQ) axiom** stated rigorously in the CPW Type II framework, with three parts: (i) regional content given by the algebra-state, (ii) the renormalized entropy bound postulated as axiom, (iii) the physical-instantiation precision-floor postulate.

(c) **Theorem 3 (finite physical resolution)** as the structural consequence of the literal reading: $\epsilon(R) > 0$, amplitudes within $\epsilon$ of 0 or 1 physically equivalent to exact 0 or 1.

(d) **The mechanism (§6, Theorem 4):** the structural combination of (FQ) precision floor + decoherence + microscopic IC produces single-record per-run wave functions without collapse.

(e) The **formal/per-run distinction** within the algebraic framework.

(f) The **schematic Born-typicality program** identified as the central quantitative open problem.

The credit division is sharp: CPW supplies the mathematical infrastructure (Type II regional algebras); we supply the literal physical-instantiation reading of the bound on top, and develop its structural consequences for the measurement problem.

### 11.6 Closing remarks

The framework retains standard quantum mechanics exactly at the level of the underlying field algebra. It adds one foundational axiom, (FQ) in its literal physical-instantiation reading, and one distinction (formal vs per-run wave function). From these, the structural consequences follow: finite physical resolution, decoherence-driven concentration, single-record per-run wave functions, the macroscopic world emerging without dynamical modification.

The framework is empirically conservative, Schrödinger and Born preserved exactly, no laboratory deviations predicted. It is metaphysically modest, no actuality primitive beyond the per-run wave function as a physical state of spacetime. It is mathematically grounded in the CPW Type II algebra framework. The principal open problems are quantitative, the explicit form of $\epsilon(R)$ and the rigorous Born typicality theorem.

The wave function is one. The realized world per run is one. The Bekenstein-Bousso holographic bound, taken literally as a Lorentz-invariant physical information limit on the wave function in spacetime, supplies the precision structure that selects the macroscopic world from the formal superposition. The Schrödinger equation is unchanged. The Born rule is unchanged. The macroscopic world emerges as a structural consequence, single outcomes per run, no collapse postulate, no hidden particles, no branching, no modal value-rule.

---

## Acknowledgements

The author thanks the participants in extended discussions that informed the framework developed here. The mathematical apparatus draws on the work of Chandrasekaran, Penington, Witten, and others in the Type II crossed-product algebra construction; we are indebted to that line of work for providing the rigorous home for the regional information bound.

---

## References

1. Ballentine, L. E. (1970). The statistical interpretation of quantum mechanics. *Rev. Mod. Phys.*, 42, 358.
2. Banks, T. (2025). *Finite Entropy Implies Finite Dimension in Quantum Gravity.* arXiv:2509.17856.
3. Bassi, A., Dorato, M., & Ulbricht, H. (2023). *Collapse Models: A Theoretical, Experimental and Philosophical Review.* Entropy 25, 645. arXiv:2310.14969. (See also Tomaz, A. A., Mattos, R. S., & Barbatti, M. (2025). *The Quantum Measurement Problem: A Review of Recent Trends.* Phil. Mag. C. arXiv:2502.19278, for a broader recent survey.)
4. Bekenstein, J. D. (1981). Universal upper bound on the entropy-to-energy ratio for bounded systems. *Phys. Rev. D*, 23, 287.
5. Bohm, D. (1952). A suggested interpretation of the quantum theory in terms of "hidden" variables. *Phys. Rev.*, 85, 166.
6. Bousso, R. (2002). The holographic principle. *Rev. Mod. Phys.*, 74, 825. arXiv:hep-th/0203101.
7. Carroll, S. M., & Sebens, C. (2014). Many worlds, the Born rule, and self-locating uncertainty. In *Quantum Theory: A Two-Time Success Story: Yakir Aharonov Festschrift*, Springer, pp. 157–169. arXiv:1405.7907.
8. **Chandrasekaran, V., Longo, R., Penington, G., & Witten, E. (2022).** *An algebra of observables for de Sitter space.* JHEP 02 (2023) 082. arXiv:2206.10780.
9. **Chandrasekaran, V., Penington, G., & Witten, E. (2022).** *Large N algebras and generalized entropy.* JHEP 04 (2023) 009. arXiv:2209.10454.
10. Dieks, D. (1989). Quantum mechanics without the projection postulate. *Foundations of Physics*, 19, 1397.
11. Diósi, L. (1989). Models for universal reduction of macroscopic quantum fluctuations. *Phys. Rev. A*, 40, 1165.
12. Dürr, D., Goldstein, S., & Zanghì, N. (1992). Quantum equilibrium and the origin of absolute uncertainty. *J. Stat. Phys.*, 67, 843–907. arXiv:quant-ph/0308039.
13. Engelhardt, N., & Wall, A. C. (2015). *Quantum extremal surfaces: holographic entanglement entropy beyond the classical regime.* JHEP 01 (2015) 073. arXiv:1408.3203.
14. Everett, H. (1957). "Relative state" formulation of quantum mechanics. *Rev. Mod. Phys.*, 29, 454.
15. Gell-Mann, M., & Hartle, J. B. (1993). Classical equations for quantum systems. *Phys. Rev. D*, 47, 3345. arXiv:gr-qc/9210010.
16. Ghirardi, G. C., Rimini, A., & Weber, T. (1986). Unified dynamics for microscopic and macroscopic systems. *Phys. Rev. D*, 34, 470.
17. Griffiths, R. B. (2002). *Consistent Quantum Theory.* Cambridge University Press.
18. **Haag, R. (1992).** *Local Quantum Physics: Fields, Particles, Algebras.* Springer.
19. **Haag, R., & Kastler, D. (1964).** An algebraic approach to quantum field theory. *J. Math. Phys.*, 5, 848.
20. Healey, R. (2017). *The Quantum Revolution in Philosophy.* Oxford University Press.
21. 't Hooft, G. (1993). *Dimensional reduction in quantum gravity.* arXiv:gr-qc/9310026.
22. Jacobson, T. (1995). Thermodynamics of spacetime: The Einstein equation of state. *Phys. Rev. Lett.*, 75, 1260–1263. arXiv:gr-qc/9504004.
23. **Jensen, K., Sorce, J., & Speranza, A. J. (2023).** *Generalized entropy for general subregions in quantum gravity.* arXiv:2306.01837.
24. Joos, E., Zeh, H. D., Kiefer, C., Giulini, D., Kupsch, J., & Stamatescu, I.-O. (2003). *Decoherence and the Appearance of a Classical World in Quantum Theory.* Springer.
25. **Murray, F. J., & von Neumann, J. (1936).** On rings of operators. *Annals of Mathematics*, 37, 116.
26. Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information.* Cambridge.
27. Omnès, R. (1994). *The Interpretation of Quantum Mechanics.* Princeton University Press.
28. Palmer, T. N. (2025). *Rational Quantum Mechanics: Testing Quantum Theory with Quantum Computers.* Proc. Natl. Acad. Sci. USA (PNAS). arXiv:2510.02877. (See also Palmer, T. N. (2009). *The Invariant Set Postulate: A New Geometric Framework for the Foundations of Quantum Theory and the Role Played by Gravity.* Proc. Roy. Soc. A 465, 3165–3185. DOI: 10.1098/rspa.2009.0080. arXiv:0812.1148; and subsequent IST development.)
29. Pearle, P. (1989). Combining stochastic dynamical state-vector reduction with spontaneous localization. *Phys. Rev. A*, 39, 2277.
30. Penrose, R. (1996). On gravity's role in quantum state reduction. *Gen. Rel. Grav.*, 28, 581.
31. Susskind, L. (1995). The world as a hologram. *J. Math. Phys.*, 36, 6377. arXiv:hep-th/9409089.
32. von Neumann, J. (1932). *Mathematische Grundlagen der Quantenmechanik.* Springer.
33. Wald, R. M. (1993). Black hole entropy is the Noether charge. *Phys. Rev. D*, 48, R3427–R3431. arXiv:gr-qc/9307038.
34. Wall, A. C. (2012). A proof of the generalized second law for rapidly changing fields and arbitrary horizon slices. *Phys. Rev. D*, 85, 104049. arXiv:1105.3445. (Erratum: *Phys. Rev. D* 87, 069904, 2013.)
35. Wallace, D. (2012). *The Emergent Multiverse: Quantum Theory according to the Everett Interpretation.* Oxford University Press.
36. **Witten, E. (2022).** *Gravity and the crossed product.* JHEP 10 (2022) 008. arXiv:2112.12828.
37. Zurek, W. H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Rev. Mod. Phys.*, 75, 715–775. arXiv:quant-ph/0105127.
38. Kapłański, P. (2026). *One Wave Function, One World: How the Holographic Information Bound Selects the Macroscopic World.* (Position paper, companion to this one.)

---

*End of manuscript.*
