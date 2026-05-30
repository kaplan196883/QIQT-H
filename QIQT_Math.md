---
title: "The QIQT-H Framework in Action: A Worked Mathematical Account of the Double-Slit Experiment"
author: "Paweł Kapłański"
date: 2026-05-25
keywords: [double-slit experiment, holographic principle, Bekenstein-Bousso bound, Type II von Neumann algebras, crossed product, decoherence, measurement problem, finite-precision wave function]
---

# The QIQT-H Framework in Action: A Worked Mathematical Account of the Double-Slit Experiment

## Abstract

We present a fully worked mathematical account of the double-slit experiment in the QIQT-H framework (Kapłański 2026, position paper and companion foundations paper). The framework combines the Chandrasekaran-Penington-Witten (2022) and Witten (2022) Type II crossed-product algebra construction with a foundational axiom (FQ) postulating finite physical specification precision on the wave function as a physical state of spacetime. The double-slit serves as an ideal testbed: it contains both the wave-like interference pattern that builds up across many runs and the particle-like single-spot detection in each individual run. We work through the experiment step by step. First, we set up the algebraic QFT description with the screen region $R_S$ and its Type II crossed-product algebra $\hat{\mathcal{A}}(R_S)$. Second, we show how decoherence, the entanglement of the particle's position with the screen's microscopic substrate and the surrounding electromagnetic environment, dynamically suppresses off-diagonal coherence between distinct spot positions on the screen. Third, we distinguish the formal wave function (the textbook $\psi(x)$ pattern) from the per-run wave function (the actual physical state in any specific run). Fourth, we explain the decisive step: a regional content carrying two or more macroscopically distinct spot-records would exceed the screen region's finite holographic capacity $Q_R$ and so is not an instantiable physical state, leaving the resident regional content single-record — with the specific microscopic initial conditions of the run only indexing *which* spot it carries. Fifth, we show how this works together with decoherence (which removes interference) and the (FQ) resolution floor (which makes the residual sub-threshold coherence have no physical referent): the per-run wave function on the screen region is, after detection, physically a single-spot state — with no amplitude trimmed, the dynamics left exactly unitary, and no probability fundamental (probability emerges only as the relative branch-frequency across runs). No collapse postulate is invoked. The Schrödinger evolution of the underlying field algebra is preserved exactly. The macroscopic single-spot outcome per run emerges as the structural consequence of decoherence + microscopic initial conditions + the (FQ) finite-precision postulate. Across many runs, the typicality distribution of microscopic initial conditions reproduces the Born interference pattern $|\psi_A(x) + \psi_B(x)|^2$. We then work through the which-path case, showing how the detector at one slit destroys the interference pattern (the standard result) in the same framework. Throughout, the QIQT-H reading clarifies what "collapse" actually is: not a dynamical reduction but the structural consequence of decoherence (removing interference) together with the finite-information restriction that makes a multi-record regional content non-instantiable, with the dynamics left exactly unitary.

**Keywords:** double-slit experiment; holographic principle; Bekenstein-Bousso bound; Type II algebra; crossed product; finite-precision wave function; measurement problem; decoherence.

**Formal verification.** The framework's deductive core (Theorems 3, 6, 7, Lemma 1, Donald's identity, no-signaling, Bell/CHSH inequalities with rigorous singlet construction, seven structural audits including (H1)/(H2) independence with reference-weight sharpening, decoherence-vs-concentration, $\chi_R$ vs CPW renormalized entropy, branch-summed cost vs Shannon, FQ-finite dynamics no-go, compression-locality leakage, $\mu$-selection for Born and the support-vs-equivariance gap, plus three sub-theorems for the Canonical IC Measure Principle (typicality Mackey-Gleason, operational data insufficient, FQ-equivariance uniqueness)) is machine-verified in Lean 4 with Mathlib. A subsequent A1+A2+A4+A6 strengthening pass adds: the marginal-locality step proved for *any* measure (`MarginalLocality.pushforward_marginal_local`), reducing locality to a named bridge axiom; the permutation-symmetry collapse component of Goldstein-Struyve sub-lemma 1c proved under its necessary hypothesis (`step1c_collapse_of_perm_symmetric`), the full Schur classification remaining a named interface axiom; single-trial Chebyshev frequency concentration and the variance-addition lemma (`BornConcentration`), with the $N$-trial scaling on the LLN axiom; a unified independence/minimality package (`BornMinimalityTable`); and consolidation of `FQEquivarianceUniqueness` plus deletion of five false/unused Step-1 placeholder sub-axioms (axiom total 57 → 40, `canonical_ic_measure_principle` now depends on exactly two project-specific axioms). See `lean/mathlib/QIQTH/` and `lean/mathlib/QIQTH/AxiomAudit.lean`, including the worked double-slit instance (`QIQTH.DoubleSlit`) that exercises Theorem 6 on the screen-region branch decomposition discussed in §9A.

---

## 1. Introduction

### 1.1 What this paper does

The QIQT-H framework (Kapłański 2026, position paper and companion foundations paper) proposes a foundational position in quantum mechanics built from two ingredients:

1. The Chandrasekaran-Penington-Witten (2022) and Witten (2022) Type II crossed-product algebra construction for regional observables in algebraic QFT with gravitational dressing.

2. A foundational axiom (FQ) postulating that the wave function, regarded as a physical state of spacetime, has finite physical specification precision determined by the holographic information capacity of the region, the *literal physical-instantiation reading* of the Bekenstein-Bousso bound.

The framework's central foundational claim is that the measurement problem, the apparent collapse of the wave function during measurement, is resolved by recognizing that:

- The formal wave function of standard QM is an ensemble descriptor.
- Per-run wave functions have specific microscopic initial conditions that index which single record is realized in any specific run (decoherence removes interference; the finite-information restriction makes a multi-record regional content non-instantiable — that is what makes the content single-record).
- The (FQ) resolution floor removes the residual sub-$\epsilon$ record-coherence (resolution-equivalence on regional states), and the finite-information restriction makes a $\ge 2$-record regional content non-instantiable — leaving single-record regional content, with the dynamics exactly unitary and no amplitude trimmed.
- The single-record per-run wave function is the structural consequence; no collapse postulate is invoked.

This paper works through the double-slit experiment as a concrete worked example of the framework in action. We chose the double-slit because:

- It is the textbook archetype of "collapse", a particle exhibits wave-like behavior in transit and particle-like behavior at detection.
- It contains both the formal-wave-function pattern $|\psi(x)|^2$ (built up statistically across many runs) and the per-run single-spot detection.
- It naturally exhibits the framework's distinction between formal (ensemble) and per-run (actual) wave functions.
- It provides a controlled setting in which we can apply the (FQ) precision floor concretely.

We give explicit calculations where they illuminate the framework's structure. The paper is intended as a *demonstrative companion* to the position and foundations papers, showing the framework working end-to-end on a concrete experiment.

### 1.2 What this paper does not claim

This paper does not prove the (FQ) axiom from first principles (that is the topic of the foundations paper); does not prove the Concentration claim rigorously (it remains the central open dynamical problem); does not derive the explicit form of the resolution floor $\epsilon(R)$ as a function of regional geometry; does not derive the Born rule from typicality rigorously (that is the second open problem). What it does is show that *if* the framework's postulates hold, the double-slit phenomenology is reproduced exactly, with the apparent "collapse" emerging as a structural consequence.

### 1.3 Roadmap

§2 reviews the standard QM account of the double-slit. §3 sets up the algebraic QFT framework. §4 introduces the Type II regional algebra of the screen. §5 develops the decoherence calculation. §6 distinguishes formal and per-run wave functions for the double-slit. §7 develops single-record regional content (finite-information restriction + IC indexing). §8 applies the (FQ) resolution floor and capacity restriction for single-spot emergence. §9 shows how Born statistics across runs reproduce the interference pattern. §10 works through the which-path case. §11 compares with standard textbook accounts. §12 concludes.

---

## 2. The Double-Slit Experiment: Standard Account

### 2.1 Setup

A source $S$ emits particles (electrons, photons, neutrons, the physics is the same) one at a time. Each particle propagates to a barrier with two narrow slits $A$ and $B$ separated by distance $d$. Behind the barrier at distance $L$ is a screen, a position-sensitive detector array.

A particle's state immediately after passing the slits is, in the standard idealization,
$$|\psi\rangle = \frac{1}{\sqrt{2}}\left(|A\rangle + |B\rangle\right),$$
where $|A\rangle$ and $|B\rangle$ are localized states of the particle just after passing slit $A$ or $B$ respectively.

Free propagation to the screen gives spatial wave functions:
$$\psi(x) = \psi_A(x) + \psi_B(x),$$
where $\psi_A(x), \psi_B(x)$ are the propagated wave functions from each slit. For monochromatic particles with momentum $p = h/\lambda$:
$$\psi_A(x) \approx \frac{1}{\sqrt{2}} e^{ipr_A/\hbar}/r_A, \quad \psi_B(x) \approx \frac{1}{\sqrt{2}} e^{ipr_B/\hbar}/r_B,$$
with $r_A, r_B$ the distances from each slit to screen position $x$.

### 2.2 Predicted probability density

The Born rule gives:
$$P(x) = |\psi(x)|^2 = |\psi_A(x)|^2 + |\psi_B(x)|^2 + 2\,\mathrm{Re}\,[\psi_A^*(x)\psi_B(x)].$$

The third term, the *interference term*, produces the characteristic fringe pattern. With $\Delta r = r_B - r_A \approx d \sin\theta$ and $\theta \approx x/L$:
$$2\,\mathrm{Re}\,[\psi_A^*\psi_B] \propto \cos\left(\frac{2\pi d x}{\lambda L}\right),$$
giving bright fringes at $x_n = n\lambda L/d$ and dark fringes at $x_n = (n+1/2)\lambda L/d$.

### 2.3 The puzzle

In any single run, only one spot appears on the screen. The interference pattern $P(x)$ is built up *statistically* across many runs. Two questions arise:

**Question 1 (single-outcome puzzle):** Why does each run produce one specific spot rather than a smeared distribution? The wave function $\psi(x)$ is delocalized across the screen; if it is the complete physical state, where does the localization come from?

**Question 2 (interference puzzle):** How does each individual particle "know" to go through both slits to produce the interference pattern, if it is also localized at a single spot at the end?

The standard textbook responses invoke wave-particle duality, Bohr's complementarity, the Copenhagen collapse postulate, or one of the established interpretations. Each pays a foundational price. We work through the QIQT-H account in what follows.

---

## 3. Algebraic QFT Setup

### 3.1 The field-theoretic description

The double-slit experiment is properly described in QFT: the particles are excitations of a quantum field (Dirac field for electrons, electromagnetic field for photons, etc.), and the screen is a localized matter system that detects field quanta.

We work in the Heisenberg picture. The underlying state $|\Psi\rangle$ of the universe (particles + screen + environment) evolves unitarily under the full Hamiltonian $H$. Local observables are organized in the Haag-Kastler net $R \mapsto \mathcal{A}(R)$ assigning to each bounded spacetime region $R$ a von Neumann algebra of observables localizable in $R$.

For any double-cone or causal-diamond region in a generic QFT (Buchholz, Wichmann, Borchers, Longo), $\mathcal{A}(R)$ is a Type III$_1$ factor: no trace, no Hilbert-space factorization $\mathcal{H} = \mathcal{H}_R \otimes \mathcal{H}_{\bar R}$, UV-divergent entanglement entropy. This is the standard mathematical structure of relativistic QFT.

### 3.2 Relevant regions for the double-slit

We identify three bounded spacetime regions:

- $R_S$: a thin slab containing the screen, taken at the moment of particle detection
- $R_E$: the environmental region containing thermal radiation, surrounding gas, and electromagnetic background near the screen at detection time
- $R_{SE} = R_S \cup R_E$: the joint region

For each, the Type III$_1$ local algebra $\mathcal{A}(R)$ is well-defined in the underlying QFT.

### 3.3 Crossed-product Type II algebras

Following CPW 2022 and Witten 2022, gravitational dressing (perturbatively in $G_N$ or $1/N$) is implemented by taking the crossed product with the modular flow of a reference state $\Omega$ (we take $\Omega$ to be the vacuum or a quasi-vacuum state appropriate to the asymptotic background):

$$\hat{\mathcal{A}}(R) := \mathcal{A}(R) \rtimes_{\sigma^\Omega} \mathbb{R}.$$

The crossed-product algebra $\hat{\mathcal{A}}(R)$ is of Type II in the Murray-von Neumann classification, with a semifinite trace $\tau$ permitting a renormalized entropy $S_{\rm ren}(\rho) = -\tau(\rho \log \rho)$ for suitable states. The algebra is naturally represented on the enlarged Hilbert space $\mathcal{H} \otimes L^2(\mathbb{R})$, with the $L^2(\mathbb{R})$ factor encoding observer-frame / clock degrees of freedom.

For the screen region $R_S$, the Type II algebra $\hat{\mathcal{A}}(R_S)$ is the rigorous mathematical home for "physical observables localized in the screen." States on $\hat{\mathcal{A}}(R_S)$, that is, normal positive linear functionals $\omega: \hat{\mathcal{A}}(R_S) \to \mathbb{C}$, represent the physical content of the wave function in $R_S$.

### 3.4 (FQ) axiom for the screen region

The (FQ) axiom asserts: for the screen region $R_S$ and the per-run wave function $|\Psi\rangle_{\rm run}$,

(i) The physical content of $|\Psi\rangle_{\rm run}$ in $R_S$ is given by the state $\omega_\Psi$ on $\hat{\mathcal{A}}(R_S)$ defined by $\omega_\Psi(O) = \langle\Psi_{\rm run}|O|\Psi_{\rm run}\rangle$.

(ii) The renormalized entropy is bounded:
$$S_{\rm ren}(\omega_\Psi) \le Q_{R_S} \equiv C(R_S) := \frac{A(\partial R_S)}{4\ell_P^2}.$$

(We use $Q_{R_S}$ and $C(R_S)$ interchangeably for the regional holographic capacity throughout this paper.)

(iii) The wave function in $R_S$ is regarded as a physical state of spacetime with finite physical information capacity $Q_{R_S}$. Two abstract wave functions whose physical instantiations in $R_S$ are indistinguishable at the precision floor $\epsilon(R_S)$ are physically identical in $R_S$.

For a macroscopic screen, $Q_{R_S}$ is astronomical in conventional units (a typical screen of area $\sim 10^{-2}$ m² and thickness $\sim 10^{-3}$ m has $A(\partial R_S) \sim 10^{-4}$ m² and $Q_{R_S} \sim 10^{68}$ nats). The precision floor $\epsilon(R_S)$ is correspondingly fine, but, crucially, finite.

---

## 4. The Type II Regional Algebra of the Screen

### 4.1 Macroscopic record observables

The screen is a macroscopic matter system, a photographic plate, a CCD array, a fluorescent screen, that records the arrival position of a particle through a physical amplification cascade. The screen's quantum state is, for our purposes, fully specified by:
- The microscopic state of all atoms / molecules / electronic excitations in the screen material
- The state of any photons emitted by the detection event
- The state of any electrical signals from the CCD pixels

For each position $x_k$ on the screen (where $k$ labels distinct macroscopic positions distinguishable at the screen's resolution), there is a *macroscopic record state* $\omega_k \in \mathcal{S}(\hat{\mathcal{A}}(R_S))$ corresponding to "particle detected at position $x_k$." These are distinct, mutually approximately orthogonal states in the normal-state space of $\hat{\mathcal{A}}(R_S)$.

The record observables form a set of projectors $\{P_k\}_{k=1}^N$ in $\hat{\mathcal{A}}(R_S)$:
$$P_k \in \hat{\mathcal{A}}(R_S), \quad P_k P_j = \delta_{jk} P_k, \quad \sum_k P_k = \mathbf{1}_{R_S}^{\rm record},$$
where $\mathbf{1}_{R_S}^{\rm record}$ is the projector onto the subalgebra of macroscopic record observables. The number $N$ of distinct spot positions is finite, determined by the screen's pixel resolution, the detector physics, and the (FQ) information capacity (in practice $N \sim 10^6 - 10^9$ for typical screens).

The record states are $\omega_k(O) := \tau(P_k O P_k) / \tau(P_k)$ for $O \in \hat{\mathcal{A}}(R_S)$, the Type II algebra-state associated with the record projector $P_k$.

### 4.2 The environmental algebra

The screen does not exist in isolation. It is surrounded by an environment $R_E$, thermal photons, residual gas molecules, ambient electromagnetic fields, that interacts with the screen during the detection event. The environmental algebra $\hat{\mathcal{A}}(R_E)$ contains observables on this surrounding region.

For each record $k$, there is a corresponding *environmental record state* $\omega_k^E \in \mathcal{S}(\hat{\mathcal{A}}(R_E))$, the state of the environment after the screen has registered the particle at position $x_k$, with thermal/optical signatures propagating outward. The environmental records are mutually approximately orthogonal:
$$\omega_j^E \perp \omega_k^E \quad \text{for } j \ne k \text{ (to good approximation, after decoherence)}.$$

This is the algebraic formulation of einselection (Zurek 2003): the environment "selects" the position basis $\{P_k\}$ as the macroscopic pointer basis by becoming entangled with it.

---

## 5. Decoherence: The Particle-Screen-Environment Interaction

### 5.1 The unitary detection process

The particle arrives at the screen with formal wave function $\psi(x)$ (a superposition over screen positions, by §2). The detection event is a unitary interaction between the particle's quantum field state and the screen's macroscopic substrate. We model it schematically as:

$$\hat{U}_{\rm det}\left(\int dx \,\psi(x)|x\rangle\right)|S_0\rangle|E_0\rangle = \int dx\, \psi(x) |x\rangle |S_x\rangle |E_x\rangle,$$

where:
- $|S_0\rangle$ is the initial state of the screen (atoms in ground states, no detection yet)
- $|E_0\rangle$ is the initial state of the environment
- $|S_x\rangle$ is the screen state after a particle arrives at position $x$ (electron-hole pair, fluorescence, electrical signal, etc.)
- $|E_x\rangle$ is the environment state after the detection signature has propagated outward from position $x$

The detection process is unitary at the underlying field-algebra level. No collapse is invoked; the dynamics is exactly Schrödinger / Heisenberg.

### 5.2 Decoherence: off-diagonal suppression

After the detection interaction, the reduced state of the particle's position degree of freedom, traced over the screen + environment, is:
$$\rho_{\rm particle}(x, x') = \psi(x) \psi^*(x') \langle E_{x'} | E_x \rangle \langle S_{x'} | S_x \rangle.$$

Decoherence theory (Zurek 2003; Joos et al. 2003) establishes that for macroscopically distinct positions $x \ne x'$:
$$\langle E_{x'} | E_x \rangle \to 0 \quad \text{and} \quad \langle S_{x'} | S_x \rangle \to 0 \quad \text{rapidly},$$
by the product-of-overlaps argument over many independent environmental degrees of freedom (see the companion *Tutorial* §2 for an explicit derivation).

The off-diagonal terms in the density matrix are dynamically suppressed. The reduced state of the particle becomes (approximately) diagonal in the position basis, this is einselection: the position basis is selected because the system-environment interaction is position-local (see *Tutorial* §6.2):
$$\rho_{\rm particle}(x, x') \to |\psi(x)|^2 \delta(x - x').$$

In algebraic terms, the formal state on the apparatus + environment algebra $\hat{\mathcal{A}}(R_{SE})$ becomes:
$$\omega_\Psi^{\rm formal} = \sum_k p_k\, \omega_k \otimes \omega_k^E, \quad p_k = |\psi(x_k)|^2,$$
where the sum runs over distinct macroscopic positions and the off-diagonal coherence terms have been dynamically suppressed.

### 5.3 What decoherence does and does not give

**What decoherence gives:** A formal mixed state $\omega_\Psi^{\rm formal} = \sum_k p_k \omega_k \otimes \omega_k^E$ on the apparatus + environment algebra, approximately diagonal in the macroscopic position basis with Born weights $p_k = |\psi(x_k)|^2$.

**What decoherence does not give:** A single-record state. The formal state is a mixture of records, not a single record. In standard interpretations, this is where the measurement problem reasserts itself: the mixture has the form of a classical probability distribution over records, but each branch remains present in the global pure state $|\Psi\rangle = \sum_k c_k |x_k\rangle|S_k\rangle|E_k\rangle$.

The QIQT-H framework's resolution begins at this point. The formal state is the *ensemble descriptor*, the average over the ensemble of per-run wave functions. The per-run wave function in any specific run is *not* the formal mixed state; it is a single-record state, made physically exact by the (FQ) precision floor.

---

## 6. One Wave Function Per Run; Subsystem vs Universal Description

### 6.1 One wave function per run

**The central commitment of the framework: one wave function per run.** Each individual particle sent through the double-slit corresponds to one universal wave function of the universe at that moment. We do *not* claim that the same particle preparation secretly corresponds to many different "per-run wave functions", that would conflict with the extremality of pure quantum states and would constitute a problematic ψ-supplementation.

Each particle sent through the double-slit has its own wave function. Each particle interacts with a screen + environment whose actual microscopic state is specific to that particle's arrival. The Born statistical pattern emerges across *many actual particles in many actual runs*, each with its own actual universal wave function evolving from its own actual initial conditions.

### 6.2 Subsystem wave function vs universal wave function

There are two senses in which one talks about "the wave function" of the double-slit experiment, and conflating them generates confusion. The framework distinguishes them.

**Subsystem wave function** $|\psi\rangle_{\rm sub}$: the textbook abstraction for the prepared particle alone, $|\psi\rangle_{\rm sub} = (|A\rangle + |B\rangle)/\sqrt{2}$ after the slits, with $\psi(x) = \psi_A(x) + \psi_B(x)$ on the screen. This treats the particle as a closed quantum system, abstracting away from the apparatus and environment. It is correct for calculating expectation values of subsystem observables in the standard QM way, but it is *not* the complete physical state of the universe.

**Per-run universal wave function** $|\Psi\rangle_{\rm run}$: the actual physical wave function of the universe in any specific run, the particle + apparatus + environment + everything. It is the sole *dynamical* ontology in any specific run (the complete per-run state being the pair $(\Phi, \lambda)$, with $\lambda$ the non-dynamical run-index that selects which record is realized; §8.4). Its content on the regional algebra $\hat{\mathcal{A}}(R_S)$ of the screen region is given by $\omega_\Psi^{R_S}$ on the regional Type II algebra.

The textbook ($\sum_k c_k |x_k\rangle$ after diffraction; $\sum_k c_k |x_k\rangle|S_k\rangle|E_k\rangle$ after entanglement with apparatus + environment) is the *subsystem wave function evolved up through the relevant interactions*. It uses the formal Hilbert-space superposition structure to encode the joint quantum state of particle + apparatus + environment.

**The framework's claim is not that this is wrong**, but that it is the *subsystem-level* description. The per-run universal wave function is the actual state of the universe in that run. The framework says nothing the textbook doesn't already say at this level, the per-run universal wave function evolves unitarily under the universal Hamiltonian from the actual initial conditions of the universe in that run.

### 6.3 What varies across runs

Different runs of the double-slit experiment have:

- Different actual particles emitted (each with its own quantum state)
- Different actual microscopic states of the screen substrate (different atoms in different excited states; different lattice vibrations; different free electrons)
- Different actual environmental configurations (different photons in different cavity modes; different residual gas molecule positions; different cosmological background fluctuations)
- Different actual phases, polarizations, momenta of incoming particles

These are not "alternative possible wave functions for the same preparation." They are *actual physical differences* between actual physical universes in actual different runs. Standard QM at the universal-wave-function level already accommodates this trivially: the universal wave function is a function of all degrees of freedom in the universe; those degrees of freedom take different actual values in different runs.

### 6.4 What the framework adds (and what it doesn't)

The framework adds *no second dynamical substance* beyond the universal wave function. It is **ψ-monist in the weak (dynamical) sense** — $\Phi$ is the sole dynamical ontology. The framework's additions to standard QM are:

1. **Recognition that the subsystem wave function $|\psi\rangle_{\rm sub}$ is an abstraction**, not the complete physical state. The per-run universal wave function $|\Psi\rangle_{\rm run}$ is the actual state. This is just standard QM at the universal level (which is always the full story; the subsystem description is a calculational convenience).

2. **The (FQ) axiom** limiting the physical information content of the universal wave function in any bounded region. This is the foundational postulate.

3. **A non-dynamical run-index $\lambda$** (the run's actual microscopic initial conditions) selecting which single record is realized.

None of these introduces a second *dynamical* layer or a guidance law. The complete per-run state is the pair $(\Phi, \lambda)$: weak-ψ-monist standard QM with (FQ) added, plus a non-dynamical actuality selector. In Spekkens–Harrigan terms the framework is ψ-ontic, weak-ψ-monist, and formal-ψ-incomplete.

### 6.5 The Born statistics as ensemble over actual runs

The Born statistics across many runs of the double-slit experiment, the interference fringe pattern building up dot by dot, emerge from the distribution of *actual initial conditions* across *actual different particles in actual different runs*. Each particle has its own universal wave function evolving from its own actual initial conditions through unitary dynamics + (FQ). Each particle ends up at one specific spot on the screen. Across many particles, the distribution of spots reproduces $|\psi_A + \psi_B|^2$ (the Born conjecture from typicality).

**This is not "averaging over different per-run wave functions for the same preparation."** It is averaging over actual different physical particles in actual different physical runs of the experiment. The Born rule is a statement about the statistical distribution of outcomes across many actual independent runs, each with its own actual universal wave function.

### 6.6 No ontological-models supplementation, just standard QM made explicit

Foundations-of-physics literature (Spekkens–Harrigan ontological-models framework) uses "ontic state" $\lambda$ for whatever fully specifies the physical state of a single system. In QIQT-H the complete per-run ontic state is the pair $(\Phi, \lambda)$: the per-run universal wave function $|\Psi\rangle_{\rm run}$ together with a *non-dynamical* run-index $\lambda$ (the run's actual microscopic initial conditions) that fixes which single record is realized. $\Phi$ is the sole *dynamical* ontology (so the framework is **weak-ψ-monist** and ψ-ontic), but $\lambda$ is a genuine extra fact not contained in the bare formal wave function — a broad-sense beable with no guidance law and no back-reaction on $\Phi$. Relative to the textbook formal wave function the framework is therefore **formal-ψ-incomplete**: the actual ontic state $(\Phi, \lambda)$ is finer-grained than the formal $\Phi$, which labels an ensemble over runs. (This is the same structural move every single-world deterministic reading makes — Bohmian configuration, modal actual-history — without adding a guided second substance.)

The textbook subsystem wave function $|\psi\rangle_{\rm sub}$ is *not* the ontic state, it is the subsystem description. Confusing $|\psi\rangle_{\rm sub}$ with $|\Psi\rangle_{\rm run}$ is what generates the apparent puzzle of "how does the formal pure state correspond to a distribution of per-run pure states?" The puzzle dissolves: $|\psi\rangle_{\rm sub}$ is not the universal wave function in any run; $|\Psi\rangle_{\rm run}$ is. There is one $|\Psi\rangle_{\rm run}$ per run, and different runs have actually different universal wave functions because the actual physical universe is actually different in each run.

---

## 7. What Decoherence Actually Does at the Screen

### 7.1 The naive picture is wrong

A common but misleading reading treats the post-detection state on the screen as a "naive superposition" of spots, say, "amplitude $\psi(x_1)$ at spot 1, amplitude $\psi(x_2)$ at spot 2, …, sitting there as accessible alternatives." The puzzle then becomes "how do these amplitudes magically transition to one specific spot per run?"

This picture is wrong. We never have direct access to amplitudes. We have access only to the macroscopic record on the screen, which is itself a complex quantum system with $\sim 10^{20}$–$10^{25}$ degrees of freedom (atoms, electronic excitations, photon emissions, electrical signals), entangled with the particle that was just absorbed.

The question to ask is not "how do amplitudes transition to 0 or 1?" but "what does the joint particle-screen-environment state actually look like as a state on the regional algebra $\hat{\mathcal{A}}(R_{SE})$?"

### 7.2 Exponential orthogonality of macroscopic records

After the detection interaction (§5), the joint state is
$$|\Psi\rangle = \sum_k c_k |x_k\rangle_{\rm particle} \otimes |S_k\rangle_{\rm screen} \otimes |E_k\rangle_{\rm env},$$
where $|S_k\rangle$ is the macroscopic screen state with a spot at $x_k$, $|E_k\rangle$ is the corresponding environment state, and $c_k = \psi(x_k)\sqrt{\Delta x}$ (with $\Delta x$ the pixel width).

Standard decoherence theory (Zurek 2003; Joos et al. 2003) establishes that for any pair of macroscopically distinct spots $j \ne k$:
$$\langle E_j | E_k \rangle \sim \exp(-\Gamma_E t), \quad \langle S_j | S_k \rangle \sim \exp(-\Gamma_S t),$$
where $\Gamma_E$ is the environmental decoherence rate and $\Gamma_S$ the intra-screen decoherence rate. For typical screen materials at room temperature interacting with electromagnetic and phonon environments, $\Gamma_E t$ and $\Gamma_S t$ reach $\sim 10^{20}$ on timescales much shorter than the screen's response time. The cross-overlap between macroscopic spot states is therefore **exponentially small**, on the order of $\exp(-10^{20})$.

The induced state on the apparatus + environment regional algebra $\hat{\mathcal{A}}(R_{SE})$ is, after this decoherence:
$$\omega_\Psi^{R_{SE}} = \sum_k |c_k|^2 \omega_k^{SE} + O(\exp(-10^{20})),$$
where $\omega_k^{SE}$ are the macroscopic record states on the joint algebra (with appropriate screen-environment correlations) and the off-diagonal coherence terms are exponentially suppressed.

**This is a classical-looking mixture** in the macroscopic record basis: probability $|c_k|^2$ on spot $k$, no remaining interference between macroscopically distinct spots, off-diagonal coherence below any operationally accessible threshold.

### 7.3 The (FQ) floor renders off-diagonal coherence physically zero

The off-diagonal coherence terms are exponentially small, on the order of $\exp(-10^{20})$, but mathematically nonzero. In standard QM without (FQ), this is the source of the measurement problem: even though the coherence is operationally inaccessible, it is mathematically present, and one is forced to either (a) treat all branches as real (MWI) or (b) invoke an additional selection mechanism (collapse, modal value-rule, hidden variable).

Under (FQ), the off-diagonal coherence is **physically zero**, not merely suppressed. The (FQ) precision floor $\epsilon(R_{SE})$ on the regional algebra-state, while astronomically fine in absolute terms, is enormously larger than $\exp(-10^{20})$. Therefore by Lemma 1 (from foundations paper §5.1), the off-diagonal coherence terms, being below the (FQ) precision floor, are physically equivalent to exactly zero.

The post-decoherence + (FQ) regional state on $\hat{\mathcal{A}}(R_{SE})$ is therefore the **strict classical mixture**:
$$\omega_\Psi^{R_{SE}} = \sum_k |c_k|^2 \omega_k^{SE},$$
with macroscopic record states physically exclusive (no off-diagonal coherence between distinct $\omega_k^{SE}$).

This is the cooperative role of decoherence and (FQ): decoherence drives off-diagonal coherence to exponentially small values dynamically; (FQ) renders these values physically zero. The result is a **strictly-exclusive classical mixture** over macroscopic records on the regional algebra.

---

## 8. Per-Run Branch Selection: The Single Spot

### 8.1 What the framework actually claims

The strict classical mixture $\sum_k |c_k|^2 \omega_k^{SE}$ on $\hat{\mathcal{A}}(R_{SE})$ is not a single record. It is a weighted list of records carrying the weights $|c_k|^2$ — the across-run relative frequencies, not per-run probabilities (the framework has no fundamental probabilities). It still carries every record; decoherence has removed interference, not multiplicity. In any specific run, which record actually obtains, and why is it a *single* record at all?

**The framework's claim: in any specific run, the per-run universe occupies one specific branch of the strictly-exclusive classical mixture. Which branch is determined by the per-run microscopic initial conditions of the screen + environment.**

This is *not* a claim that amplitudes magically transition from $|c_k|^2$ to $\delta_{k,k_{\rm run}}$. The amplitudes don't need to transition: after decoherence + (FQ), the regional state is already a strict classical mixture with exclusive macroscopic records. The framework's per-run claim is simply that, in any specific run, the universe is in *one* of these now-exclusive branches, analogous to how, in classical statistical mechanics, a thermodynamic ensemble at temperature $T$ describes a probability distribution over microstates, but any specific physical realization sits at one specific microstate.

### 8.2 The classical statistical mechanics analogy made precise

Consider a gas at temperature $T$ with $N \sim 10^{23}$ molecules. The canonical ensemble assigns probability $e^{-\beta E_i}/Z$ to each microstate $i$. We do not say "the gas is in a quantum superposition of all microstates with weights $e^{-\beta E_i}/Z$." We say:

- The gas in any specific physical realization is in *one* specific microstate.
- Across many realizations (or across time, under ergodicity), the empirical distribution over microstates is the canonical distribution.
- The thermodynamic descriptor $T$ is not the per-realization state; it is the parameter labeling the distribution over realizations.

The QIQT-H framework reads the quantum case analogously, with the *additional* ingredient that decoherence + (FQ) make the macroscopic-record alternatives strictly exclusive on the regional algebra. After decoherence + (FQ):

- The regional algebra-state $\omega_\Psi^{R_{SE}} = \sum_k |c_k|^2 \omega_k^{SE}$ is a strict classical mixture over macroscopic records.
- The per-run universe is in *one* specific branch, one specific $\omega_{k_{\rm run}}^{SE}$.
- Across many runs, the empirical distribution over branches is $|c_k|^2$ (Born statistics).
- The formal wave function $|\Psi\rangle$ is the descriptor of this distribution, not the per-run physical state.

### 8.3 Which branch? The role of microscopic initial conditions

Within any specific run, the screen + environment has specific microscopic initial conditions: the actual thermal microstate of the screen substrate, the actual configurations of vacuum fluctuations, the actual positions and velocities of residual gas molecules, the actual ambient radiation field. These microscopic conditions are not controlled by the experimenter and vary across runs.

The amplification cascade in the screen, single particle absorption at one specific atom, secondary electron emission, electrical signal, is extraordinarily sensitive to these microscopic conditions. Which atom in the screen substrate is "available" to absorb the particle (in the right energy state, with the right local field configuration) depends on the run-specific microstate. The amplification then locks in this specific atom as the realized spot.

In algebraic terms: the per-run universe is in the branch $\omega_{k_{\rm run}}^{SE}$ corresponding to the specific microstate-determined amplification path of that run. Across many runs, the distribution of selected branches follows the Born weights $|c_k|^2$ (under the typicality conjecture for the measure on microscopic IC; see §9).

**This is the framework's account of "collapse" for the double-slit:**
1. Decoherence drives off-diagonal coherence between macroscopic spot states to $\sim e^{-10^{20}}$
2. (FQ) renders these exponentially-small coherence terms physically zero
3. The regional state on $\hat{\mathcal{A}}(R_{SE})$ becomes a strict classical mixture over spot records
4. The per-run universe occupies one specific branch of this mixture
5. Which branch is determined by per-run microscopic IC

No collapse postulate is invoked. Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly. The single-spot per-run outcome emerges as the structural consequence of decoherence + (FQ) + per-run microscopic IC.

### 8.4 Weak ψ-monism: one dynamical ontology, plus a non-dynamical actuality fact

The per-run microscopic IC ($\lambda$) are *not* a second dynamical substance and not a guided hidden variable: there are no Bohmian particles, no extra fields, no guidance law. The framework is **weak-ψ-monist** — the wave function $\Phi$ is the sole *dynamical* ontology. It is, however, honest to record that $\lambda$ — the run's actual microscopic configuration, which selects the realized record — is a *broad-sense* beable: a non-dynamical actuality fact not contained in the bare textbook formal wave function. So the complete per-run state is the pair $(\Phi, \lambda)$, and the framework is ψ-ontic, weak-ψ-monist, and formal-ψ-incomplete.

What the framework adds is the distinction between two senses of "wave function":

**Formal wave function** $|\Psi\rangle_{\rm formal}$: the textbook abstract wave function used in calculations, for example $\alpha|0\rangle + \beta|1\rangle$ for a prepared qubit, or $\sum_k c_k |x_k\rangle|S_k\rangle|E_k\rangle$ after measurement. This is a *descriptor of the ensemble* of possible runs, not the per-run physical state.

**Per-run wave function** $|\Psi\rangle_{\rm run}$: the actual physical wave function of the universe in any specific run. This is a definite physical state at any moment. Different runs of the "same" experiment correspond to different per-run universal wave functions because the actual physical universe is different in each run (different photon configurations, different thermal microstates, different vacuum fluctuations).

The "per-run microscopic IC" are not additional ontology. They are simply *the run-specific values of degrees of freedom that the formal wave function ensemble-averages over*. The formal wave function aggregates over apparatus + environment microstates; the per-run wave function in any specific run has the apparatus + environment in one specific microstate. There is nothing beyond the wave function, but the wave function in each actual run is finer-grained than the textbook ensemble descriptor.

Compare to Bohm: Bohm adds particle positions *on top of* the wave function as a separate ontological layer, with a guidance equation. The framework does nothing analogous. The wave function is the *only* ontology. The per-run wave function is just the actual wave function; the formal wave function is the calculational descriptor of the distribution across runs.

The framework's claim is that taking ψ-monism seriously, combined with the recognition that (FQ) makes bounded spacetime physically incapable of storing macroscopic-superposition wave functions, gives single-outcome per-run reality without modifying Schrödinger dynamics and without adding particles, fields, branches, or any other ontological layer.

### 8.5 Quantitative scale

For a typical macroscopic screen, $Q_{R_{SE}} \sim 10^{68}$ nats. The (FQ) precision floor $\epsilon(R_{SE})$ is astronomically fine in absolute terms, but enormously larger than the decoherence suppression $\sim e^{-10^{20}}$. The (FQ) floor's role is to convert "exponentially small but mathematically nonzero" off-diagonal coherence into "physically zero", converting the merely-approximate classical mixture that standard decoherence delivers into a strictly-exclusive classical mixture. The per-run branch selection then proceeds as in classical statistical mechanics: one specific realization occupies one specific microstate.

---

## 9. Born Statistics Across Runs: The Interference Pattern

### 9.1 Single runs and ensemble statistics

We have established (§§7–8) that in any specific run, the per-run wave function on the screen region is, after detection, physically equivalent to a single-record state $\omega_{k_{\rm run}}$, one specific spot.

Across many runs, the realized records $\{k_{\rm run}^{(1)}, k_{\rm run}^{(2)}, \ldots, k_{\rm run}^{(M)}\}$ form a statistical distribution. The empirical relative frequency of spot $k$ across $M$ runs is:
$$f_k^{(M)} := \frac{1}{M} \sum_{j=1}^M \delta_{k, k_{\rm run}^{(j)}}.$$

### 9.2 The Born typicality claim

The framework's typicality claim is:

> For an appropriately chosen measure $\mu$ on microscopic initial conditions, the empirical relative frequency $f_k^{(M)}$ converges to the Born weight $|c_k|^2 = |\psi(x_k)|^2$ as $M \to \infty$.

For the double-slit, this means:
$$f_k^{(M)} \to |\psi(x_k)|^2 = |\psi_A(x_k) + \psi_B(x_k)|^2 = |\psi_A|^2 + |\psi_B|^2 + 2\,\mathrm{Re}\,[\psi_A^*\psi_B](x_k).$$

The interference term is present in the empirical distribution across many runs. The fringe pattern of the standard double-slit experiment is reproduced as the statistical distribution of single-spot outcomes.

### 9.3 What is happening physically

In the QIQT-H reading:

- Each individual run: the per-run wave function does propagate through both slits (the unitary evolution is the standard QM evolution). The per-run wave function on the screen region has, just before detection, the full interference structure $|\psi(x)|^2$.
- Per-run detection: amplification + microscopic IC + (FQ) precision floor select one spot. The per-run wave function after detection is the single-record state $\omega_{k_{\rm run}}$.
- Which spot is selected depends on the microscopic IC of the specific run.
- Across many runs: the distribution of selected spots reproduces the Born weights $|\psi(x_k)|^2$, including the interference term.

There is no "wave-particle duality" mystery in the framework: the wave function is always a physical wave (in the underlying field algebra), and the apparent particle-like single-spot is the single-record regional content the finite-information restriction leaves resident on the screen region. The interference fringe pattern is the *statistical signature* across many runs that the underlying wave function did propagate through both slits in each run.

### 9.4 The Born rule as the open problem

We emphasize that the framework does not derive the Born rule rigorously; it sketches a typicality argument and identifies rigorous derivation as the second open problem (alongside the Concentration Conjecture). The conjectured measure $\mu$ on microscopic IC that yields Born statistics must be specified, the equivariance-type theorem must be proved, and the measure must be justified as empirically realized.

For the present worked example, we treat Born from typicality as a working assumption that the framework intends to establish; the framework's structure is what we are demonstrating.

---

## 9A. The Modular-Local Holographic Superselection Rule Applied to the Double-Slit Screen

The framework's central new physical principle (foundations paper §7.6), the **Modular-Local Holographic Bound as superselection rule**, has a concrete interpretation for the double-slit screen. Working through it here makes explicit what the postulate means in a familiar setting.

### 9A.0 Modular-local form and its classical-mixture reduction

The *foundational* statement of the bound is modular-local (foundations paper §7.6): for the screen region $R_S$ with local algebra $\hat{\mathcal{A}}(R_S)$ and the canonical sector reference state $\sigma_{R_S}$ (foundations paper §7.6),

$$\chi_{R_S}(\omega) := S_{\hat{\mathcal{A}}(R_S)}(\omega_{R_S} \,\|\, \sigma_{R_S}) \;\le\; C(R_S) = \frac{A(\partial R_S)}{4\ell_P^2},$$

where $\chi_{R_S}$ is Araki / Type II core relative entropy, finite, basis-independent, defined directly on the Type III local algebra via the CPW Type II core construction (foundations paper §3). This is the form that delivers no-signaling automatically from AQFT microcausality (foundations paper §7.7).

After decoherence the post-detection regional state on the screen is a strict classical mixture over distinguishable spot records (§7 of this paper):

$$\omega_{R_S} = \sum_k p_k \,\omega_k,$$

with $p_k$ the spot probabilities and $\omega_k$ the single-spot regional states. Let $\tilde p_k := p_k / q$ be the normalized active distribution on the smooth active set $\mathcal{A}_\epsilon$, with total weight $q := \sum_{k \in \mathcal{A}_\epsilon} p_k$ (in the strict-classical-mixture regime $q \to 1$ and $\tilde p_k \to p_k$). In this classical-mixture regime Donald's identity for Araki relative entropy gives

$$\chi_{R_S}(\bar\omega_{R_S}) \;=\; \sum_k \tilde p_k\, c_{R_S}(r_k) - I_{\rm Hol}^{R_S},$$

with $\bar\omega_{R_S} := \sum_k \tilde p_k \omega_{k,R_S}$, $c_{R_S}(r_k) = S(\omega_k \| \sigma_{R_S})$ the per-record cost, and $I_{\rm Hol}^{R_S} = \sum_k \tilde p_k S(\omega_k \| \bar\omega_{R_S})$ the Holevo information of the spot mixture. In the strict distinguishable-record limit $I_{\rm Hol}^{R_S} \approx H(\{p_k\})$. The **branch-summed cost** $I_\Sigma^\varepsilon$ is a derived classical-mixture quantity in this sense, useful for operational calibration of $I_0$ against the Schrödinger-cat scale but not the fundamental statement of the bound, which is the modular-local capacity $\chi_{R_S}(\omega) \le C(R_S)$ on the algebra-state pair.

The rest of §9A works in this classical-mixture approximation. All the conclusions about $N_{\max}$, $I_0$ calibration, the Schrödinger-cat scale, and the operational kinematic-exclusion of multi-spot states therefore carry over from the modular-local bound directly. The branch-counting language is the right intuitive handle for this single-region detector calculation.

**Important qualification (effective vs. literal definiteness, via Donald's identity).** Under the modular-local bound (foundations paper §7.6, Theorem 6), the macroscopic-definiteness claim for the screen is more carefully stated than "$N_{\max}$ records fit iff $N \cdot I_0 \le Q_{R_S}$". It uses **Donald's identity** for Araki relative entropy:

$$
\sum_{k} \tilde p_k \, \chi_{R_S}(\omega_{k, R_S}) \;=\; \chi_{R_S}(\bar\omega_{R_S}) + I_{\rm Hol}^{R_S},
$$

where $\tilde p_k = p_k / q$ is the normalized active distribution ($q$ the active-set total weight), $\bar\omega_{R_S} = \sum_k \tilde p_k \omega_{k, R_S}$ the mean state, and $I_{\rm Hol}^{R_S}$ the Holevo-like quantity. Given (H1) branchwise admissibility $\chi_{R_S}(\omega_{k,R_S}) \le C(R_S)$, (H2) the record-instantiation-cost postulate $\chi_{R_S}(\bar\omega_{R_S}) \ge I_0 - \eta_0$, and (H3) operational distinguishability of records (so $H_\epsilon \le I_{\rm Hol}^{R_S} + \eta_{\rm def}$ via Fano), one derives

$$
H_\epsilon \;\le\; C(R_S) - I_0 + \eta_0 + \eta_{\rm def}, \qquad N^{(\epsilon)}_{\rm eff} := \exp H_\epsilon.
$$

Hence the bound is on the *effective* number of spots, not on the raw cardinality of the active set. Single-spot-per-run is *exact* only at exact saturation $I_0 = C(R_S)$ and $\eta_0 = \eta_{\rm def} = 0$; for finite tolerances the bound weakens to $H_\epsilon \le \eta_0 + \eta_{\rm def}$, meaning one spot dominates with probability $\ge 1 - O(\eta_0 + \eta_{\rm def})$ while the others are exponentially suppressed. For the screen example with $C(R_S) \sim 10^{68}$ nats and macroscopic record cost $I_0$ of comparable order, this saturation condition is exactly what calibration of $I_0$ against the observed quantum-to-classical transition is supposed to deliver. The discussion in §9A.3–9A.7 below treats this effective statement as the operational content.

The framework's central commitment is the **record-instantiation-cost postulate (H2)**: instantiating a macroscopic record on $R_S$ requires modular cost at least $I_0$. This is an independent postulate beyond standard AQFT / holography and is calibrated empirically.

**Sharpened structural form of (H2).** A machine-verified audit (`lean/mathlib/QIQTH/H1H2Audit.lean`) establishes that (H2) is genuinely independent of (H1), Donald's identity, Klein positivity, and DPI — a classical KL countermodel satisfying all four hypotheses violates (H2). The same audit yields the equivalent reformulation: for a perfect-record state on event $E_{\rm record}$,
$$\chi_{R_S}(\bar\omega_{R_S}) \ge I_0 - \eta_0 \quad \Longleftrightarrow \quad \sigma_{R_S}(E_{\rm record}) \le e^{-(I_0 - \eta_0)}.$$
Thus (H2) is exactly the assertion that **macroscopic record sectors have exponentially small reference weight** under the canonical sector reference state $\sigma_{R_S}$. A future derivation of (H2) from modular/holographic first principles must produce this reference-weight bound on pointer sectors; Donald's identity and Klein positivity alone are insufficient.

### 9A.1 The macroscopic record subalgebra and the spectrum of screen spots

For the screen region $R_S$, the macroscopic record subalgebra $\mathcal{C}(R_S) \subset \hat{\mathcal{A}}(R_S)$ is generated by the position-localized record projectors $\{P_k\}_{k=1}^N$, one for each macroscopically distinct spot position, with $N \sim 10^6 - 10^9$ for typical screen resolutions. These projectors are mutually commuting and decoherence-stable; off-diagonal coherence between distinct $P_j, P_k$ is suppressed exponentially $\sim e^{-10^{20}}$ and physically zero under (FQ).

The spectrum $\mathrm{Spec}(\mathcal{C}(R_S)) = \{r_1, \ldots, r_N\}$ is the discrete set of macroscopic spot positions. States on $\mathcal{C}(R_S)$ are probability distributions $\{p_k\}$ over spots.

### 9A.2 Per-record cost and the branch-summed cost for the screen

For each spot position $r_k$, define the per-record cost $c_{R_S}(r_k)$ as the Zurek-style physical entropy of the macroscopic record, combining the algorithmic complexity of the macroscopic description (which spot, with what apparatus state) and the residual microscopic entropy of the screen + environment configuration consistent with that record.

For a regional state $\omega_{R_S}$ with spot probabilities $p_k = \omega_{R_S}(P_k)$, the smooth active set $\mathcal{A}_\epsilon(\omega_{R_S})$ is the smallest set of spots carrying total probability $\ge 1 - \epsilon$. The **branch-summed record cost** is:
$$I_\Sigma^\epsilon[\omega_{R_S}] = \sum_{r \in \mathcal{A}_\epsilon} c_{R_S}(r)$$

For a single-spot state: $I_\Sigma \approx I_0$ (one record's cost).
For an $N$-spot state with comparable record costs: $I_\Sigma \approx N \cdot I_0$.

This is **not** the standard von Neumann or renormalized entropy on the screen algebra. It counts the *additive* cost of each occupied macroscopic spot sector, summing rather than coarse-graining over alternatives.

### 9A.3 The Branch-Summed Bound as superselection rule for the screen

The Branch-Summed Holographic Bound applied to the screen region:
$$I_\Sigma^\epsilon[\omega_{R_S}] \le Q_{R_S} = \frac{A(\partial R_S)}{4\ell_P^2} \sim 10^{68} \text{ nats}$$

is the framework's new physical postulate (a derived classical-mixture approximation of the modular-local bound; §9A.0). It is **not** a theorem of standard holography (which bounds entropy, not branch-summed cost), but a *strengthening* of the holographic principle that the framework adopts as a superselection rule.

The conclusions below are stated in the **exact-saturation limit** of Theorem 6 ($I_0 = C(R_S)$, $\eta_0 = \eta_{\rm def} = 0$). For finite tolerances, the precise effective form is the entropy bound $H_\epsilon \le C(R_S) - I_0 + \eta_0 + \eta_{\rm def}$ (§9A.0 / foundations paper Theorem 6), with multi-record states *exponentially suppressed* rather than literally forbidden.

In the exact-saturation limit:
- The physical state space $\mathcal{H}_{\rm phys}$ excludes universal wave functions whose induced regional state on the screen has $I_\Sigma > Q_{R_S}$
- The maximum number of coexisting macroscopic spot records in any physical state is $N_{\max} \approx \lfloor Q_{R_S}/I_0 \rfloor$
- In the regime where each macroscopic record approximately saturates the regional capacity (e.g., the screen substrate has thermal entropy comparable to its holographic capacity at relevant scales), $N_{\max} = 1$, **only single-spot states are physically realizable on the screen** (effective form: a single spot has active probability $\ge 1 - O(\eta_0+\eta_{\rm def})$)

### 9A.4 Per run: one spot, as a kinematic consequence

In any specific run, the universal wave function (within $\mathcal{H}_{\rm phys}$) has its induced state on $\mathcal{C}(R_S)$ supported on a single spot. This is not because of dynamical collapse, not because of branch selection from many physically real branches, but because, at exact saturation, multi-spot states violate the superselection rule (effective form: a single spot dominates the active distribution with overwhelming probability; §9A.3).

Which specific spot is realized depends on the actual physical initial conditions of the screen + environment at the moment of detection (the actual microscopic configuration of screen atoms, vacuum fluctuations, environmental modes). The dynamics is exactly unitary throughout; the resident regional content is single-record because a $\ge 2$-record content is not instantiable under the finite-information restriction, and the run's microscopic initial conditions index *which* single spot it is.

### 9A.5 The Everett-branch question dissolved by superselection

The often-asked question "which Everett branch is realized in this run?" doesn't arise as a foundational puzzle under the superselection rule. The "Everett branches" of an unrestricted-Hilbert-space superposition $\sum_k c_k |x_k\rangle|S_k\rangle|E_k\rangle$ correspond, at exact saturation, to a multi-spot state with $I_\Sigma > Q_{R_S}$ that violates the bound; at finite tolerances, to a state with effective multiplicity $N^{(\epsilon)}_{\rm eff} \ll N_{\rm Everett}$. Either way, the unrestricted Hilbert-space formalism allows writing such states mathematically, but they are either kinematically forbidden (exact saturation) or exponentially suppressed (approximate saturation).

The standard unitary mapping $(a|0\rangle + b|1\rangle)|S_0\rangle \mapsto a|0\rangle|S_0\rangle + b|1\rangle|S_1\rangle$ that textbook QM writes is exactly what the (unmodified, exactly-unitary) dynamics does at the level of the global formal wave function. That formal multi-record vector is a perfectly good calculational/ensemble descriptor; the framework's claim is that its *regional content* — carrying two macroscopically distinct records — exceeds the region's capacity and so is not an instantiable per-run physical content. The resident per-run regional content is therefore single-record, and which record is realized is indexed by the specific actual initial conditions. No Hamiltonian is restricted and the dynamics is exactly unitary.

### 9A.5b The operational answer to the linear measurement obstruction

A standard objection: "By linearity, $U(\alpha|0\rangle + \beta|1\rangle)|S_{\rm ready}\rangle = \alpha|0\rangle|S_0\rangle + \beta|1\rangle|S_1\rangle$, exactly the multi-record state the framework wants to forbid."

This objection assumes that the unrestricted-Hilbert-space wave function is the physically primary object that we have direct access to. The framework denies this.

**We never have direct physical access to amplitudes of the universal wave function.** We have access only to the macroscopic record content on the screen, which is itself a complex quantum system with $\sim 10^{20}$–$10^{25}$ degrees of freedom, entangled with the particle. When decoherence acts on the joint particle + screen + environment system, the cross-overlaps between distinct macroscopic record states become exponentially small:
$$\langle E_0 | E_1 \rangle \sim e^{-\Gamma t} \sim e^{-10^{20}}$$
on physically realistic detection timescales. Under (FQ), these exponentially-small off-diagonal coherence terms are *physically zero* (§7.3 makes this rigorous via the (FQ) precision floor applied to the regional algebra-state).

At the level of physically observable content on the screen, the formal "multi-record state" $\alpha|S_0\rangle + \beta|S_1\rangle$ is therefore *exponentially close to a strict classical mixture*, and under (FQ), exactly a strict classical mixture. The off-diagonal phase coherence that would distinguish the formal multi-record state from a classical mixture is below the precision the regional substrate can encode.

**The physical reality of the screen's macroscopic content**, what's actually displayed on the screen, what cameras would record, what an observer would see, is what we have access to. That content is a classical mixture, not a coherent superposition. The superselection rule then forbids even this classical mixture for sufficiently saturating records.

What actually happens per run: the dynamics is exactly the standard unitary evolution (no Hamiltonian is restricted), but the *physically instantiable regional content* is single-record, because a $\ge 2$-record regional content exceeds $Q_R$ and has no per-run physical referent. The run's actual screen + environment initial conditions index which single record it carries; different runs with different actual initial conditions carry different records. The standard "linear measurement obstruction" describes the formal multi-record global vector — a perfectly good calculational/ensemble descriptor — but that vector is not the per-run regional physical content, which is single-record.

### 9A.6 The Born statistics across runs

Across many runs (sequential detection events in the same universe with one universal wave function evolving through them), different actual initial conditions of screen + environment produce different actual realized spots. Each spot is selected from $\mathrm{Spec}(\mathcal{C}(R_S))$ by the physical (constrained) dynamics from the actual initial conditions.

The Born conjecture: across many runs, the distribution of realized spots reproduces the Born weights $p_k = |\psi_A(x_k) + \psi_B(x_k)|^2$ as the emergent empirical relative frequency. This requires a typicality theorem: for the appropriate measure on actual screen + environment initial conditions, the distribution of realized records under the exactly-unitary dynamics matches the Born weights of the standard QM calculation. This is the second central open problem of the framework.

### 9A.7 Mathematical status

The framework gives a complete structural account of single-spot per run + Born interference across runs *if* the following are established rigorously:

1. **Precise specification of $\mathcal{C}(R_S)$** as the einselected/Darwinistic record subalgebra. Existing math to draw on: decoherent histories, Quantum Darwinism, spectrum broadcast structures.

2. **Per-record cost $c_{R_S}(r)$** rigorously defined via Zurek-style physical entropy.

3. **Branch-Summed Holographic Bound** as a new physical postulate. Connection to deeper finite-information constraints in quantum gravity is conjectural.

4. **Characterization of instantiable regional content** for the screen + environment system, which regional algebra-states satisfy $I_\Sigma \le Q_R$, and the proof that a $\ge 2$-record content violates it (the Macroscopic Definiteness Conjecture). This is a restriction on regional content, not on Hamiltonians; the dynamics is left exactly unitary.

5. **Born typicality theorem** under the exactly-unitary dynamics, the typicality measure on actual screen + environment initial conditions that reproduces the Born weights as emergent across-run realized-spot frequencies.

Each of these is a concrete open problem; together they constitute the framework's explicit research program beyond the borrowed CPW/Witten scaffolding.

### 9A.8 Operational scale: where the superselection bites

The Branch-Summed Bound has a two-parameter structure:
- $Q_R = A(\partial R)/(4\ell_P^2)$: regional holographic capacity (geometric; set by quantum gravity)
- $I_0$: per-record physical cost (experimental parameter, calibrated against the empirically observed quantum-to-classical boundary)

The single-outcome enforcement threshold is at $N \cdot I_0 \approx Q_R$.

**Microscopic regime ($N \cdot I_0 \ll Q_R$): constraint vacuous.** For a lab-scale qubit (single atom, ion, photon polarization), per-record cost is small relative to regional capacity; many coexisting microscopic-record states are allowed; standard QM behavior recovered. Quantum interferometers, atom interferometry, ion traps, superconducting qubits all operate in this regime, and the framework predicts no deviations from standard QM.

**Macroscopic regime ($N \cdot I_0 \to Q_R$): constraint enforces single-record per run.** For screen spots, photographic emulsions, CCD readouts, brain states, etc., per-record cost approaches the regional holographic capacity, and the superselection rule restricts to single-record states. This is precisely the regime where the measurement problem traditionally lives.

**The empirical calibration of $I_0$.** The framework's per-record cost $I_0$ is an experimental parameter of the theory, analogous to GRW's collapse rate $\lambda$. Its value must be calibrated against:
- The largest scale at which Schrödinger-cat-like coherence has been experimentally maintained (best results to date: ~$10^4$-atom molecular interference; macroscopic mechanical oscillators in superposition over picometer distances)
- The smallest scale at which classical-definite outcomes are experimentally established

Current best theoretical estimate from Zurek physical entropy of macroscopic records gives $I_0 \sim 10^{25}$ bits. For this to enforce single-record outcomes at the empirically observed scale, either: (a) the relevant regional capacity is the local detection region (not 1m but the few-cm volume of a CCD pixel and its immediate environment, giving smaller $Q_R$), or (b) the effective per-record cost includes environmental entanglement out to a larger radius, increasing $I_0$ above Zurek's estimate. Both options are under study.

**The framework's empirical content.** Unlike standard QM (which makes no prediction about where the quantum-classical boundary lies) and Many-Worlds (which has no boundary), the framework predicts:
1. There IS a definite scale where macroscopic superpositions become physically impossible
2. This scale is set by the ratio $Q_R/I_0$
3. $I_0$ is an experimental parameter; once calibrated against one boundary observation, the framework predicts the boundary at all other scales
4. The framework distinguishes itself from GRW empirically: GRW predicts stochastic collapse events with rate $\lambda$ producing tiny localization signals (e.g., heating of bulk matter); QIQT-H predicts kinematic exclusion with no stochastic signal, only the boundary itself
5. The framework converges to standard QM in any regime where $N \cdot I_0 \ll Q_R$

This makes the framework empirically testable in a clean way: find the empirical scale at which macroscopic superpositions break down; set $I_0$ to match this scale; predict boundary behavior at other scales; distinguish QIQT-H from GRW via absence of stochastic signal.

---

## 10. The Which-Path Case

### 10.1 Adding a detector at the slit

Now suppose we add a detector at slit $A$ that registers whether the particle passed through slit $A$. The standard QM treatment: after the slits + detector, the formal wave function is
$$|\Psi\rangle_{\rm formal} = \frac{1}{\sqrt{2}}\left(|A\rangle|D_A\rangle + |B\rangle|D_0\rangle\right),$$
where $|D_A\rangle$ is the detector state "registered A" and $|D_0\rangle$ is "did not register."

The detector at slit $A$ becomes entangled with the path. By the time the particle reaches the screen and is detected there, the full formal state is:
$$|\Psi\rangle_{\rm formal}^{\rm post} = \frac{1}{\sqrt{2}}\sum_k\left(\psi_A(x_k) |x_k\rangle|D_A\rangle|S_k^A\rangle|E_k^A\rangle + \psi_B(x_k) |x_k\rangle|D_0\rangle|S_k^B\rangle|E_k^B\rangle\right),$$
where the $S_k^A, S_k^B$ and $E_k^A, E_k^B$ states include the path-detector correlation.

### 10.2 Reduced state at the screen

When we trace over the path-detector + environment (i.e., compute the reduced state on the screen-position algebra), the off-diagonal terms in path are suppressed by decoherence:
$$\rho_{\rm screen}(x, x') = \frac{1}{2}\left[\psi_A(x)\psi_A^*(x') + \psi_B(x)\psi_B^*(x')\right] \cdot \delta_{xx'} \text{ (approx)}.$$

The interference term between $\psi_A$ and $\psi_B$, the cross term $\psi_A^*\psi_B$, is absent because of the path-detector correlation. The screen position distribution is:
$$P_{\rm screen}(x) = \frac{1}{2}|\psi_A(x)|^2 + \frac{1}{2}|\psi_B(x)|^2.$$

No interference fringes. This is the standard "which-path" result.

### 10.3 QIQT-H reading of the which-path case

In the framework:

- The formal wave function includes both paths and their path-detector correlations.
- Per-run wave functions correspond to specific microscopic IC. In any specific run, the path-detector either registers or does not.
- Decoherence at the path detector removes interference between the two paths (standard, unitary); the finite-information restriction then makes a $\ge 2$-record regional content on the path-detector + screen algebra non-instantiable.
- The resident per-run regional content is therefore one specific record: either "(A, $x_k$)" or "(no detection, $x_k$)" for some $k$, with the run's microscopic initial conditions indexing which. The dynamics is exactly unitary and no amplitude is trimmed.
- Across many runs: the distribution is $\frac{1}{2}|\psi_A(x_k)|^2 + \frac{1}{2}|\psi_B(x_k)|^2$ for the spot distribution, with the path-detector correlated with the spot.

The QIQT-H reading is the same structure as in the no-detector case: per-run, single record; across runs, Born statistics. The difference is that the path-detector record correlates per-run with the path taken; this breaks the symmetry between paths $A$ and $B$ in each individual run, so the interference cross-term is absent in the empirical distribution.

**The key point:** the framework does not need a separate "wave function collapse on the path detector" event. The path detector is just another macroscopic recording device; its detection is, in the framework, exactly the same kind of decoherence + finite-information-restriction (single-record regional content) that the screen detection is. The framework's account of the which-path case is structurally identical to the no-detector case, with the path detector simply adding another macroscopic record.

### 10.4 Erasure experiments

In delayed-choice quantum eraser experiments, the path information can be erased after detection, restoring the interference pattern. In standard treatments, this raises subtle questions about retrocausality.

In the framework: the erasure process is itself a unitary interaction at the field-algebra level. If the path information is erased before the path record has become a decohered, macroscopically distinct regional content (before the finite-information restriction makes it single-record), then the erasure can restore the interference. If the erasure is performed after that point (after the per-run regional content on the screen + path-detector region is a single-record content), then the recorded outcome is fixed and erasure does not change it (though it can affect statistical correlations with subsequent measurements).

The framework's reading of the quantum eraser is consistent with the standard one but reframes the puzzle: the question is not "when does collapse happen" but "when does the which-path record become a decohered, macroscopically distinct regional content (so the finite-information restriction makes it single-record)." This is a question about the timing of the decoherence/amplification cascade, not a foundational puzzle; the dynamics remains exactly unitary throughout.

---

## 11. Comparison with Standard Textbook Accounts

### 11.1 Copenhagen account

Standard Copenhagen: "The wave function propagates as a superposition until measurement, at which point it collapses to one outcome with probability $|\psi(x_k)|^2$."

QIQT-H account: "The wave function evolves unitarily throughout — no amplitude is trimmed and the dynamics is exactly unitary. Decoherence makes the macroscopic spot-records non-interfering, and the (FQ) resolution floor makes the residual sub-$\epsilon$ coherence have no physical referent (regional states differing below it are the same physical state). The decisive step is the finite-information restriction: a regional content carrying two or more macroscopically distinct spot-records would exceed the screen region's holographic capacity $Q_R$ and so is not an instantiable physical state, leaving the resident content single-record. The microscopic IC index *which* single spot the run carries. The per-run wave function on the screen region is, after detection, physically a single-record state. No collapse postulate is invoked, and no probability is fundamental — probability emerges only as the relative branch-frequency across runs."

**The difference:** Copenhagen invokes collapse as a fundamental dynamical postulate. QIQT-H derives the single-record outcome as a structural consequence of (FQ) + standard QM ingredients.

### 11.2 Many-Worlds account

MWI: "Every component of the post-measurement superposition is a real branch. The 'observer' is in one branch and 'sees' the spot there, but other branches are equally real."

QIQT-H: "The per-run regional content on the screen region is a single-record content, because a $\ge 2$-record content exceeds the region's finite information capacity and is not instantiable (decoherence having first removed interference; the (FQ) resolution floor removing residual sub-$\epsilon$ coherence). The unrealized records have no per-run physical referent — not 'real elsewhere.' There is one realized outcome per run, not many; the dynamics is exactly unitary and no amplitude is trimmed."

**The difference:** MWI keeps all components of the formal superposition as physically real. QIQT-H takes seriously the finite physical information capacity of bounded spacetime regions: below the (FQ) precision floor, alternative-record amplitudes are physically zero.

### 11.3 Bohmian account

Bohm: "The particle has a definite position at all times, guided by the wave function. The position determines which spot is hit. The wave function passes through both slits; the particle goes through one. There are two ontological layers: the wave function and the particle position."

QIQT-H: "The wave function $\Phi$ is the only *dynamical* ontology (weak ψ-monism); the complete per-run state is the pair $(\Phi, \lambda)$, with $\lambda$ the run's non-dynamical actuality fact. The per-run universal wave function is the actual physical state of the universe in any specific run; the formal wave function is the textbook ensemble descriptor. In any specific run, the per-run regional content is single-record — because a multi-record regional content exceeds the region's finite information capacity and is not instantiable (the capacity bound does this negative work) — and which record is realized is selected by $\lambda$, the run's actual microscopic initial conditions. No particles, no separate dynamical ontology, no guidance equation; the dynamics is exactly unitary."

**The difference:** Bohm adds primitive particle positions as a second *dynamical* layer, guided by $\Phi$. QIQT-H is **weak-ψ-monist** — $\Phi$ is the sole dynamical ontology, with no guidance law and no guided second substance. The structural counterpart of the Bohmian configuration is the non-dynamical run-index $\lambda$ selecting the realized record; the complete per-run state is $(\Phi, \lambda)$. The framework's contribution is the distinction between the formal wave function (ensemble descriptor) and the per-run state (actual physical state), and the recovery of single outcomes from the finite-capacity bound plus $\lambda$, not the addition of a guided second substance.

### 11.4 Decoherence-without-collapse accounts

Some accounts argue that decoherence alone "solves" the measurement problem. QIQT-H agrees that decoherence is part of the answer but explicitly identifies what decoherence does not do:

Decoherence gives the diagonal formal mixed state $\sum_k p_k \omega_k$. It removes interference, but it does **not** by itself select a single record per run — the diagonal mixture still carries every record. The single-record content comes from the finite-information bound: a regional content carrying two or more macroscopically distinct records (coherent or mixed) would cost more information than the screen region's holographic capacity $Q_R$ can hold, so it is not an instantiable physical state. The (FQ) resolution floor separately removes the residual sub-$\epsilon$ coherence (two regional states differing below it are the same physical state). No amplitude is trimmed and the dynamics stays exactly unitary; the per-run microscopic IC only index which single-record outcome the run carries.

---

## 12. Conclusion

### 12.1 What this paper has shown

We have worked through the double-slit experiment end-to-end in the QIQT-H framework:

1. The algebraic QFT setup, with Type II crossed-product algebras for the screen and environment regions.
2. The decoherence calculation, showing how the off-diagonal coherence between distinct screen positions is suppressed by particle-screen-environment entanglement.
3. The distinction between formal wave function (ensemble descriptor) and per-run wave function (specific run with specific microscopic IC).
4. The finite-information capacity bound: a regional content carrying $\ge 2$ macroscopically distinct spot-records costs more information than the screen region's holographic capacity $Q_R$ can hold, so it is not an instantiable physical state — this is what makes the resident content single-record (the decisive step), with the per-run microscopic initial conditions only indexing *which* single spot the run carries.
5. The (FQ) precision floor, which removes the residual sub-$\epsilon$ record-coherence (regional states differing below it are the same physical state), so the resident regional content is a single-record state — with no amplitude trimmed and the dynamics left exactly unitary.
6. The Born interference pattern emerging as the statistical distribution of single-spot outcomes across many runs.
7. The which-path case, where the path-detector correlation breaks the symmetry between paths and absent the cross term in the empirical distribution.

The framework gives a complete structural account of the double-slit phenomenology without invoking any collapse postulate, without adding particle positions, without multiplying worlds, and without modifying the Schrödinger evolution of the underlying field algebra.

### 12.2 What the framework's account of "collapse" actually is

In the QIQT-H reading, "collapse" is not a dynamical event. It is the *structural consequence* of three ingredients working together:

- **Decoherence** (standard QM, unitary): off-diagonal coherence between macroscopic records is suppressed by environmental entanglement. This removes interference but leaves a multi-record mixture — it does not by itself select one record.
- **Finite-information restriction** (the decisive step): a regional content carrying two or more macroscopically distinct records exceeds the region's holographic capacity $Q_R$ and so is not an instantiable physical state. The resident regional content is therefore single-record. The run's microscopic initial conditions index *which* record (they do not produce the single-ness).
- **(FQ) resolution floor** (foundational postulate): the residual sub-$\epsilon$ record-coherence has no physical referent (regional states differing below the floor are the same physical state). No amplitude is trimmed; the dynamics stays exactly unitary.

The Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly. The "collapse" is what the standard textbook observes from outside the framework: a single spot appears on the screen, the wave function "seems to" jump from a continuous superposition to a localized state. In the framework, what is really happening is that the per-run regional content on the screen region is, after detection, a single-record content — because a multi-record content is not instantiable in the region's finite information capacity. The apparent "jump" is just the recognition that the per-run physical content was always a finite-information regional content; there is no dynamical jump, no amplitude trimmed, and the global evolution stays exactly unitary.

### 12.3 What remains open: the math status

The framework's account of the double-slit relies on:
- The (FQ) precision floor with quantitative form $\epsilon(R)$, qualitative existence follows from the foundational postulate; quantitative form is open
- Decoherence + (FQ) yielding strict classical mixture on the regional algebra, argued qualitatively with numerical scaling; not yet a formal theorem
- The Born-typicality theorem (the appropriate measure on actual initial conditions across actual runs yields Born weights), sketched here, rigorous proof open

**Mathematical status of the framework, honestly characterized:**

| Component | Status |
|---|---|
| Type III$_1$ classification of local QFT algebras | Rigorous theorem (Buchholz, Borchers, Longo) |
| Crossed-product Type II construction with gravitational dressing | Rigorous (Witten 2022; CPW 2022; CLPW 2022) |
| Renormalized entropy on Type II algebras = generalized entropy differences | Rigorous (in CPW's setting) |
| (FQ) axiom as foundational postulate | Clearly stated; not derived |
| Qualitative existence of precision floor $\epsilon(R) > 0$ | Lemma argued qualitatively |
| Decoherence-suppression numerical scaling ($\sim e^{-10^{20}}$) | Standard decoherence theory; numerically estimable |
| Strict classical mixture from decoherence + (FQ) | Asserted, not formally proved |
| Born statistics from typicality of initial conditions across runs | Conjectural; explicit theorem missing |

The framework has the *scaffolding* (Type II algebras from CPW/Witten) and the *axiom* ((FQ) literal reading). Qualitative consequences are worked out. Explicit theorems for the central claims are open.

This is the status of a research program with concrete, well-defined open problems, not the status of a completed mathematical theory. Each open problem can be attacked by an analyst willing to engage with algebraic QFT and foundations of QM.

The present worked example demonstrates that *if the open problems are resolved*, the framework gives a complete and structurally clean account of the double-slit. It does not constitute a rigorous proof of the framework's resolution of the measurement problem; it demonstrates the *structure* of that resolution on a concrete textbook case.

### 12.4 The take-home

The double-slit experiment, the textbook archetype of "wave-particle duality" and "collapse," is in the QIQT-H framework simply a worked example of finite physical specification precision applied to wave-function instantiation in bounded spacetime regions. The wave-like pattern is what the wave function physically *is*; the particle-like spot is the single-record regional content the finite-information restriction leaves resident on the screen (decoherence having removed interference, the (FQ) resolution floor removing residual sub-$\epsilon$ coherence); the Born statistics across runs reproduce the interference pattern as an emergent frequency. There is no duality, no collapse, no mystery, and the dynamics is exactly unitary — only the literal physical-instantiation reading of the holographic information bound, applied carefully to a regional Type II algebra with proper attention to per-run vs ensemble structure.

---

## Acknowledgements

The author thanks the participants in extended discussions that informed the framework and this worked example.

---

## References

1. Bekenstein, J. D. (1981). Universal upper bound on the entropy-to-energy ratio for bounded systems. *Phys. Rev. D*, 23, 287.
2. Bohm, D. (1952). A suggested interpretation of the quantum theory in terms of "hidden" variables. *Phys. Rev.*, 85, 166.
3. Bousso, R. (2002). The holographic principle. *Rev. Mod. Phys.*, 74, 825.
4. Chandrasekaran, V., Longo, R., Penington, G., & Witten, E. (2022). *An algebra of observables for de Sitter space.* JHEP 02 (2023) 082. arXiv:2206.10780.
5. Chandrasekaran, V., Penington, G., & Witten, E. (2022). *Large N algebras and generalized entropy.* JHEP 04 (2023) 009. arXiv:2209.10454.
6. Everett, H. (1957). "Relative state" formulation of quantum mechanics. *Rev. Mod. Phys.*, 29, 454.
7. Feynman, R. P., Leighton, R. B., & Sands, M. (1965). *The Feynman Lectures on Physics, Vol. III.* Addison-Wesley. (Double-slit Ch. 1.)
8. Haag, R. (1992). *Local Quantum Physics: Fields, Particles, Algebras.* Springer.
9. Jensen, K., Sorce, J., & Speranza, A. J. (2023). *Generalized entropy for general subregions in quantum gravity.* arXiv:2306.01837.
10. Joos, E., Zeh, H. D., Kiefer, C., Giulini, D., Kupsch, J., & Stamatescu, I.-O. (2003). *Decoherence and the Appearance of a Classical World in Quantum Theory.* Springer.
11. Kapłański, P. (2026). *One Wave Function, One World: How the Holographic Information Bound Selects the Macroscopic World.* (Position paper.)
12. Kapłański, P. (2026). *One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint.* (Foundations paper.)
13. Palmer, T. N. (2025). *Rational Quantum Mechanics: Testing Quantum Theory with Quantum Computers.* Proc. Natl. Acad. Sci. USA. arXiv:2510.02877.
14. Susskind, L. (1995). The world as a hologram. *J. Math. Phys.*, 36, 6377. arXiv:hep-th/9409089.
15. 't Hooft, G. (1993). *Dimensional reduction in quantum gravity.* arXiv:gr-qc/9310026.
16. Wallace, D. (2012). *The Emergent Multiverse.* Oxford University Press.
17. Witten, E. (2022). *Gravity and the crossed product.* JHEP 10 (2022) 008. arXiv:2112.12828.
18. Zurek, W. H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Rev. Mod. Phys.*, 75, 715.

---

*End of manuscript.*
