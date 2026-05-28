---
title: "One Wave Function, One World: How the Holographic Information Bound Selects the Macroscopic World"
author: "Paweł Kapłański"
date: 2026-05-25
keywords: [foundations of quantum mechanics, holographic principle, Bekenstein-Bousso bound, measurement problem, finite-precision wave function]
---

# One Wave Function, One World: How the Holographic Information Bound Selects the Macroscopic World

## Abstract

The Bekenstein-Bousso bound is a Lorentz-invariant limit on the information content of any bounded region of spacetime. Taken **literally** as a physical information limit on the wave function, and not merely as an entanglement-entropy inequality on a reduced density matrix, this bound has a direct consequence for the measurement problem. The wave function, regarded as a physical object instantiated in spacetime, has finite physical specification precision determined by the holographic capacity of the region. Amplitudes physically within $\epsilon(R)$ of $0$ are physically equivalent to amplitude exactly $0$; amplitudes within $\epsilon(R)$ of $1$ are physically equivalent to amplitude exactly $1$. In any per-run universal wave function, dynamical concentration via decoherence and microscopic initial conditions drives the amplitudes for distinct macroscopic record components toward $0$ or $1$. Below the resolution floor set by the bound, these amplitudes *are* $0$ or $1$ physically: the per-run wave function physically *is* a single-record state. The macroscopic world, a single realized outcome per run, emerges as a structural consequence of applying the holographic information bound literally to the wave function as a physical state of spacetime. No collapse postulate, no hidden particle positions, no branching worlds, no modal value-rule are required. The Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly. The Born rule is preserved exactly. Born statistics emerge from typicality of microscopic initial conditions across runs (identified as the central open quantitative problem). The mathematical home of the bound is the algebraic QFT framework with gravitational dressing, the Type II crossed-product algebra construction of Chandrasekaran-Penington-Witten (2022) and Witten (2022) provides the rigorous infrastructure; the literal physical-instantiation reading of the bound is our additional foundational postulate on top.

---

## 1. The starting point: a hidden inconsistency

Standard foundational discussion of quantum mechanics typically holds four claims simultaneously:

1. The wave function is physically real.
2. Bounded spacetime regions have finite physical information capacity (the holographic principle of quantum gravity).
3. The amplitudes of the wave function are exact real numbers, specifiable to arbitrary precision in principle.
4. Macroscopic superpositions, once formed, persist as physically real components forever.

These four claims cannot all be true. If the wave function is physically real (1) and amplitudes are exact real numbers (3), specifying the wave function in any bounded region requires infinitely many physical bits, contradicting (2). If (4) is added, macroscopic record alternatives persist as infinite-precision-amplitude branches that the region cannot physically contain. *The standard measurement problem is, at root, an inconsistency between (1)–(4).*

The standard interpretations of QM each resolve the tension by denying one of the four claims:

- **Many-Worlds** keeps (1)–(4) but pays in branching ontology, infinitely many physically real branches; spacetime-information overflow rarely confronted.
- **Bohmian mechanics** denies (1) in its strong form (wave function is not the complete physical content); adds continuum-valued particle positions.
- **Objective collapse** (GRW, CSL, DP, OR) denies (4) by modifying Schrödinger evolution.
- **QBism, relational QM** deny (1) in favor of epistemic or relational status.
- **Modal interpretations, decoherent histories** add value-rules or history-selection structures to break (4) without modifying dynamics.

Each pays a distinct foundational price.

This paper proposes a different resolution: **deny (3) at the level of physical instantiation while preserving the mathematical formalism, and recognize that the textbook formal wave function is the ensemble descriptor, not the per-run physical state**. The framework is **ψ-monist**: the wave function is the only ontology. No Bohmian particles, no extra fields, no second physical layer of any kind. What the framework adds is the distinction between the *formal wave function* (the textbook abstract one, an ensemble descriptor across many runs) and the *per-run wave function* (the actual physical wave function of the universe in any specific run). The wave function in any bounded region of any specific run has finite physical specification precision determined by the holographic information capacity of the region. Amplitudes physically within $\epsilon(R)$ of $0$ are physically equivalent to amplitude exactly $0$; within $\epsilon(R)$ of $1$, physically equivalent to amplitude exactly $1$. The mathematical continuum of amplitudes remains the indispensable formal apparatus; the physical instantiation is finite-precision.

With this denial of (3), all four claims can be reconciled: the wave function is physically real (1); bounded spacetime has finite capacity (2); amplitudes have finite physical specification precision (denial of (3) at the physical-instantiation level); macroscopic superpositions resolve dynamically into single-record states (denial of (4) as structural consequence, not as added postulate).

**This is arguably the least radical resolution.** It does not multiply worlds, add particles, modify dynamics, or subjectivize the wave function. It is **ψ-monist**, the wave function is the only ontology, and accepts one physically natural constraint: bounded spacetime cannot physically contain infinite information. This constraint is *independently motivated* by holography and quantum gravity. The measurement problem is resolved by recognizing that (1)–(4) cannot all hold at the level of physical instantiation, that the textbook formal wave function is the ensemble descriptor rather than the per-run physical state, and that denying (3) at the physical-instantiation level (combined with the formal/per-run distinction) is the move that preserves the most.

## 2. The bound

The holographic information bound, in its modern Bousso form, asserts that for any bounded region $R$ of spacetime, the information content of any physical state in $R$ is bounded:

$$Q_R \le \frac{A(\partial R)}{4 \ell_P^2}.$$

The right-hand side is the intrinsic Lorentz-invariant 2-area of the region's boundary in Planck units. The area is a geometric quantity, the same for every observer in every reference frame.

The bound has pedigree across the quantum-gravity literature. Bekenstein's argument from black-hole thermodynamics. Hawking's derivation of $S_{\rm BH} = A/(4\ell_P^2)$ (see the companion *Tutorial* §3 for a textbook-level derivation via the Hawking temperature and the first law). 't Hooft's dimensional-reduction arguments. Susskind's holographic principle. Bousso's covariant generalization. Banks (2025) arguing that finite entropy implies finite Hilbert-space dimension for bounded subsystems.

The values are enormous in conventional terms, $\sim 10^{70}$ nats for a one-meter region (one nat $= 1/\ln 2 \approx 1.443$ bits; numerical values below are units-independent), but **finite**, and they **scale as boundary area rather than volume**. This is the *holographic* character of the bound.

In standard treatments, $Q_R$ is read narrowly as a bound on the entanglement entropy $S_{\rm ent}(R) = -\mathrm{Tr}(\rho_R \log \rho_R)$ of region $R$ with its complement. We propose reading it **literally**: as a bound on the physical information content of the wave function in $R$, the information actually needed to physically instantiate the wave function as a state of spacetime in that region. We call this axiom **(FQ)**:

> **(FQ).** *For every physical per-run wave function $|\Psi\rangle_{\rm run}$ of the universe and every bounded region $R$ of space, the total information content needed to physically instantiate $|\Psi\rangle_{\rm run}$ in $R$ is bounded by $A(\partial R)/(4\ell_P^2)$.*

The literal reading is the strong reading. It is not the standard entropy-of-the-reduced-state reading. It is what Bekenstein's original information-theoretic motivation suggests, and it is what taking the bound "as a Lorentz-invariant information limit in spacetime" literally requires.

The mathematical home for the bound at the foundational level is **algebraic quantum field theory with gravitational dressing**. In ordinary QFT, the local algebra $\mathcal{A}(R)$ of a bounded region is of Type III$_1$ in the von Neumann classification, it has no trace, no factorization of the Hilbert space, no notion of "number of degrees of freedom," and entanglement entropy is UV-divergent. This is the formal obstruction that the narrow entanglement-entropy reading was implicitly papering over. The recent work of Chandrasekaran, Penington, and Witten (2022) and Witten (2022) shows that gravitational dressing, implemented as the crossed product with the modular flow, converts the Type III$_1$ regional algebra into a **Type II algebra** with semifinite trace (finite trace in the special case of the de Sitter static patch) and a well-defined renormalized entropy whose differences match the generalized entropy $A(\partial R)/(4\ell_P^2) + S_{\rm matter}$.

We take this algebraic infrastructure as the rigorous home for the foundational application. The CPW framework provides the mathematics, the Type II structure, the trace, the renormalized entropy. We postulate the holographic bound $S_{\rm ren} \le A(\partial R)/(4\ell_P^2)$ on the regional Type II algebra as the foundational axiom (FQ). The bound is motivated by the holographic principle of quantum gravity; it is not a derived theorem of CPW. The credit division is sharp: CPW supplies the algebraic infrastructure; we supply the foundational axiom and the application to QM measurement.

**The framework's central new physical principle, the Branch-Summed Holographic Bound**, is then formulated on top of this CPW scaffolding. It is a **superselection rule** on the physical state space, not a derivation from standard holography. It states (in the exact-saturation limit; the precise effective form is in the *Honest qualifications* paragraph below and in technical paper Theorem 6): *the sum of per-record costs across coexisting decoherent macroscopic records in any bounded region $R$ is bounded by the holographic capacity $Q_R$. Universal wave functions violating this bound are kinematically excluded from the physical state space; physical Hamiltonians are constrained to preserve the physical state space (analogous to gauge invariance in gauge theory).* Within the physical state space, Schrödinger / Heisenberg evolution holds exactly under physical Hamiltonians. The macroscopic world, single-record per region per run, emerges as a **kinematic structural feature** at exact saturation (and as exponentially-suppressed multi-record content at approximate saturation), not as a dynamical selection event. The Everett branches of unrestricted-Hilbert-space superpositions are either forbidden or exponentially suppressed depending on the saturation regime; they don't enter physics. The framework is **ψ-monist** (wave function as only ontology) with the physical state space constrained by the Branch-Summed Bound.

**Modular-local form (technical note).** The branch-summed expression above is an operational calibration of the bound. The *foundational* form of the bound (technical paper §7.6, §7.7) is **modular-local**: for each bounded region $R$, the Araki / Type II core relative entropy $\chi_R(\omega) = S_{\hat{\mathcal{A}}(R)}(\omega_R \| \sigma_R)$ (with $\sigma_R$ the canonical sector reference state of §7.6) is bounded by the regional capacity $C(R) = A(\partial R)/(4\ell_P^2) = Q_R$; for spacelike-separated regions $D_A, D_B$ admissibility is the *meet* of local predicates, $\mathrm{Adm}(D_A \cup D_B) = \mathrm{Adm}(D_A) \wedge \mathrm{Adm}(D_B)$, with no joint cutoff imposed on $\hat{\mathcal{A}}(D_A) \vee \hat{\mathcal{A}}(D_B)$. Under this modular-local form, **no-signaling follows automatically from microcausality for localized non-selective operations** $[\hat{\mathcal{A}}(D_A), \hat{\mathcal{A}}(D_B)] = 0$, it is not an additional axiom. The branch-summed cost is the classical-mixture approximation of $\chi_R$ in the regime where the regional state is a strict mixture over decoherent macroscopic records (which is what measurement produces after decoherence). The operational language of "counting records" remains valid in this approximation and is what the experimental parameter $I_0$ calibrates against.

**Honest qualifications.** In the modular-local formulation (technical paper §7.6), four precise statements: (a) macroscopic definiteness is an *effective* statement on the *normalized active distribution* $\tilde p_k = p_k/q$ (where $q$ is the active-set total weight), the relevant bound is on the active-set Shannon entropy $H_\epsilon$, with $N^{(\epsilon)}_{\rm eff} := \exp H_\epsilon \le \exp(C(R) - I_0 + 2\eta_\epsilon)$ (where $\eta_\epsilon := (\eta_0 + \eta_{\rm def})/2$ amalgamates the technical paper's record-cost slack $\eta_0$ and Fano residual $\eta_{\rm def}$), not on the raw cardinality of records; single-record-per-run is exact only at exact saturation $I_0 = C(R)$ and $\eta_\epsilon = 0$, with finite $\eta_\epsilon$ giving the weaker $H_\epsilon \le 2\eta_\epsilon$; (b) admissibility is *stagewise*, imposed at each process stage on causally-instantiated regions, not as a single global condition; (c) admissibility applies *causally*, a future joint diamond's capacity constrains the future joint state only when that diamond becomes instantiated, never retroactively deleting past separately-admissible branches; (d) instruments must be *branchwise* admissibility-preserving on every region $R \Subset J^+(O_a)$ in the causal future of each outcome record $O_a$. The lab-scale Born deviation is bounded as $\delta_R \le \mathbb{E}[\chi_R]/C(R)$, with the **conditional** order-of-magnitude estimate $\delta_R \sim 10^{-27}$ for a 1-m, 1-kg region, applicable under enclosing-wedge / CFT-ball hypotheses and assuming $\Delta S_R \ge 0$, *not* a generic QFT consequence.

**The theory has two physical inputs:** the **regional holographic capacity** $Q_R = A(\partial R)/(4\ell_P^2)$, a geometric quantity set by quantum gravity (not adjustable); and the **per-record physical cost** $I_0$, an **experimental parameter** of the theory analogous to GRW's collapse rate $\lambda$. The single-outcome enforcement threshold is at $N \cdot I_0 \approx Q_R$: below this scale the constraint is operationally vacuous (standard QM recovered); above it the constraint kinematically enforces single-record per run. The empirical content of the framework: there is a definite quantum-to-classical boundary scale set by $I_0$; this scale is testable against current and future Schrödinger-cat-type experiments; and the framework distinguishes itself from GRW empirically, GRW predicts stochastic collapse events with tunable parameter $\lambda$; QIQT-H predicts kinematic exclusion (no stochastic signal beyond the boundary itself).

The technical paper (§§6.8 and 7.6) formalizes the postulate using decoherent histories, Quantum Darwinism, smooth support / Rényi-0 counting, and Zurek-style per-record cost, and identifies what new physics this requires (the Branch-Summed Bound itself is a new strengthening of holography, not derivable from standard QG results). The price the framework pays: the set of physical Hamiltonians is restricted; standard Hilbert-space Hamiltonians are mathematically writeable but unphysical at scales where the constraint bites. At lab scales the constraint is operationally vacuous; at macroscopic measurement scales (where records approach the regional capacity) it enforces single-record per run kinematically. We develop the formal apparatus in the companion technical paper; here we proceed informally.

## 3. The mechanism: finite physical precision

A wave function in $R$ with bounded physical information content has bounded **physical resolution**.

To say that the wave function's amplitudes have specific values requires *encoding* those values in the physical state of the region, that is, in the actual physical substrate of spacetime that the wave function is a state of. Encoding requires information. The information available is bounded by $Q_R = A(\partial R)/(4\ell_P^2)$. Therefore the amplitudes of the per-run wave function in $R$ are physically specified only up to a finite resolution.

**The consequence is decisive.** Let $\epsilon(R)$ be the physical resolution floor for the per-run wave function in $R$, the smallest amplitude difference that the physical substrate of $R$ can encode. Then:

- Two amplitudes within $\epsilon(R)$ of each other are *physically the same state*.
- An amplitude within $\epsilon(R)$ of $0$ is *physically the same as amplitude exactly $0$*.
- An amplitude within $\epsilon(R)$ of $1$ is *physically the same as amplitude exactly $1$*.

This is not a measurement-precision limitation imposed by external observers. It is a *physical* limitation on the wave function itself as a state of spacetime. Below the resolution, there is no physical fact about whether the amplitude is exactly $0$ or some tiny nonzero value, these are the same physical state. The wave function, as a physical object, simply does not encode the distinction.

**The Mandelbrot rendering analogy.** The mathematical Mandelbrot set has infinite fractal detail. A physical rendering on a finite-resolution display, pixels, bits, screen geometry, cannot resolve detail finer than its pixel scale. Below pixel scale, two mathematically distinct points are the *same physical pixel*. The pixel does not partially exist or fractionally exist; it is one specific color.

The wave function is similar. As an abstract Hilbert-space vector it can have arbitrary continuous amplitudes. As a *physical* state of spacetime it is rendered with finite resolution determined by the holographic bound on the region. Below resolution, fractional amplitudes are not physically realized; they are physically equivalent to exact $0$ or exact $1$.

**Defense against the qubit objection.** A standard objection: "A qubit has Hilbert dimension 2 and entropy bound $\log 2$, but the Bloch sphere is a continuum of pure states $\alpha|0\rangle + \beta|1\rangle$. Finite entropy doesn't imply finite amplitude precision."

The framework's response distinguishes the mathematical idealization from the physical instantiation. **The Bloch sphere stands in the same relation to a physical qubit as Euclidean geometry stands to a physical measuring rod**: indispensable, extraordinarily accurate mathematical idealization, but not a literal description of what the physical object instantiates with infinite precision. No physical measuring rod realizes exact Euclidean points; no physical qubit realizes exact Bloch-sphere amplitudes.

A physical qubit lives somewhere, in some atomic, photonic, or other physical substrate occupying a spatial region. The amplitudes $\alpha, \beta$ must be physically encoded in that substrate. The holographic bound on the region gives the precision budget. For a qubit in a 1m region, $Q_R \sim 10^{70}$ bits, amplitude precision is astronomically fine; the Bloch sphere is effectively continuous. **This is precisely why standard QM works at lab scales: the framework reproduces ordinary continuous-qubit phenomenology because the physical precision floor is far below experimental resolution.** For a qubit in a Planck-scale region, the bound bites and the Bloch sphere is genuinely discretized.

For *macroscopic* systems, where each macroscopic record component, considered as the full quantum state of the apparatus+environment region, uses a substantial fraction of the regional capacity, and superpositions of multiple records require encoding all of them, the available precision for amplitudes between records is finite. This is the operationally relevant regime for the measurement problem, and it is where the resolution floor has structural consequences.

**Witten provides the mathematical infrastructure; we add the literal reading.** The Chandrasekaran-Penington-Witten Type II algebra framework rigorously gives the regional algebra and its renormalized entropy. But Witten's algebraic theorem operates on a continuous normal-state space; algebraic equality is exact, not approximate. The literal physical-instantiation reading we postulate goes beyond Witten: amplitudes within physical precision are physically the same state, not merely close. This is the additional foundational postulate. It is compatible with Witten's framework, it is the stronger physical reading that taking the bound literally as an information limit in spacetime requires, but it is not derived from Witten's theorem directly. (See companion technical paper §4.3 for the precise distinction.)

## 4. Why per-run amplitudes concentrate

For the precision mechanism to deliver a single realized outcome per run, the per-run wave function's amplitudes for distinct macroscopic record components must actually concentrate near $0$ and $1$, not remain spread evenly.

They do, dynamically. This is the role of **decoherence** combined with **microscopic initial conditions**, read as physical per-run dynamics rather than ensemble diagonalization.

**The classical statistical mechanics analogy.** When one says a gas has temperature $T$, one is not saying every molecule has the same energy. The macrostate $T$ is a *descriptor over actual microstates* across realizations: each actual gas realization has its specific molecular configuration; "temperature $T$" labels the distribution across realizations.

Likewise, when one talks about "the double-slit experiment" with a particle in state $\alpha|0\rangle + \beta|1\rangle$, one is using a subsystem-level abstraction. The actual physical wave function of the universe in any specific particle's run is the *universal wave function*, particle + apparatus + environment + everything, which differs across runs because actual physical universes differ in actual physical detail (different particles, different apparatus microstates, different environments). There is *one* universal wave function per run; the textbook subsystem expression $\alpha|0\rangle + \beta|1\rangle$ is a subsystem abstraction, not the per-run universal wave function.

This is wavefunction-monist standard QM: the universal wave function is the complete physical state. What the framework adds is (FQ), a finite-information constraint on this universal wave function per region. Different runs of "the same experiment" correspond to different actual universal wave functions because the actual universe differs in each run.

In any actual run of any actual measurement, the system entangles with an apparatus and with an environment. The environment in any specific run has specific microscopic initial conditions, particular molecular configurations, particular thermal photons, particular vacuum fluctuations, uncontrolled by the experimental preparation. Measurement is a highly unstable, amplifying, decohering physical process: tiny microscopic differences are amplified into distinct macroscopic record outcomes. In any specific run, the per-run dynamics maps the specific microscopic IC into a specific macroscopic record. The ensemble average across many runs reproduces the formal mixed-state $\sum_i |c_i|^2 \omega_i$; per-run states are individually concentrated.

**Response to the standard decoherence objection.** A standard objection: "Linear unitary evolution preserves the formal amplitudes; $c_i$ does not become 0 or 1." This objection treats the textbook subsystem wave function as if it were the complete per-run physical state. The framework denies this: the textbook expression is a subsystem-level abstraction; the per-run physical state is the universal wave function, which in any specific run starts from specific actual physical initial conditions of the universe (specific particle, specific apparatus microstate, specific environment). The amplifying decoherent measurement process maps the specific actual initial conditions of that run into a specific macroscopic record, analogous to how, in classical statistical mechanics, a thermal cascade in a specific gas realization produces a specific macroscopic trajectory while the canonical ensemble aggregates over different realizations with different actual molecular configurations.

This is not hidden variables in *any* sense, Bohmian or otherwise. The framework is **ψ-monist**: the wave function is the only ontology. There are no Bohmian particles, no extra fields, no second ontological layer. The "microscopic structure" of the per-run wave function is not an additional ontological commitment, it is simply *the actual physical wave function of the universe in any specific run*, which is finer-grained than the textbook formal ensemble descriptor. The per-run wave function is what the wave function IS in each run. The formal wave function is the calculational descriptor of the distribution of per-run wave functions across many runs. There is one ontology, the wave function, but it comes in two senses: per-run (the actual physical reality) and formal (the ensemble descriptor used in textbook calculations).

**The decisive role of (FQ)**: once the per-run amplitudes shrink below the resolution floor $\epsilon(R)$, *they are physically the same state as amplitude $0$*. The branch is not "weighted small"; it physically does not exist. Once one amplitude grows above $1 - \epsilon(R)$, *it is physically the same state as amplitude $1$*. The realized outcome is the wave function's actual physical state.

The combination, dynamical concentration of amplitudes via decoherence + finite physical resolution of the wave function via (FQ), produces a single-record per-run wave function as a structural consequence. No collapse postulate is needed. The Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly; the holographic bound limits the wave function's physical resolution; the per-run state physically *is* one definite outcome.

Standard unitary QM without (FQ) gives only approximate decoherence, branches retain their formal amplitudes, and we're forced into Many-Worlds or into a separate selection mechanism. With (FQ) read literally, the precision floor *does the selection structurally*: branches below resolution are physically nonexistent. The macroscopic world emerges.

## 5. The position

With (FQ) read literally and the precision mechanism in place, the position has the following structure.

**One wave function.** The universe is described by a wave function evolving unitarily under the Schrödinger / Heisenberg evolution of the underlying field algebra. The dynamics is not modified.

**One world per run.** Each actual run corresponds to one specific per-run universal wave function, evolving unitarily from specific microscopic initial conditions, subject to (FQ). The per-run wave function in any region containing apparatus + environment has a single macroscopic record component above the (FQ) resolution; alternative components have amplitudes below the resolution and *are physically the same state as* amplitude zero.

**Born statistics from typicality.** Across many runs, the distribution of microscopic initial conditions reproduces the Born weights $|c_i|^2$ for relative frequency of macroscopic outcome $i$. This is a typicality argument analogous to those in classical statistical mechanics and analogous to (but distinct from) Bohmian $|\psi|^2$-equivariance; we sketch it here and identify rigorous formulation as the central open quantitative problem in the companion technical paper.

**The holographic bound as the structural ingredient.** Without (FQ), per-run amplitudes never become exactly $0$ or exactly $1$, branches remain present with small but nonzero weight, and we are forced into Many-Worlds (every branch is real) or into a separate selection mechanism (collapse, modal value-rule, hidden variable). With (FQ) read literally as a Lorentz-invariant physical information limit on the wave function in spacetime, the precision floor *does the selection structurally*: branches below resolution are physically nonexistent. The macroscopic world emerges as a structural consequence, single outcomes per run, no collapse postulate.

## 6. What this avoids and what it does not avoid

**No collapse postulate.** The Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly. No non-unitary transition during measurement. What appears in standard accounts as collapse is the joint product of decoherence (dynamical amplitude concentration) and finite physical resolution (the (FQ) bound rendering near-zero amplitudes physically equivalent to zero).

**No hidden particle positions.** No Bohmian particles in $3N$-dim configuration space.

**No branching realities.** Single-world per run. The "branches" of the formal-textbook superposition are mathematical artifacts of the ensemble description; the per-run physical wave function has a single record above the (FQ) resolution.

**No modified Schrödinger.** No stochastic terms, no gravitational reduction parameters tuned against experiment.

**No epistemic reading.** The wave function is real, the realized outcome is real, the holographic bound is real, the resolution floor is real.

**No additional value-rule, no modal logic.** The macroscopic world emerges from the dynamics and the bound; no separate rule is required.

**ψ-monism: only the wave function.** The framework adds no ontology beyond the wave function, no Bohmian particles, no extra fields, no second ontological layer. What it adds is the recognition that the *per-run wave function* (the actual physical wave function of the universe in any specific run) differs from the *formal wave function* (the textbook ensemble descriptor used in calculations). The per-run wave function in each actual run is a definite physical state at the level of the holographic bound's resolution; the formal wave function is the descriptor of the distribution across runs. There is one ontology, the wave function, but it comes in two senses, and the textbook conflation of "formal" with "per-run" is what generates the apparent measurement problem.

**The Bell escape: measurement independence via holographic nonseparability.** The framework rejects Bell's measurement-independence assumption $\rho(\lambda \mid a, b) = \rho(\lambda)$, but not in the form of conspiratorial classical superdeterminism. The rejection is principled: a Bell experiment is one finite-information physical process embedded in a common spacetime history, not three independently variable pieces (source, Alice's setting, Bob's setting). In QFT, local algebras don't factor independently between region and complement (Type III$_1$); under gravitational dressing, regional structure is globally constrained by holographic information bounds. Classical separability of "this region's variables vary independently of that region's variables" is *already false at the algebraic level* in QFT. Operational free choice is preserved (no signaling, no loss of empirical freedom); what is denied is the metaphysical counterfactual that exact source-state and arbitrary later-setting are independently variable physical facts. The framework pays the Bell price at measurement independence rather than at relativistic locality or unitary dynamics. This preserves the framework's commitments to no preferred foliation, no nonlocal collapse, exact unitary evolution, and Lorentz-covariant information bounds.

## 7. The role of microscopic initial conditions

A standard preparation procedure fixes the macroscopic features of the prepared state but does not fix microscopic environmental detail, air molecules, thermal photons, vacuum fluctuations, the cosmological background. These microscopic details are encoded in the per-run universal wave function.

Different runs of the "same" experiment correspond to slightly different per-run universal wave functions. Under the Concentration Conjecture, these microscopic differences are exactly what drives different per-run regional states to concentrate on different macroscopic records. The Born rule, on the present view (conditional on the conjecture and on the Born-typicality program), describes the *distribution of which record is realized* across the ensemble of microscopic initial conditions, propagated through (FQ)-constrained dynamics.

This structurally parallels classical statistical mechanics, the macroscopic state of a gas emerges from uncontrolled microscopic phase-space conditions, with the important caveat that the parallel is currently a conjecture, not a derivation.

## 8. Comparison with standard alternatives

**Versus Copenhagen.** Copenhagen invokes a collapse postulate without dynamics. We invoke none. The (conjectural) single-record per-run behavior is structural in the algebraic framework, not dynamical collapse.

**Versus Many-Worlds.** MWI posits all components of the formal wave function as equally real branches. We are (conditionally) single-world per run: only one record is realized on the regional algebra-state. The "branches" are artifacts of the formal ensemble description.

**Versus Bohmian mechanics.** Bohm adds particle positions in $3N$-dim configuration space as a separate ontological layer beyond the wave function, with a guidance equation connecting the two. We add no second ontological layer. The framework is ψ-monist: only the wave function exists. The per-run wave function is just the actual physical wave function; the formal wave function is the ensemble descriptor. No particles, no fields, no extra structure, just the recognition that textbook QM computes ensemble averages rather than per-run states.

**Versus objective collapse.** GRW, CSL, DP, OR modify Schrödinger with collapse terms. We modify nothing dynamical at the level of the underlying field algebra. The single-outcome behavior, conditional on the conjecture, is structural.

**Versus QBism and relational QM.** Those treat the wave function as epistemic or perspectival. We are objectively realist about both the per-run wave function and the regional Type II algebra.

**Versus Ballentine's ensemble interpretation.** The closest neighbor. Ballentine treats the formal wave function as an ensemble descriptor with per-run states unspecified. We supply: (a) the algebraic mathematical home for per-run states (regional Type II algebra states); (b) the (FQ) axiom relating per-run physical content to algebra-state structure; (c) the explicit Concentration Conjecture as the dynamical claim required for the ensemble interpretation to yield single outcomes per run. We are a holographically grounded, algebraically rigorous version of Ballentine, with the open conjecture identified explicitly.

**Versus Palmer's RaQM / Invariant Set Theory.** Palmer's program (RaQM 2025, PNAS; IST since 2009) is the closest neighbor in the *single-world + measurement-dependence + structural-physical-principle* cluster, closer in strategic shape than any of the above. Both Palmer and the present framework: (a) preserve single-world realism per run; (b) escape Bell by principled rejection of measurement independence (not nonlocality, not collapse); (c) recognize that the per-run physical state has microscopic structure not captured by the textbook formal wave function (though here the frameworks differ in interpretation: Palmer treats the actual physical state as a definite point on a fractal invariant set; we take the ψ-monist view that the per-run wave function itself is the actual physical state, finer-grained than the textbook formal ensemble descriptor, with no additional ontological layer); (d) ground the rejection of "free variables" in deep structural physics rather than ad hoc fine-tuning. The frameworks differ in their motivating principle (Palmer: chaos / fractal invariant set in cosmological state space; ours: holographic information capacity of bounded spacetime regions) and in their mathematical apparatus (Palmer: p-adic measures + Niven's theorem; ours: CPW Type II crossed-product algebra + finite-precision physical-instantiation postulate). They are **complementary research programs, not competitors**: Palmer's invariant set could be one possible characterization of which per-run microscopic configurations are physically realized; our holographic finite-precision bound could be one possible physical reason the invariant set has its structure. Both could be true simultaneously. The present framework is more conservative dynamically (preserves Schrödinger exactly) and uses mainstream algebraic QFT machinery; Palmer's program is more developed empirically (cosmological predictions, explicit Bell-correlation models) and has a longer publication track record. Detailed comparison is in §10.8 of the companion technical paper.

## 9. What this position leaves open

We acknowledge what is not delivered.

**Quantitative form of the resolution floor $\epsilon(R)$.** The statement that amplitudes below $\epsilon(R)$ are physically equivalent to $0$ requires explicit specification of $\epsilon$ as a function of regional geometry. Qualitative existence ($\epsilon(R) > 0$) follows from the literal reading of (FQ); the explicit functional form is identified as the principal quantitative open problem.

**Rigorous Born-typicality theorem.** Why does the appropriate measure on microscopic initial conditions produce Born weights as realized-outcome frequencies? Sketched here as a typicality argument; full proof analogous to Bohmian $|\psi|^2$-equivariance is open work.

**Specific outcome of any given run.** Depends on microscopic initial conditions inaccessible in practice.

**Lab predictions.** None deviating from standard QM in standard regimes, the (FQ) bound is astronomically large at lab scales, and the resolution floor is astronomically tight. The framework is empirically conservative.

**Defense of the literal reading.** The literal physical-instantiation reading of the bound is a foundational interpretation that goes beyond what Witten's algebraic theorem directly establishes. Defending it against alternative narrow readings is a substantive philosophical / foundational task developed in the companion technical paper.

**Reference-state dependence and state-extension issues.** The crossed-product algebra requires a reference state $\Omega$, and per-run wave functions live on the enlarged Hilbert space $\mathcal{H} \otimes L^2(\mathbb{R})$. Both are technical subtleties addressed in the companion technical paper.

**Cosmological and horizon applications.** The de Sitter static patch and black-hole horizon regions are natural arenas. Deferred to subsequent work.

**Math status, honestly.** The framework has *rigorous mathematical scaffolding*, Type II crossed-product algebras (Witten 2022; CPW 2022), renormalized entropy matching generalized entropy in semiclassical gravity (CPW, Jensen-Sorce-Speranza 2023), Haag-Kastler algebraic QFT (Haag 1992). It has a *clearly stated foundational axiom*, (FQ) in its literal physical-instantiation reading. It has *qualitative consequences* worked out: precision-floor existence (Lemma 1), strict classical mixture from decoherence + (FQ), single-record per-run outcome. It does *not yet have* explicit theorems for the central claims: a closed-form $\epsilon(R)$, a formal proof that decoherence + (FQ) gives strict mixture, a Born-typicality theorem analogous to Bohmian $|\psi|^2$-equivariance. These are concrete, well-defined open problems, the explicit research agenda the framework opens. The technical paper (§11.2a) gives a detailed table of the math status. The framework is a research program with rigorous scaffolding and clearly identified open theorems, not a completed mathematical theory.

## 10. The hill we stand on

In one paragraph:

> The wave function evolves unitarily under the Schrödinger / Heisenberg evolution of the underlying field algebra. The Bekenstein-Bousso holographic bound, the holographic principle of general relativity, taken literally as a Lorentz-invariant physical information limit on the wave function as a state of spacetime, applies as a foundational constraint on every physical wave function. Under this literal reading, the wave function in any bounded region has finite physical specification precision; amplitudes physically within $\epsilon(R)$ of $0$ are physically the same state as exact $0$, and amplitudes within $\epsilon(R)$ of $1$ are physically the same state as exact $1$. In any actual run, decoherence + microscopic initial conditions drive the amplitudes for distinct macroscopic record components dynamically toward $0$ or $1$; the (FQ) precision floor renders the concentrated per-run wave function physically a single-record state. The macroscopic world, a single realized outcome per run, emerges as a structural consequence. No collapse, no hidden particle positions, no branching ontology, no modal value-rule. The Chandrasekaran-Penington-Witten Type II crossed-product algebra framework provides the rigorous mathematical infrastructure for the bound; the literal physical-instantiation reading of the bound is our additional foundational postulate on top, and it is what does the structural work of selecting the macroscopic world.

## 11. Conclusion

The wave function is one. The realized world per run is one. The Bekenstein-Bousso entropy bound, taken literally as a physical information limit on the wave function in spacetime, is the structural ingredient that selects the macroscopic world from the formal superposition. The standard interpretations of QM each pay a price: extra branches (MWI), hidden particles (Bohm), modal logic (modal interpretations), modified Schrödinger (GRW, CSL, DP, OR), or perspectival non-realism (QBism, RQM). The present position pays a different price: it adopts the CPW Type II algebra framework as the rigorous mathematical home (borrowed infrastructure), and adopts the literal physical-instantiation reading of the bound as the foundational postulate that does the structural work (our contribution).

The framework is empirically conservative, Schrödinger and Born preserved exactly, no laboratory deviations predicted. It is metaphysically modest, no actuality primitive beyond the per-run wave function as a physical state of spacetime. The principal open problems are quantitative: the explicit form of $\epsilon(R)$ and the rigorous Born-typicality theorem.

We have presented the position informally here. The formal algebraic apparatus, the precise form of (FQ), the explicit distinction between Witten's mathematical theorem and our literal physical-instantiation postulate (§4.3 of the companion technical paper), the four theorems, and the open problems are developed in detail in the companion technical paper.

---

## Acknowledgements

The author thanks the participants in extended discussions that informed the position developed here.

---

## Brief reference list

- Bekenstein, J. D. (1981). Universal upper bound on the entropy-to-energy ratio. *Phys. Rev. D*, 23, 287.
- Bousso, R. (2002). The holographic principle. *Rev. Mod. Phys.*, 74, 825.
- Banks, T. (2025). *Finite Entropy Implies Finite Dimension in Quantum Gravity.* arXiv:2509.17856.
- Witten, E. (2022). *Gravity and the crossed product.* JHEP 10 (2022) 008. arXiv:2112.12828.
- Chandrasekaran, V., Longo, R., Penington, G., & Witten, E. (2022). *An algebra of observables for de Sitter space.* JHEP 02 (2023) 082. arXiv:2206.10780.
- Chandrasekaran, V., Penington, G., & Witten, E. (2022). *Large N algebras and generalized entropy.* JHEP 04 (2023) 009. arXiv:2209.10454.
- Jensen, K., Sorce, J., & Speranza, A. J. (2023). *Generalized entropy for general subregions in quantum gravity.* arXiv:2306.01837.
- Haag, R. (1992). *Local Quantum Physics: Fields, Particles, Algebras.* Springer.
- Ballentine, L. E. (1970). The statistical interpretation of quantum mechanics. *Rev. Mod. Phys.*, 42, 358.
- Bohm, D. (1952). A suggested interpretation of the quantum theory in terms of "hidden" variables. *Phys. Rev.*, 85, 166.
- Everett, H. (1957). "Relative state" formulation of quantum mechanics. *Rev. Mod. Phys.*, 29, 454.
- Ghirardi, G. C., Rimini, A., & Weber, T. (1986). Unified dynamics for microscopic and macroscopic systems. *Phys. Rev. D*, 34, 470.
- 't Hooft, G. (1993). Dimensional reduction in quantum gravity. arXiv:gr-qc/9310026.
- Penrose, R. (1996). On gravity's role in quantum state reduction. *Gen. Rel. Grav.*, 28, 581.
- Palmer, T. N. (2025). *Rational Quantum Mechanics: Testing Quantum Theory with Quantum Computers.* Proc. Natl. Acad. Sci. USA. arXiv:2510.02877. (See also Palmer, T. N. (2009). *The Invariant Set Postulate: A New Geometric Framework for the Foundations of Quantum Theory and the Role Played by Gravity.* Proc. Roy. Soc. A 465, 3165. arXiv:0812.1148.)
- Wallace, D. (2012). *The Emergent Multiverse.* Oxford University Press.
- Zurek, W. H. (2003). Decoherence, einselection, and the quantum origins of the classical. *Rev. Mod. Phys.*, 75, 715.
- Kapłański, P. (2026). *One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint.* (Companion technical paper.)

---

*End of position paper.*
