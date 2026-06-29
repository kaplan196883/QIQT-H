---
title: "One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint"
author: "Paweł Kapłański"
date: 2026-05-25
keywords: [foundations of quantum mechanics, holographic principle, Bekenstein-Bousso bound, Type II von Neumann algebras, crossed product, generalized entropy, finite-precision wave function, measurement problem, typicality]
---

# One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from Holographic Constraint

## Abstract

We develop a foundational framework for quantum mechanics that combines the algebraic quantum field theory framework with the recent crossed-product / Type II construction of Chandrasekaran-Penington-Witten (2022) and Witten (2022). In ordinary QFT, the local algebras of bounded regions are of Type III$_1$, admitting no trace, no Hilbert-space factorization, and UV-divergent entanglement entropy. CPW and Witten show that gravitational dressing, implemented via the crossed product with the modular flow of a reference state, produces a Type II algebra $\hat{\mathcal{A}}(R)$ with a semifinite trace and a well-defined renormalized entropy whose differences match the generalized entropy expression $A/(4\ell_P^2) + S_{\rm matter}$. We use this algebraic infrastructure as the mathematical home for a foundational axiom (FQ) that we propose: *for every per-run physical wave function and every bounded region $R$, the state $\omega_\Psi$ induced on the gravitationally dressed regional algebra $\hat{\mathcal{A}}(R)$ has renormalized entropy bounded by $Q_R := A(\partial R)/(4\ell_P^2)$, and two abstract wave functions inducing the same state on $\hat{\mathcal{A}}(R)$ are physically identical in $R$.* The crossed-product construction is borrowed from CPW/Witten; the holographic bound $S_{\rm ren} \le Q_R$ is postulated as a finite-information axiom in this algebraic setting (not derived from CPW); the foundational application of this algebraic infrastructure to the measurement problem is our contribution. We distinguish the **formal wave function** of standard QM (an idealized ensemble description) from the **per-run wave function** (whose regional physical content is given by its values on the regional Type II algebras). Algebra-state equivalence provides a basis-independent notion of regional physical indistinguishability, two abstract Hilbert vectors are physically the same regional state iff they agree on every observable in $\hat{\mathcal{A}}(R)$. After decoherence renders the records non-interfering, the single actual record per run is fixed by the non-dynamical selector $\lambda$ — the run's microscopic initial conditions indexing which record — with the global evolution left exactly unitary and no amplitude trimmed. **(Revised position, 2026.** An earlier version of this program advanced a *Macroscopic Definiteness Conjecture* — that the finite capacity *itself* forbids a two-record regional state, $I_\Sigma \approx K\cdot I_0 > Q_R$. We **retire** it as a category error: $Q_R$ bounds the von Neumann entropy $S(\rho_R)$ of the pre-selection state, and a second macroscopic branch adds only $\sim\!\log K$ to $S(\rho_R)$ — far below $Q_R$ — so a two-record state does *not* overflow capacity; moreover a kinematic entropy bound cannot, in a unitarily-evolving theory, *select* an outcome. Definiteness is the work of the selector $\lambda$, not of the capacity bound. Capacity remains load-bearing — but as the *kinematic* constraint that yields the holographic area floor and, for the free field, the Einstein field equations, **not** as a mechanism for single outcomes. This supersedes the conditional-on-Macroscopic-Definiteness language in §4, §7.3, and §7.6 below.) The Schrödinger / Heisenberg evolution of the underlying field algebra is preserved exactly; (FQ) operates at the level of regional algebraic content. No collapse, no Bohmian particles, no MWI branches, no modal value-rule are added. Born statistics from typicality is stated schematically and identified as a key open problem. We state two propositions and two explicit conjectures, identify four explicit open problems, and frame the construction as a research program rather than a completed interpretation.

**Keywords:** foundations of quantum mechanics; Bekenstein-Bousso bound; holographic principle; Type II von Neumann algebras; crossed product; generalized entropy; finite-resolution wave function; ensemble interpretation; typicality.

**Formal verification.** The deductive core of this framework is machine-checked in Lean 4 / Mathlib and is now **axiom-free**: every audited theorem depends only on the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with **no `sorry`** and **no project-specific axioms** (CI-guarded by `scripts/axiom_budget_check.sh` at budget 0; the per-theorem `#print axioms` audit in `lean/mathlib/QIQTH/AxiomAudit.lean` carries 830 directives over 192 modules and roughly 2,010 theorems, the whole library building green). This is the endpoint of a sustained discharge effort in which the project axiom total fell **57 → 40 → 37 → 35 → … → 0**, each interface axiom either proved in a concrete finite model or recast as an explicit hypothesis. The machine-checked, axiom-free content includes: Theorems 3, 6, 7 and Lemma 1; Donald's identity and the entire `ArakiInterface` relative-entropy layer (11 axioms discharged to theorems, including the Holevo bound $\chi \le H(p)$ via operator-monotonicity of the logarithm through a `CStarMatrix` bridge) together with the `EntropyBridge`; the data-processing inequality and Klein positivity; the Goldstein-Struyve Schur classification (`GoldsteinStruyveStep1.schur_classification_real`, formerly a named interface axiom, now proved outright) and the Tsirelson-attainability bound; the no-signaling chain; the seven structural audits; and a **finite no-collapse Born representation** (`BornJoin.finite_noCollapseBornRepresentation`): finite capacity forces a unique actual record, effect-Gleason (`EffectGleason.finite_effect_gleason`) forces the outcome weights to be Born *from positivity*, product preparation gives independent trials, and the actual-value histories carry the Born product law and are Chebyshev-typical. The formalization also includes deliberate **negative audits** proving what does *not* follow: linear unitary decoherence does not concentrate branch weights (`NoConcentration`); the structural axioms do not single out Born (`NoBornFromNothing`); support preservation is strictly weaker than Born equivariance (`EquivarianceGap`); operational click-statistics underdetermine the IC measure (`OperationalNoGo`). The single-record *mechanism* (the number-bound form of the Macroscopic Definiteness Conjecture, §7.6) is mechanized as a conditional theorem (`CoreNoCollapse`, `CapacityModel`, `SBSBridge`, `CollisionalGamma`): a redundant Spectrum-Broadcast record forces storage $\ge R\log n$, a finite additive capacity then admits at most one macroscopic record (the threshold *derived* from pointer-state orthonormality, not stipulated), and the per-collision distinguishability $\gamma = |\cos 2\theta| < 1$ is *derived* from the toy Hamiltonian $H_{\rm int}=g\,\sigma_z^S\otimes\sigma_x^E$; the one remaining open input is the *field-theoretic* origin of that scattering premise. **(Revised 2026.** This conditional theorem concerns an *additive* record cost; since the additive (branch-summed) cost is provably *not* the holographic von Neumann entropy that $Q_R$ bounds — `BranchLedger.branchSummed_not_bounded_by_Shannon` — it does **not** establish that the physical capacity forbids a two-record state. The "Macroscopic Definiteness" reading is accordingly **retired** as a category error, §1.1a: single outcomes are fixed by the non-dynamical selector $\lambda$, not by the capacity bound, and the formalization's own negative audits confirm capacity alone neither concentrates weights nor selects a basis — `NoConcentration`, `RealmSelection.capacity_underdetermines_realm`.)** What machine verification does and does not establish must be stated plainly:** it certifies that the framework's *conditional and structural* mathematics is correct and rests on no hidden axiom; it does **not** establish the framework's *physical* postulates — the (FQ) holographic bound, the Macroscopic Definiteness Conjecture, the Canonical IC Measure (Born) Principle, and Lorentz covariance of the selector — which remain the open problems of §11.4. A continuum Type II / Fock / modular-flow tower (`QIQTH/Fock`, `QIQTH/Spectral`, `QIQTH/Entropy`) is in active development toward those open problems and is not complete. The complete audit is in `lean/mathlib/QIQTH/AxiomAudit.lean`; see `lean/mathlib/QIQTH/` in the project repository.

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

This paper proposes a different resolution: **deny (3) at the level of physical instantiation while preserving the mathematical formalism**. The wave function in any bounded region has finite physical specification precision determined by the holographic information capacity of the region. Amplitudes physically within $\epsilon(R)$ of $0$ are physically equivalent to amplitude exactly $0$. The mathematical continuum of amplitudes remains the indispensable formal apparatus; the physical instantiation is finite-precision. With this denial of (3), all four claims can be reconciled: the wave function is physically real (1), bounded spacetime has finite capacity (2), amplitudes have finite physical specification precision (denial of (3)), and after decoherence the per-run regional content is a single actual record fixed by the non-dynamical selector $\lambda$ (denial of (4) — *via* the $(\Phi,\lambda)$ ontology (P1), the global evolution left exactly unitary). [*Revised 2026:* an earlier version attributed the single record to the finite capacity *itself* forbidding a two-record state ("a structural consequence, not an added postulate"); that Macroscopic-Definiteness claim is **retired as a category error** — see §1.1a. Capacity is the kinematic constraint behind the area law and the field equations; it does not, and cannot, perform the outcome selection, which is $\lambda$'s role.]

This is arguably the *least radical* resolution. It does not multiply worlds, add particles, modify dynamics, or subjectivize the wave function. It accepts one physically natural constraint, bounded spacetime cannot physically contain infinite information, which is *independently motivated* by holography and quantum gravity. The measurement problem is resolved by recognizing that we were illegitimately combining (1)–(4) when only three of the four can hold at the level of physical instantiation.

### 1.0a Two facts, one world

The framework rests on two physical commitments.

**Fact 1, There is only the wave function, and it carries no probability.** $\Phi$ is the whole of physical reality, evolving by one exactly-unitary law: no collapse, no branches-as-substances, no observer standing outside it, and no probability built into it. What is conventionally called the Born rule is an *across-run frequency*, not a number the world assigns to a single run. The only further fact is $\lambda$, *which* of $\Phi$'s macroscopic realizations is the actual one. $\lambda$ is not a substance, not an observer, and not a probability; it is actuality, and nothing more (§7.6, §11.3).

**Fact 2, Information is limited by surface area.** Every bounded region $R$ can physically hold only $Q_R = A(\partial R)/4\ell_P^2$ worth of information (Bekenstein–Bousso, read as a literal instantiation bound; (FQ) below). A region can instantiate only *finitely many distinguishable records.*

From these, with decoherence, the measurement problem dissolves, not by adding a mechanism but by removing a mistake: **the binary, definite outcomes we observe are a feature of macroscopic record-structures, which are area-limited and einselected, not of the wave function.** We measure in $0/1$ because *we* are macroscopic.

The positive thesis makes the division of labor explicit, and is deliberate about what each ingredient does and does *not* do:

- **Continuous, conserved amplitude.** The weights $|c_k|^2$ are continuous and are *conserved* under unitary evolution; decoherence never drives them to $0$ or $1$ (formalized as `NoConcentration`; §9). The wave function itself has no binary structure and no probability.
- **Decoherence + einselection ⟹ stable, Boolean *records*.** What becomes effectively $0/1$ is a *different* variable from the amplitude: macroscopic record-existence (whether a definite pointer-record is instantiated in this region). Einselection makes such records redundant, robust, and mutually exclusive; this is *why a macroscopic system: apparatus, brain, or AI, can only register a definite result.* This explains the **stability and classicality** of outcomes, not their **uniqueness**.
- **The holographic bound ⟹ finitely many records.** $Q_R$ caps *how many* distinguishable records a region can hold (its genuine, non-redundant role). It does **not**, by itself, forbid a superposition of records (§7.6).
- **$\lambda$ ⟹ which record is actual.** That exactly one record is the lived one is the non-dynamical actuality fact $\lambda$. Born statistics are the across-run tally of $\lambda$ under a typicality measure: emergent bookkeeping, not a per-run probability (§8, Open Problem on the typicality measure).

The dissolution is then this: there is **no external observer to whom a probability is assigned.** "The outcome" is simply which macroscopic realization of $\Phi$ is actual. Collapse and fundamental probability were posited to explain a definiteness that lives in *us*, macroscopic, area-limited record-structures, and was never a feature of $\Phi$. There is only $\Phi$; the binary is the texture of our scale, not of the world.

### 1.1 The position

This paper develops a position in the foundations of quantum mechanics whose structure is:

1. The wave function of the universe evolves unitarily under the Schrödinger / Heisenberg evolution of the underlying field theory. Standard QM dynamics is preserved exactly.

2. The Bekenstein-Bousso holographic bound is treated as a foundational constraint on the **physical content of the wave function in any bounded region $R$**, not narrowly on the entanglement entropy of a reduced state, but on the total physical information needed to specify the state's content in $R$ as a state of spacetime.

3. The mathematical home of this constraint is the algebraic QFT framework with gravitational dressing. The regional algebra $\hat{\mathcal{A}}(R)$, obtained from the standard Type III$_1$ local algebra $\mathcal{A}(R)$ via the crossed product with the modular flow of a reference state, is of **Type II** and admits a semifinite trace whose finite values realize finite renormalized entropy for regional states. This is the framework of Chandrasekaran-Penington-Witten (2022), Witten (2022), and successors.

4. The (FQ) axiom: *the physical content of the per-run wave function in any bounded region $R$ is given by its expectation values on $\hat{\mathcal{A}}(R)$, and the renormalized entropy is bounded by $Q_R = A(\partial R)/(4\ell_P^2)$.*

5. The Type II structure of $\hat{\mathcal{A}}(R)$ implies a finite physical resolution for regional states: states agreeing on all operators in $\hat{\mathcal{A}}(R)$ are physically identical in $R$. This is the natural mathematical realization of "amplitudes physically within $\epsilon$ of $0$ are physically the same state as amplitude exactly $0$", the equivalence is between regional states, not between abstract Hilbert vectors.

6. The standard textbook formal wave function, a superposition $\sum_i c_i |s_i\rangle|A_i\rangle|E_i\rangle$, is an idealized statistical description of an ensemble of per-run wave functions across many runs. The per-run wave function evolves unitarily from specific microscopic initial conditions; decoherence renders the macroscopic record components non-interfering; and the non-dynamical selector $\lambda$ (P1) marks exactly one decohered record actual (capacity is kinematic and does *not* forbid a $\ge 2$-record state — §1.1a) leaves the per-run regional content single-record. The run's microscopic initial conditions index which record.

7. Born statistics emerge from typicality of microscopic initial conditions across runs.

### 1.1a The irreducible postulates

After the machine-checked discharge-and-grounding effort (§11.4b), the framework's content reduces to a small set of postulates, of which only one is distinctive physics:

- **(P1) The $(\Phi,\lambda)$ ontology.** The universal wave function $\Phi$ is the complete ontology (no external observer, no fundamental probability); a non-dynamical selector $\lambda$ makes exactly one decoherent record actual per run — no collapse term, no branching.
- **(P2) Quantum kinematics.** The complex-Hilbert-space / operator-algebraic framework (states as positive normalized functionals, observables as a net of algebras, the $\operatorname{tr}(\rho\,\cdot)$ pairing). The Born *squared modulus is not a separate postulate*: it is the inner-product geometry of this arena ($\operatorname{tr}(|\psi\rangle\langle\psi|\,P_k)=|\langle k|\psi\rangle|^2$), forced into linear/trace form by (P5) and *selected* — exponent $1$ over the $\alpha$-family — by refinement no-signaling.
- **(P3) Microcausality.** Spacelike-separated regional algebras commute. This is the Lorentz-covariance input; it is *not* the source of the Born premises (see below).
- **(P4) The (FQ) holographic capacity bound.** The regional renormalized entropy is bounded by $Q_R = A(\partial R)/(4\ell_P^2)$. This is the single distinctive physical postulate and the sole genuine input to the machine-checked QIQT$\to$GR chain (§11.4b). That chain is now instantiated for an explicit free Klein–Gordon field on a curved **pp-wave** spacetime (`qiqt_gr_ppwave_showcase`), in which *every geometric and analytic premise is discharged* — the metric and tetrad, the Raychaudhuri **area derivative** (an expansion-free congruence has constant cross-sectional area), and the **entropy bound** $S\le\eta A$ (Shannon's maximum at the holographic capacity) — leaving as hypotheses *exactly* the irreducible floor: the matter equation of motion, (P4) itself, and the **localization map** (the field-coupled record law whose entropy rate equals the stress flux $2\pi\hbar^{-1}T_{kk}$). The localization map is provably *not* dischargeable by analysis: at the uniform reference the Shannon entropy is stationary ($\sum p'=0$), so the heat rate's value is forced to be the stress flux. Thus the Einstein field equations for the pp-wave spacetime follow, machine-checked and axiom-free, from the matter equation of motion $+$ (P4) $+$ the localization map.
- **(P5) Quantum equilibrium of the typicality measure.** $\lambda$'s measure is refinement-equivariant (the Dürr–Goldstein–Zanghì / Valentini condition).

**Internal-consistency constraint ($\Phi$, not the selected branch, carries the holographic entropy).** Because the holographic value $Q_R = A(\partial R)/4\ell_P^2$ is an *entanglement* (von Neumann) entropy of the regional state — not a Boltzmann log-count of decohered branches — (P4) is necessarily a statement about the **pre-selection constitution $\Phi$**, whose reduced state $\rho_R$ carries that entropy. The non-dynamical, inert character of $\lambda$ in (P1) is therefore not merely interpretive but *required*: conditioning on the $\lambda$-selected record would destroy the off-diagonal coherence the area measures (the entropy would collapse from $S(\rho_R)$ to the within-branch $S(\rho_{R,i})$ in the decomposition $S(\rho_R) = H(\{p_i\}) + \sum_i p_i\,S(\rho_{R,i})$), making (P4) incompatible with the Bekenstein–Hawking / Ryu–Takayanagi reading. So geometry responds to $\Phi$, never to the actualized branch; equivalently, the regional "record count" $\log|R|$ must be read as the effective modular rank $e^{S(\rho_R)}$ — a quantum edge-mode degeneracy of the pre-selection state — not as a cardinality of classical outcomes. (This is also why a microscopic *derivation* of (P4) — replacing the postulate by a JLMS-type identity $K_{\partial R} = A/4\ell_P^2 + K_{\rm bulk}$ on the modular/edge algebra — is the natural next target rather than any counting of actualized records.)

The refinement of this account is that the two Born-rule premises of earlier formulations — the additivity / non-contextuality *bridge* and the $\mu$-*selection* — both reduce to **(P5) alone**. In the Lean development: refinement-equivariance implies selector no-signaling (`BornMuSelection.equivariant_no_signaling`); selector no-signaling is *equivalent* to additivity (`BornActualityConsistency.apc_iff_positiveAdditive`), hence to the Born rule; and equivariance grounds the measure-selection directly (`equivariant_context_independent`, `mu_selection_martingale`), with the no-go theorems certifying that a selection principle is unavoidable (`NoBornFromNothing.any_anti_born_realizable`) and non-vacuous (`BornRoutes.sqRule_refinement_signals`). Crucially, (P5) is **not** reducible to (P3): the formalization proves that observable microcausality does *not* entail selector no-signaling (`SelectorRefinement.alphaSq_selector_signals`) — the two live at different layers (observable algebra vs.\ actuality measure), so they cannot be merged. The genuinely irreducible *physics* therefore reduces to **(P4) + (P5)**, on the (P1) ontology, with (P2)–(P3) the standard quantum-relativistic arena.

**(P4) refined — the area *floor* is now a derived theorem; only the finite *capacity* is postulated (the P4-MICRO formalization, 2026).** The machine-checked development separates two things earlier bundled in (P4). The *postulate* is only that the regional capacity is **finite** — a UV-finite record structure, $N_R < \infty$ (the "Quantized Information" core). Finiteness *alone* gives only $S_{\mathrm{vN}}(\rho_R) \le \log N_R$; it does **not** by itself fix whether $\log N_R$ scales with **area** or volume (a generic finite local cutoff has *volume*-scaling maximum entropy — the area law is a property of *vacuum entanglement*, not an automatic property of the capacity). That the bound takes the **holographic area form** ($\log N_R \le A(\partial R)/4\ell_P^2$) is **derived**, but in a *conditional* Sakharov / induced-gravity **bridge** — assuming local relativistic QFT on a smooth background with a covariant UV cutoff identified with the finite microstructure — **not** from finiteness alone: there the area law $S\propto A$ *emerges* from the conical-deficit geometry (the cone curvature is a $\delta$-function on the boundary surface, whose integral is the area), and the $1/4$ is the universal ratio between the conical replica-entropy coefficient and the induced Einstein–Hilbert coefficient — two quantities sharing one UV coefficient (the *ratio* machine-checked, `SakharovRatio.sakharov_ratio`; the emergence is the standard Susskind–Uglum/Solodukhin heat-kernel result, Stage B, `docs/SAKHAROV_KG_STAGE_B.md`). The carried inputs are the *value* of $G$/$\ell_P$ (the species/cutoff problem) and, for the full effective action, $\Lambda$ and higher-curvature terms. The capacity $Q_R$ is read, per the internal-consistency constraint above, as the effective modular rank $e^{S(\rho_R)}$ of the pre-selection constitution $\Phi$, and is carried in Lean as the `HolographicCapacityBound` typeclass hypothesis, *not* a Lean `axiom`. The **only** carried datum is the *value* of $G$/$\ell_P$ (the species/cutoff problem). The *area floor itself*, $S_{\mathrm{vN}}(\rho_R) \le Q_R$, is then a **theorem** — `area_floor_vonNeumann` (`QIQTH/FQBoundMicro.lean`): the elementary finite-dimensional maximum-entropy bound $S_{\mathrm{vN}} \le \log\dim$ applied to the spectrum, axiom-free (standard three). Three honesty refinements are *enforced* in the formal statements: the bound is on the **von Neumann** entropy of the spectrum (not the Shannon entropy of a decohered record law — the two coincide only diagonally, $S_{\mathrm{vN}}\le H(\text{record})$ in general), consistent with the entanglement-entropy reading above; only the inequality $\le$ is needed for the floor, with equality reserved for the maximally-mixed/saturating sector (`HolographicCapacityBound` vs `HolographicCapacityExact`); and $N_R$ is the **regional** capacity — an explicit finite type-I/code cutoff of the genuinely type-III$_1$ local algebra, not a global Hilbert-space dimension. The (P4)$\to$GR chain is recast accordingly: `gr_from_p4micro` (`QIQTH/GRFromMicro.lean`) feeds this *derived* area floor into the Jacobson capstone `qiqt_bekenstein_gives_gr`, yielding the Einstein field equations with **exactly** the residual labelled inputs — the Bisognano–Wichmann / Unruh modular flux `hFlux` (discharged for the free field via `Fock.OneParticleBW`), Raychaudhuri focusing, stress-energy conservation, metric regularity, and — the genuine residual — the **joint reference-state identification**: that the horizon equilibrium reference is *both* the Bisognano–Wichmann modular state (whose modular Hamiltonian gives the Unruh flux, $\beta = 2\pi/\kappa$) *and*, in its record/edge sector, capacity-saturating ($S = \log\dim = \eta A$ for the same geometric area). These are different states in general ($\beta = 2\pi/\kappa$ vs the maximally-mixed $\beta = 0$), so the physical content sits in this identification. The entropy-area *variation* $\delta S = \eta\,\delta A$ that Jacobson needs is itself a **derived theorem** — `DifferentialAreaLaw.differential_area_law`: the capacity bound + point-saturation (`area_floor_saturates`, $S(0)=\eta A(0)$ at the maximally-mixed record) + the entanglement first law *entail* it, with **no** hypothesis asserting $S=\eta A$ or $\delta S=\eta\,\delta A$. So there is **no** separate "Clausius / area-saturation postulate" — saturation is discharged; the open Lean target is to prove the reference of `relEntropy_self`/`hFlux` coincides (or shares its record marginal) with the one `area_floor_saturates` uses, likely via an edge$\otimes$bulk split (the area entropy from a uniform record/edge sector, the BW flux from the bulk). The Lean now *enforces* the honest scope: **the capacity postulate alone does not give GR** — a microstate *count* cannot supply a *temperature*, so the thermal `hFlux` slot is irreducibly modular (Route 1 / Type II) and is not derivable from (P4). The $1/4$ coefficient is the separately-derived Sakharov induced-gravity ratio (`SakharovRatio.sakharov_ratio`, regulator- and matter-independent); the value of $G$ remains a carried UV datum. Deriving the capacity *law* itself — replacing the postulate by a JLMS-type modular identity $K_{\partial R} = A/4\ell_P^2 + K_{\rm bulk}$ — remains the natural next target (Route 1), as noted above.

**The code–capacity bridge — a formalized, separated refinement (2026).** A small axiom-free Lean module (`QIQTH/CodeCapacityBridge.lean`) makes the capacity constraint a *typed interface* between the field and the microstructure, rather than silently identifying field states with microstates. It keeps the field's regional **code space** $C$ separate from the microstate space $\mathcal{H}_R$ and links them only by an explicit isometric encoding $V:C\hookrightarrow\mathcal{H}_R$. Then `encoded_field_entropy_le_area`: given the encoding (so $\dim C \le \dim\mathcal{H}_R$) and the `HolographicCapacityBound` hypothesis $\log\dim\mathcal{H}_R \le A/4\ell_P^2$, every code density obeys $S_{\mathrm{vN}}(\rho) \le \log\dim C \le \log\dim\mathcal{H}_R \le A/4\ell_P^2$, with all encoded record expectations preserved (`encoded_record_expectation`: $\operatorname{Tr}((V\rho V^\dagger)(VOV^\dagger))=\operatorname{Tr}(\rho O)$); instantiated for the actual free-field code dimensions — the CAR Fock $2^n$ and the number-cutoff symmetric Fock $\binom{d+N}{N}$ — and capped by a record-count bound $\log|I|\le A/4\ell_P^2$ for any family of perfectly distinguishable records (`record_log_card_le_area`). The one genuine *structural* asymmetry it certifies is the CAR/CCR cutoff distinction: exact finite-dimensional canonical commutation $[a,a^\dagger]=1$ is impossible ($\operatorname{Tr}[a,a^\dagger]=0\ne\dim\mathcal{H}$, `no_finiteDim_CCR`), so the photon's bosonic mode requires a number/energy cutoff to fit a finite microstate sector, whereas a fermionic CAR sector $\bigwedge h$ is finite-dimensional and fits exactly. **Scope, enforced in the statements:** these are *conditional* bounds — the Lean proofs *transport* an assumed finite microstate capacity through an isometric code encoding; they do **not** derive the holographic bound, the value of $G$, the Type-II renormalized entropy, or the matter spectrum beyond the CAR-vs-CCR cutoff distinction. Capacity here constrains the field's entropy and record count *through* the fitting inequality; it does not generate the field.

**Macroscopic Definiteness (H2) — retired as a category error (2026).** Earlier formulations made a further, *load-bearing* conjectural claim (the "Macroscopic Definiteness Conjecture", §7.6): that a regional content carrying two or more macroscopically distinct records has summed cost $I_\Sigma \approx K\cdot I_0$ exceeding $Q_R$, so that finite capacity *itself* forbids the multi-record state and thereby forces a single outcome. **We retire this claim.** It conflates two different entropies. The capacity $Q_R$ bounds the *von Neumann* entropy $S(\rho_R) = H(\{p_i\}) + \sum_i p_i\,S(\rho_{R,i})$ of the pre-selection state $\Phi$ (the constraint above), in which a second macroscopic branch raises only the *branch-count* term $H(\{p_i\})$ — by $\sim\!\log K$, a handful of bits — while the enormous *within-branch* term $\sum_i p_i\,S(\rho_{R,i})$ is essentially the same whether $K=1$ or $K=2$. A two-record regional state therefore does **not** overflow $Q_R$. The "$I_\Sigma \approx K\cdot I_0$" branch-summed cost is precisely the additive fiction that drove the false conclusion; the Lean development itself records that the branch-summed cost is *not* bounded by — and is not — the entropy (`BranchLedger.branchSummed_not_bounded_by_Shannon`). More fundamentally, in a unitarily-evolving theory no *kinematic* entropy inequality can *select* an outcome: the branch weights $|c_k|^2$ are conserved (`NoConcentration`), and a capacity (cardinality) bound *underdetermines* the record basis (`RealmSelection.capacity_underdetermines_realm` — "the area budget is not the metaselector"). **Single outcomes are the work of $\lambda$ (P1) — decoherence fixes the record basis, $\lambda$ selects one — not of the capacity bound.** What survives, and is load-bearing, is the *kinematic* role of $Q_R$: it bounds $S(\rho_R)$ (the now-derived area floor, above) and feeds the field equations. Sections §4, §7.3, and §7.6 are to be read accordingly — their single-record conclusions stand via (P1) + decoherence, but every clause there asserting that capacity *forbids* a multi-record state, or that a multi-record content is *not instantiable for capacity reasons*, is **superseded** by this note. The genuinely open problems are therefore $\lambda$'s **law** (Born from typicality / the canonical IC measure, (P5)) and its **dynamical, Lorentz-covariant realization** — not Macroscopic Definiteness.

### 1.2 What this paper does and does not claim

**Does.** Introduces (FQ) in its rigorous algebraic form using Type II crossed-product algebras. Distinguishes formal vs per-run wave functions. Establishes the finite-physical-resolution consequence of Type II regional algebras. Discusses the decoherence-plus-finite-information-restriction mechanism for single-record regional content. States four formal results. Identifies three explicit open problems.

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

**The framework adds no second *dynamical* substance beyond the wave function** (no Bohmian particles, no extra fields, no guidance law). The framework's contributions are:
1. The recognition that the textbook subsystem wave function $|\psi\rangle_{\rm sub}$ is *not* the relevant complete dynamical quantum state of a run; the per-run universal wave function $\Phi = |\Psi\rangle_{\rm run}$ is. (The complete per-run *ontology*, however, is not $\Phi$ alone but the pair $(\Phi, \lambda)$; see the note below.) This is standard QM at the universal level.
2. The (FQ) axiom limiting the physical information content of the universal wave function per region.
3. A *non-dynamical run-index* $\lambda$: a global, atemporal actuality fact about *which* of $\Phi$'s macroscopic realizations the whole run is (fixed for the entire 4-dimensional history; *not* past-localized "initial data," to avoid any setting-correlation / Conway–Kochen reading; see §6.9), that selects which single record is realized (§7.6).

**A note on "ψ-monism" as used throughout.** The framework is **ψ-monist in the weak (dynamical) sense**: the wave function $\Phi$ is the only thing carrying a law of motion (exactly unitary), and no second *dynamical* ontology is added. It is **not** ψ-monist in the strong sense that $\Phi$ alone is the complete per-run state, the single realized record per run is fixed by $\lambda$, a *non-dynamical actuality fact* (a broad-sense beable, structurally analogous to the configuration in Bohmian mechanics or the actual history in modal interpretations, but with no guidance law and no back-reaction on $\Phi$; see §7.6). In the Spekkens–Harrigan taxonomy the framework is therefore **ψ-ontic, weak-ψ-monist, and formal-ψ-incomplete**: $\Phi$ is real and is the sole dynamical ontology, but the complete per-run description is the pair $(\Phi, \lambda)$. Every later use of "ψ-monist" in this paper is shorthand for this weak/dynamical sense.

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

*Notational caveat: we will also write this functional as $S_{\rm ren}(\omega_\Psi)$ for emphasis on "modular-local information content", and (FQ)(ii) then reads $S_{\rm ren}(\omega_\Psi) \le Q_R$. This $S_{\rm ren}$ is **not** the same functional as the CPW/Witten "renormalized entropy" of the state on the Type II crossed-product algebra, they are distinct functionals related by the modular identity*
$$
\chi_R(\omega) \;=\; \Delta_\omega \langle K_R^\sigma \rangle - \Delta_\omega S_R^{\rm CPW}
$$
*where $K_R^\sigma$ is the modular Hamiltonian of $\sigma_R$ and $S_R^{\rm CPW}$ is the CPW renormalized entropy. **The (FQ) bound is on the relative-entropy functional $\chi_R$, not on the CPW renormalized entropy.** The two functionals can disagree substantially (a state may satisfy one bound and violate the other; see the formal verification module `lean/mathlib/QIQTH/EntropyBridge.lean` for a classical counterexample making this concrete).*

**Machine-checked modular substrate (companion formalization).** A companion Lean 4/Mathlib formalization (§11.4b; project repository `lean/mathlib/QIQTH/`) independently verifies the bounded modular-theoretic and coherent-state relative-entropy *calculus* on which $\chi_R$ rests, for the free-field coherent-state case: the finite Araki/Umegaki convention lock $S_{\rm Araki}(\rho\,\|\,\sigma)=\operatorname{tr}\rho(\log\rho-\log\sigma)$; the bounded Rieffel-Van Daele standard-subspace Tomita-Takesaki construction (modular conjugation $J$, the relation $JRJ=2-R$, the continuum modular group $\Delta^{it}$ and its strong continuity); the Casini-Grillo-Pontello one-particle relative entropy as a bounded scalar spectral integral together with its *positivity* $S(\xi)\ge 0$ for localized $\xi$; the free-field (Fock) modular flow $\Gamma(\Delta^{it})$ with $\sigma_t(W(u))=W(\Delta^{it}u)$ and the vacuum as the modular state; the coherent-state relative modular operator $\Delta^{it}_{W(f)\Omega\,|\,\Omega}=W(f)\,\Gamma(\Delta^{it})\,W(f)^*$ (valid for $W(f)$ in the local algebra) with its Connes cocycle $[D\omega_{W(f)\Omega}:D\omega_\Omega]_t=W(f)W(-\Delta^{it}f)$ and cocycle chain rule; and the *entropy reduction* $S_{\rm Araki}(\omega_{W(f)\Omega}\,\|\,\omega_\Omega)=S_{\rm CGP}(f)$ identifying the coherent-state Araki relative entropy with the one-particle CGP value. The development carries no `sorry` and, as reported by `#print axioms`, depends only on the standard classical foundations of Lean/Mathlib (`propext`, `Classical.choice`, `Quot.sound`); it introduces no further axioms.

*Scope.* What is verified is the modular/relative-entropy *calculus* motivating $\chi_R$, in the finite and free-field coherent sectors, **not** the dressed Type II regional content map itself, the CPW/Witten crossed product, the holographic capacity axiom (FQ), the Donald/Fano argument, or Born-from-typicality, all of which remain explicit physical assumptions or open problems of this paper. (The *Macroscopic Definiteness Conjecture* — that capacity forbids a $\ge 2$-record state — is **retired** as a category error, §1.1a.) The single-record results (Theorem 4) rest on $\lambda$-selection (P1) + decoherence, not on capacity. Their *dynamical, Lorentz-covariant* realization (that unitary measurement evolution produces the decoherent record structure $\lambda$ selects from) and Born-from-typicality are the load-bearing gaps the formalization does not close.

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
| Single-record per run | Requires separate Concentration Conjecture | Structural consequence of decoherence + finite-information capacity restriction |
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

**Stability requirement (recoherence).** For the resolution-$\epsilon$ relation to be a well-defined identity of physical states, it must be *stable* under admissible subsequent evolution: two regional contents identified as the same physical state at resolution $\epsilon(R)$ must not be separable by later dynamics into distinct macroscopic records. In the measurement/decoherence setting this holds because the relevant sub-$\epsilon$ content is the residual record-coherence of an already-decohered, effectively irreversible interaction with $\sim 10^{20}$ environmental degrees of freedom; recoherence of distinct macroscopic records is dynamically excluded on any physical timescale. The general characterization of which contexts guarantee this stability is recorded as a subsidiary part of Open Problem 3.

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

## 6. The Mechanism: Decoherence, Finite-Information Restriction, and Algebraic Resolution

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

The classical mixture $\sum_k |c_k|^2 \omega_k^R$ is *not* a single record. It is a weighted list of records carrying the Born weights $|c_k|^2$, weights that the framework reads as the *empirical frequency pattern across runs* (§7.4), not as a fundamental per-run probability (QIQT-H has no fundamental probabilities).

Two distinct questions must be separated. *Why is the resident content a single record at all (rather than a multi-record mixture)?* and *which* record is it in this run? The first is answered by the $(\Phi,\lambda)$ ontology (P1): once decoherence renders the records non-interfering, the non-dynamical selector $\lambda$ marks exactly one of them actual. (An earlier version answered it by a *finite-information restriction* — that a $\ge 2$-record content exceeds $Q_R$ and is "not instantiable"; that Macroscopic-Definiteness reading is **retired** as a category error, §1.1a: a second branch raises $S(\rho_R)$ by only $\sim\!\log K$, far below $Q_R$, so capacity does not forbid it.) The second is answered by the run's actual microscopic initial conditions:

**Per-run, the universe carries one specific record of the decohered-and-(FQ)-restricted regional content. *Which* record is fixed by the per-run microscopic initial conditions of the apparatus + environment, propagated through the unitary dynamics from these specific microstates. The initial conditions do not *produce* the single-ness, the finite-information restriction does that; they merely *index* which single-record universe this run is.**

This is analogous to how, in classical statistical mechanics, a system at temperature $T$ has specific molecular configurations in any individual realization. The thermodynamic ensemble $e^{-\beta H}$ is a probability distribution over microstates; any specific realization sits at one microstate. We do not say "the system is in a quantum superposition of all microstates with thermal weights"; we say "the system is in some specific microstate, the distribution over runs follows the thermal ensemble."

In the quantum case, the same structure obtains with one additional ingredient: the per-run microstate must be consistent with the (FQ)-decohered structure on the regional algebra. After decoherence + (FQ), the regional algebra-state is strictly classical (no remaining off-diagonal coherence); the per-run universe occupies one branch of this strictly-classical mixture; which branch is determined by the specific microscopic initial conditions.

**This is not a magic transition from "70% A + 30% B as a superposition" to "100% A as a single outcome".** It is the recognition that:
1. We never have direct access to a "70%/30% superposition" of macroscopic alternatives, we have access only to macroscopic records, which after decoherence are exponentially exclusive
2. (FQ) makes "exponentially exclusive" into "strictly exclusive": the residual sub-$\epsilon$ record-coherence has no physical referent
3. After decoherence renders the records non-interfering, the non-dynamical selector $\lambda$ (P1) makes exactly one record actual — this is what makes the outcome single (an earlier version attributed single-ness to capacity forbidding a $\ge 2$-record content; that reading is **retired** as a category error, §1.1a — capacity does not forbid multiplicity)
4. *Which* single record the per-run universe carries is indexed by its microscopic IC (the IC does not produce the single-ness: step 3 does)

The per-run "microscopic initial conditions" are *not* hidden variables in any ontological sense. They are simply *the actual physical state of the apparatus + environment in the specific run*. Different runs of an experiment correspond to different actual physical universes, different particles emitted, different microscopic apparatus states, different environmental configurations. These differences are not added structure; they are the standard fact that *actual physical universes differ across actual physical experiments*. Standard QM, at the universal-wave-function level, already accommodates this trivially: the universal wave function is a function of all degrees of freedom in the universe; those degrees of freedom take different actual values in different runs.

The framework is **ψ-monist in the weak (dynamical) sense** (§2.2): the wave function is the only ontology carrying a law of motion; the only additional fact is the non-dynamical run-index $\lambda$, not a second dynamical substance. What the framework does, and what standard textbook QM elides, is to take seriously that:
1. The universal wave function (not the textbook subsystem wave function) is the actual physical state in each run
2. Different runs are different actual physical universes, not different versions of "the same" universe
3. The Born statistics across runs come from the distribution of *actual* initial conditions across *actual* runs, not from any "alternative" wave functions for a single preparation

In Bohmian language: there are no Bohmian particles and no second *dynamical* ontology; the wave function $\Phi$ is the only thing carrying a law of motion. What plays a role structurally analogous to the Bohmian configuration is the run-index $\lambda$, the run's actual microscopic initial conditions, a *non-dynamical* actuality fact (no guidance law, no back-reaction on $\Phi$) that selects which single record is realized. Different runs carry different $\lambda$. This is weak-ψ-monist standard QM with (FQ) added as a finite-information constraint, plus the non-dynamical actuality selector $\lambda$.

### 6.5 Theorem: Single-record per-run wave functions

**Theorem 1 (Single-record per-run wave functions).** *Under (FQ) and standard decoherence dynamics of unitary QFT, the per-run physical state on the regional algebra $\hat{\mathcal{A}}(R)$ for $R$ containing apparatus + environment after measurement is, with regional physical content given by the algebraic-state-modulo-(FQ)-precision equivalence class, a single-record state $\omega_{k_{\rm run}}^R$.*

*Proof.* By standard decoherence theory, after measurement interaction, the joint state's induced regional state on $\hat{\mathcal{A}}(R)$ has off-diagonal coherence terms suppressed exponentially: $\omega_\Psi^R = \sum_k |c_k|^2 \omega_k^R + O(\exp(-N))$. By Lemma 1 (§5.1), components below the (FQ) precision floor $\epsilon(R)$ are physically equivalent to zero. Since $e^{-N} \ll \epsilon(R)$ for any reasonable macroscopic decoherence regime, the off-diagonal coherence terms are physically exactly zero. The resulting regional state is the strict classical mixture $\sum_k |c_k|^2 \omega_k^R$, with macroscopic records physically exclusive (no remaining coherence between distinct $\omega_k^R$).

This strict classical mixture still carries every record; decoherence has removed interference, not multiplicity. The single-record conclusion is supplied by the selector $\lambda$ (P1): on the decohered (non-interfering) record set, $\lambda$ marks exactly one record actual, $\omega_{k_{\rm run}}^R$ for some specific $k_{\rm run}$, with the per-run microscopic initial conditions indexing which $k_{\rm run}$ (the ICs index the run; $\lambda$, not capacity, is what makes the content single). (An earlier version derived single-ness from a *finite-information restriction* — summed cost $I_\Sigma \approx K\cdot I_0 > Q_R$; that is **retired** as a category error, §1.1a: the branch-summed cost is not the von Neumann entropy $Q_R$ bounds — `branchSummed_not_bounded_by_Shannon` — and a second branch raises $S(\rho_R)$ by only $\sim\!\log K$.) The global evolution remains exactly unitary throughout; no amplitude is trimmed. $\blacksquare$

*(The single-record step is now carried by $\lambda$-selection (P1) + decoherence; the former §7.6 Macroscopic-Definiteness / $I_\Sigma > Q_R$ step is **retired** as a category error, §1.1a — not an open problem. The (FQ) resolution-equivalence of §5.1 still removes the residual sub-$\epsilon$ off-diagonal coherence.)*

**Remark on the role of each ingredient:**
- **Decoherence** drives the regional algebra-state to be exponentially close to a classical mixture (standard QM, no postulate)
- **(FQ)** converts "exponentially close" to "physically exact" (foundational postulate; renders off-diagonal coherence physically zero)
- **The per-run wave function itself** is one specific branch of the strictly-exclusive classical mixture, this is ψ-monism: no additional ontology, the wave function in each actual run is simply different from the textbook formal ensemble descriptor
- **Born statistics** across runs follow from the typicality of microscopic IC (open: Concentration / Born-typicality program)

**What standard linear QM does not provide:** the strict classical exclusivity (off-diagonal coherence is exponentially small, not zero) and the per-run branch selection. (FQ) provides the first; per-run microscopic IC provide the second. Neither requires modifying the Schrödinger evolution.

### 6.6 What is preserved, and what algebraic restriction is (and is not)

**Preserved exactly:** the unitary Schrödinger / Heisenberg evolution of the underlying field algebra. No modification of dynamics, no stochastic term, no projection operator, no restriction on the admissible Hamiltonians. The evolution law is exactly standard QM; what the framework adds operates not on the dynamics but on which *regional contents* count as physically instantiable (next paragraph).

**Constrained at the kinematic level:** what is restricted is which *regional contents* are physically instantiable, those with regional information cost $I_\Sigma \le Q_R$. A global wave function whose induced regional content carries $\ge 2$ macroscopically distinct records (cost exceeding $Q_R$) is a perfectly good *formal/calculational* descriptor but has no single-region per-run physical referent. **This is not a restriction on the Hamiltonians and not a modification of the dynamics:** the global Schrödinger / Heisenberg evolution law is exactly unitary and unconstrained, including ordinary measurement interactions. The restriction is purely on physical *instantiability of regional content* (FQ part (iii) + the formal/per-run distinction), unlike gauge theory, where one additionally restricts the admissible Hamiltonians.

**The relationship between global evolution and regional physical content.** On $\mathcal{H}_{\rm phys}$ the universal state evolves unitarily under a physical Hamiltonian: $|\Psi_t\rangle = U(t)|\Psi_0\rangle$. The induced regional algebra-state evolves linearly: $\omega_t(O) = \omega_0(U(t)^\dagger O U(t))$ for $O \in \hat{\mathcal{A}}(R)$. The map $|\Psi\rangle \mapsto \omega_\Psi$ from Hilbert vectors to regional algebra-states is a structural restriction (analogous to forming a reduced state). It is mathematically linear on density operators and quadratic in vectors.

What is *not* a standard mathematical operation: the physical-precision quotient. Under the literal physical-instantiation reading, the physical wave function in $R$ is not the algebra-state $\omega_\Psi$ but the *equivalence class of $\omega_\Psi$ under physical resolution-$\epsilon$ equivalence*. This quotient is coarser than the algebra-state equivalence; it is the operative equivalence relation on physical regional states.

The physical-precision quotient is what does the foundational work. It is what renders exponentially-small off-diagonal coherence between macroscopic records physically equal to exact zero, converting the merely-approximate classical mixture that standard decoherence delivers into a strictly-exclusive classical mixture. Per-run branch selection (which one of the now-strictly-exclusive branches the universe occupies in a specific run) is supplied by the per-run microscopic IC, not by the precision quotient itself. The quotient is not present in standard QM (which has continuous Hilbert state space); it is not present in Witten's algebraic framework (which has continuous normal-state space on the Type II algebra); it is present in our literal reading of (FQ).

### 6.7 Physics is the macroscopic observable content; branches are not part of it

A potential objection to the framework: even after decoherence + (FQ) render off-diagonal coherence physically zero, the resulting strict classical mixture $\sum_k p_k \omega_k^R$ on $\hat{\mathcal{A}}(R)$ is still a mixture over multiple macroscopic records. To get a single-record per run, one might think the framework needs an additional "selection rule", leading either to MWI (all branches real) or to a hidden-variable mechanism for which branch is actual.

The framework's response cuts deeper than introducing a selection mechanism. It refuses the question of "which Everett branch is realized" by reframing what counts as physical content:

> **Physics is what is encoded in the macroscopic observable algebra. The full universal wave function (with all its mathematical branch structure) is a calculational/formal apparatus; the physical content of any region is the state on the macroscopic record subalgebra $\mathcal{C}(R) \subset \hat{\mathcal{A}}(R)$. We do not have direct physical access to "the universal wave function's branch structure", only to the macroscopic record content. (FQ) constrains the macroscopic record content. At that level, multi-record states are forbidden (conjecturally, see §7.6). Single-record per run is therefore not a "selection" from multiple physically real branches, it is the structural consequence of (FQ) on the macroscopic observable algebra. The microscopic branch question is not part of the physics because it does not appear in the macroscopic observable content.**

This is the operational-realist + algebraic + holographic move. Physics is the content of macroscopic observable algebras (algebraic QFT lineage). These algebras are constrained by (FQ). The "Everett branches" of the universal wave function are mathematical artifacts of the underlying Hilbert-space formalism; they don't enter the macroscopic observable content; they're not part of physics.

This reframing originally motivated the *Macroscopic Definiteness Conjecture* (§7.6); that conjecture is now **retired** as a category error (§1.1a) — capacity is kinematic and does not select outcomes, which is $\lambda$'s role.

### 6.8 The macroscopic record subalgebra and the spectrum of records

**Definition (Macroscopic record subalgebra).** *Let $\hat{\mathcal{A}}(R)$ be the regional Type II crossed-product algebra for region $R$ containing apparatus + environment. The **macroscopic record subalgebra** $\mathcal{C}(R) \subset \hat{\mathcal{A}}(R)$ is the maximal commutative subalgebra of observables that are decoherence-stable under the dynamics of the apparatus + environment, that is, the subalgebra selected by einselection (Zurek) and that supports definite macroscopic records over the relevant timescales.*

For the double-slit screen, $\mathcal{C}(R)$ is generated by the position-localized record projectors $\{P_k\}$ corresponding to spots at different positions. For a generic measurement, $\mathcal{C}(R)$ is the algebra of pointer-basis observables. The subalgebra is approximately commutative (off-diagonal terms between distinct records are exponentially suppressed by decoherence and physically zero under (FQ); cf. §6.2–6.3).

**Spectrum of records.** $\mathrm{Spec}(\mathcal{C}(R))$ is the set of macroscopic record configurations, for the screen, the set of distinct spot positions; for a Stern-Gerlach detector, the set of distinct deflection records; etc. By the Gelfand representation theorem, $\mathcal{C}(R) \cong C(\mathrm{Spec}(\mathcal{C}(R)))$ (continuous functions on the spectrum), and states on $\mathcal{C}(R)$ are probability measures on $\mathrm{Spec}(\mathcal{C}(R))$.

For a finite or countable spectrum (which is the relevant case for macroscopic records on a finite-resolution screen), states on $\mathcal{C}(R)$ are probability distributions $\{p_k\}$ over records.

**Thickened-state construction.** For each record $r \in \mathrm{Spec}(\mathcal{C}(R))$, the **thickened state** $\tilde{\delta}_r$ on the full algebra $\hat{\mathcal{A}}(R)$ is the state corresponding to "record $r$ realized", including all the microscopic structure of the apparatus + environment configuration that produces macroscopic record $r$. This thickened state uses approximately $Q_R$ bits of physical information (it is a specific microscopic configuration of the full apparatus + environment region; macroscopic records consume approximately the full regional holographic capacity).

For a multi-record state, a probability measure $\mu = \sum_k p_k \delta_{r_k}$ on $\mathrm{Spec}(\mathcal{C}(R))$ with multiple records, the *thickened state* is $\tilde{\mu} = \sum_k p_k \tilde{\delta}_{r_k}$ on $\hat{\mathcal{A}}(R)$. This thickened state must encode each constituent macroscopic record's full microscopic configuration plus the probability weights.

**Conjecture (Information cost of multi-record thickened states):** *The renormalized entropy $S_{\rm ren}(\tilde{\mu})$ of a thickened multi-record state $\tilde{\mu} = \sum_k p_k \tilde{\delta}_{r_k}$ scales as $\sum_k p_k S_{\rm ren}(\tilde{\delta}_{r_k}) + H(\{p_k\})$ where $H$ is the Shannon entropy, when the constituent records $\{r_k\}$ are physically distinct macroscopic configurations with mutually exclusive microscopic specifications. When each $S_{\rm ren}(\tilde{\delta}_{r_k}) \approx Q_R$ (records saturate the regional capacity), the thickened multi-record state has $S_{\rm ren}(\tilde{\mu}) \approx Q_R + H(\{p_k\})$, which exceeds $Q_R$ when $H(\{p_k\}) > 0$, i.e., for genuinely multi-record states.*

This is the cost-counting argument the framework rests on for the Macroscopic Definiteness Theorem of §7.6.

**Formalization note, the number-bound is a machine-checked conditional theorem (the strong form is not).** The cost-counting argument above has a *continuum* part (the renormalized-entropy scaling on the Type II regional algebra, which remains the open Macroscopic Definiteness Conjecture, Open Problem 3) and a *finite-dimensional core* that we have now mechanized. In a tractable finite model the argument is no longer a conjecture but an axiom-free Lean theorem (modules `CoreNoCollapse.lean`, `CapacityModel.lean`, `SBSBridge.lean`; standard Lean axioms only). Concretely: realizing the constituent records as an objective Quantum-Darwinist record, a Spectrum Broadcast Structure (Korbicz, arXiv:2007.04276) in which the $n$-outcome pointer is redundantly broadcast to $R$ environment fragments, forces the broadcast support to have Hilbert dimension $\ge n^{R}$ (the fragment Hilbert spaces tensor, so dimensions multiply), hence an *information* storage cost $\ge R\log n$ (`SBSBridge.redundancy_le_logStorage`). Under a finite additive storage capacity $Q_{\max}$, a "macroscopic" record (large redundancy $R$) then has cost exceeding $Q_{\max}/2$, so a region cannot carry two of them: at most one such record is active (`CoreNoCollapse.coactual_subsingleton`, `SBSBridge.sbs_single_outcome`); the selector $\lambda$ supplies which one. The capacity threshold is *derived* from orthonormality of the pointer states ($\sum_j\dim_j\le D$, `CapacityModel.capacity_total`), not stipulated, and the chain is robust to *approximate* decoherence, a near-orthonormal fragment family (pairwise overlap $<1/(n-1)$) is still linearly independent, so the dimension bound survives imperfect distinguishability (`fragment_finrank_ge_approx`), with an amplification lemma showing that weak per-collision distinguishability $\gamma<1$ compounds to exponentially reliable records (block overlap $\le\gamma^{L}\to 0$). This mechanizes the *number-bound* (at most one macroscopic record) form of the conjecture; it does **not** establish the strong superposition-exclusion form (the redundant cat state $\alpha|0\rangle^{\otimes N}+\beta|1\rangle^{\otimes N}$ remains the obstruction, §7.6, Open Problem 3). It is moreover a *conditional* theorem whose one physical input is the factorized, branch-dependent scattering premise ($\gamma<1$); **for the standard collisional/QND monitoring model that premise is itself now a machine-checked theorem.** Taking the textbook interaction $H_{\rm int} = g\,\sigma_z^S \otimes \sigma_x^E$ (Zurek), the branch-conditioned environment records overlap by $\langle E_+|E_-\rangle = \cos^2\theta - \sin^2\theta = \cos 2\theta$, so the per-collision distinguishability $\gamma = |\cos 2\theta| < 1$ for generic coupling $\theta = g\tau$ is *derived*, not assumed (module `CollisionalGamma.lean`: `branch_overlap`, `gamma_lt_one`). The propagator $U_s(\theta) = \exp(-i\theta\,sA)$ is a verified one-parameter unitary group ($A = \sigma_x$ a self-adjoint involution; `collisionU_group`, `hamiltonian_isSymmetric`), the pointer basis is einselected because $[H_{\rm int},\sigma_z^S]=0$, and over $L$ independent collisions the overlap factorizes to $\gamma^L \to 0$ (`collisional_overlap_tendsto_zero`), supplying the previously-assumed amplification input. The residual open physics is the *field-theoretic* version, deriving uniform $\gamma<1$, and the QND/no-recoherence structure itself, from a realistic system–environment Hamiltonian rather than positing the collisional form, a sharply isolated form of the Strasberg–Winter "branch selection problem" (arXiv:2601.19703). Everything downstream of the premise is machine-checked.

### 6.9 Bell: the framework violates Parameter Independence, not measurement independence

A natural objection: any deterministic single-world theory reproducing standard quantum predictions must confront Bell's theorem. The framework is **ψ-monist in the weak (dynamical) sense** (no extra dynamical particles or fields; §2.2), the complete per-run description is the pair $(\Phi, \lambda)$, with $\lambda$ a non-dynamical actuality selector, it reproduces standard quantum predictions, and it has single outcomes per run. *No theory* reproducing the quantum correlations can keep all of Bell's premises; the only question is which one it gives up. We answer that question precisely.

**The framework's commitment: it keeps measurement independence (free settings) and violates Bell local causality, specifically Parameter Independence, at the ontic level, while preserving operational no-signaling.**

Bell's *local causality* factorizes (Jarrett; Shimony) into two sub-conditions, conditional on the complete ontic state:

- **Outcome Independence (OI):** Alice's outcome distribution is independent of Bob's *outcome*, given the ontic state.
- **Parameter Independence (PI):** Alice's outcome distribution is independent of Bob's *setting*, given the ontic state.

The framework's commitments fix the choice with no remaining freedom:

1. It keeps **outcome definiteness** (a single record per run): so the Everett escape (denying definite outcomes) is unavailable.
2. It keeps **measurement independence / free settings**: the settings $a,b$ are statistically independent of the run's actuality fact $\lambda$, $\;\rho(\lambda\mid a,b)=\rho(\lambda)$. The framework therefore **rejects superdeterminism**: this escape is deliberately closed.
3. Because the per-run selection is **deterministic** in $(\Phi,\lambda)$, **Outcome Independence holds trivially** (a deterministic outcome is automatically independent of the distant outcome given $\lambda$).

With (1), (2), and (3) fixed, the only Bell premise left to deny is **Parameter Independence**. There is no fourth door. The framework is therefore **Bell-nonlocal by necessity**, exactly as every single-world, non-superdeterministic, definite-outcome theory must be, and it is honest about *which* horn that is.

**This is not a special property of holography; it is the generic price.** Orthodox quantum mechanics *also* violates Bell local causality. What the present framework adds on top of orthodox QM is *definite $\lambda$-selected outcomes*, and that addition is exactly what re-incurs a burden orthodox (statistical, no-signaling) QM avoids: the ontic-level PI violation must wash out, after averaging over the actuality measure $\mu$, to **operational no-signaling**,
$$
P(A\mid a,b) = P(A\mid a),
$$
even though at the ontic level $P(A\mid a,b,\lambda)\neq P(A\mid a,\lambda)$. Operational no-signaling is established for the framework's instruments (Theorem 7, §7.7; Lean `Theorem7.Setup.no_signaling`). That the *required* cancellation is not fine-tuned, i.e. that the same $\mu$ delivering Born weights also enforces no-signaling without an experiment-by-experiment conspiracy, is a genuine open burden (the Wood–Spekkens fine-tuning problem), recorded as part of the open Born-typicality program (§7.4, §11.4) and in `PROGRAM_STATUS.md`.

**What holographic nonseparability does and does not contribute.** It is tempting to say the Bell correlations are "explained by holographic nonseparability." We resist this: Bell local causality can be formulated for *commuting spacelike algebras* and does **not** require a Hilbert-space tensor factorization, so the Type III$_1$ non-factorization of local algebras (Reeh–Schlieder, vacuum entanglement) is shared with *orthodox* AQFT and does not by itself explain definite-outcome correlations or supply a local completion. Algebraic nonseparability explains why the *state* is nonseparable; it does not select outcomes. The genuine, non-redundant content is the ontic PI violation above; "nonseparability" is the *register* in which that violation lives, not an independent escape. (We also avoid leaning on "no tensor factorization" as the escape while simultaneously invoking the split property elsewhere to model local instruments; the split property supplies an *approximate* Type I factorization adequate for ordinary Bell experiments, and the two registers must not be conflated.)

**No-signaling ≠ locality ≠ Lorentz invariance.** These are distinct, and we claim only what is established: PR-box correlations are no-signaling yet *more* nonlocal than quantum mechanics, so operational no-signaling (which we have) does not by itself secure Bell-correct correlations *or* Lorentz invariance of the beable $C_R$. Lorentz covariance of the selection map $A_R[\Phi,\lambda]$, that it carries no hidden foliation, is **not** established and is recorded as an open problem of equal rank to the Born-typicality measure (§11; `PROGRAM_STATUS.md`).

**Position with respect to Kochen–Specker.** If per-run structure determines outcomes, value assignments must be contextual, which the framework accepts. The per-run wave function's content on a regional algebra is naturally contextual: different measurement contexts probe different algebra-projections, with no requirement of joint-value consistency across noncommuting contexts.

**Position with respect to PBR.** The framework is **ψ-ontic and ψ-monist in the weak (dynamical) sense**: $\Phi$ is physically real and is the sole *dynamical* ontology. It adds no hidden particle positions, no hidden fields, no second *dynamical* layer. It does include one non-dynamical actuality fact, the selector $\lambda$ fixing which single record is realized (§2.2, §7.6), so it is **formal-ψ-incomplete**: the actual per-run ontic state is the pair $(\Phi, \lambda)$, finer-grained than the textbook formal wave function (which describes the across-run distribution). PBR rules out certain ψ-epistemic positions; the framework is ψ-ontic and not one of those, $\Phi$ is real, not a state of knowledge.

**Contrast (not alliance) with Palmer's RaQM / Invariant Set Theory.** Palmer (2025 and prior work) takes the *other* horn: a principled rejection of **measurement independence** via the geometry of a fractal invariant set, formally a (non-conspiratorial) measurement-dependence / superdeterminism-family escape. The present framework deliberately takes the opposite horn: it *keeps* measurement independence and pays at Parameter Independence instead. The two programs share only single-world realism and a finite-information motivation; on the Bell question they are contrasting, not allied. Detailed comparison is in §10.8.

### 6.10 Tunneling: standard dynamics, record-level reading

Quantum tunneling is a useful test of what QIQT-H does and does not modify. The under-barrier amplitude is real physical content of the formal field state, and **all tunneling amplitudes and rates are exactly those of standard quantum theory**, coherent tunneling (ammonia inversion, Josephson oscillation, double-well coherent oscillation), WKB barrier penetration, $\alpha$-decay and fusion rates, instanton / vacuum-decay amplitudes, and Quantum Zeno / anti-Zeno effects are all unchanged, because (FQ) does not modify the Schrödinger evolution of the underlying field algebra.

**The information limit constrains how the wave function *resides*; it does not trim it.** This point must be stated carefully, because QIQT-H is ψ-monist and deterministic: there are **no fundamental probabilities** in the theory, only the wave function and its unitary evolution. The holographic / (FQ) bound is a constraint on the *physical specification capacity* of a region, on how much amplitude/phase structure the wave function can be instantiated with in $R$, not a dynamical rule that sets small amplitudes to zero. Concretely:

- The under-barrier evanescent tail is **genuine wave-function content** and stays so. (FQ) never deletes it, never truncates it to zero, and never alters its unitary evolution. The Schrödinger equation runs untouched.
- (FQ) does *not* act pointwise on $\psi$ in the forbidden region. The pointwise value $\psi(x)$ is not even a well-defined physical target for a floor: it is basis-, normalization-, and coarse-graining-dependent, and in the continuum it is dimensionful. The bound is a statement about the regional algebra-state's information content, not about individual amplitudes.
- There is therefore **no kinematic cutoff on tunneling amplitudes**. Any reading on which "a tunneling amplitude below $\varepsilon(R)$ is excluded" is mistaken. The decisive objection is dynamical and basis-theoretic: a fixed pointwise floor would be ill-defined (a transition amplitude over a time slice scales with the arbitrary slice duration; the pointwise value is basis-, normalization-, and coarse-graining-dependent) and, applied to the dynamics, would break unitarity and wrongly freeze ordinary decay. Independently, such a reading misreads (FQ): (FQ) is a capacity constraint on regional residence, not an amplitude-trimming operation: and, since the theory has no fundamental probabilities, "excluding a low-amplitude outcome" is not even a move the framework can make.

What (FQ) *does* constrain is the regional **record structure**: distinct, decohered, macroscopically distinguishable records cannot be co-instantiated in $R$ beyond its finite capacity $Q_R$. This is where the framework's content enters, not in the coherent tunneling amplitude, but in how a tunneling *outcome* can reside as a definite regional record.

The correct statement is therefore: QIQT-H leaves the tunneling wave function and its evolution exactly as in standard quantum theory, and differs only in what it says about the **regional record once decoherence has occurred** (the particle is found, or not, on the far side). Per run, the deterministic evolution of the full wave function, together with the finite regional capacity, which cannot hold a co-resident superposition of macroscopically distinct records, leaves a single record physically instantiated in $R$. The textbook Born numbers $|\psi|^2$ are recovered as the *empirical frequency pattern* of records across many runs (the typicality reading of §7.4, §11.4), never as a fundamental per-run probability. This is the same mechanism as for any other measurement (§6); tunneling is not a special case. **Standard dynamics (barrier penetration, unchanged); QIQT-H reading of the regional record only, and even there, by capacity constraint, not by amplitude trimming.**

**Horizon tunneling (Hawking radiation).** The Parikh-Wilczek (1999) tunneling derivation of Hawking emission expresses the emission rate as $\Gamma \sim \Gamma_{\rm grey}\, e^{\Delta S_{\rm BH}}$, where $\Delta S_{\rm BH} = \Delta A/(4\ell_P^2)$ is the change in Bekenstein-Hawking entropy (in nats). For an emitted quantum the horizon area decreases, $\Delta A < 0$, so the exponential factor *suppresses* emission; writing the positive entropy loss $\Delta S_{\rm loss} = S_i - S_f > 0$, $\Gamma \sim \Gamma_{\rm grey}\, e^{-\Delta S_{\rm loss}}$ (greybody prefactor $\Gamma_{\rm grey}$ aside). The same entropy is what QIQT-H reads as the finite information content of the horizon region (in bits, $Q_{\rm hor} = S_{\rm BH}/\ln 2 = A/(4\ell_P^2 \ln 2)$). This is a clean conceptual alignment, the same quantity governs lab-scale per-run wave functions and the horizon's information budget, but it is a *reinterpretation*, not a new prediction: QIQT-H does not by itself modify or re-derive the Parikh-Wilczek emission rate.

---

## 7. Formal Consequences

### 7.1 Theorem (FQ restricts physically realized wave functions)

**Theorem 2.** *The class of per-run wave functions consistent with (FQ) is a proper subclass of formally describable wave functions in standard $T_{QM}$. Specifically, formal wave functions whose induced state on some $\hat{\mathcal{A}}(R)$ violates the renormalized entropy bound $S_{\rm ren}(\omega_\Psi) > Q_R$ are excluded as physically realized per-run states.*

*Proof.* (FQ) part (ii) imposes $S_{\rm ren}(\omega_\Psi) \le Q_R$ on per-run wave functions. Formal wave functions in standard $T_{QM}$ are not subject to this constraint; we can construct formal states whose induced regional states violate the bound. Such formal states are excluded from the physical model class. $\blacksquare$

### 7.2 Theorem (Finite physical resolution)

**Theorem 3.** *Under the literal physical-instantiation reading of (FQ), the per-run wave function in any bounded region $R$ has a finite physical resolution floor $\epsilon(R) > 0$. Amplitudes within $\epsilon(R)$ of $0$ are physically equivalent to amplitude exactly $0$; amplitudes within $\epsilon(R)$ of $1$ are physically equivalent to amplitude exactly $1$.*

*Proof sketch.* By (FQ) part (iii), the wave function in $R$ has total physical information content bounded by $Q_R$. Specifying amplitudes to arbitrary precision requires unbounded information. Therefore amplitudes are physically specified only to finite precision $\epsilon(R)$. Within this precision, distinct mathematical amplitudes correspond to the same physical state. Functional dependence of $\epsilon(R)$ on regional geometry, macroscopic record dimension, and the (FQ) bound is identified as an open quantitative problem (§11.4); the qualitative existence of $\epsilon(R) > 0$ follows from the literal reading. $\blacksquare$

### 7.3 Theorem (Single-record per-run wave functions)

> **Superseded (2026) — see the Macroscopic Definiteness retraction in §1.1a.** The single-record conclusion stands, but it follows from $\lambda$-selection (P1) + decoherence — **not** from the finite capacity forbidding a $\ge 2$-record state. The "summed information cost $I_\Sigma \approx K\cdot I_0 > Q_R$ / not instantiable" step (and its labelling as "the load-bearing step") is the **retired category error**: the branch-summed cost is not the entropy (`BranchLedger.branchSummed_not_bounded_by_Shannon`), and a second branch adds only $\sim\!\log K$ to $S(\rho_R)$, far below $Q_R$. Throughout this theorem and its remarks, read "the load-bearing single-ness step" as **$\lambda$-selection**, and the capacity bound as playing only its kinematic role.

**Theorem 4 (Single-record per-run).** *Under (FQ) in its literal physical-instantiation reading, together with (i) standard decoherence (which renders the macroscopic records non-interfering) and (ii) the non-dynamical selector $\lambda$ of the $(\Phi,\lambda)$ ontology (P1), which marks exactly one decohered record actual per run, the per-run wave function in any region $R$ containing apparatus + environment after measurement is physically a single-record state. Which record is realized is indexed by the run's microscopic initial conditions; the unrealized records have no physical referent in $R$ (they are not instantiable, not "real elsewhere"). No amplitude is trimmed and the global evolution is exactly unitary throughout.*

*Proof.* By standard (unitary) decoherence, the regional state on $\hat{\mathcal{A}}(R)$ is exponentially close to a strict classical mixture $\sum_k |c_k|^2 \omega_k^R$ of macroscopic records, interference is gone, but the mixture still carries every record (branch weights $|c_k|^2$ are conserved; cf. `NoConcentration.lean`). By Theorem 3 the (FQ) resolution floor $\epsilon(R) > 0$ makes the residual sub-$\epsilon$ off-diagonal coherence have no physical referent (a resolution-equivalence on regional states, §5.1), so the resident content is exactly that strict mixture. By $\lambda$-selection (P1), on the decohered (non-interfering) record set exactly one record is marked actual; hence the resident regional content is single-record. (The earlier "summed cost $I_\Sigma \approx K\cdot I_0 > Q_R$ / not instantiable" route is **retired** as a category error, §1.1a.) Which record is realized is indexed by the run's microscopic initial conditions. The global evolution remains exactly unitary; no amplitude is trimmed. $\blacksquare$

*(The single-record step is supplied by $\lambda$-selection (P1) + decoherence; the former §7.6 Macroscopic-Definiteness / $I_\Sigma > Q_R$ step is **retired** as a category error, §1.1a — not an open problem. The (FQ) resolution-equivalence of §5.1 removes the residual sub-$\epsilon$ off-diagonal coherence. The machine-checked `CoreNoCollapse`/`CapacityModel`/`SBSBridge` development (§6.8) proves a conditional single-record statement for a finite **additive**-cost model; but since the additive (branch-summed) cost is provably not the holographic von Neumann entropy `branchSummed_not_bounded_by_Shannon`, this models the storage of the $\lambda$-selected record, and does **not** revive the retired "capacity forbids two records" reading.)*

*Remark on what does the work (not "amplitude concentration").* It would be a mistake to read Theorem 4 as "decoherence + microscopic IC drive the per-run amplitudes dynamically to $0$ or $1$." They do not: by unitarity the branch weights $|c_k|^2$ are conserved (the `NoConcentration.lean` audit makes this precise), so decoherence removes *interference* but never *selects* a record, the decohered diagonal content still carries every record. The single-record conclusion comes instead from the selector $\lambda$ (P1): on the decohered record set, $\lambda$ marks exactly one record actual. (The earlier "finite-information restriction / summed cost $> Q_R$" route is **retired**, §1.1a — capacity is kinematic, not exclusionary.) The (FQ) resolution floor plays the subsidiary role of removing the residual sub-$\epsilon$ off-diagonal coherence (as a resolution-equivalence on regional states, not by trimming any amplitude). Microscopic IC then merely index which single record the run carries. This is the cooperative structure: decoherence (interference) + $\lambda$-selection (single-ness, the load-bearing step) + IC (which one).

*Remark on how a single record arises (decoherence is necessary but not sufficient).* A machine-verified audit (`lean/mathlib/QIQTH/NoConcentration.lean`) confirms that linear unitary measurement-decoherence **alone** cannot produce a single record: branch weights $|c_k|^2$ are conserved by unitarity, not concentrated toward $0$ or $1$. The equal-superposition input $\psi = (|0\rangle + |1\rangle)/\sqrt{2}$ leaves post-measurement weights exactly $(1/2, 1/2)$. Decoherence solves the *interference* problem (it makes distinct records exponentially distinguishable), but it does **not** solve the *selection* problem: the decohered regional state $\sum_k |c_k|^2 \omega_k^R$ is diagonal yet still carries $K \ge 2$ macroscopic records. The single-record-per-run content comes from the **finite-information space itself**, in two cooperating steps with the second doing the load-bearing work:

1. **Decoherence (unitary, standard, dynamical).** Entangling a record with $N$ apparatus + environment particles drives the off-diagonal coherence between macroscopically distinct records down like $e^{-N}$. This is ordinary Schrödinger evolution: no modification, no probability, no amplitude trimming.

2. **Holographic restriction on the physical state space (the one-world source).** The region has finite information capacity $Q_R$, and the physical wave function *resides on that restricted information space*. A regional content carrying $K \ge 2$ macroscopically distinct records: whether coherently superposed *or* classically mixed, has summed information cost $I_\Sigma \approx K \cdot I_0$, and with $I_0 \approx Q_R$ at macroscopic scale this exceeds $Q_R$ for $K \ge 2$. Such a content is therefore **not a point of the region's physical state space at all** (the Branch-Summed Holographic Bound / Macroscopic Definiteness Conjecture, §7.6). The resident regional physical content is single-record.

This is decisively **not** many-worlds with regional coarse-graining: the unrealized records are not "real elsewhere", they have *no physical referent*, because $\lambda$ (P1) marks exactly one decohered record as the actual regional content (the unselected records remain in $\Phi$ but are not regionally instantiated). It is also **not** a modification of the dynamics: the Schrödinger / Heisenberg evolution *law* is exactly unitary throughout; what is restricted is the *physical state space* (the finite-information regional content). A formal multi-record Hilbert-space vector remains a perfectly good *calculational* descriptor; it simply has no per-run physical referent in $R$, this is (FQ) part (iii) together with the formal/per-run distinction, not a ban on Hamiltonians and not a non-unitary projection. **There are no fundamental probabilities anywhere:** the weights $|c_k|^2$ are the empirical frequency pattern of records *across runs* (§7.4, §11.4), and the per-run microscopic initial conditions merely *index which* single-record universe a given run is (distinct runs are distinct actual universes), IC does not *produce* single-ness; the selector $\lambda$ does.

### 7.4 Theorem (Conditional Born typicality)

**Reframing.** QIQT-H has no fundamental probabilities. The framework is deterministic per run: microscopic initial conditions of that run determine which macroscopic record is realized. "Born" in QIQT-H refers to the *empirical frequency pattern* across many runs, a statistical regularity that must emerge from the IC distribution, not a primitive probability assignment. Accordingly Theorem 5 is best understood not in the probability-axiomatic mode of Gleason's theorem, but in the **typicality** mode of Bohmian Dürr-Goldstein-Zanghì equivariance (adapted to QIQT-H's no-particle, no-branching ontology).

**Theorem 5 (Conditional Born typicality).** *Let $\rho$ be a preparation state, $\Omega_\rho$ the QIQT-H microscopic-IC space, and $O_M : \Omega_\rho \to \mathrm{Outcomes}(M)$ the deterministic outcome map for a measurement protocol $M$. Suppose:*

*(i) **Canonicality.** There exists a measure $\mu_\rho$ on $\Omega_\rho$ defined from QIQT-H primitives (not fitted per measurement).*

*(ii) **Born pushforward.** $(O_M)_* \mu_\rho(i) = \mathrm{tr}(\rho E_i)$ for every allowed outcome effect $E_i$ in the measurement protocol $M$.*

*(iii) **Equivariance / stationarity.** $\mu_\rho$ is preserved (up to allowed parameter-dependence on $\rho$) by the (FQ)-restricted physical Hamiltonian.*

*(iv) **Repeated-trial typicality.** Repeated trials of the prepare-measure procedure are represented by a $\mu_\rho$-typical iid (or stationary-ergodic) process on $\Omega_\rho$.*

*Then for $\mu_\rho$-typical microscopic-IC sequences, the empirical relative frequency of macroscopic outcome $k$ across many runs converges to the Born weight $\mathrm{tr}(\rho E_k)$ (= $|c_k|^2$ for pure states with $\rho = |\psi\rangle\langle\psi|$ and projective measurements).* $\blacksquare$

**Status of the four hypotheses.** Hypotheses (ii) and (iv) are standard: (ii) is what defines $\mu_\rho$ as "the Born measure" for $\rho$; (iv) is a routine LLN/ergodicity input. Hypotheses (i) and (iii), *canonicality* and *equivariance*, are the **framework's load-bearing open commitments**. They are not delivered by FQ + AQFT + holography alone; see machine-verified audits below.

The conditional shape of Theorem 5 is now formalized in `lean/mathlib/QIQTH/BornTypicality.lean` (theorem `qiqth_born_typicality_conditional`). The deterministic core (mean per-run frequency equals the outcome marginal) is rigorously proved; the LLN step is taken as a standard probability black box at the interface layer.

**Important, QIQT-H does not derive the Born measure.** It identifies the exact canonical-measure / equivariance principle required for Born frequencies, and reduces the Born problem to that principle. This is the typicality-paradigm analog of Bohmian $|\psi|^2$-equivariance, adapted for QIQT-H's no-particle ontology.

**Audit remark, universal realizability (the negative companion).** A machine-verified audit (`lean/mathlib/QIQTH/NoBornFromNothing.lean`) establishes that for **any** target outcome distribution $p$ (not just $|c_k|^2$) and any surjective outcome map from the IC space, there exists a measure $\mu_p$ whose outcome-marginal equals $p$. Construction: choose a section of the outcome map and place mass $p_k$ on $s(k)$. Hence the framework's structural axioms (FQ, microcausality, Donald, holographic bound) do *not* select Born over any other distribution. Hypothesis (i) of Theorem 5 is therefore *genuinely independent* of the other QIQT-H postulates, it must be added as a separate principle, not derived.

**Audit remark, support preservation $\neq$ Born equivariance.** A second machine-verified audit (`lean/mathlib/QIQTH/EquivarianceGap.lean`) establishes that the framework's claim that the exactly-unitary dynamics carries instantiable regional contents to instantiable regional contents (the closure property of §7.6, preservation of the *support* of the admissible set) is strictly weaker than the measure-preservation hypothesis (iii) of Theorem 5. Concrete counterexample: a bijection on a 2-point space preserves the support trivially yet shuffles a non-uniform measure. Hypothesis (iii) is therefore a *genuine additional commitment* beyond the framework's current postulates.

**Candidate principles for hypothesis (i).** Four candidate physical mechanisms could supply the Canonical IC Measure Principle. A 2026-06 circularity audit (GPT-5.5-pro consultation, cross-checked against the Lean Born modules) sharpened their relative status. The discriminating ingredient that every route must supply is one and the same: **additivity / non-contextuality of the selector measure** (equivalently, no-signaling of the outcome marginal under record refinement). This is not a neutral regularity condition: on the quantum effect algebra, positivity + normalization + that additivity is *equivalent* to the Born trace form $\mu(E)=\mathrm{tr}(\rho E)$ (the machine-checked `EffectGleason.finite_effect_gleason`, all finite dimensions), and the $\alpha$-deformation $q_k \propto w_k^{\alpha}$ that satisfies every $\alpha$-blind structural axiom fails *exactly* additivity (`RefinementBorn.sq_not_additive`). The candidates therefore differ not in *whether* they need a Born-strength premise, but in whether that premise is stated transparently or is smuggled through structure that already encodes $|c_k|^2$.

*(α) **Canonical tracial typicality from CPW Type II structure.** The crossed-product Type II algebra $\hat{\mathcal{A}}(R)$ carries a canonical normal semifinite trace $\tau_R$ (unique up to scale), and it is tempting to read $\tau_R$ as the canonical IC measure. The audit flags this as **high-circularity**, and we accordingly retract the earlier "leading candidate" status. The trace alone yields the relative-dimension / maximally-mixed measure $\tau_R(P)/\tau_R(\mathbf 1)$, **not** the Born measure for a given $\Phi$; recovering Born requires the $\Phi$-normal state $\omega_\Phi(P)=\tau_R(h_\Phi P)$ with Haagerup/Radon–Nikodym density $h_\Phi=d\omega_\Phi/d\tau_R$, and the identification $\mu_\rho := \omega_\Phi$ **is** the Born postulate in algebraic dress (precisely the empirical-selection step isolated in §11.4.2). Moreover the existence and uniqueness of $\tau_R$ are $\alpha$-blind: they do not exclude $q_k \propto \omega_\Phi(P_k)^{\alpha}$. So (α) supplies the most QIQT-H-native *language* but does not by itself force additivity.*

*(β) **Symmetric equiprobability** on a natural decomposition of $\Omega_\rho$ into record-fibers, with Born weights emerging from fiber-volume ratios (formalized for an equal-amplitude orthonormal fine-graining in `BornEquiprobable.lean`). The Zurek amplitude→count bridge is machine-checked: the *uniform* measure over an equal-**norm** orthonormal fine-graining has outcome-marginal exactly $|c_k|^2$, by orthonormality alone (Pythagoras), discharging the previously-posited multiplicity $\mathrm{count}=M\,w_k$. But the load-bearing premises survive untouched: (i) **envariance** — why the measure is uniform over the equal-amplitude atoms — and (ii) **canonicity of the equal-norm fine-graining** (refinement-additivity, which is exactly what excludes the $\alpha$-family); the unequal-amplitude step itself *is* refinement-additivity. So (β) relocates, but does not eliminate, the additivity premise.*

*(γ) **Holographic / modular construction** from the canonical sector reference state $\sigma_R$ (vacuum on Minkowski, KMS on stationary thermal, Bunch-Davies on de Sitter, etc.) via a modular-theoretic construction yielding $\mu_\rho$. Physically attractive but the least developed; the audit notes it inherits (α)'s circularity, since the modular flow / $\Phi$-normal state already carries the $|c_k|^2$ content.*

*(δ) **Actuality Projective Consistency** (a selector-level principle, and the one *syntactically* Born-free option). Upgrade $\lambda$ from a flat index over histories to a **projective/sheaf-like assignment over record refinements**, and impose: a local nondemolition (e.g. Spectrum-Broadcast) refinement $C'$ of a recorded coarse observable $C$ only *refines* the selected history — it does not change its coarse restriction — pointwise in the IC, $s_C(\omega)=\pi\!\big(s_{C'}(\omega)\big)$ for the forgetful map $\pi:H_{C'}\to H_C$. Ordinary within-context additivity of any measure $\mu$ on the IC then *pushes forward* to refinement-additivity of the outcome marginal, hence, with positivity, to Born (via `RefinementBorn.refinementNatural_additive` composed with `EffectGleason`). The distinctive feature is that this premise mentions **no amplitudes, no $|c_k|^2$, no trace**: it is *syntactically* Born-free, an ontic statement purely about the consistency of $\lambda$ under coarse/fine-graining of records. It is **not** thereby Born-*weak* — it is the ontic form of no-refinement-signaling, and on the effect algebra it is Born-strength — but it isolates the missing premise at the selector level without smuggling the Born numbers, and is therefore the **most honest** statement of what must be assumed. Two caveats keep it honest: (a) it must be restricted to *pure refinements of the same recorded coarse observable*; extended to arbitrary settings it would collide with the Parameter-Independence horn of §6.9 (deterministic parameter independence for all settings plus measurement independence is Bell-local and cannot reproduce the quantum correlations); and (b) its own *weak* grounding fails — microcausality of $\Phi$ together with an inert, non-back-reacting $\lambda$ does **not** force no-signaling of $\mu$. The $\alpha=2$ rule is the explicit counterexample: it leaves $\Phi$ exactly unitary and $\lambda$ inert, yet a local binary split of a remote-correlated branch changes the remote marginal (a $\tfrac12\!\to\!\tfrac13$ shift). So (δ) names the irreducible premise sharply; it does not derive it.*

None of (α)–(δ) is derivable from FQ + AQFT + holography alone; each supplies — transparently in (δ), implicitly in (α)–(γ) — the single additivity / non-contextuality bridge that the `NoBornFromNothing` and `RefinementBorn.sq_not_additive` countermodels show to be **necessary and independent**. The position the framework adopts (§11.4) is accordingly that *one* such bridge must be posited, the relativistic analogue of Bohmian quantum equilibrium and of the Everettian probability postulate; the contribution of this audit is to identify that bridge as additivity/non-contextuality, to retract the over-optimistic reading of the tracial route (α), and — via (δ) — to state the bridge in its most honest, amplitude-free, selector-level form. Open Problem 1 (§11.4) sharpens the canonical-measure problem with explicit sub-conditions.

*Remark on Gleason.* Gleason's theorem derives the Born rule from probability-axiomatic constraints (noncontextuality + orthogonal additivity) on a projection lattice. It is *not* the appropriate primary derivation for QIQT-H, which is deterministic per run and has no primitive probability assignment. Gleason functions as a consistency check on the *target* empirical frequencies (Born is the unique probability rule consistent with the noncontextuality axioms), but cannot select the microscopic IC measure $\mu_\rho$, many distinct $\mu_\rho$ push forward to the same Born outcome distribution. Closing the gap requires the typicality argument above, not Gleason.

### 7.5 What §7.1–7.4 establishes

(FQ) restricts the model class properly (Theorem 2); the literal physical-instantiation reading implies finite physical resolution (Theorem 3); combined with decoherence (which removes interference) and the finite-information restriction of §7.6 (which makes a $\ge 2$-record regional content non-instantiable), this yields single-record per-run regional content structurally (Theorem 4); Born statistics emerge as an across-run typicality / relative-frequency result (Theorem 5, schematic).

The framework's structural skeleton: (FQ) is the literal physical-instantiation reading of the Bekenstein-Bousso bound, stated rigorously in the CPW Type II algebraic framework; the finite-information restriction on regional content is what makes the resident regional state single-record, with the run's microscopic initial conditions indexing which record and the global evolution left exactly unitary.

### 7.6 The Modular-Local Holographic Superselection Rule (foundational postulate)

> **Retired (2026) — see the Macroscopic Definiteness retraction in §1.1a.** This section's central postulate — that a $\ge 2$-record regional content has summed cost exceeding $Q_R$ and is therefore *not an instantiable physical state* (the Branch-Summed Holographic Bound / Macroscopic Definiteness Conjecture) — is **withdrawn as a category error**: $Q_R$ bounds the von Neumann entropy $S(\rho_R)$, which a second macroscopic branch raises by only $\sim\!\log K$ (not by a further $\approx Q_R$), so a multi-record state does **not** overflow capacity; and no kinematic entropy bound can *select* an outcome in a unitarily-evolving theory. Single-record definiteness comes from the selector $\lambda$ (P1) together with decoherence, **not** from this rule. The material below is retained for the historical record and for the parts that *do* stand — the kinematic bound $S(\rho_R)\le Q_R$ and the no-signaling corollary (§7.7) — but its single-ness / superselection / "not instantiable" claims are superseded.

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

**Scope: what the bound does *not* forbid, and what therefore does the work (important).** It is essential to be precise about the reach of any entropy-type bound, because a naive reading overclaims. The naive argument, "a two-record content must encode the joint information of both records, which exceeds $Q_R$", *does not follow from the Bekenstein–Bousso bound, and we explicitly disavow it.* An entropy bound limits the number of mutually **distinguishable** records a region can carry ($\# \le e^{Q_R}$); it does **not** forbid a **superposition** of records. The decisive counterexample is a redundant cat state,
$$
|\Psi\rangle = \alpha\,|0\rangle^{\otimes N} + \beta\,|1\rangle^{\otimes N},
$$
which encodes two macroscopically distinct, redundantly copied records, fits in $N$ qubits, and is a **pure state of zero entropy**, violating no entropy bound whatsoever. More generally, by linearity of the exactly-unitary dynamics, if $|R_0\rangle$ and $|R_1\rangle$ are each individually instantiable in $R$, then so is $\alpha|R_0\rangle + \beta|R_1\rangle$, *unless an additional superselection-type principle is imposed*, and any such principle stands in tension with the exact unitary linearity this framework otherwise preserves. (This is precisely why the single-record claim is a *postulated superselection rule* above, a strengthening of standard holography, and not a corollary of it.)

Consequently the honest **division of labor** is: decoherence + einselection supply *stable, robust, effectively Boolean* candidate records (the classical stage; this gives robustness, not uniqueness); the modular-local capacity bound makes the set of *distinguishable* records *finite* (cardinality, not superposition-exclusion); and the **uniqueness of the actual record is supplied by the non-dynamical actuality fact $\lambda$** (§1.0a, §11.3), not derived from $Q_R$. The framework's single-record-per-run content rests on $\lambda$ regardless of whether the superselection rule below can be established. A positive resolution of that rule would upgrade $\lambda$-selection from a postulate toward a structural consequence; a negative resolution leaves all empirical claims intact, with the selection mechanism explicitly postulated. In its strong "finite capacity *forbids* macroscopic superposition" form, the rule is not merely unproven but, in light of the cat-state obstruction above, currently *implausible* without additional nonstandard structure; this is recorded honestly as Open Problem 3.

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

*Here $\mathcal{S}_{\rm phys}$ is the set of physically instantiable regional contents (those satisfying the finite-information admissibility bound). The condition says only that physical evolution carries instantiable contents to instantiable contents; it is **not** a restriction on the admissible Hamiltonians. The global Schrödinger / Heisenberg law is exactly unitary and unconstrained, a formal global state whose regional content leaves $\mathcal{S}_{\rm phys}$ remains a valid calculational descriptor, it simply has no per-run physical referent in that region.*

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

Equivalently: physical evolution preserves the set of instantiable regional contents. This is a closure property of $\mathcal{S}_{\rm phys}$ under the (exactly unitary, unconstrained) dynamics, not a selection rule on Hamiltonians, every standard Hamiltonian is admissible; what the framework restricts is which *regional contents* count as physically instantiated, not which evolutions are allowed.

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

**Sharpening of (H2), reference-weight form.** A machine-verified audit (see `lean/mathlib/QIQTH/H1H2Audit.lean` in the project repository) confirms that (H2) is genuinely independent of (H1), Donald's identity, Klein positivity, and DPI: a classical KL countermodel with $\sigma=(1/2,1/2)$ and $\rho=\delta_0$ satisfies all the structural hypotheses but violates (H2) with $I_0=1$. The same audit also yields the following sharp structural reformulation of (H2). For a perfect-record state on event $E_{\rm record}$,
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

**The adopted reading: a restriction on the physical state space, not on the dynamics.** Standard Hilbert-space QM is the unconstrained formalism. The constrained set $\mathcal{H}_{\rm phys}$, regional contents with $I_\Sigma \le Q_R$, is a *nonlinear set of admissible regional contents* (the possible values of $C_R$), **not** an invariant Hilbert subspace in which the global $\Phi(t)$ evolves; the constraint $I_\Sigma \le Q_R$ is nonlinear in the state. The restriction is on *which regional contents are instantiable physical states*, **not** a restriction on the allowed Hamiltonians and **not** a claim that "certain unitaries do not occur." The Schrödinger / Heisenberg evolution law is exactly unitary and entirely standard, including ordinary measurement interactions. What the formalism's linearity produces, the global multi-record vector $\sum_k c_k |A_k\rangle|E_k\rangle$, remains a perfectly good *calculational* descriptor; the framework's claim is that its regional content in $R$, carrying $\ge 2$ macroscopic records at summed cost $I_\Sigma \approx K \cdot I_0 > Q_R$, **cannot be instantiated in its entirety as the actual content of $R$**.

It is essential to be precise about what this does and does not deliver. The capacity bound does *negative* work only: it forbids a $\ge 2$-record regional content. It does **not**, by itself, pick out which single record is the actual one, and decoherence cannot do so either (it conserves the branch weights $|c_k|^2$; `NoConcentration.lean`). The actual single-record content of $R$ in a given run is the derived beable
$$C_R = A_R[\Phi, \lambda],$$
the single record sector selected by $\lambda$, the run's actual microscopic initial conditions of apparatus + environment. Here $A_R$ is a *fixed, non-dynamical reading functional*, part of the interpretive postulate (not a per-run free object): given $\Phi(t)$, the run-index $\lambda$, and the decoherence-defined record decomposition of region $R$, it returns one admissible record sector $C_R(t)$. It carries no run-dependent degrees of freedom beyond $\lambda$, does not alter $\Phi$, and is required to be consistent across overlapping/nested regions and across time. Thus the per-run ontology is the pair $(\Phi, \lambda)$ (the exactly-unitary global $\Phi$ plus the non-dynamical actuality selector $\lambda$), and the fixed theoretical structure comprises the unitary law, the capacity bound, the typicality measure, and the reading functionals $\{A_R\}$, lawlike structure, not a further per-run substance. $C_R$ is not a third substance and is not $\Phi$ restricted to $R$ (that restriction is the full $K$-record mixture); it is the $\lambda$-selected sector, eliminable in favour of $(\Phi, \lambda, A_R)$ but **not** in favour of $\Phi$ alone. Two honest consequences follow. First, $\lambda$ is a *broad-sense* beable, an actuality fact not contained in bare $\Phi$, so the framework is ψ-monist only in the *weak (dynamical)* sense ($\Phi$ is the sole dynamical ontology), not in the strong sense that $\Phi$ alone is the complete per-run state. Second, the selection role of $\lambda$ and the typicality measure it carries are genuine additional commitments (consistent with the `EquivarianceGap.lean` audit), not consequences of (FQ) alone. This is (FQ) part (iii) plus the formal/per-run distinction, a statement about physical instantiability of regional contents and their $\lambda$-selection, with the global evolution law left untouched.

**Response to the linear measurement obstruction.** A standard objection: "By linearity, $U(\alpha|0\rangle + \beta|1\rangle)|A_{\rm ready}\rangle = \alpha|A_0\rangle + \beta|A_1\rangle$, exactly the forbidden multi-record state."

This objection assumes that the unrestricted-Hilbert-space wave function $\alpha|A_0\rangle + \beta|A_1\rangle$ is the physically primary object, the actual physical state that we have direct access to. The framework denies this. **We do not have direct physical access to unrestricted-Hilbert-space states; we have access only to the physical observable content of bounded regions, the state on the macroscopic record subalgebra $\mathcal{C}(R)$, with the (FQ) precision floor.**

The screen is a complex quantum system with $\sim 10^{20}$–$10^{25}$ degrees of freedom that becomes entangled with the particle during detection. Decoherence between distinct macroscopic record states $|A_0\rangle$ and $|A_1\rangle$ produces environmental cross-overlaps $\langle E_0 | E_1 \rangle \sim e^{-10^{20}}$ on physically realistic timescales (§6.2). Under (FQ), these exponentially-small off-diagonal coherence terms are *physically zero* (§6.3).

So at the level of physical observable content, which is what physics is about, the formal $\alpha|A_0\rangle + \beta|A_1\rangle$ structure decoheres to a classical-looking expression, and the residual sub-$\epsilon$ coherence has no physical referent under (FQ) (a resolution-equivalence on regional states). The physical content on the macroscopic observable algebra is a strict classical mixture over records. The finite-information restriction then says: a regional content carrying $\ge 2$ macroscopically distinct records (summed cost $I_\Sigma \approx K\cdot I_0$ approaching/exceeding $Q_R$) is *not an instantiable physical state of the region*, it has no per-run physical referent.

It is essential that this is a restriction on which *regional contents* are physically instantiable, **not** a modification of the dynamics. The formal global vector $\alpha|A_0\rangle|E_0\rangle + \beta|A_1\rangle|E_1\rangle$ produced by ordinary linear unitary evolution is a perfectly good *calculational descriptor*, it is the cross-run ensemble descriptor, not the per-run physical state. What is physically real per run is the regional content, and by the finite-information restriction that content is single-record. *Which* record a given run carries is fixed by that run's actual microscopic initial conditions (distinct runs are distinct actual universes; the IC index the run, they do not produce the single-ness). The global Schrödinger / Heisenberg evolution law is left exactly unitary and entirely standard throughout; no Hamiltonian is restricted and no amplitude is trimmed.

The "linear measurement obstruction" thus disappears once one recognizes that (a) physical content is the regional algebra-state content of bounded regions, not the unrestricted global Hilbert-space vector; (b) decoherence removes interference and (FQ) removes the residual sub-$\epsilon$ coherence as a resolution-equivalence; (c) the finite-information restriction makes a $\ge 2$-record *regional content* non-instantiable, the multi-record global vector remains a valid ensemble descriptor but has no single-region per-run physical referent.

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

A clarifying contrast with gauge theory: in gauge theory the physical state space is a constrained submanifold (gauge-invariant states) and one *also* restricts the admissible Hamiltonians to gauge-preserving ones. QIQT-H is **not** of this form. The restriction here is on which *regional contents* count as instantiable physical states (those with $I_\Sigma \le Q_R$); the global evolution law is left exactly unitary and unconstrained, and the formal global wave function, including formal multi-record vectors, evolves by ordinary standard QM. The Branch-Summed Bound constrains what can physically *reside* in a region, not which Hamiltonians may act.

**The Schrödinger law is exactly unitary and unmodified.** There is no restriction on Hamiltonians and no non-unitary or non-linear term anywhere. What the framework adds is a kinematic statement about regional physical instantiability: a regional content carrying $\ge 2$ macroscopically distinct records has no per-run physical referent. This is (FQ) part (iii) plus the formal/per-run distinction, not a dynamical modification.

**The price the framework pays.** The commitment is a new *kinematic postulate*, the Branch-Summed Holographic Bound on instantiable regional content, not a change to the dynamics. It is substantive at the foundational level, but only in regimes where the branch-summed cost approaches the holographic capacity. At lab scales, where macroscopic records use only $\sim 10^{25}$ bits of an available $\sim 10^{70}$-bit holographic capacity per cubic meter, the restriction is operationally vacuous and standard QM is recovered exactly. The restriction becomes operationally relevant only when branch-summed cost approaches $Q_R$, i.e., for macroscopic measurement records, where its content is to make $\ge 2$-record regional content non-instantiable, single-record per run at the kinematic level, with the dynamics still exactly unitary.

**Mathematical work needed:**

1. **Precise specification of $\mathcal{C}(R)$** as the einselected/Darwinistic record subalgebra (drawing on decoherent histories, Quantum Darwinism).
2. **Per-record cost $c_R(r)$** rigorously defined via Zurek physical entropy.
3. **Branch-summed bound $I_\Sigma^\epsilon \le Q_R$** as new physical principle, not derivable from existing holography, but conjecturally connectable to deeper quantum-gravity arguments about distinguishable record content per region.
4. **Characterization of instantiable regional content**: a precise statement of which regional algebra-states satisfy $I_\Sigma \le Q_R$, and the proof that $\ge 2$-record content violates it (the Macroscopic Definiteness Conjecture, Open Problem 3). This is a constraint on regional content, not on Hamiltonians; the dynamics is left exactly unitary.
5. **Born statistics from typicality**: the typicality theorem for which single-record content is realized per run, with the across-run realization frequency reproducing Born weights $|c_k|^2$ (probability emergent, not a per-run primitive).

Each of these is a concrete open mathematical problem; together they constitute the framework's explicit research program beyond the borrowed CPW/Witten scaffolding.

**Why this dissolves the MWI tension.** Under the Branch-Summed Superselection Postulate (Theorem 6), the framework escapes the MWI-without-many-worlds problem cleanly:

- The unconstrained Hilbert space contains states with multi-record macroscopic content; these are mathematically writeable but not in $\mathcal{H}_{\rm phys}$
- Physical states (those in $\mathcal{H}_{\rm phys}$) have $I_\Sigma \le Q_R$ for every bounded region; with $I_0 \approx Q_R$ at macroscopic scales, this means single-record per region
- The "Everett branches" are mathematical artifacts of considering unrestricted Hilbert-space states; the actual physical state space excludes them by the superselection rule
- We don't need to "select" one branch from many physically real branches, there are no multi-branch physical states to select from

The framework's single-world per run is therefore a *kinematic structural feature* of the physical state space, not a dynamical selection event. The superselection rule is what makes this true.

**Why this is genuinely new physics beyond Witten/CPW.** Witten/CPW provide the Type II algebraic infrastructure for regional generalized entropy. They do *not* establish:
- The branch-summed bound as a strengthening of standard holographic entropy
- The kinematic non-instantiability of $\ge 2$-record regional content (a restriction on which regional contents are physical, not on the dynamics)
- The exclusion of multi-record regional content as kinematically forbidden

These are the framework's specific new physical principles, building on the Witten/CPW scaffolding. They constitute a concrete research program: define the branch-summed cost rigorously; postulate the Branch-Summed Bound on instantiable regional content as new physics; prove that $\ge 2$-record content is excluded; derive Born statistics as an across-run typicality / relative-frequency result. The global evolution law remains exactly unitary throughout.

### 7.7 Theorem (No-signaling from modular-local admissibility)

**Non-selective-instrument convention.** All operations used in the no-signaling argument below are deterministic *non-selective* channels, i.e., instruments enter only through their sum $\mathcal{I} = \sum_a \mathcal{I}_a$. Selective conditional states $\omega_a$ are admissibility-checked branchwise (cf. §7.6 Definition (Physical instruments)), but **postselection on the outcome label $a$ is not an operation available for spacelike signaling**; it becomes operational only once the outcome record is classically available in the common future. Without this restriction, even ordinary Born probabilities can be made to "signal" by postselecting on rare outcomes; with it, no-signaling reduces cleanly to algebraic commutation.

**Theorem 7 (No-signaling).** *Let $D_A, D_B$ be spacelike-separated causally complete regions with $[\hat{\mathcal{A}}(D_A), \hat{\mathcal{A}}(D_B)] = 0$. Let $\{\Phi_a^x\}$ be a normal CP instrument localized in $\hat{\mathcal{A}}(D_A)$ with setting $x$ and outcomes $a$, and let $\{\Psi_b^y\}$ be similarly localized in $\hat{\mathcal{A}}(D_B)$. Under the modular-local finite-information admissibility restriction (§7.6) and the non-selective-instrument convention above, Alice's marginal probability is independent of Bob's setting:*
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

Invokes collapse without dynamics. We invoke no collapse. The single-record per-run regional content is a consequence of decoherence (removing interference) + the finite-information restriction on regional content (making a $\ge 2$-record content non-instantiable), not of dynamical reduction.

### 10.2 Many-Worlds

Posits all formal components as equally real branches. We are single-world per run: the per-run regional content is single-record because the non-dynamical selector $\lambda$ (P1) marks exactly one decohered record actual; the unrealized records have no physical referent (they are not "real elsewhere"), in contrast to Many-Worlds.

### 10.3 Bohmian mechanics

Bohm adds particle positions in $3N$-dim configuration space as a *second dynamical layer* beyond the wave function, with a guidance equation connecting the two, the configuration evolves under a law driven by $\Phi$. The framework adds *no second dynamical layer and no guidance law*: $\Phi$ is the sole dynamical ontology (weak ψ-monism; §2.2). The structural counterpart of the Bohmian configuration is the run-index $\lambda$, the run's actual microscopic initial conditions, which select the realized record, but $\lambda$ is *non-dynamical*: it carries no equation of motion and exerts no back-reaction on $\Phi$. So the difference from Bohm is sharp: same single-world realism and a run-indexing actuality fact, but no extra guided substance and no modification of the dynamics. The complete per-run state is the pair $(\Phi, \lambda)$; the formal wave function is the textbook ensemble descriptor.

### 10.4 Objective collapse (GRW, CSL, DP, OR)

Modify Schrödinger with collapse terms. We modify nothing dynamical. The Schrödinger evolution of the underlying field algebra is exactly unitary; the regional physical content is single-record because the non-dynamical selector $\lambda$ (P1) marks exactly one decohered record actual — a fact about actuality, not a modification of the dynamics.

### 10.5 QBism, relational quantum mechanics

Treat the wave function as epistemic / perspectival. We are objectively realist: the per-run wave function is real, the (FQ) constraint is real, the Type II algebra structure is real, the regional states are real physical states.

### 10.6 Modal interpretations, decoherent histories

Introduce a modal value-rule or history-selection structure. We require neither. The finite-information restriction on regional content makes a $\ge 2$-record content non-instantiable, yielding single records without external value-rules.

### 10.7 Ensemble interpretations (Ballentine)

The closest neighbor. Ballentine treats the formal wave function as ensemble-descriptive with per-run states underdetermined. We supply the mechanism: the Type II regional algebra structure makes per-run states physically single-record despite the formal wave function's superposed appearance.

### 10.8 Palmer's Rational Quantum Mechanics / Invariant Set Theory (nearest neighbour on motivation, opposite horn on Bell)

Palmer's Rational Quantum Mechanics (RaQM 2025, PNAS) and the broader Invariant Set Theory (IST) program is the closest neighbor in the space of *single-world, structural-principle, finite-information* frameworks. Both treat the wave function as not exhausting the per-run physical content, and both seek to ground the measurement problem's resolution in a deep structural feature of physics rather than in collapse, branching, or particle ontology. **On the Bell question, however, the two take opposite horns:** Palmer rejects Bell's measurement-independence assumption (a measurement-dependence / superdeterminism-family escape, principled rather than conspiratorial), whereas the present framework *keeps* measurement independence and rejects superdeterminism, paying instead at Parameter Independence at the ontic level (§6.9). The comparison below is therefore a contrast on the central Bell move, not an alliance.

**Shared structural commitments:**
- Single-world realism per run
- Recognition that the textbook formal wave function does not exhaust the per-run physical content
- Motivation by deep structural principles rather than ad hoc modification of QM

**The decisive difference (Bell horn):** Palmer denies measurement independence (a measurement-dependence / superdeterminism-family escape, with a non-conspiratorial rejection of metaphysical counterfactual recombination); the present framework *keeps* measurement independence and rejects superdeterminism, denying Parameter Independence at the ontic level instead (§6.9). This is the opposite Bell move, not a shared one.

(The frameworks differ in ontology: Palmer treats the wave function as derived/emergent from invariant-set statistics, with the underlying ontology being points on the fractal invariant set $I_U$; our framework is weak-ψ-monist, with $\Phi$ the sole dynamical ontology plus a non-dynamical run-index $\lambda$ selecting the realized record, the per-run state $(\Phi,\lambda)$ being finer-grained than the textbook formal ensemble descriptor. Interestingly Palmer's $I_U$-point and our $\lambda$ play structurally similar run-indexing roles.)

**Differences in mathematical apparatus and motivating principle:**

| | Palmer's RaQM / IST | Present framework |
|---|---|---|
| Mathematical apparatus | p-adic measures; Niven's theorem; fractal invariant set $I_U$ in cosmological state space | CPW Type II crossed-product algebra; finite-precision physical-instantiation postulate |
| Bell horn | Denies measurement independence (counterfactual settings off the invariant set not realizable; Impossible Triangle Corollary), superdeterminism-family | Keeps measurement independence; denies Parameter Independence at the ontic level; rejects superdeterminism (§6.9) |
| Status of wave function | Derived / emergent from invariant-set statistics; not fundamentally physically real | Physically real but finite-precision (ψ-ontic) |
| Status of Schrödinger evolution | Emergent from chaotic dynamics on invariant set | Preserved exactly at the underlying field-algebra level |
| Connection to quantum gravity | Indirect: chaos-based, cosmological motivation | Direct: Bekenstein-Hawking entropy, Witten/CPW Type II structure |
| Empirical predictions | Cosmological (CMB anomalies, fine-tuning, dark matter); explicit Bell-correlation models | Empirically conservative at lab scales; possible long-baseline signatures; cosmological extensions deferred |

**Relationship: same motivation, opposite Bell horn.** The two frameworks share single-world realism and a finite-information motivation, but they are *not* the same Bell escape: Palmer pays at measurement independence, the present framework pays at Parameter Independence (§6.9). They are therefore contrasting positions on the central Bell move, not interchangeable. (They are not in direct conflict as research programs, one could imagine a hybrid in which an invariant-set structure characterizes which per-run configurations are realized while a holographic bound constrains regional record capacity, but on the Bell question itself they diverge.)

**Where the frameworks complement each other's weaknesses:** Palmer's program is more developed (PNAS-published, decade of prior literature, explicit cosmological predictions, concrete Bell-model with Niven's theorem) but uses a more idiosyncratic mathematical machinery (p-adic measures, rational/irrational distinction). Our framework uses mainstream algebraic QFT + holographic bound (lower entry cost for the foundations community) but is at the proposal stage with the Concentration Conjecture and Born-typicality program as open work.

**For readers familiar with Palmer:** do *not* read the present framework as "Palmer with holography", that conflates the two on Bell. Palmer takes the measurement-dependence horn; the present framework takes the Parameter-Independence horn while keeping free settings (§6.9). The shared content is single-world realism plus a finite-information motivation; the Bell move is opposite.

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
| **(FQ) literal reading framework** | **No** | No second *dynamical* ontology (weak ψ-monist); one non-dynamical run-index $\lambda$, formal-ψ-incomplete | **No** | **Finite physical resolution + finite-information capacity on regional content** | **One single-record regional content $C_R = A_R[\Phi,\lambda]$: $\lambda$ selects the single actual record (capacity is kinematic, not exclusionary — §1.1a); dynamics exactly unitary** |

The (FQ) literal reading framework is uniquely characterized by a **finite physical resolution structure from the holographic bound**: the wave function as a physical state of spacetime has finite specification precision; amplitudes within precision of 0 or 1 are physically equivalent to exact 0 or 1; combined with decoherence and microscopic initial conditions, this yields a single-record per-run wave function structurally, without collapse, without modified dynamics, without hidden particles, without branches. The CPW Type II algebra framework provides the rigorous mathematical infrastructure; the literal physical-instantiation reading of the bound is the additional foundational postulate that does the work.

---

## 11. Conclusion

### 11.1 Summary

We have developed a foundational framework for quantum mechanics that combines two ingredients: (a) the algebraic-QFT-plus-gravitational-dressing framework of Chandrasekaran-Penington-Witten and Witten, providing the rigorous mathematical infrastructure for finite renormalized entropy on bounded regions; and (b) the *literal physical-instantiation reading* of the Bekenstein-Bousso bound (postulated as axiom (FQ)), that the wave function as a physical state of spacetime has finite physical specification precision determined by the holographic bound on the region.

The structure rests on:

1. **The CPW/Witten algebraic infrastructure (borrowed).** Local algebras in QFT with gravitational dressing are Type II with semifinite trace and well-defined renormalized entropy differences matching generalized entropy. This provides the rigorous algebraic home for the bound.

2. **The (FQ) axiom in its literal physical-instantiation reading (our postulate).** The wave function in any bounded region $R$ is a physical state of spacetime with finite physical information capacity $Q_R = A(\partial R)/(4\ell_P^2)$. Amplitudes have finite physical specification precision $\epsilon(R) > 0$; below the precision, distinct mathematical wave functions are the same physical state. The literal reading goes beyond Witten's algebraic theorem, Witten supplies the mathematical scaffold; the literal physical-instantiation reading is an additional foundational interpretation.

3. **Finite physical resolution (Theorem 3, consequence of (FQ) under the literal reading).** Amplitudes within $\epsilon(R)$ of $0$ are physically equivalent to exact $0$; amplitudes within $\epsilon(R)$ of $1$ are physically equivalent to exact $1$. This is the structural consequence that does the foundational work.

4. **The decoherence-plus-finite-information-restriction mechanism.** Under standard unitary dynamics, decoherence removes interference between macroscopic record components (their weights $|c_k|^2$ are conserved, not driven to $0$ or $1$); the (FQ) resolution floor removes the residual sub-$\epsilon$ coherence as a resolution-equivalence; and the finite-information restriction (a $\ge 2$-record regional content exceeds $Q_R$) makes the resident regional content single-record, with the run's microscopic initial conditions indexing which record (Theorem 4).

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
| Born-typicality theorem | A measure $\mu$ on the space of universal initial conditions, plus an equivariance-type theorem $\mu\{\lambda : k(\lambda, \Psi) = k\} = \vert c_k\vert ^2$ |
| FQ as operational equivalence (not literal thresholding) | A clean mathematical formulation: states differing on the regional algebra by less than $\epsilon$ (in some operational metric like trace distance) are physically equivalent |
| Connection to Bell correlations | An explicit $(\Phi,\lambda)$ model reproducing CHSH $=2\sqrt2$ via ontic Parameter-Independence violation, keeping free settings and yielding operational no-signaling without fine-tuning (§6.9) |

**Honest characterization of math status:** the framework provides the *scaffolding* (Type II algebras from CPW/Witten) and the *axiom* ((FQ) literal reading). It establishes *qualitative* consequences. It does not yet have *explicit theorems* for the central claims. This is the status of a research program, not a completed mathematical theory.

**Updated formal-verification status.** The characterization above remains correct *about the physics*: the central *physical* claims (the (FQ) literal reading, the explicit form of $\epsilon(R)$, and the continuum Macroscopic Definiteness and Born-typicality results) are not theorems and remain the research agenda. What has changed since earlier drafts is the *formal* status of the **deductive core**, which is now machine-checked and **axiom-free** (0 project-specific axioms, no `sorry`; CI budget 0, verified by `scripts/axiom_budget_check.sh`). Three layers must be held apart:

| Layer | Formal status |
|---|---|
| Conditional/structural deductive core (Theorems 3, 6, 7; Lemma 1; Donald's identity; the no-signaling chain; the finite no-collapse Born representation; the negative audits) | Machine-checked, **axiom-free** (standard Lean axioms only) |
| Physical postulates ((FQ); Macroscopic Definiteness Conjecture; Canonical IC / Born Principle; Lorentz covariance of $A_R[\Phi,\lambda]$) | **Open** — not theorems; axiom-free Lean does not bear on their truth |
| Continuum realization (Type II crossed-product entropy scaling; Fock / Weyl / CCR modular flow) | **Formalization frontier**, in active development (`QIQTH/Fock`, `Spectral`, `Entropy`) |

A subtlety the axiom *count* alone cannot see: a vacuous hypothesis (an interface axiom whose antecedent is trivially true) can trivialize a theorem without any axiom being declared. The project guards against this with a vacuity lint (`scripts/vacuity_lint.sh`) alongside the axiom-budget check; one historical instance (a `True`-antecedent locality axiom) was caught and converted to an explicit hypothesis, and the current lint reports a single benign site (an indiscrete-preorder definition).

The open problems are *concrete and well-defined*: each can be attacked in principle by an analyst willing to engage with both algebraic QFT and foundations of QM. We identify them not as defects of the framework but as the explicit research agenda the framework opens.

**Comparison with other foundations programs:** Bohmian mechanics has a complete mathematical theory (configuration space, guidance equation, $|\psi|^2$-equivariance) but adds a second ontology and faces relativistic incompatibility. Many-Worlds keeps standard QM but multiplies branches and lacks a derivation of Born from amplitudes. GRW modifies dynamics with specific parameters and faces empirical bounds on those parameters. QIQT-H, by comparison, has a partial mathematical theory (scaffolding + axiom + qualitative consequences) with explicit open theorems; in exchange, it preserves Schrödinger evolution exactly, adds no extra ontology, and is grounded in holography and quantum gravity. The mathematical work needed to complete it is well-defined, not vague.

### 11.3 The central thesis, in one paragraph

> The Bekenstein-Bousso holographic bound, taken literally as a Lorentz-invariant physical information limit on bounded regions of spacetime, bounds the number of mutually *distinguishable* macroscopic records a region can carry ($\# \le e^{Q_R}$). We are explicit that this is a **capacity (cardinality) bound, not a superposition-exclusion rule**: by linearity of the exactly-unitary dynamics it does *not*, on its own, forbid a macroscopic superposition of records, the redundant zero-entropy cat state $\alpha|0\rangle^{\otimes N}+\beta|1\rangle^{\otimes N}$ is the obstruction (§7.6). Whether finite capacity plus einselection can be strengthened into a genuine macroscopic *superselection* rule consistent with unitarity is the open Macroscopic Definiteness Conjecture (Open Problem 3); its strong "forbids superposition" form is currently *implausible*, and the framework's single-outcome content does **not** depend on its resolution. The Schrödinger / Heisenberg evolution law of the underlying field algebra is left **exactly unitary and entirely standard** (including ordinary measurement interactions); no amplitude is trimmed and no Hamiltonian is restricted. **The per-run ontology is the pair $(\Phi, \lambda)$:** an exactly-unitarily-evolving global wavefunction $\Phi(t)$, together with a fixed *non-dynamical, atemporal actuality selector* $\lambda$, a single global fact about which macroscopic realization the run is, fixed for the whole 4-dimensional history (not past-localized "initial data," to avoid any Conway–Kochen / setting-correlation reading; see §6.9). For each region $R$ the actual regional content is the derived beable $C_R(t) = A_R[\Phi(t), \lambda]$, the single $\lambda$-selected decoherent record sector of $\Phi(t)$; the unselected sectors remain in $\Phi(t)$ but are not regionally instantiated. The mechanism has a clean **division of labour**: decoherence removes interference and einselects stable, robust, effectively Boolean records (conserving the weights $|c_k|^2$; proved *not* to select an outcome, `NoConcentration.lean`), this gives robustness, not uniqueness; the capacity bound makes the set of distinguishable records *finite*, cardinality, not selection; and **$\lambda$ supplies which single record is actual**, this is where outcome-uniqueness genuinely comes from. No collapse dynamics, no Bohmian particle-position ontology or guidance law, no Everettian parallel *actual* branches (the unrealized records are not a parallel reality, they remain in $\Phi$ but are not regionally instantiated), and **no modification of the dynamics** are added; the only actuality rule is the fixed $\lambda / A_R$ reading rule, not a stochastic or modal dynamics. The framework is **ψ-monist in the weak (dynamical) sense**: $\Phi$ is the only thing that dynamically evolves and the only ontology subject to a law of motion, but the complete description of a run is the pair $(\Phi, \lambda)$, with $\lambda$ a non-dynamical actuality fact (a broad-sense beable, structurally analogous to the configuration in Bohmian mechanics or the actual history in modal interpretations, but with no guidance law and no back-reaction on $\Phi$). There are **no fundamental single-run probabilities**, no per-run stochastic or collapse chance is postulated; the Born weights $|c_k|^2$ are to be recovered, *if at all*, as an emergent relative frequency across the $\lambda$-indexed ensemble of runs, conditional on a typicality measure $\mu$ over actuality selectors that is **currently unconstructed / interface-level** (the Born-typicality program, §7.4, §11.4, the framework's central open problem, together with the requirement that the same $\mu$ enforce operational no-signaling without fine-tuning, §6.9). The CPW Type II crossed-product algebra framework provides the rigorous mathematical infrastructure; the holographic capacity bound is the framework's new physical input on top. The single-record-per-region claim is therefore an *architecture* in which decoherence + holography furnish a finite stage of robust classical records and $\lambda$ makes one actual, **a decomposition of the measurement problem into a robustness part, a finiteness part, and two clearly-stated primitives ($\lambda$ actuality, $\mu$ typicality), not a completed derivation of single outcomes from the bound alone.**

### 11.4 Open problems

> **Audit status (current).** The discharge narrative in this section is historical. As of the latest audit the project is **axiom-free**: 0 project-specific axioms, no `sorry`, CI budget 0 (`scripts/axiom_budget_check.sh`), 830 `#print axioms` directives over 192 modules and roughly 2,010 theorems, full build green. Every interface axiom mentioned below as "remaining" has since been discharged in its finite-dimensional realization — the Goldstein-Struyve Schur classification (`schur_classification_real`) and tensor multiplicativity, Klein's inequality, Donald's identity, the data-processing inequality, the Araki/`EntropyBridge` relative-entropy layer, the Tsirelson-attainability bound, and the Fano / `RelEntPositivity` finite steps — and the `TypicalityMackeyGleason` packaging was retired in favour of the axiom-free `EffectGleason`. The figures "57 → 40 → 37 → 35" below trace that effort; it has since reached **0**. What remains genuinely open is the *continuum* (von Neumann-algebraic) version of these results and the *physical* postulates (Open Problems 1–3b); neither is touched by the finite-dimensional formal discharge.

The Lean audit work (see `lean/mathlib/QIQTH/` and the formal-verification footnote in the abstract) has sharpened the boundary between what the framework derives from FQ + AQFT + holography and what remains as load-bearing additional commitments. The open problems are reorganized here to reflect that sharpened boundary, with the Born / canonical-measure problem promoted to first position as the most central remaining commitment.

**Open Problem 1, Canonical IC Measure Principle (the central Born/typicality problem).**

This problem decomposes naturally into six layers, each requiring different kinds of work. The decomposition is based on a closing audit (`lean/mathlib/QIQTH/AxiomAudit.lean` + GPT-5.5-pro consultation) that distinguishes what is mathematically derivable from what is genuinely open physics from what is irreducible empirical calibration.

**Goal.** Specify, for each preparation state $\rho$, a measure $\mu_\rho$ on the QIQT-H microscopic-IC space $\Omega_\rho$ (alternatively: a typicality structure on the FQ-restricted physical Hilbert space) satisfying:
   (a) **Canonicality**, defined from QIQT-H primitives, not fitted per measurement;
   (b) **Born pushforward**, $(O_M)_* \mu_\rho(i) = \mathrm{tr}(\rho E_i)$ for every allowed measurement protocol $M$ with effects $\{E_i\}$;
   (c) **Equivariance / stationarity**, preserved by the (FQ)-restricted physical Hamiltonian;
   (d) **Repeated-trial typicality**, supports iid / exchangeable / stationary-ergodic frequency theorems;
   (e) **Measurement-setting independence**, $\mu_\rho$ does not depend on the measurement context (unless the theory explicitly accepts contextual / measurement-dependent typicality);
   (f) **Uniqueness / stability**, robust under coarse-graining and equivalent IC descriptions.

Machine-verified audits flag the difficulty: `NoBornFromNothing.lean` (any distribution realizable; the structural axioms do not pick out Born), `EquivarianceGap.lean` (support preservation $\neq$ Born equivariance), `OperationalNoGo.lean` (operational frequency data alone insufficient). The independence package `BornMinimalityTable.lean` re-exports these three countermodels and shows that the locality premise is *not* an independent Born-selection sub-axiom, its marginal-level content is a theorem holding for any measure (`MarginalLocality.pushforward_marginal_local`), modulo a named Hilbert→set-level bridge axiom (§11.4.5). Relative to the current finite formal decomposition, the Canonical IC Measure Principle's irreducible Born-selection content is three named sub-axioms (canonical measure, equivariance, operational sufficiency), each provably necessary by concrete finite countermodel, alongside the two acknowledged operator-algebra interface axioms (Schur classification, tensor multiplicativity) that the Born representation itself rests on.

***The recommended route: a Gleason spine (GPT-5.5-pro μ-options consultation).*** Of the six candidate constructions for $\mu$, (i) POVM-Gleason / Mackey-Gleason representation, (ii) decoherent-histories quantum measure + a typicality postulate, (iii) envariance / self-locating symmetry (Zurek; Sebens–Carroll), (iv) Bohmian quantum-equilibrium equivariance (Dürr–Goldstein–Zanghì), (v) frequency-operator (Hartle; Farhi–Goldstone–Gutmann), (vi) Deutsch–Wallace decision theory, only **(i)** plausibly yields an *objective, Lorentz-equivariant* $\mu$ meeting all of (a)–(f), with operational no-signaling following structurally from *one* canonical $\mu$ rather than per-experiment tuning. The recommended architecture is therefore: **Gleason as the spine** (the representation theorem that *forces* the weights), the **decoherence functional as the cylinder construction** ($\mu_\Phi(\mathrm{Cyl}\,\alpha) = D_\Phi(\alpha,\alpha) = \langle\Phi|C_\alpha^\dagger C_\alpha|\Phi\rangle$, extended by Kolmogorov–Carathéodory), and a **frequency theorem as the LLN corollary**; envariance enters only as optional symmetry motivation.

The decisive conceptual point: the Born content is *not* contained in any single record/Boolean algebra, a single measurement context admits **any** probability vector on its outcomes (this is exactly the `NoBornFromNothing` countermodel). What forces Born is **non-contextuality across overlapping effect contexts** together with state-certainty, the Gleason hypotheses. Concretely, the target is a *record-effect Gleason theorem*: a normalized, additive, non-contextual effect-weight $w$ that is certain on the state's ray ($w(P_\Phi)=1$) must equal the Born functional $w(E)=\langle\Phi|E|\Phi\rangle$; hence on any complete record family $\{C_k\}$ ($\sum_k C_k^\dagger C_k = I$) the selector measure is *forced* to $\mu(k) = \langle\Phi|C_k^\dagger C_k|\Phi\rangle$. This is **uniqueness/canonicity of $\mu$ from structural hypotheses**, not "probability from nothing".

*Lean status (`GleasonSelector.lean`), Born forced from positivity.* The architecture is formalized in the finite-dimensional record model. A first version named the Busch / POVM-Gleason step as an interface axiom; a soundness review (GPT-5.5-pro) showed that axiom was **false as stated**, it omitted *positivity*, and the explicit weight $w(E) = E_{00} + E_{01}$ on $\mathbb{C}^2$ satisfies normalization, additivity, homogeneity, and ray-certainty yet is not the Born functional. The axiom was **retired** and replaced by *proved* content (every theorem standard-axioms-only, verified by `AxiomAudit.lean`, except where the two standard linear-algebra interface axioms below are explicitly invoked):
- `naive_gleason_premises_insufficient`: the $\mathbb{C}^2$ counterexample, proved: the positivity-free premises do *not* force Born (a soundness red-team result that documents why positivity is indispensable);
- `rankOne_sandwich`: proved (no normalization needed): $|\psi\rangle\langle\psi|\, E\, |\psi\rangle\langle\psi| = \langle\psi|E|\psi\rangle \cdot |\psi\rangle\langle\psi|$ (the algebraic heart of "ray-certainty $\Rightarrow$ Born");
- `support_of_positive_certain`: proved: a **positive**, additive, homogeneous, ray-certain functional is **ray-supported** ($w(E) = w(P_\psi E P_\psi)$), via the Cauchy–Schwarz null-radical argument ($Q = I - P_\psi$ has $w(Q) = 0$, so all off-ray terms vanish). This *derives* the support property from positivity, the genuine Gleason/Busch bridge, rather than assuming it;
- `positive_ray_certain_forces_born`: **the capstone, proved**: a positive, normalized, ray-certain weight $w$ **is** the Born functional. Born now follows from *positivity + normalization + ray-certainty*, with positivity (not a conclusion-equivalent support premise) as the substantive hypothesis;
- `history_measure_is_born` / `history_measure_total`: the record measure is the Born / decoherence-functional measure, normalized;
- `no_signaling_marginal`: requirement (e)/no-signaling, honest form: one bilinear correlation gives spacelike-marginal independence for *all* of Bob's settings.

The capstone originally rested on two *standard* linear-algebra interface axioms; **both have since been discharged**, so the entire finite-dimensional Gleason module is now **axiom-free** (every theorem, including the capstone, depends only on Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`, verified by `AxiomAudit.lean`). Specifically: `positive_functional_hermitian` (a positive functional is a $*$-functional) is proved by the standard polarization argument (realness of $w((A+X)^\dagger(A+X))$ and $w((A+iX)^\dagger(A+iX))$ forces conjugate symmetry); and `psd_null_radical` (a null vector of a positive-semidefinite sesquilinear form lies in its radical, the Cauchy–Schwarz core) is proved by deriving first-slot conjugate-linearity from conjugate symmetry, then applying the real-quadratic discriminant lemma `quadratic_nonneg_forall_linear_zero` (also proved) at $c = t$ and $c = it$ to force $\mathrm{Re}\,(B\,Q\,X) = \mathrm{Im}\,(B\,Q\,X) = 0$. The honest residual is now only the *continuum* Type II / history-net version (the finite-dimensional case is complete and unconditional).

*Honest verdict, and the position adopted.* We do **not** claim to derive $\mu$ from unitarity plus the bare existence of $\lambda$; on structural grounds **one** bridge principle is required (here: *positivity* of the selector functional + state-certainty), the same status that quantum equilibrium has in Bohmian mechanics, and the analogue of the Everettian probability problem. (We do not assert a formal no-go that such a derivation is *impossible*, only that this framework, like every single-world programme, supplies one bridge principle rather than deriving probability from nothing.) The adopted position is: *QIQT-H posits a selector functional constrained by positivity, finite-record non-contextuality, covariance, and state-certainty; a Gleason-type theorem (`positive_ray_certain_forces_born`, proved) then shows the only canonical $\mu$ is the decoherence-functional measure $\mu_\Phi(\mathrm{Cyl}\,\alpha) = D_\Phi(\alpha,\alpha)$; the one remaining postulate is that the actual $\lambda$ is $\mu$-typical*, the relativistic analogue of quantum equilibrium. Strict Wood–Spekkens "no fine-tuning" in the causal-faithfulness sense is unachievable for any ontic-Parameter-Independence-violating model (a known no-go); what *is* achieved is the defensible weaker form, one canonical $\mu$ enforces operational no-signaling for every spacelike instrument pair, with no per-experiment tuning (`no_signaling_marginal`).

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

**Lean status:** the finite-dimensional content is now the axiom-free `EffectGleason.finite_effect_gleason` (Born forced from positivity); the earlier `TypicalityMackeyGleason` packaging was retired and deleted. The full von Neumann-algebraic Mackey-Gleason + noncommutative Radon-Nikodym version remains a Mathlib-formalization task (multi-week).

#### 11.4.2 Existence and canonicality in finite factors (Type $II_1$)

**Standard mathematical existence (NOT open).** For a finite Type II factor $M$ with faithful normal tracial state $\tau$, the construction
$$\mu_\rho(p) = \tau(\rho \cdot p), \quad \rho \in L^1(M, \tau)_+, \quad \tau(\rho) = 1$$
yields a normal probability measure on the projection lattice $\mathrm{Proj}(M)$. Positivity, normalization, orthogonal additivity, normality, and unitary covariance are all standard theorems. **In a $II_1$ factor, the trace $\tau$ is the unique normal state invariant under all inner unitaries**, so canonicality under unitary invariance is *not* an open problem; it is a consequence of factor structure.

**What remains open in $II_1$:** none of the *mathematical* existence; only the (genuinely open) question of canonical *physical selection*, what makes a particular $\rho$ correspond to a particular preparation. That is the empirical calibration step (§11.4.4 below).

**Lean status:** This is a Lean formalization gap, *not* an open math problem. The construction can be formalised directly given the requisite vN-algebra infrastructure in Mathlib.

#### 11.4.3 Infinite trace and Type $II_\infty$, a sharp obstruction

**The obstruction.** For a Type $II_\infty$ factor with semifinite trace $\tau$, the trace satisfies $\tau(1) = \infty$. Therefore the trace itself is a *weight*, not a probability state. There is **no normalized normal state on a $II_\infty$ factor invariant under all unitaries**.

Concretely: one cannot define a "canonical uniform" probability measure $\mu(p) = \tau(p)$ in $II_\infty$; the candidate is not normalizable.

**Options for the QIQT-H Type II setting:**
1. Choose a density $\rho$: $\mu_\rho(p) = \tau(\rho \cdot p)$ with $\rho \in L^1(M, \tau)_+$ and $\tau(\rho) = 1$. The measure exists; canonicality requires an additional principle to select $\rho$ for a given physical preparation.
2. Restrict to a finite corner $eMe$ with $\tau(e) < \infty$: recovers the $II_1$ analysis above on the corner.
3. Use semifinite *typicality weight* rather than probability measure: appropriate if the framework adopts a non-probability typicality reading.
4. Provide additional physical selection principles (canonical sector reference state, modular structure, holographic origin).

**Lean status:** Sub-theorem A's interface (Mackey-Gleason + RN) applies to $II_\infty$; the obstruction is *physical canonicality*, not formal existence of $\mu_\rho$.

#### 11.4.3a Type III caveat (AQFT local algebras)

**A non-trivial caveat.** AQFT local algebras of bounded regions are typically Type $III_1$, not Type II (Buchholz, Borchers, Longo; see foundations paper §3). The QIQT-H framework uses the CPW Type II crossed-product construction (CPW 2022, Witten 2022) precisely to *escape* Type III to a well-defined entropy structure. But:

- **There is no trace-density picture in Type III.** Normal states still give projection probabilities $\phi(p)$, but the formula $\phi(p) = \tau(\rho \cdot p)$ has no analog in Type III (no trace).
- The relationship between the underlying Type III local algebras and the crossed-product Type II algebras is mediated by the modular flow of the canonical sector reference state $\sigma_R$.
- The Born representation problem in Type III is structurally different and requires either passing through the Type II crossed product or using Connes' spatial derivative / Haagerup's $L^p$-space construction.

**Open:** make explicit how the Type II crossed-product trace-density picture relates to the underlying Type III local-algebra structure, particularly whether the canonical IC measure $\mu_\rho$ on the Type II core has a natural Type III pullback.

#### 11.4.4 Operational calibration, split into derivable and irreducible parts

**Splitting the calibration step.** The "measurement-calibration" step (often informally called "the Born content bridge") is actually two parts:

- **(4a) Mathematical restriction (derivable).** If $A \cong M_d(\mathbb{C})$ is a finite-dimensional measurement subalgebra of a Type II factor and $\phi$ is a normal state, then $\phi|_A(a) = \mathrm{tr}_d(\rho_A \cdot a)$ for a unique ordinary $d \times d$ density matrix $\rho_A$. If the embedding is trace-preserving, the Type II trace restricts to the normalized matrix trace on $A$. *This is standard mathematics.*

- **(4b) Empirical calibration (irreducible).** The identifications:
  - this detector $\leftrightarrow$ this projection / effect;
  - this preparation $\leftrightarrow$ this density;
  - this pointer event $\leftrightarrow$ this subalgebra;
  - this finite-dimensional operational model $\leftrightarrow$ the right model of the actual lab.
  
  Operational reconstructions (Hardy 2001; Chiribella-D'Ariano-Perinotti 2011; Masanes-Müller 2011; Brukner-Zeilinger) derive the Born pairing from operational axioms, but the axioms themselves are physical/empirical inputs. *Calibration is not eliminated; it is relocated.*

**The irreducible part is small but real.** Any deterministic theory needs (4b). It is the analog of the bridge from Liouville measure to thermodynamic ensembles in classical statistical mechanics.

**POVMs and instruments.** Modern operational treatments use POVMs (effects) rather than PVMs (projections). For sequential measurements and state update, Davies-Lewis / Ozawa instruments are the appropriate framework. The QIQT-H paper should include POVM formulations in §7.6 and §7.7 to avoid the bare-qubit Gleason exception.

#### 11.4.5 Dynamics, equivariance, and locality

The conditional Born typicality theorem (`BornTypicality.lean`) requires three additional physical inputs:

- **Equivariance theorem.** If $\rho_t = U_t \rho_0 U_t^*$ under FQ-restricted unitary dynamics, then $\mu_{\rho_t}(p) = \mu_{\rho_0}(U_t^* p U_t)$. For QFT-style Hamiltonians, this requires careful treatment of domain / self-adjointness issues. The `EquivarianceGap.lean` audit establishes that support preservation (the framework's current claim) is strictly weaker than measure preservation.

- **Projection locality.** Need precise assumptions on the local algebraic structure: tensor product factorisation (or its absence in Type III), commuting local algebras (microcausality), split property, finite corners. The `CompressionLocality.lean` audit isolates the compression-locality leakage identity and identifies when the FQ projection preserves microcausality at the restricted level. *Post A1 strengthening* (`MarginalLocality.pushforward_marginal_local`): given set-level locality of Bob's dynamics ($r\circ T = r$), the Alice-marginal is invariant for **any** IC measure: with no equivariance assumption, so locality of the marginal is a theorem, not a separate Born-selection postulate. This reduction is, however, *conditional* on a named Hilbert→set-level locality bridge axiom (`set_level_locality_from_unitary_dilation`, a standard Heisenberg↔Schrödinger correspondence): locality has been relocated into that explicit bridge, not eliminated. Subject to that caveat, locality is no longer counted among the independent Born-selection sub-axioms of the Canonical IC Measure Principle.

- **Empirical frequency bridge.** If μ is interpreted as typicality (rather than primitive probability), one needs a DGZ-style step from typical initial configurations to observed frequencies. The `BornTypicality.lean` module formalizes this conditionally via standard finite LLN.

#### 11.4.6 Typicality vs probability

**The conceptual framing.** QIQT-H is fully deterministic; the "measure" $\mu_\rho$ is a *typicality structure* on the microscopic-IC space (à la Dürr-Goldstein-Zanghì 1992 in Bohmian mechanics), not a primitive probability assignment. The candidate routes for canonicality (§7.4 α/β/γ) are typicality principles, not probability axioms.

**Caveats and references:**
- **Frequency concentration (PROVED, single-trial + independence step).** The Lean module `BornConcentration.lean` proves Chebyshev's tail bound on finite probability spaces ($\Pr(|X-\mu| \ge \varepsilon) \le \mathrm{Var}/\varepsilon^2$), computes the Bernoulli variance ($p(1-p)$), proves the variance-addition (independence) lemma `variance_add_of_product` (variance of a sum of independent variables equals the sum of variances), and combines these to give the single-trial concentration inequality and the two-trial Bernoulli variance $2p(1-p)$. *What is proved:* the single-trial Chebyshev bound and the reusable variance-addition lemma the $N$-fold induction would iterate. *What remains axiomatic:* the full $N$-trial product-measure scaling $\Pr(|\mathrm{freq}_N - p| \ge \varepsilon) \le p(1-p)/(N\varepsilon^2)$ rests on the LLN interface axiom in `BornTypicality.lean`. Accordingly the framework's frequency statement ("Born *frequencies*", not merely "Born *means*") is established up to that single named scaling axiom: for which the per-trial variance and the independence step are now both in hand.
- **Goldstein-Struyve uniqueness** (J. Stat. Phys. 128, 1197, 2007): in Bohmian mechanics, $|\psi|^2$ is the unique local equivariant typicality density. The adaptation to QIQT-H's Type II + (FQ) setting is precisely the multi-week mathematical task of Sub-theorem C.
- **Valentini nonequilibrium** (1991, 2002; Valentini-Westman 2005): there exist non-Born typicality measures whose dynamics relaxes (or fails to relax) to equilibrium. This is the principled objection to "canonical = equivariant": equivariance is necessary but may not be sufficient without an additional relaxation argument.
- **Noncontextuality** in this deterministic-with-typicality setting refers to the equilibrium probability assignment to quantum effects (Spekkens 2005 generalised noncontextuality), *not* to noncontextual pre-existing values (which Kochen-Specker rules out in $d \ge 3$).

#### 11.4.7 Independence / minimality of the remaining sub-axioms

Per GPT-5.5-pro's sixth audit, the honest Born claim is not "Born is derived from holography alone", `NoBornFromNothing` refutes that, but rather:

> *Born is the unique admissible measure given a NAMED minimal set of additional postulates, and each postulate is INDEPENDENT, dropping any one yields a finite countermodel where Born fails.*

The independence package `BornMinimalityTable.lean` makes this explicit. Relative to the current finite formal decomposition, the Canonical IC Measure Principle has three irreducible Born-selection sub-axioms, each with a concrete finite countermodel witnessing its necessity (with the locality premise reducible, modulo the named bridge axiom of §11.4.5):

| Tag | Premise | Minimality witness (Lean module) | Countermodel size |
|---|---|---|---|
| P1 | Canonical IC measure (some structurally-distinguished $\mu$ is selected) | `NoBornFromNothing.any_anti_born_realizable` | $\Gamma$ arbitrary finite |
| P2 | Measure equivariance under FQ-restricted dynamics | `EquivarianceGap.support_preservation_does_not_imply_…` | $\mathrm{Fin}\,2$ swap |
| P3 | Operational sufficiency (click-statistics determine IC marginal) | `OperationalNoGo.operational_data_insufficient` | $\mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ |
| P4 | Locality of Alice's marginal under Bob's local dynamics | **REDUCIBLE**, proved as a theorem holding for *any* measure (`MarginalLocality.pushforward_marginal_local`), conditional on the named Hilbert→set-level bridge axiom (§11.4.5) | (not an independent Born-selection axiom) |

This converts the standing concern "you still assume X" into a sharper audit conclusion: X is *necessary*. Relative to the current finite formal decomposition, the irreducible Born-selection premise set is $\{P1, P2, P3\}$ (down from four, once the marginal-locality step is theoremized modulo its bridge axiom); each premise has a finite-dimensional countermodel; and Born follows uniquely when all three hold, together with the operator-algebraic Mackey-Gleason / Radon-Nikodym input (the finite Schur classification and tensor multiplicativity, once acknowledged interface axioms, are now proved axiom-free). This is the strongest honest statement available without resolving the *continuum* Sub-theorems A and C as theorems-in-Mathlib; it is a *minimality relative to this decomposition*, not a proof that no coarser axiom set could suffice.

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

**Bottom line.** The Canonical IC Measure Principle is **not** a monolithic mystery. The hard parts are: the $II_\infty$ canonicality obstruction (11.4.3); the Type III correspondence (11.4.3a); the equivariance theorem for FQ-restricted dynamics (11.4.5); and the typicality justification (11.4.6). The mathematical core (11.4.1, 11.4.2, 11.4.4a) is standard given operator-algebra infrastructure; the empirical calibration (11.4.4b) is irreducible. **After the A1+A2+A4+A6 strengthening pass:** the marginal-locality step is theoremized (for *any* measure, no equivariance assumed) so locality is no longer an independent Born-selection sub-axiom, modulo a named Hilbert→set-level bridge axiom into which the locality content is relocated, not eliminated; relative to the current decomposition the irreducible Born-selection set has three named members (P1/P2/P3), each provably necessary by concrete finite countermodel; and single-trial Born frequency concentration plus the variance-addition (independence) lemma are proved, with the $N$-trial scaling to full frequency convergence still resting on the named product-measure LLN axiom. These are minimality and reduction results *relative to this formal decomposition*, not claims that the underlying operator-algebra interface axioms (Schur classification, tensor multiplicativity, Mackey-Gleason/Radon-Nikodym) have been discharged.

**Open Problem 2, Reference-weight bound (sharpened H2).**
The record-instantiation-cost postulate (H2 in Theorem 6) is *equivalent* to the reference-weight bound $\sigma_R(E_{\rm record}) \le \exp(-(I_0 - \eta_0))$ on macroscopic pointer sectors (see §7.6 Sharpening of (H2); formalized in `lean/mathlib/QIQTH/H1H2Audit.lean`). Derive this reference-weight bound from modular / holographic first principles, as a strengthening of standard Bekenstein-Bousso. Donald's identity + Klein positivity + DPI alone are insufficient. This is genuinely new physics; progress here feeds directly into Open Problem 3.

**Open Problem 3 — WITHDRAWN (2026): the Macroscopic Definiteness Conjecture is retired as a category error.**
This problem formerly asked to *prove the Branch-Summed bound* — that a regional content carrying $K \ge 2$ macroscopically distinct records has summed information cost $I_\Sigma \approx K\cdot I_0 > Q_R$ and is therefore not an instantiable physical state, so that finite capacity itself *forbids* the multi-record state. **We withdraw it** (§1.1a). $Q_R$ bounds the *von Neumann* entropy $S(\rho_R) = H(\{p_i\}) + \sum_i p_i S(\rho_{R,i})$ of the pre-selection state $\Phi$, and a second macroscopic branch raises only the branch-count term — by $\sim\!\log K$, far below $Q_R$ — so a $\ge 2$-record state does **not** overflow capacity; the branch-summed cost $I_\Sigma$ is provably not the entropy $Q_R$ bounds (`BranchLedger.branchSummed_not_bounded_by_Shannon`); and in a unitarily-evolving theory a kinematic bound cannot in any case *select* an outcome (`NoConcentration`, `RealmSelection.capacity_underdetermines_realm` — "the area budget is not the metaselector"). **Single-record definiteness is the work of the selector $\lambda$ (P1) together with decoherence, not of a capacity exclusion.** What remains genuinely open is *not* this conjecture but the **dynamical, Lorentz-covariant realization** of $\lambda$-selection (Open Problem 3b below) and $\lambda$'s law (Born from typicality); the subsidiary quantitative questions — recoherence stability, $\epsilon(R)$, $I_0$, and no-signaling consistency (Open Problem 10) — are retained under their own headings.

*Status (2026-06), the finite additive-cost number-bound is mechanized — but it does **not** revive the withdrawn capacity-exclusion.* In a tractable finite-dimensional **additive-cost** model the number-bound is an axiom-free theorem; however the additive (branch-summed) cost it bounds is provably *not* the holographic von Neumann entropy $Q_R$ bounds (`branchSummed_not_bounded_by_Shannon`), so it models the storage of the $\lambda$-selected record, not a capacity exclusion of multi-record states. Concretely: realizing records as a redundant Spectrum Broadcast Structure makes the summed cost a genuine *information* quantity $\ge R\log n$ (broadcasting tensors the fragments, so dimensions multiply), and a finite additive capacity then admits at most one macroscopic record, an axiom-free Lean theorem (`SBSBridge.sbs_single_outcome`, `CoreNoCollapse.coactual_subsingleton`), with the threshold *derived* from pointer-state orthonormality (`CapacityModel.capacity_total`) and robust to approximate decoherence (`fragment_finrank_ge_approx`). This is the *number-bound* (one-record) content; what remains genuinely open is (i) the continuum realization, reproducing this scaling as a renormalized-entropy bound on the Type II regional algebra rather than a finite register, and (ii) the *field-theoretic* origin of the scattering premise. Input (ii) has been **discharged for the standard collisional/QND toy Hamiltonian** $H_{\rm int}=g\,\sigma_z^S\otimes\sigma_x^E$ (`CollisionalGamma.lean`): the branch overlap is $\cos 2\theta$, so $\gamma=|\cos 2\theta|<1$ is derived and amplifies to $\gamma^L\to0$ (§6.8); what stays open is deriving the *uniform-$\gamma$, factorized, no-recoherence* structure itself from a realistic field-theoretic Hamiltonian (the constructive form of the Strasberg–Winter branch-selection problem, arXiv:2601.19703). The strong superposition-exclusion form (forbidding the cat state) is *not* claimed and is not needed for the single-record content.

**Open Problem 3b, Lorentz covariance of the selection structure (of equal rank to the Born/typicality problem).**
Establish that the actuality selector $\lambda$ and the regional reading map $A_R[\Phi,\lambda]$ introduce **no hidden preferred foliation**, i.e. that the single-world structure is genuinely Lorentz-covariant, not merely operationally no-signaling. This is the relativistic counterpart of the Born/typicality problem (Open Problem 1) and is its equal in rank; it is *not* secured by the operational no-signaling theorem (§7.7), since no-signaling $\neq$ Lorentz invariance of the beable (§6.9, §11). The framework is structurally *better placed* than Bohmian mechanics here, because $\Phi$ evolves by exactly-unitary, already-covariant dynamics and $\lambda$ is *non-dynamical* (there is no collapse or guidance event that must be time-ordered, hence nothing that requires a "now"), but "better placed" is not "proved." Five explicit requirements, in increasing difficulty:

1. **$\lambda$ as a genuinely 4-dimensional object.** $\lambda$ must be defined geometrically over the whole spacetime history: e.g. a choice of one globally consistent decoherent history of $\Phi$, or a section of an appropriate bundle over spacetime, with the Poincaré group acting on it *geometrically* and with no reference to a Cauchy slice. Any definition that reduces $\lambda$ to "initial data on $\Sigma_0$" reintroduces a preferred frame and fails. (This is the substance of the relabel from "microscopic initial conditions" to "atemporal actuality selector," §2.2, §6.9, here it is made a covariance *requirement*, not just terminology.)

2. **Covariant region structure.** $Q_R = A(\partial R)/4\ell_P^2$ and the resolution floor $\epsilon(R)$ must be defined on **causal diamonds** via the **covariant (Bousso light-sheet) entropy bound**, *not* on spatial slices: the area of $\partial R$ on a spacelike slice is frame-dependent. The CPW/Witten Type II scaffolding already lives on causal diamonds with microcausality built in (and machine-checked), so the scaffolding is covariant; the burden is to make $Q_R$, $\epsilon(R)$, and the reading map respect it. *This requirement is concrete and fixable now* and should be discharged first.

3. **The covariance identity (the core theorem).** Prove
$$A_{gR}[\,U_g\Phi,\; g\!\cdot\!\lambda\,] \;=\; g\cdot A_R[\Phi,\lambda] \qquad \text{for every Poincaré } g,$$
i.e. selecting the record in the boosted diamond $gR$ from the boosted state $U_g\Phi$ and boosted selector $g\lambda$ yields the boost of the originally-selected record. This is the precise statement that "every observer in every frame agrees on the physical facts." Open.

4. **Foliation-free global consistency.** Show that the family $\{C_R = A_R[\Phi,\lambda]\}$ over all diamonds is globally consistent: restriction-compatible on nested diamonds (extending the $\sigma_R$ restriction-compatibility of §7.6 to the $\lambda$-selected content), and jointly consistent on spacelike-separated diamonds, *with the consistency condition statable purely in the causal partial order*, requiring no global time function. The danger is that a "global history" selection covertly needs a foliation to define "consistent across time"; operational no-signaling (§7.7) is the observable shadow of this consistency, but the ontic statement must be proved. Open.

5. **Poincaré-*equivariant* typicality.** The measure $\mu$ over $\lambda$ (Open Problem 1) must transform *covariantly with the state*, $g_*\mu_\Phi = \mu_{U_g\Phi}$: **not** strict invariance $\mu(g\cdot S)=\mu(S)$, which is too strong since the Born weights depend on $\Phi$ (strict invariance is the special case where $\Phi$ is itself Poincaré-invariant, e.g. the vacuum). This couples the relativistic problem to the Born problem: an equivariant $\mu_\Phi$ is strictly harder than a single-frame $\mu$, and a non-equivariant family would re-import a preferred frame through the statistics even if $\lambda$ itself is clean. This is the relativistic analogue of the difficulty Bohmian mechanics has with frame-dependence of $|\psi|^2$-equilibrium. Open, and entangled with Open Problem 1.

We note candidly that requirements 3–5 are genuine open theorems, requirement 5 the hardest; that the program's Lorentz-friendliness is *bought with* an atemporal / all-at-once (block-universe, mildly retrocausal-flavored) reading of $\lambda$, which is owned openly rather than hidden; and that this places QIQT-H in the Lorentz-friendly family of single-world proposals (Kent final-boundary; Wharton/Sutherland all-at-once) rather than the foliation-bound Bohm/GRW family, a structural advantage that is, as yet, a promissory note.

***Proposed construction (a concrete attack, not yet a theorem).*** Two design choices make the five requirements simultaneously well-posed and, we argue, jointly natural; they are recorded here as the intended line of attack.

*(i) Relativistic dynamics: $\Phi$ is a quantum field, not a Schrödinger wavefunction.* Throughout this paper "Schrödinger / Heisenberg evolution" is shorthand for the manifestly covariant dynamics of the underlying field theory; for matter the relevant equation is the **Dirac equation** $(i\gamma^\mu\partial_\mu - m)\psi = 0$ (second-quantized: the Dirac quantum field), not its non-relativistic limit. This is not cosmetic but *required*: requirement 3's covariance identity $A_{gR}[U_g\Phi, g\!\cdot\!\lambda] = g\cdot A_R[\Phi,\lambda]$ is only statable once $\Phi$ carries a genuine Poincaré action $U_g$, which the Dirac field provides through the spinor representation $S(\Lambda)$, and a Galilean Schrödinger equation does not. The Dirac field is also the natural matter content of the CPW/Witten AQFT scaffolding (the local algebras are field algebras), so this choice merely names the QFT the algebras already presuppose. (The single-particle Dirac equation's negative-energy / Klein pathologies are why the *field*, not the one-particle wave equation, is the carrier; $\Phi$ is the global QFT state.)

*(ii) $\lambda$ as holographic boundary data on causal-diamond screens.* We propose that $\lambda$ be **encoded on boundaries, not in the bulk**: for each causal diamond $D$, the $\lambda$-selected record sector $C_D = A_D[\Phi,\lambda]$ is reconstructed from $\lambda$'s restriction to the diamond's edge / holographic screen $\partial D$. The motivation is internal and, we think, forcing: the *capacity* that constrains records is itself a boundary quantity, $Q_R = A(\partial R)/4\ell_P^2$, so the actuality fact that *spends* that capacity should live where the budget does. This single choice addresses three requirements at once. (1) The boundary of a causal diamond is a Lorentz-covariant geometric object, it transforms under boosts with no preferred slicing, so boundary data is the slice-free 4-D object requirement 1 demands (boundary data $\neq$ Cauchy data on $\Sigma_0$). (2) $Q_R$ and $\lambda$ then live on the same screen, automatically aligning the covariant capacity bound with the selector. (4) Boundary data on nested / overlapping diamonds carries a natural restriction-compatibility (agreement on shared edges), turning "foliation-free global consistency" into an order-theoretic gluing condition on the causal-diamond poset rather than a statement requiring a global time function.

*Honest status of the proposal.* "Boundary data determines the bulk record sector" is the holographic principle / bulk reconstruction, and in controlled settings (AdS/CFT: HKLL, entanglement-wedge reconstruction) that reconstruction is *subtle and not literal*; for general causal diamonds in non-AdS spacetimes it is an open question in its own right. So this proposal does not *solve* requirements 3–4, it *relocates* them to the sharper, more tractable question of whether holographic boundary data on a causal-diamond screen uniquely and covariantly fixes the $\lambda$-selected bulk record. That is the theorem to attempt. The merit of the proposal is that it gives $\lambda$ a concrete geometric home (a covariant holographic screen) and a manifestly covariant dynamics (Dirac/QFT $U_g$), so both halves of the pair $(\Phi,\lambda)$ transform geometrically, with nothing referencing a "now."

***Reduction, corrections, and the linchpin theorem (GPT-5.5-pro adversarial sharpening).*** Subjecting the proposal to an adversarial review converts the slogan into a precise target and corrects three mistakes in its naive form. We record both the corrections and the resulting linchpin theorem, because a sharply-posed target is itself a contribution.

*Correction A, the gluing is over bulk overlaps, not screen intersections.* For nested diamonds $K \subset D$ the boundary $\partial K$ is in general **not** a subset of $\partial D$, so literal "agreement on shared edges" is too weak. The correct, frame-free consistency condition is **bulk-overlap agreement**: writing $\rho_{D,L}$ for the restriction of a $D$-record to a subdiamond $L$,
$$
\rho_{D,L}(C_D) = \rho_{E,L}(C_E) \qquad \text{for every } L \subset D \cap E .
$$
Equivalently, organize the admissible record sectors as a contravariant functor $X_\Phi(D) = \mathrm{Stone}(\mathsf{B}_\Phi(D))$ on the causal-diamond poset $\mathsf{Diam}$ (where $\mathsf{B}_\Phi(D) \subset \mathrm{Proj}(\widehat{\mathcal A}(D))$ is the finite Boolean algebra of decoherent macroscopic record propositions), with restriction maps $\rho_{D,K} : X_\Phi(D) \to X_\Phi(K)$ for $K \subset D$. Then $\lambda$ is a **global section**,
$$
\lambda \in \Gamma(X_\Phi) = \varprojlim_{D \in \mathsf{Diam}} X_\Phi(D), \qquad \rho_{D,K}(\lambda_D) = \lambda_K ,
$$
and requirement 4 ("foliation-free global consistency") *is* the existence of such a global section. This is the precise, order-theoretic, time-function-free statement we wanted.

*Correction B, the gluing obstruction is AQFT net cohomology, and the split property does not trivialize it.* When local record-sector labels are defined only up to automorphism, gluing requires transition functions $g_{ij} \in \mathrm{Aut}(X_\Phi)$ on overlaps satisfying the cocycle condition $g_{ij}g_{jk}g_{ki} = 1$ on triple overlaps; the obstruction is a class $[g_{ij}] \in \check{H}^1(\mathcal U, \mathrm{Aut}(X_\Phi))$ (rising to an $H^2$ / gerbe class if agreement is only projective). In AQFT this is precisely **Roberts net cohomology**, the same machinery that classifies DHR superselection sectors under Haag duality, so the obstruction can carry charge sectors, gauge flux, and edge modes; it is not mere topological Čech cohomology. The Type III$_1$ **split property** (Type-I intermediate factors for separated inclusions) and **Haag duality** *help*, they let one define finite local pointer algebras and identify causal complements, but they do **not** by themselves trivialize the obstruction: the split inclusion is *non-canonical*, and a non-canonical choice breaks covariance unless one proves a coherent, Poincaré-natural split. (Gauge theories further complicate naive Haag duality via edge/flux degrees of freedom, and the Kochen–Specker theorem forbids $\lambda$ from being a global valuation on the *full* projection lattice, $\lambda$ must select one compatible recorded-history *realm*, not assign values to all contexts.)

*Correction C, requirement 5 is equivariance, not invariance* (already folded into requirement 5 above): $g_*\mu_\Phi = \mu_{U_g\Phi}$, not $\mu(g\cdot S) = \mu(S)$.

*The covariance identity becomes automatic from equivariant naturality.* Requirement 3 is cleanest categorically, but not as "$A_R$ is a natural transformation of nets" ($A_R$ is not a $*$-homomorphism; it selects a classical sector). Rather: build the record-sector functor $X_\Phi$ *naturally* from the covariant Haag–Kastler net $(\mathcal A, U)$ over the action category $\mathsf{Diam} \rtimes G$ (with $G = \mathcal{P}^\uparrow_+$, or its spin cover $\mathrm{ISpin}(1,3)$ for the Dirac field), with natural isomorphisms $\gamma_g : X_\Phi(D) \to X_{U_g\Phi}(gD)$, and take $\lambda$ to be an **equivariant global section**. Then requirement 3 is one line:
$$
A_{gD}[U_g\Phi, g\lambda] = (g\lambda)_{gD} = \gamma_g(\lambda_D) = g \cdot A_D[\Phi,\lambda].
$$
So requirement 3 reduces to proving that $X_\Phi$ is (i) functorial under inclusions, (ii) Poincaré-equivariant, (iii) compatible with the boundary-reconstruction maps. Bisognano–Wichmann / Borchers supply modular covariance ($\Delta_W^{it} = U(\Lambda_W(-2\pi t))$ for wedges); what *breaks* naturality is exactly the list of frame-dependent choices to avoid: a non-canonical pointer basis, a non-canonical split inclusion, state-dependent modular crossed products not respecting inclusions, a frame-dependent decoherence threshold $\epsilon(D)$, gauge-fixing / missing edge modes, and tie-breaking rules in any "most decoherent branch" prescription.

*The measure: the decoherence functional is the Born-reproducing, covariant $\mu$.* Of the candidates, the canonical Type II trace $\tau_D$ is a *carrier* (it writes local Born weights as $p_i^D = \omega_{\Phi,D}(P_i^D) = \tau_D(h_{\Phi,D}\,P_i^D)$ via the Haagerup density $h_{\Phi,D}$) but its uniqueness-up-to-scale does **not** by itself pin $\mu$ (the bare trace gives uniform counting, not Born for arbitrary $\Phi$); Bisognano–Wichmann / KMS is geometric only for wedges and CFT diamonds, not general interacting diamonds. The winning candidate is the **Gell-Mann–Hartle decoherence functional**: for a medium-decoherent recorded-history family $\{\alpha\}$ with class operators $C_\alpha$,
$$
\mu_\Phi(\mathrm{Cyl}(\alpha)) = D_\Phi(\alpha,\alpha) = \langle \Phi | C_\alpha^\dagger C_\alpha | \Phi \rangle = \tau_D(h_{\Phi,D}\,P_\alpha),
$$
extended from finite compatible cylinder events to global histories by a Kolmogorov–Carathéodory extension theorem. Its covariance is immediate from covariant class operators, $C_{g\alpha} = U_g C_\alpha U_g^{-1} \Rightarrow D_{U_g\Phi}(g\alpha,g\alpha) = D_\Phi(\alpha,\alpha)$, giving exactly the equivariance $g_*\mu_\Phi = \mu_{U_g\Phi}$ of requirement 5, and it reproduces Born by construction (the Kolmogorov sum rules hold on decoherent families). This unifies requirements 1 and 5: $\lambda$ = a maximal consistent recorded decoherent history, $\mu$ = the decoherence-functional measure on history space, implemented locally through Type II trace densities.

*No-signaling survives, conditional on one lemma.* Boundary-data $\lambda$ does not threaten the proved operational no-signaling **provided** one proves a **screen-local marginal lemma**: for every local AQFT instrument, the $\mu$-pushforward of $\lambda$ to its outcome records equals the AQFT Born state $\omega_\Phi$ and is independent of spacelike-separated instrument choices, i.e. $\sum_y \omega_\Phi(E_x^a F_y^b) = \omega_\Phi(E_x^a)$ using microcausality $[E_x^a, F_y^b]=0$ and completeness $\sum_y F_y^b = 1$. The named dangers to exclude are: screen-dependence (two screens reconstructing different records for the same diamond), remote-setting dependence of *local* marginals, and any access to sub-$\lambda$ boundary data beyond ordinary QFT observables (which would enable postselection-style signaling). **One reformulation is forced here:** if $\lambda$ is a *whole-history* object that already contains the setting records, then Bell measurement independence $\rho(\lambda \mid a,b) = \rho(\lambda)$ is ill-posed as stated; MI must be re-expressed for the **past / common-cause component** of $\lambda$ (the conditional history measure), not for the global history. This is the relativistic refinement of the §6.9 Bell stance, and is itself an open sub-task.

*Borrowed machinery and what breaks.* The reduction "$\lambda$ = maximal consistent recorded decoherent history (Gell-Mann–Hartle; Isham History Projection Operator formalism, already 4-D and time-neutral) + $\mu$ = decoherence-functional measure" lets QIQT-H import the spacetime-QM / decoherent-histories apparatus wholesale, but **seven repairs are required**, and naming them is part of the honest agenda: (1) the realm-selection / Dowker–Kent "many incompatible quasiclassical sets" problem, there is no automatic unique maximal realm; (2) contrary-inference pathologies, controlled only by restricting to *recorded* quasiclassical histories; (3) relativistic frame-dependence of time-ordered class operators $C_\alpha = P_{\alpha_n}(t_n)\cdots P_{\alpha_1}(t_1)$, must be replaced by genuinely spacetime / Schwinger–Keldysh / Tomonaga–Schwinger coarse-grainings; (4) Type III$_1$ obstruction to exact projection-valued local histories (needs split / Type-II-core / coarse-grained pointer algebras); (5) exact decoherence is rare, approximate decoherence needs explicit $\epsilon(D)$ bounds *stable under restriction and gluing*; (6) **the holographic capacity bound $\log \#\mathrm{Atoms}(\mathsf{B}_\Phi(D)) \le Q_D$ is NOT automatic in Gell-Mann–Hartle**, it is QIQT-H's genuinely new ingredient and must be proved compatible with refinement; (7) the measurement-independence reformulation of the previous paragraph.

***The linchpin: a Poincaré-equivariant holographic recorded-history sheaf theorem.*** The single theorem that, if proved, discharges the most requirements at once. For a Poincaré-covariant Haag–Kastler net $(\mathcal A, U)$ satisfying locality, isotony, additivity, time-slice, Haag duality, split/nuclearity, and Bisognano–Wichmann modular covariance, and for every admissible global state $\Phi$, there exist: (1) finite Boolean record algebras $\mathsf{B}_\Phi(D) \subset \mathrm{Proj}(\widehat{\mathcal A}(D))$ for every causal diamond $D$; (2) boundary record algebras $\mathsf{B}_{\Phi,\partial}(D)$ with natural reconstruction isomorphisms $\mathsf{B}_{\Phi,\partial}(D) \cong \mathsf{B}_\Phi(D)$; (3) capacity and decoherence bounds $\log\#\mathrm{Atoms}(\mathsf{B}_\Phi(D)) \le Q_D$ and $\mathrm{DecErr}(D) \le \epsilon(D)$; (4) functorial restriction maps making $X_\Phi(D) = \mathrm{Stone}(\mathsf{B}_\Phi(D))$ a sheaf/stack over $\mathsf{Diam}$; (5) a nonempty global-section space $\Lambda_\Phi = \Gamma(X_\Phi)$; (6) a probability measure $\mu_\Phi$ on $\Lambda_\Phi$ given on cylinder events by the decoherence-functional / Born weights $\mu_\Phi(\lambda_D = i) = \omega_{\Phi,D}(P_i^D) = \tau_D(h_{\Phi,D}P_i^D)$; (7) Kolmogorov consistency $\sum_{j : \rho_{D,K}(j)=i} \mu_\Phi(\lambda_D = j) = \mu_\Phi(\lambda_K = i)$; (8) Poincaré equivariance $X_{U_g\Phi}(gD) \cong X_\Phi(D)$ and $g_*\mu_\Phi = \mu_{U_g\Phi}$; (9) operational no-signaling marginals for all local AQFT instruments. The selector is then mere evaluation, $A_D[\Phi,\lambda] = \lambda_D$, and the covariance identity (requirement 3) follows immediately: $A_{gD}[U_g\Phi, g\lambda] = g\cdot A_D[\Phi,\lambda]$. **This theorem is the real target of Open Problem 3b.** Its nine hypotheses are exactly the framework's five requirements made precise, plus the AQFT regularity conditions; proving it (even for free fields, as a first case) would convert the Lorentz-covariance promissory note into a structural result.

*Formalization note (Lean), now partially carried out.* The linchpin's discrete skeleton is more amenable to machine verification than its analytic core, and the project's existing strategy, prove the order-theoretic / combinatorial scaffold, name the functional-analytic inputs as interface axioms (cf. `AxiomAudit.lean`), applies directly. Four Lean modules now realize this, all compiling and axiom-audited (full build $\approx$ 2994 jobs; standard axioms only on every headline theorem):

- **`LorentzSelection.lean`**: the poset/sheaf layer: the causal-diamond poset $\mathsf{Diam}$, the record-sector presheaf $X_\Phi$ with functorial restriction, the global section $\lambda \in \Gamma(X_\Phi)$, `bulk_overlap_agreement` (Correction A; *no axioms*), and the **evaluation-gives-covariance theorem** $A_{gD}[U_g\Phi,g\lambda] = g\cdot A_D[\Phi,\lambda]$, proved from equivariant naturality, depending on standard axioms only and on *none* of the (now-retired) AQFT axioms. The Poincaré action is an `OrderIso` of diamonds; this makes the pushed-forward section's consistency a *proved theorem* (`actSection_consistent`) rather than an axiom, the earlier transport-bookkeeping axiom was thereby eliminated. The four AQFT analytic inputs are no longer opaque axioms but an explicit `RecordedHistoryNet` structure (holographic finiteness bound, boundary-reconstruction natural iso, decoherence-functional probability weights, projective/no-signaling marginal), over which the covariance result becomes the conditional theorems `covariant_selection_of_net` / `covariant_selection_exists` and no-signaling becomes the theorem `net_no_signaling`, leaving the module **axiom-free**.
- **`FiniteModularTheory.lean`**: the finite-matrix modular engine: the inner conjugation automorphism, the KMS *boundary* identity $\omega(xy)=\omega(y\,\sigma(x))$ from trace cyclicity, and, the genuine modular *data*, the **real-time modular flow** $\sigma_t(x)=\rho^{it}x\rho^{-it}$ in the diagonal case, proved to be a real one-parameter group ($\sigma_s\circ\sigma_t=\sigma_{s+t}$). This is honestly the *finite Type-I* modular skeleton, not the continuum Tomita–Takesaki data (GNS $\Delta$, $J$, $S=J\Delta^{1/2}$, the implementation theorem, KMS strip-analyticity remain future work).
- **`FreeFieldRecord.lean`**: the free-field finite-mode instance: the holographic record count $\log_2 \#\mathrm{Atoms} = N \le Q_R$; the **decoherence factorization** $\langle E_\alpha|E_\beta\rangle = \prod_i \langle E_{\alpha_i}|E_{\beta_i}\rangle$ with the *derived* bound $|\langle E_\alpha|E_\beta\rangle| \le q^{\,d_H(\alpha,\beta)} \to 0$ (Gaussian/Wick suppression, derived from the mode product rather than postulated); and the finite-mode Lorentz action on record sectors (a one-parameter group of bijections, capacity-covariant).
- **`LorentzSelectionStrong.lean`**: the *strengthening* pass that answers the adversarial-review caveats (i)–(ii) above with genuine content (the review's items A–G), keeping the interface *conditional* but making it **rigid** and **connected** rather than vacuous, and still axiom-free: **(A)** an *externalized* `GeometrySpec` fixes the area-law budget $N$ and the boundary presheaf *before* a net is chosen, so the holographic bound and reconstruction can no longer be satisfied by the cheap $N:=\#X_\Phi$, $P_b:=P$ choices (consuming theorems: `card_le_of_le`, using holographic monotonicity, and `reconSection`, the screen-encoded selected history as a consistent boundary section); **(B)** a genuine Poincaré *group* action `GroupAction G P` with identity/composition laws, giving covariance for *every* $g$ (`group_evaluation_covariance`) and law-consuming identities (`act_one_diam`, `act_mul_diam`), replacing the single order-automorphism; **(C)** `measure_pushforward_total`, a theorem that *consumes* the measure-covariance hypothesis (a $g$-covariant weight has $g$-invariant total mass, by reindexing along the sector equivalence), the measure-level content the bare covariance theorem ignored; and **(G)** the **Born link** (the anti-vacuity lock): a `BornData` pins the weights to Born values $\omega_\Phi(P_i^D)=\langle\psi_D|E_x^D|\psi_D\rangle$ of an actual unit state on a resolution of identity, whence *normalization is a theorem* (`bornω_sum_one` / `bornωRe_sum_one`: $\sum_x\omega = \langle\psi|\,{\textstyle\sum_x}E_x\,|\psi\rangle = \langle\psi|\psi\rangle = 1$) derived from the already-discharged Born functional (`GleasonSelector.born_add`/`born_one`), tying the Lorentz strand to the axiom-free Gleason strand. A second pass (after a follow-up adversarial review) closes the three remaining gaps that review named: **(probabilities, not just affine normalization)** a `PVMData` adds the projection hypotheses $E_x^\dagger=E_x$, $E_x^2=E_x$ that `BornData` lacked, whence `born_posSemidef_nonneg` ($\langle\psi|E|\psi\rangle\ge 0$ for positive-semidefinite $E$, via `Matrix.PosSemidef.dotProduct_mulVec_nonneg`) gives `pvm_bornωRe_nonneg` and `pvm_bornω_im_zero`, so `pvm_isProbability` certifies the weights are a genuine finite probability distribution (nonnegative *and* summing to $1$), not the signed/complex "weights" the bare $\sum_x E_x=1$ would have permitted; **(a real representation)** the γ-cocycle laws `IsRepOne`/`IsRepMul` (with the fibre transport `fibCast`) upgrade the family $\{\gamma_g\}$ from a per-element natural equivalence to a genuine action on the record fibres, with `γ_cocycle_apply` ($\gamma_{g_1 g_2}=\gamma_{g_2}\circ\gamma_{g_1}$ up to the diamond cast) as the consuming theorem; and **(per-cell covariance)** `measure_pushforward_cell` strengthens the total-mass statement to per-sector equality $\omega_{gD}(y)=\omega_D(\gamma_g^{-1}y)$. A third pass then **discharges the measure-covariance hypothesis itself** (`hcov`, previously the marquee *assumption*): the unconditional theorem `born_unitary_invariant` ($\langle U\psi|UEU^\dagger|U\psi\rangle=\langle\psi|E|\psi\rangle$ for $U^\dagger U=1$, proved by the adjoint identities `star_mulVec`/`dotProduct_mulVec`/`vecMul_vecMul`) is the engine; a `UnitaryCovariance` records the *lower-level* equivariance, the state transforms $\psi_{gD}=U_{g,D}\psi_D$ and the effects conjugate $E_{gD}(\gamma_g x)=U_{g,D}E_x^D U_{g,D}^\dagger$, from which `ubornω_covariant` *derives* $\omega_{gD}(\gamma_g x)=\omega_D(x)$ as a **theorem**, and `ubornω_pushforward_cell` / `ubornω_total_invariant` then make the per-cell and total-mass covariances **unconditional on `hcov`**. This converts caveats (i)–(ii) from "the analytic fields are ignored / non-rigid" into "the fields are externally rigid, consumed by theorems, the weights are certified probabilities, and their Poincaré covariance is *derived from unitarity* rather than assumed." A fourth pass then threads the γ-cocycle onto the *selection itself*, `selection_cocycle` proves $\gamma_{g_1 g_2}(\lambda_D)=\gamma_{g_2}\big(\text{selector}(g_1\!\cdot\!\lambda)(g_1 D)\big)$ (up to the diamond cast), i.e. multi-step transformed selections agree with the one-step transform, consuming both `IsRepMul` and `group_evaluation_covariance`, and fuses the two strands into a single object: `UniformPVMData` carries the projection hypotheses *and* the uniform-dimension Born data, and `upvm_covariant_probability` certifies the weights on each diamond are simultaneously (i) nonnegative, (ii) summing to $1$, and (iii) Poincaré-covariant $\omega_{gD}(\gamma_g x)=\omega_D(x)$, a genuine **covariant probability distribution** whose covariance is *derived*. A coherence check is also discharged as a theorem: `proj_conj_unitary` (unitary conjugation preserves a Hermitian projection) gives `E_cov_preserves_proj`, the boosted effects $E_{gD}(\gamma_g x)=U E_x^D U^\dagger$ remain a PVM, so `UnitaryCovariance` over a `UniformPVMData` is internally consistent (not over-determined); and `covariantProbability_of_unitaryPVM` packages the three facts as a `CovariantProbability` bundle. A final pass discharges the two remaining reachable in-interface statements. **(Section-object group action)** `LorentzSelection` now exposes a public spec `actSection_val` (the `actVal` field is private) plus `GlobalSection.ext` and `GlobalSection.val_cast`; on top of these `actSection_one` ($1\cdot\lambda=\lambda$) and `actSection_mul` ($(g_1 g_2)\cdot\lambda = g_2\cdot(g_1\cdot\lambda)$) are *proved*, so `actSection` is a genuine **group action on $\Gamma(X)$**, of which the earlier selector-level `selection_cocycle` was only the evaluation shadow. The transport casts are handled cleanly by `actSection_val_act'` (the cast-free evaluation $(g\cdot\lambda)(gD)=\gamma_g(\lambda_D)$), `val_cast`, and `fibCast_symm_castSector`, no raw `HEq`, the route the adversarial review outlined. **(Full PVM preservation)** `unitary_preserves_resolution` proves $U(\sum_x E_x)U^\dagger = U\,U^\dagger = 1$ (using $UU^\dagger=1$ derived from the finite-square $U^\dagger U=1$), so the unitary transport preserves the *resolution of identity*, not just individual projections, the boosted effects are a *full* PVM. What remains genuinely open is now only: the boundary-action/reconstruction compatibility, and, the principal gap, the continuum *realization* (existence of such a net, with its unitary Poincaré transport, from a genuine relativistic QFT: the Type III$_1$ / Tomita–Takesaki problem). Every reachable assumption-to-theorem conversion in the finite conditional interface is complete: the interface is rigid, connected, a *covariant probability distribution* with covariance derived from unitarity, coherent under transport (a full PVM preserved by the action), and carries a genuine group action on its global sections; its *instantiation* from QFT is the open problem.
- **`LorentzWitness.lean`**: a **concrete non-trivial model** of the strengthened interface, settling the *vacuity* question the review raised (the structure also admits the trivial one-point net, so "a model exists" alone is empty). Over a single causal diamond with a two-element record fibre `Fin 2`, a two-dimensional Hilbert space, the rational unit state $\psi=(3/5,4/5)$, and the diagonal projective measurement, it builds a full `UniformPVMData` + `UnitaryCovariance` and hence (via `covariantProbability_of_unitaryPVM`) a `CovariantProbability`, with `witness_nondegenerate` proving the Born weights are $\omega(0)=9/25,\ \omega(1)=16/25 \in (0,1)$, a genuinely *spread* two-outcome distribution rather than a point mass, and `witness_fibre_card` confirming the fibre has two elements (not one). So the conditional interface has real content: it is satisfiable by non-degenerate models, not only the trivial net (standard Lean axioms only). A second witness exercises the *covariance* machinery on a genuine orbit: two causal diamonds with the indiscrete preorder (so every permutation is an order-isomorphism), the group $G=\mathrm{Perm}$ permuting them, and homogeneous PVM data, `witness2_covariantProbability` gives a `CovariantProbability` over this non-trivial group, and `witness2_action_nontrivial` proves the swap moves diamond $d_0$ to $d_1$ (the action is genuinely non-trivial, unlike Witness A's trivial group). *Honest scope:* these are finite, rational (no $\sqrt 2$), homogeneous models that prove the interface is non-vacuous and its covariance applies to a non-trivial orbit; the continuum QFT realization (Type III$_1$ / Tomita–Takesaki) remains the genuine open content, untouched.

What was previously deferred to *four opaque interface axioms* in `LorentzSelection.lean`, corresponding to the existence of the finite record algebras with the holographic bound (linchpin hypotheses 1–3), the boundary-reconstruction isomorphism (2), the Born/decoherence-functional measure with its Kolmogorov consistency and $\sigma$-additive extension (6), and the no-signaling marginal lemma (9), has been **removed from the axiom budget**: those four `axiom _ : Prop` placeholders (which asserted nothing and were used by no theorem) are **retired** and replaced by an explicit `RecordedHistoryNet` structure that *writes the content down* as type-checked data and propositions (a holographic finiteness/cardinality bound, a boundary-reconstruction natural isomorphism commuting with restriction, decoherence-functional probability weights, and the projective/no-signaling marginal). The covariance result is then a *conditional theorem over this structure* (`covariant_selection_of_net`, `covariant_selection_exists`), and the projective marginal yields the convenience theorem `net_no_signaling` (the marginal onto a sub-diamond $K$ is the same regardless of which larger diamond $D\supseteq K$ it is computed from). The whole `LorentzSelection` module now adds **zero project axioms** (every headline theorem depends on the standard Lean axioms only, per `AxiomAudit.lean`; the project-wide raw axiom count drops $44\to 40$).

*What this does and does not establish (adversarial-review caveat, GPT-5.5-pro).* This is the corpus's *interface-as-hypothesis, not axiom* discipline applied to the AQFT inputs, and as such it is a genuine improvement in formal hygiene, but it must not be overstated, and three honest limitations are recorded here. **(i) The covariance theorem is evaluation-equivariance, not covariance of the physics.** `covariant_selection_of_net` consumes only the presheaf field `net.P`; its proof is the structural identity `evaluation_covariance`, and the analytic fields (`N`, `recon`, `ω`, `ω_marg`) play no role in it, so what is machine-checked is "a transformed global section, evaluated at the transformed diamond, equals the transform of the evaluation," not covariance of the decoherence measure or of a *fixed* selection rule. **(ii) Several fields are non-rigid as written, so the structure admits degenerate models.** Because `N`, `Pb`/`recon`, and `ω` are chosen *within* the same structure, the holographic bound is satisfiable by taking $N(D) := \#X_\Phi(D)$, boundary reconstruction by $P_b := P,\ \mathrm{recon} := \mathrm{id}$, and the weights by any finite PMF; in particular the one-point net ($X_\Phi(D) := \mathbf 1$) satisfies every field. **Consequently the bare existence statement "a `RecordedHistoryNet` exists" is *not* the open problem, it is trivially true.** The genuine Open Problem 3b is the *realization* problem: existence of a net whose data are *extracted from a fixed relativistic QFT and geometry*, the area-law $N(D)=\lfloor e^{Q_D}\rfloor$ and boundary algebra fixed externally, and the weights pinned to Born values $\omega_\Phi(P_i^D)$ of an actual global state $\Phi$, together with a genuine Poincaré *group* action (the current `PoincareAction` is a single order-automorphism, not a representation) under which the measure is equivariant. **(iii) `net_no_signaling` is a two-line rewrite of the assumed marginal**, not a derivation of operational no-signaling from microcausality; the real content remains the *assumption* `ω_marg`. The honest status, then: the four opaque axioms are gone and the finite combinatorial skeleton (functorial restriction, global sections, evaluation-equivariance, the finite Type-I modular flow, and the free-field finite-mode record structure) is machine-checked and axiom-free; but the substantive Lorentz-covariance content, Born-pinned covariant measure, externally-rigid holographic/boundary data, a true group action, and the Type III$_1$ / Tomita–Takesaki / Haagerup-$L^p$ *realization*, remains open, and is the agenda for the next formalization pass (§11.4 strengthening targets: externalize the geometry spec, replace the single automorphism by a group action with equivariant weights, and tie $\omega$ to the already-formalized Born functional).

**Open Problem 4, Quantitative form of $\epsilon(R)$.**
The (FQ)(iii) resolution floor satisfies $\epsilon(R) > 0$ (Theorem 3; formalized in `Resolution.lean`). Derive an explicit functional form $\epsilon(R) = f(\text{geometry}, Q_R, \text{macroscopic record dimension})$ tying the framework to numerical predictions. Downstream of Open Problems 2 and 3.

**Open Problem 5, Empirical calibration of $I_0$.**
The per-record physical cost $I_0$ is a phenomenological parameter, analogous to GRW's collapse rate $\lambda$. Current best estimates (Zurek physical entropy for typical macroscopic records) give $I_0 \sim 10^{25}$ bits. The framework's prediction: a definite calibrated value of $I_0$ such that the saturation condition $I_0 \approx C(R)$ matches the observed quantum-to-classical transition. Downstream of Open Problem 4.

---

**Algebraic / mathematical-physics infrastructure.** *Finite-classical discharge note (Lean).* The pieces of items 6 and 9 that are *finite-classical*, and were previously carried as named axioms with an in-file proof sketch, have now been **proved** and removed from the axiom budget (project raw axiom count $40 \to 37$, machine-verified, standard Lean axioms only): the **Fano-step bound** behind item 6 (`ShannonFano.H_bound_imp_max_lb`: the Rényi-$\infty \le$ Shannon relation $\max_i p_i \ge e^{-H(p)}$, with `H_zero_imp_dirac` now a corollary), and the **finite relative-entropy positivity** behind item 9 (`RelEntPositivity.KL_classical_nonneg`: Gibbs' inequality $\sum_i p_i\log(p_i/q_i)\ge 0$ from $\log x \le x-1$). What remains axiomatic in this stack is exactly the genuinely *vN-algebraic / continuum* content, Klein's inequality at the von Neumann level (operator convexity of $-\log$), Donald's identity, the quantum data-processing inequality, the CPW entropy bridge, and Araki relative entropy, none of which Mathlib yet reaches; these are the true open analytic inputs, not finite bookkeeping.

6. **Operational distinguishability axiomatization (H3).** Make precise, under decoherence + Quantum Darwinism, when the macroscopic-record subalgebra admits a normal measurement instrument decoding the record index with small error, so that the Fano-type bound $H_\epsilon \le I_{\rm Hol}^R + \eta_{\rm def}$ holds. *(The finite-classical Fano step: `H_bound_imp_max_lb`, is now proved, §above; the open part is the operational existence of the small-error decoding instrument at the AQFT level.)* Existing ingredients: spectrum broadcast structure (Zurek, Brandão-Piani-Horodecki), redundancy plateaus, decoherent-histories medium-decoherence conditions.

7. **Stagewise adapted process and refinement compatibility.** Construct rigorously the stagewise process $h \mapsto \omega_t^h$ of §7.6, including: existence under Cauchy-slice refinement; compatibility of $\mathfrak{R}_t(h)$ with the AQFT net's isotony; conditions under which the adapted family extends to a completed-history limit.

8. **Functorial / isotonic crossed-product local nets.** Establish the functorial structure $D \mapsto \hat{\mathcal{A}}(D)$ as a covariant net of Type II crossed-product algebras with normal embeddings under inclusion. Needed for the modular-local bound to behave consistently under region refinement / coarse-graining.

9. **Modular-Hamiltonian estimates beyond wedges and CFT balls.** Generalize the wedge / CFT-ball modular-Hamiltonian estimate to broader classes of regions, either via tighter enclosing-wedge monotonicity arguments or new geometric forms of $K_R^\sigma$. Without this the conditional $\delta_R \sim 10^{-27}$ estimate cannot be extended to generic laboratory geometries. *(The finite-classical relative-entropy positivity that anchors the modular bound: `KL_classical_nonneg`, Gibbs, is now proved, §above; the open part is the continuum modular geometry and vN-level Klein inequality.)*

10. **State-extension and reference-state issues** in the crossed-product algebra formulation: extension of states across causal-diamond boundaries, choice of $\sigma_R$ in cosmological / non-stationary backgrounds.

11. **Locality of the (FQ)-restricted dynamics.** The (FQ) projection onto $\mathcal{H}_{\rm phys}$ must commute with the local algebras' observables for Theorem 7's no-signaling argument to apply to the *restricted* (physical) theory rather than only the ambient (unrestricted) theory. The compression-locality leakage identity (formalized in `CompressionLocality.lean`) isolates this implicit constraint. Construct concrete (FQ) projections satisfying it; characterize the class of admissible projections.

**Empirical / phenomenological:**

12. **Concrete measurement-apparatus models realizing finite $\chi_R$ budgets.** Build explicit toy models (Stern-Gerlach, interferometer, optomechanical) where $\chi_R$ for the apparatus-record state is computable and the saturation regime can be approached. Without these the framework's content cannot be confronted with experiment.

13. **Phenomenological predictions.** With $I_0$ calibrated, the framework predicts: maximum macroscopic-superposition scale (testable against Schrödinger-cat experiments with progressively larger systems); long-baseline coherence limits; specific signatures distinguishing the framework from GRW-style stochastic collapse (the framework predicts kinematic exclusion, not stochastic events).

14. **Cosmological / horizon applications**, extend to the de Sitter static patch and black-hole horizon regions, where $C(R)$ becomes finite and saturation may be physically relevant.

---

**Strategic note.** Of the central open problems, the audit work suggests two bottleneck chains:

  • **Foundations bottleneck:** Open Problem 1 (canonical $\mu$-selection / equivariance). Now decomposed into three sub-theorems A, B, C (see above), with the A1+A2+A4+A6 strengthening pass further narrowing the load-bearing content. Two of the three sub-theorems are direct applications of existing operator-algebra machinery (Mackey-Gleason + noncommutative Radon-Nikodym); the third requires adapting the Goldstein-Struyve 2007 uniqueness theorem from Bohmian dynamics to QIQT-H's Type II / (FQ) setting. Concrete progress: the permutation-symmetry collapse component of Goldstein-Struyve Step 1 sub-lemma 1c is **PROVED** under its necessary hypothesis (`step1c_collapse_of_perm_symmetric`) along with the foundational matrix-conjugation identities (`permutation_conj_matrixUnit`, `diagonalU_conj_matrixUnit`), while the full finite Schur classification has since been **PROVED** outright (`schur_classification_real`); the marginal-locality step is **PROVED** as a theorem holding for any measure (`MarginalLocality.pushforward_marginal_local`), reducing locality to a named Hilbert→set-level bridge axiom rather than eliminating it; single-trial Chebyshev frequency concentration and the variance-addition (independence) lemma are **PROVED** (`BornConcentration`), with the $N$-trial scaling still on the LLN axiom; and the duplicate axiomatization of Goldstein-Struyve sub-steps in `FQEquivarianceUniqueness` is **CONSOLIDATED** to route through the concrete `GoldsteinStruyveFinDim` proof (`canonical_ic_measure_principle` was consolidated to two project-specific axioms, down from nine — both since discharged, so it is now axiom-free), with the five false/unused Step-1 placeholder sub-axioms deleted (project axiom total 57 → 40, since driven to 0). Progress on the remaining load-bearing axioms transforms the Born section from conditional to substantive, and is the most pressing problem for foundations-of-QM defensibility.

  • **Quantitative-emergence bottleneck:** Open Problem 2 (reference-weight bound) $\Rightarrow$ Open Problem 4 ($\epsilon(R)$) $\Rightarrow$ Open Problem 5 ($I_0$ calibration). Progress on Open Problem 2 unlocks the quantitative QIQT-H pipeline. (The former Open Problem 3, Macroscopic Definiteness / Branch-Summed bound, is **withdrawn** — see §11.4; single-record definiteness is $\lambda$'s role, not a capacity exclusion.)

These are the two genuinely open research directions left after the Lean audit work has clarified the deductive boundary. The remaining items (6–14) are infrastructure and phenomenology that follow once the bottlenecks are addressed.

### 11.4a Claim-to-Lean theorem matrix

The following table maps each major paper claim to its Lean theorem, with explicit status. Status labels:

  • **U**: unconditional (no project-specific axioms; depends only on standard Lean axioms `propext`, `Classical.choice`, `Quot.sound`).
  • **C**: conditional on a standard external theorem (Mathlib-citable; axiomatized at clean interface in the project).
  • **P**: programmatic interface axiom (specific framework or AQFT-level axiom; concrete Lean discharge is a multi-day to multi-week task).
  • **N**: negative audit / counterexample (proves a *non*-derivation).

**Current status (audit): every former C and P row has been discharged to U.** The project is now axiom-free (0 project-specific axioms; CI budget 0, `scripts/axiom_budget_check.sh`). The C/P labels and the discharge notes below are retained as the historical record of how each interface axiom was either proved in a concrete finite model or recast as an explicit hypothesis. The continuum versions of these results remain the cited/open frontier (Open Problems 3/3b), and the *physical* postulates are unaffected by the formal discharge.

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
| FQ-literal finite ⇒ trivial dynamics | `FQDynamicsNoGo.finite_admissible_flow_fixed` | U | Continuous flow on finite T2 space (only, not arbitrary finite-info dynamics) |
| Compression-locality leakage identity | `CompressionLocality.compressed_commutator_with_commute` | U | Pure ring algebra |
| Any $p$ realizable (no Born from nothing) | `NoBornFromNothing.exists_probability_realizing` | N | Concrete section-based construction |
| Support preservation $\neq$ Born equivariance | `EquivarianceGap.support_preservation_does_not_imply_measure_preservation` | N | Concrete `Fin 2` counterexample |
| Born typicality (mean form) | `BornTypicality.born_mean_conditional` | U | Conditional on canonical $\mu_\rho$ with Born marginal |
| Operational data ⇏ unique IC measure | `OperationalNoGo.operational_data_insufficient` | N | Concrete `Fin 3` witness |
| Sub-thm A (Born from non-contextuality) | `EffectGleason.finite_effect_gleason` | U | **The `TypicalityMackeyGleason` module was retired and deleted.** Its Mackey-Gleason packaging is superseded by the axiom-free finite effect-Gleason theorem (Born forced from positivity + normalization + ray-certainty) |
| Sub-thm C (FQ-equivariance uniqueness) | `FQEquivarianceUniqueness.canonical_ic_measure_principle` | U | **Now axiom-free:** the former dependencies (Schur classification, tensor multiplicativity) are both proved, so `canonical_ic_measure_principle` depends only on the standard Lean axioms |
| GS Step 2 (normalization) | `GoldsteinStruyveFinDim.step2_normalization` | U | Concrete `Matrix.trace` computation |
| GS Step 4 (non-degeneracy) | `GoldsteinStruyveFinDim.step4_nondegeneracy` | U | Direct case analysis |
| GS Step 3 algebraic core | `GoldsteinStruyveStep3.step3_algebraic_core` | U | Polynomial identity via `ring` |
| GS Step 3 Kronecker bridge | `GoldsteinStruyveKronecker.step3_kronecker_bridge` | U | Concrete `d = 2` witness with E₁₁ ⊗ E₁₁ |
| GS Step 1 (Schur classification) | `GoldsteinStruyveStep1.step1_via_sub_lemmas` | U | **The `step1_schur_classification` interface axiom is RETIRED** (Step 1 is now proved outright, see `schur_classification_real` below). The five former placeholder sub-axioms (1a–1e), three literally false, all unused, were **deleted**; `permutation_conj_matrixUnit`, `diagonalU_conj_matrixUnit`, and `step1c_collapse_of_perm_symmetric` are the proved building blocks |
| GS Step 1c (coefficient unification, partial) | `GoldsteinStruyveStep1.step1c_collapse_of_perm_symmetric` | U | **NEW (A2):** the *permutation-symmetry collapse component* of Step 1c, proved via `Equiv.swap` transitivity under its necessary permutation-symmetry hypothesis. The prior bare-coefficient axiom (no hypothesis) was literally false and has been **deleted**. The *full* Schur classification (Step 1) remains the single named interface axiom |
| Permutation conjugation of matrix units | `GoldsteinStruyveStep1.permutation_conj_matrixUnit` | U | **NEW (A2):** $P_\sigma \cdot E_{ij} \cdot P_\sigma^* = E_{\sigma(i),\sigma(j)}$ via direct matrix-entry computation |
| Diagonal-unitary conjugation of matrix units | `GoldsteinStruyveStep1.diagonalU_conj_matrixUnit` | U | **NEW (A2):** $D(z)\cdot E_{ij}\cdot D(z)^* = (z_i\,\overline{z_j})\,E_{ij}$, self-contained diagonal parameterization (no `Complex.exp`) |
| Combined GS finite-dim theorem | `GoldsteinStruyveFinDim.goldstein_struyve_findim` | U | Proved by composition; Steps 1 and 3 are now proved axiom-free, so it inherits no axioms |
| Marginal locality (pure pushforward) | `MarginalLocality.pushforward_marginal_local` | U | **NEW (A1):** $r\circ T = r \Rightarrow r_*(T_*\mu) = r_*\mu$ for **any** $\mu$, no equivariance assumption; reindexing argument |
| Marginal locality (equivariant corollary) | `MarginalLocality.alice_marginal_unchanged_by_bob_dynamics` | U | **NEW (A1):** thin corollary of the pure version; discharges the *marginal-locality step* (not the Hilbert→set bridge, which stays a named axiom) |
| Chebyshev tail bound on finite probability space | `BornConcentration.chebyshev_tail_bound` | U | **NEW (A4):** abstract Chebyshev via variance-dominates-restriction |
| Bernoulli variance $p(1-p)$ | `BornConcentration.bernoulli_variance` | U | **NEW (A4):** direct two-term sum computation |
| Variance addition (independence) | `BornConcentration.variance_add_of_product` | U | **NEW (A4):** $\mathrm{Var}(X_1+X_2)=\mathrm{Var}\,X_1+\mathrm{Var}\,X_2$ on a product measure, the reusable lemma the $N$-fold LLN induction would iterate |
| Two-trial Bernoulli variance $2p(1-p)$ | `BornConcentration.two_trial_bernoulli_variance` | U | **NEW (A4):** concrete instance of variance-addition |
| Born single-trial frequency concentration | `BornConcentration.born_chebyshev_single_trial` | U | **NEW (A4):** single-trial bound; the $N$-trial scaling to full "Born frequencies" still rests on the LLN interface axiom |
| Minimality witnesses for P1, P2, P3 | `BornMinimalityTable.{P1, P2, P3}_…_necessary` | N + U | **NEW (A6):** unified independence package showing each Born sub-axiom is necessary by concrete finite countermodel (minimality *relative to the current decomposition*) |
| Locality (P4) is reducible | `BornMinimalityTable.P4_locality_reducible_to_equivariance` | U | **NEW (A6):** marginal-locality theoremized (modulo the named bridge axiom); not an independent Born-selection sub-axiom |
| **GS Step 1 (Schur classification)** | `GoldsteinStruyveStep1.schur_classification_real` | U | **2026-06 UPDATE:** the former interface axiom `step1_schur_classification` is **RETIRED**, Step 1 is now fully proved axiom-free (Hadamard relation → linear assembly → reality via `IsHermitianPreserving`). Step 3 likewise proved. The finite Goldstein–Struyve chain is axiom-free; the project axiom budget has since reached **0** |
| Finite effect (Busch) Gleason | `EffectGleason.finite_effect_gleason` | U | normalized + positive + coexistent-additive functional on effects $=\mathrm{tr}(\rho\,\cdot)$, Born from positivity, finite-dim |
| Finite weak LLN (Chebyshev) | `BornTypicalityFinite.chebyshev_freq` / `chebyshev_freq_union_le` | U | $P(\lvert\mathrm{freq}-p_k\rvert\ge\varepsilon)\le p_k(1-p_k)/(N\varepsilon^2)$; union bound $\le 1/(N\varepsilon^2)$ |
| Quantum bridge (tensor trace) | `BornTypicalityQuantum.quantumWeight_eq_w` | U | $N$-copy product-measurement weight $=$ classical product weight of the Born vector |
| Product-measure uniqueness | `BornMeasureUniqueness.product_born_measure_unique` | U | the product Born measure is the unique additive history measure with the Born marginals (independence explicit) |
| **C1** one record → one **value** | `PointerValue.existsUnique_actualValue` / `existsUnique_actualHistory` | U | in the finite additive-cost model, ≤1 distinct-valued coactual record (λ selects it); many same-value records may coexist |
| **C2** one-site Born (vector state) | `OneSiteBorn.vectorState_eq_weight` | U | $\mathrm{Re}\langle\psi,E_a\psi\rangle=\lVert E_a\psi\rVert^2$ on a PVM projection |
| **Single-trial Born from non-contextuality** | `OneSiteGleason.oneSite_forced` | U | non-contextual `EffectMeasure` $\Rightarrow$ $\mu(P_a)=\mathrm{Re}\,\mathrm{tr}(\rho P_a)$, **forced** by effect-Gleason (strong premise; not Born by hand) |
| Non-contextual $=$ Born (converse) | `OneSiteGleason.traceEffectMeasure` | U | every density matrix is a non-contextual `EffectMeasure` |
| Subadditive capacity exclusion | `CoreNoCollapse.joint_coactual_subsingleton`; `OrthogonalCapacity.pair_exceeds` | U | monotone joint cost + pairwise overflow (overflow **derived** from orthogonality; no additivity assumed) |
| **Finite no-collapse Born representation** | `BornJoin.finite_noCollapseBornRepresentation`; `BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality` | U | **the join:** unique actual history + Born product law + Chebyshev typicality; single-trial law **forced Born** from non-contextuality. *Conditional representation theorem, assumes non-contextuality + product preparation, NOT Born from $Q_{\max}$.* See `FINITE_BORN_REPRESENTATION.md` |
| Independence $=$ product preparation | `BornTypicalityFinite.w_history_factorizes` | U | product world-measure $\Rightarrow$ trial independence; independence is the irreducible product-preparation input |
| World-measure observationally free | `BornJoin.ActualEnsemble.history_law_unique` | U | same single-trial law $\Rightarrow$ identical actual-history statistics, independent of the posited world-measure on $\Omega$ |

**Finite no-collapse Born representation (2026-06).** The rows above marked C1/C2/non-contextuality/the
join formalize, **axiom-free**, a finite no-collapse Born representation theorem: capacity forces a
unique actual pointer value; finite effect-Gleason forces a non-contextual outcome assignment to be the
Born weight $\mathrm{tr}(\rho P_a)$; product preparation gives independent trials; the actual-value
histories carry the Born product law and are Chebyshev-typical. Two GPT-5.5-pro verification passes
confirm it is **sound, non-vacuous, but a *conditional representation theorem***, Born weights and
factorization are *derived* from non-contextuality + product preparation, **not** from the capacity
bound alone. Full claim→theorem map and honest scope caveats: `FINITE_BORN_REPRESENTATION.md`.

**No-signaling clarification.** All "no-signaling" results in this paper are about *nonselective* CPTP instruments, the unconditional marginal probability after Bob's measurement, marginalized over outcomes (equivalently, the trace-preserving sum over Kraus operators). Selective post-measurement conditional states can change remotely once Bob's outcome is known; this is not "signaling" because the conditional update requires classical communication.

**Tsirelson clarification.** The Lean module `QIQTH.Tsirelson` proves *attainability* of the value $2\sqrt{2}$ by an explicit singlet-state construction in 4-dimensional real Euclidean space (which is the achievability content of Tsirelson's theorem). The *upper bound* statement that CHSH $\le 2\sqrt{2}$ for *every* quantum state and *every* measurement choice, the full Tsirelson theorem, requires operator-norm machinery on C\*-algebras and is *not* proved in this formalization. The framework relies on the standard Tsirelson upper bound as a cited result.

**Markov suppression clarification.** The `CapacityPacking` module formalizes only the *Markov-style* multi-record suppression (polynomial tail in the modular slack), explicitly *not* exponential suppression. Where the paper says "exponentially suppressed", the reference is to *decoherence-driven* exponential suppression of off-diagonal coherence (which is genuinely exponential, e.g., $e^{-10^{20}}$ for macroscopic environment dimensions), not to Markov-style multi-record suppression from the entropy bound alone.

### 11.4b Machine-checked modular substrate (companion formalization)

A companion Lean 4/Mathlib development (pinned commit `4720763a7b59`, toolchain `leanprover/lean4:v4.30.0`) machine-checks the standard modular / relative-entropy *calculus* underlying the regional cost functional $\chi_R$, for the free-field coherent-state sector. Every result below has status **U** (no project-specific axioms; depends only on `propext`, `Classical.choice`, `Quot.sound`, verified in `QIQTH/AxiomAudit.lean`); none formalizes the holographic axiom (FQ), the Macroscopic Definiteness Conjecture, or Born-from-typicality. A full statement-level index with `file:line` references and the companion paper appears in `paper_strategy/45_Theorem_Paper_Index.md`.

*Finite Araki relative entropy.*

  • `arakiEntropy_eq_relEntropy`: $S_{\rm Araki}(\rho\,\|\,\sigma)=\operatorname{tr}\rho(\log\rho-\log\sigma)$ (the Umegaki form).

*Bounded Tomita-Takesaki (standard subspace).*

  • `modConj_rvdRC_modConj`: $JRJ=2-R$.
  • `modConj_rvdT_of_mem_K`: $J(T\xi)=(2-R)\xi$ for $\xi\in\mathcal{K}$.
  • `modUnitary` (`_add`, `_unitary`, `_stronglyContinuous`): $\Delta^{it}$, with group law, unitarity, and strong continuity.

*One-particle CGP relative entropy.*

  • `cgpEntropy`: $S(\xi)=-\int\log((2-r)/r)\,d\mu^R_\xi$.
  • `rvdSpec_balance`: the CGP spectral balance.
  • `cgpEntropy_nonneg`: $S(\xi)\ge 0$ for localized $\xi\in\mathcal{K}$.

*Free-field (Fock) modular flow.*

  • `secondQuantModFlowH`: $\Gamma(\Delta^{it})$ (a one-parameter group, vacuum-fixing, strongly continuous on coherent vectors).
  • `secondQuantModFlowH_weylH`: $\sigma_t(W(u))=W(\Delta^{it}u)$.

*Coherent-state relative modular operator and reduction.*

  • `relModFlowH`: $\Delta^{it}_{W(f)\Omega\,|\,\Omega}=W(f)\,\Gamma(\Delta^{it})\,W(f)^*$.
  • `connesCocycleH`, `connesCocycleH_chain`: $[D\omega_{W(f)\Omega}:D\omega_\Omega]_t=W(f)W(-\Delta^{it}f)$, together with the cocycle chain rule.
  • `hasDerivAt_relModFlow_vacuum`: $S_{\rm Araki}(\omega_{W(f)\Omega}\,\|\,\omega_\Omega)=S_{\rm CGP}(f)$ (the Casini-Grillo-Pontello identity).

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

The framework retains standard quantum mechanics exactly at the level of the underlying field algebra. It adds one foundational axiom, (FQ) in its literal physical-instantiation reading, and one distinction (formal vs per-run wave function). From these, the structural consequences follow: finite physical resolution; decoherence removing interference; the finite-information restriction on regional content making a $\ge 2$-record content non-instantiable; hence single-record per-run regional content, the macroscopic world emerging without any dynamical modification.

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
