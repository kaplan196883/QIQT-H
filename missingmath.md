# Missing Mathematics for QIQT-H

**Status:** Planning document.
**Purpose:** Catalog the mathematical objects, theorems, and predictions QIQT-H currently lacks but needs. Every entry is phrased as an *assumption the eventual math must satisfy* or a *theorem the framework needs proved*. The point is not to do the math here, but to make the to-do list precise enough that progress can be measured.

This document tracks the gap between (i) the framework as currently stated — borrowed mathematics (Type III local algebras, modular theory, CPW Type II crossed-product cores, generalized entropy) plus a new physical postulate (the Branch-Summed Holographic Bound) — and (ii) what would be needed to call QIQT-H a *theory* rather than a research program.

---

## 1. The framework as currently stated

QIQT-H postulates that for any bounded causal region $D$ and any decoherent family of histories $\{h\}$ in $D$, the smoothed support-counting entropy of physically admissible records is bounded by the generalized entropy of $\partial D$:

$$
I^{\varepsilon}_{\rm branch}(D) \;\le\; S_{\rm gen}(\partial D) \;=\; \frac{A(\partial D)}{4 G \hbar} + S^{\rm ren}_{\rm matter}.
$$

The right-hand side is borrowed from Bekenstein-Hawking and from the CPW/Witten crossed-product construction. The left-hand side and the *admissibility* notion are new.

Every "missing piece" below is a thing the LHS, the admissibility relation, or the dynamical mechanism connecting them is missing.

---

## 2. Mathematical objects that need rigorous definition

### 2.1 The branch information $I^\varepsilon_{\rm branch}(D)$

**What it must do.** Count physically distinguishable record alternatives in region $D$, smoothed by tolerance $\varepsilon$.

**Required properties.**
1. **Basis-independence.** Two coarse-grainings that produce decoherent record algebras agreeing on macroscopic content must give the same $I^\varepsilon_{\rm branch}$.
2. **Compatibility with decoherence.** $I^\varepsilon_{\rm branch}$ must be definable from the decoherent histories functional $D(h, h')$ without reference to a preferred Hilbert-space basis.
3. **Smoothing stability.** $I^\varepsilon_{\rm branch}$ must be continuous in $\varepsilon$ for $\varepsilon > 0$, and must dominate naïve Rényi-0 counts which diverge under continuous spectra.
4. **Coarse-graining monotonicity.** Refining the record algebra cannot decrease $I^\varepsilon_{\rm branch}$.
5. **Computability.** There must exist an algorithm or closed-form expression for $I^\varepsilon_{\rm branch}$ given a regional state $\omega_\Psi$ on $\hat{\mathcal{A}}(D)$.
6. **Core-choice invariance.** $I^\varepsilon_{\rm branch}$ must be invariant under the choice of modular reference weight $\varphi_D$ used to build the Type II crossed-product core, and under the normalization of the canonical semifinite trace $\tau_D$. *Not merely under intra-core basis change.* This is the strong form of basis-independence the framework actually needs.
7. **Physical trace normalization.** $\tau_D$ must be normalized to physical units (Planck area or generalized-entropy nats) so that comparing $\log \tau_D(p)$ to $A/(4G\hbar) + S^{\rm ren}_{\rm matter}$ is meaningful. Setting the Haagerup convention $\mathrm{Tr}(h_\omega) = \omega(1)$ fixes the mathematical normalization but does *not* automatically match the trace unit to the holographic unit. This is part of the substantive holographic claim, not a mathematical nuisance.

**Current state.** A concrete candidate — the $\varepsilon$-smooth support volume of the Haagerup $L^1$ density on $\widehat{\mathcal{A}}(D)$ — secures intra-core basis-independence via Connes cocycle and Fack-Kosaki rearrangement. A *conditional* theorem then gives core-choice invariance modulo a normalization constant. **Open:** (i) the precise hypotheses under which the Connes cocycle preserves the full Haagerup $L^1$ structure (dual action + canonical trace + scaling condition), (ii) the physical normalization fixing $\tau_D$ in Planck-area units. See `paper_strategy/34`, `35`, `36`, `37`.

### 2.2 The admissible-history algebra $\mathcal{H}_{\rm adm}$

**What it must do.** Specify which formal decoherent histories count as *physically realizable* records.

**Required properties.**
1. **Closure.** Admissibility is *not* closed under union for individual histories — combining two separately admissible alternatives can exceed the total holographic branch budget (this is the branch-summed nature of the bound). The right object is therefore a Boolean *subalgebra* of histories jointly satisfying the bound on every nonzero event, with closure built into the membership condition.
2. **Dynamical selection.** Under unitary evolution restricted to $D$, $\mathcal{H}_{\rm adm}$ must evolve consistently — admissible histories at $t_1$ must give rise to admissible histories at $t_2 > t_1$ via the standard decoherent-histories class operators. *Maximal admissible subalgebras are non-unique;* the framework must therefore **derive (rather than parametrize) the physically realized admissible Boolean subalgebra from dynamics, decoherence, locality, or a variational principle**.
3. **Born compatibility.** The induced probability measure restricted to $\mathcal{H}_{\rm adm}$ must reduce to Born weights $|c_i|^2$ in regimes where the holographic bound is far from saturated.

**Current state.** The Boolean-subalgebra-of-histories formulation gives the right *kind* of object, and a log-sum-exp closure bound is available (loose, but useful). A candidate selection functional has been proposed:

$$
\mathcal{F}_t(B) = R_\eta(B) \cdot H_\omega(B) - \lambda C(B) - \kappa D_{\rm off}(B),
$$

where $R_\eta$ is Quantum-Darwinism redundancy, $H_\omega$ is Shannon entropy of atom weights, $C$ is a complexity penalty, and $D_{\rm off}$ measures decoherence failure. Maximizing instantaneously fails time-stability; a filtration-level variational principle over consistent history filtrations $B_{t_1} \hookrightarrow B_{t_2} \hookrightarrow \cdots$ is the proposed fix.

**Open sub-problems** (each independently nontrivial):
1. A preferred record algebra $\mathcal{R}_t$ — defining localized subsystems in QG is hard because of gauge constraints and gravitational dressing.
2. An environment-fragment decomposition for the redundancy term.
3. A complexity functional $C(B)$ — not basis- or model-independent.
4. A metric $d(B, B')$ on Boolean subalgebras — not unique.
5. An admissibility / refinement rule for filtrations.

Also: $R_\eta \cdot H$ is *invented* for this purpose, not a standard Quantum-Darwinism criterion. Darwinism emphasizes redundancy plateaus tied to pointer-state stability and the predictability sieve. Multiplying redundancy by Boolean entropy is plausible but not established.

**Bottom line:** the variational principle clarifies the *form* the answer should take, but delegates the actual selection to five sub-problems. See `paper_strategy/34`, `35`, `36`, `37`.

### 2.3 The per-record cost $c_R(r)$ and universal constant $I_0$

**What it must do.** Assign each record type $r$ an information cost $c_R(r)$ — the contribution that record makes to $I^\varepsilon_{\rm branch}(D)$. The empirical scale parameter $I_0$ is the typical cost for macroscopic records.

**Required properties.**
1. **Universality.** $I_0$ must be either a single universal constant or a small family with principled dependence on physical features of the record (mass, size, energy scale).
2. **Composition rule.** $c_R(r_1 \oplus r_2)$ for independent records must follow from $c_R(r_1)$ and $c_R(r_2)$ — additivity, subadditivity, or another principled law.
3. **Cross-experiment transferability.** $I_0$ calibrated on one experimental class must give correct predictions for another.

**Current state.** Schematic. Risks degenerating into a per-experiment fitting parameter, which would render the framework empirically empty.

### 2.4 The region prescription

**What it must do.** Specify which spacetime region $D$ the bound applies to for a given measurement.

**Candidate prescriptions** that the framework must choose among:
- Causal diamond of the measurement event (current working choice).
- The apparatus + environment region.
- The minimal enclosing screen of the macroscopic record.
- The environmental redundancy domain (where Quantum Darwinism makes the record objective).

**Required properties.**
1. **Covariance.** Two observers must agree on the region for the same physical measurement. *Covariance under diffeomorphisms is not uniqueness:* a causal diamond covaries with the observer worldline used to define it, but the choice of worldline is extra structure. The framework must either eliminate observer-worldline dependence or derive a unique worldline / region selection rule.
2. **Enlargement invariance.** Predictions must not change discontinuously when $D$ is replaced by a larger region $D' \supset D$ — only the bound becomes weaker. Exact enlargement invariance requires a Type II core factorization $\widehat{M}_{D'} \cong \widehat{M}_D \,\bar\otimes\, \widehat{M}_K$ which does not generically exist in AQFT.
3. **Surface prescription.** The codimension-two surface $\partial D$ entering $S_{\rm gen}$ must be specified — classical extremal, maximin, or quantum-extremal — and the framework's predictions must be robust under (or independent of) that choice. The current candidates are *not neutral*: different surface prescriptions define different regions and different bounds.

**Current state.** Causal diamond is the working candidate. A candidate observer-independent capacity has been proposed:

$$
C(R) = \inf_{D \supset R} S_{\rm gen}(\partial D),
$$

minimizing over causal diamonds containing the record-comparison events $R$.

**Concrete no-go (`paper_strategy/37`).** $S_{\rm gen}$ is **not monotone** under causal-diamond enlargement. *Counter-example:* let $R$ contain one half of $N$ entangled pairs, with the partners just outside. Then $S^{\rm ren}_{\rm matter}(R) \sim N\log 2$. Enlarging $R$ to $D$ that includes the partners drops the matter entropy near zero, while the area increases by $\Delta A$. If $N\log 2 > \Delta A/(4G\hbar)$:

$$
S_{\rm gen}(D) < S_{\rm gen}(R) \quad \text{even though } D \supset R.
$$

So $S_{\rm gen}$ can *decrease* under enlargement, and the capacity definition above is **not** well-defined as stated. **Required additional restrictions** on the diamond family (energy conditions, Bekenstein bound, quantum focusing, or the generalized second law along privileged horizons) must be specified before the capacity is operational.

**Open:** observer-worldline dependence (covariance ≠ uniqueness); the restricted-monotonicity setting that makes $C(R)$ well-defined; principled choice of holographic surface prescription. Without these the framework has relocated foliation dependence rather than eliminated it. See `paper_strategy/35`, `36`, `37`.

### 2.5 The physical state space

**What it must do.** Identify which mathematical objects represent the per-run wave function of the universe.

**Candidate structures.**
- A Hilbert subspace selected by an admissibility projector.
- A nonlinear submanifold of state space.
- A quotient of Hilbert space by an equivalence relation.
- A purely algebraic object (state on a $C^*$-algebra) with no Hilbert-space representative.

**Required properties.**
1. **Per-run / formal distinction.** Whatever the structure, the *per-run* wave function (one definite single-record state per experimental run) must be distinguished from the *formal* wave function (the ensemble descriptor of standard QM, with all branches present).
2. **Unitary evolution.** Whatever the structure, the evolution it inherits from the field algebra must be exactly Schrödinger/Heisenberg.

**Current state.** The position-paper claims ψ-monism plus finite-precision instantiation; the foundations paper uses the Type II algebra-state pair. These are compatible but not yet a single mathematically rigorous object.

---

## 3. Theorems and lemmas that need to be proved

### 3.1 Equivariance-like theorem (Born compatibility)

**Statement (target).** Given the QIQT-H admissibility rule, the conditional probabilities

$$
P(h \mid \mathcal{H}_{\rm adm}) \;=\; \frac{w(h)}{\sum_{h' \in \mathcal{H}_{\rm adm}} w(h')}, \qquad w(h) = D(h, h),
$$

reduce to ordinary Born weights $|c_i|^2$ in the regime $I^\varepsilon_{\rm branch}(D) \ll S_{\rm gen}(\partial D)$, with corrections of order $I^\varepsilon_{\rm branch}/S_{\rm gen}$.

**Two distinct requirements** — only the second is non-trivial:

1. **Non-binding regime consistency (trivial).** If no histories relevant to an experiment are excluded by the bound, then $\nu = \mu$ tautologically. This is a consistency observation, not a Born-compatibility theorem.

2. **Binding-regime quantification (hard).** Quantify the deviation $|\nu(h) - \mu(h)|$ when the bound *does* exclude histories. Show that for ordinary laboratory measurements this deviation is below experimental tolerance — i.e., that ordinary laboratory contexts actually lie in the non-binding regime. The framework needs *both* a deviation bound *and* a demonstration that lab measurements satisfy the non-binding criterion.

**Required input.** A precise definition of $\mathcal{H}_{\rm adm}$ (§2.2), a typicality measure on microscopic initial conditions, and a projective-consistency theorem ensuring admissibility-restricted measures form a coherent family over time.

**Analogy.** Bohmian mechanics has its $|\psi|^2$-equivariance theorem (Dürr-Goldstein-Zanghì). QIQT-H needs the structural analogue *plus* a quantitative deviation bound.

**Result so far (`paper_strategy/36`).** A clean measure-theoretic bound holds: if $\mu(A^c) \le \delta$, then $|\nu(h) - \mu(h)| \le \delta$ for $0 \le h \le 1$. A Markov bound then gives $\delta \le \mathbb{E}_\mu[I^\varepsilon_{\rm branch}(D)]/S_{\rm gen}(\partial D)$.

**Circularity warning (`paper_strategy/37`).** The numerical estimate $\delta \lesssim 10^{-24}$ for a 1-m region used a Bekenstein-style bound $I^\varepsilon_{\rm branch}(D) \le S_{\rm Bek}(E, R)$ as input. This bound is **not** an independent theorem: standard Bekenstein / Bousso bounds constrain thermodynamic / von Neumann entropy, not smooth-support counts of decoherent Everett-style branches in a Type II core. Smooth max-support quantities can be much larger than von Neumann entropy if many tiny-weight branches exist — *unless one adds constraints that are precisely the QIQT-H postulate*. So the argument as written is circular.

**Prerequisite theorem needed.** Prove an independent Bekenstein-style bound on smooth-support branch counts:

$$
I^\varepsilon_{\rm branch}(D) \le S_{\rm Bek}(E, R)
$$

that does *not* assume the QIQT-H postulate.

**Difficulty.** Major open problem. Without (2) and the prerequisite Bekenstein-on-branches theorem, the framework either reproduces Born statistics by assumption (circular) or contradicts experiment.

### 3.2 No-signaling theorem

**Statement (target).** Prove that

$$
P_{\rm QIQT}(a \mid x, y) \;=\; P_{\rm QIQT}(a \mid x)
$$

for all spacelike-separated settings $x, y$ and outcomes $a$ under QIQT-H admissibility conditioning. *Avoiding the specific form of Gisin's nonlinear-density-matrix mechanism is not sufficient* — global history-level admissibility is structurally similar to postselection, and postselection generically enables signaling unless protected by a precise locality / factorization theorem.

**Sufficient condition (candidate).** For Alice's record-comparison diamond $D_A$ and Bob's spacelike setting region, the admissibility predicate measurable in $M_{D_A}$ alone is independent of Bob's setting $y$:

$$
\mathbf{1}_{A_{x,y}}|_{D_A} = \mathbf{1}_{A_x}^{D_A}, \quad \text{independent of } y.
$$

This is the *causal screening theorem* the framework needs.

**Required input.** Definition of $\mathcal{H}_{\rm adm}$, its behaviour under spacelike-separated operations, and a factorization or conditional-expectation property of the admissibility weight across spacelike-separated regions.

**Result so far (`paper_strategy/36`).** A *sufficient* algebraic condition for no-signaling has been identified: if $K_{xy} = K_A^x \cdot K_B^y$ with $K_A^x \in \mathcal{A}_x$, $K_B^y \in \mathcal{B}_y$, $[\mathcal{A}_x, \mathcal{B}_y] = 0$, and there exists a $\mu$-preserving conditional expectation $E_A^{xy}: \mathcal{A}_x \vee \mathcal{B}_y \to \mathcal{A}_x$ satisfying $E_A^{xy}(K_B^y) = c_y \mathbf{1}$, then $P_{\rm QIQT}(a \mid x, y) = P_{\rm QIQT}(a \mid x)$.

**Concrete no-go (`paper_strategy/36`, `37`).** The naive **global formulation** $K_{xy} = \mathbf{1}\{I_A^x + I_B^y \le S_{AB}\}$ (single global $S_{\rm gen}$ budget shared across spacelike regions) **does not split**, because Alice and Bob compete for one entropy budget — Bob's choice $y$ alters Alice's available admissibility. The sufficient condition fails, and operational signaling can occur.

**Operational restriction.** The QIQT-H bound must therefore be applied *per causal-diamond region*, not as a single global cap. Locality requires either:
- **Tensor factorization** $\mathcal{A}(D_A \cup D_B) \cong \mathcal{A}(D_A) \,\bar\otimes\, \mathcal{A}(D_B)$ — rare in QFT (Type III algebras generally do not tensor-factorize across spacelike-separated regions), or
- **State-preserving conditional expectation** onto a local subalgebra — generically absent for entangled states, since such a map would force product-like structure inconsistent with entanglement.

**Difficulty.** Gisin's specific mechanism does not directly apply. But postselection-style signaling under global admissibility is a *real* threat with a concrete counter-example. The framework's formulation must be regionally local. See `paper_strategy/34`, `35`, `36`, `37`.

### 3.3 Concentration conjecture

**Statement (target).** Under unitary evolution with decoherent histories and the QIQT-H admissibility rule, generic regional states $\omega_\Psi$ on $\hat{\mathcal{A}}(D)$ dynamically concentrate on single-record states for $D$ containing a measurement apparatus and its environment.

**Required input.** §2.1, §2.2, and a measure of typicality over initial environment states.

**Status.** Conjecture in the foundations paper. The whole "per-run = single-record" claim rests on this.

### 3.4 Covariant formulation

**Statement (target).** There exists a Lorentz-covariant formulation of the bound that does not depend on an arbitrary time-slicing.

**Required input.** Region prescription (§2.4) given covariantly, e.g. as causal diamonds.

**Difficulty.** The current Type II construction is built on a reference state and modular flow; making this fully covariant rather than wedge-relative is non-trivial.

---

## 4. Compatibility requirements

Any formalism satisfying §2 and §3 must additionally satisfy the following constraints inherited from existing physics. These are not theorems to prove — they are *floors* the formalism must clear.

### 4.1 Standard-QM reduction

In the regime $I^\varepsilon_{\rm branch}(D) \ll S_{\rm gen}(\partial D)$ (ordinary laboratory measurements, where the holographic bound is operationally vacuous), all standard QM predictions must be recovered, including:
- Born probabilities $|c_i|^2$.
- Interference in regimes without macroscopic records.
- Standard CHSH violations up to $2\sqrt{2}$.
- Standard decoherence rates.

### 4.2 Generalized-entropy compatibility

The RHS of the bound must agree with the CPW/Witten generalized entropy *for the modes of the Type II crossed-product algebra*. The Branch-Summed reading is more restrictive than the bare CPW theorem — it must not contradict it.

### 4.3 No conflict with semiclassical gravity

In semiclassical regimes (black-hole thermodynamics, de Sitter horizon), QIQT-H must recover the generalized second law and the standard $S_{\rm gen}$ behaviour.

### 4.4 Continuum / infinite-DOF compatibility

The formalism must handle:
- Continuous-spectrum observables (position, momentum) without divergent branch counts.
- Type III local QFT algebras (where there is no density matrix).
- Tiny-amplitude branches (where naïve Rényi-0 is dominated by physically irrelevant tails).

The smooth-support parameter $\varepsilon$ is the candidate regulator, but its precise dependence on the physical regime is unspecified.

---

## 5. Quantitative / predictive desiderata

Without these the framework remains philosophy.

### 5.1 Exclusion curves

The framework must predict, for at least one concrete experimental class (matter-wave interferometry, macroscopic superposition tests, optomechanical systems), a *quantitative* visibility-loss curve as a function of system size / record content / region area.

**Required input.** A concrete value or scaling law for $I_0$ and a region prescription.

### 5.2 Threshold or crossover law

The boundary regime where $I^\varepsilon_{\rm branch}(D) \approx S_{\rm gen}(\partial D)$ must be specified:
- Sharp threshold (kinematic exclusion above the bound)?
- Smooth crossover (visibility decays continuously)?
- Stochastic crossover (jump probability scales with margin)?

GRW/CSL give explicit dynamical-collapse curves; QIQT-H must give its analogue.

### 5.3 Distinguishability from GRW/CSL

Concrete experimental signatures that distinguish QIQT-H from objective-collapse theories must be identified. Candidates flagged in the position paper:
- Bulk heating (predicted by CSL, absent in QIQT-H).
- Spontaneous radiation / diffusion (CSL: yes; QIQT-H: no).
- Sharp vs. smooth visibility loss.

Each needs a calculation, not just a slogan.

### 5.4 Bell-correlation reproduction

The framework must reproduce the $2\sqrt{2}$ CHSH violation quantitatively while denying measurement independence in a non-conspiratorial way.

**Required input.** A specification of how the global record-admissibility constraint produces the correlations without invoking hidden variables sampled non-independently.

**Difficulty.** Hard. This is where any "denial of measurement independence" theory must do real work.

---

## 6. Priority ranking

By difficulty × impact, ordered from foundational to refinement:

| Rank | Item | Foundational? |
|---|---|---|
| 1 | §3.1(2) Binding-regime Born deviation bound + lab non-binding proof | Yes — non-binding regime is tautological; the real theorem is here |
| 2 | §2.2 Dynamical selection law for admissible Boolean subalgebra | Yes — prerequisite for (1); current scaffolding parametrizes but does not derive |
| 3 | §2.1 Core-choice invariance of $I^\varepsilon_{\rm branch}$ | Yes — prerequisite for (2); intra-core invariance solved, cross-reference still open |
| 4 | §3.2 Causal screening theorem (real no-signaling) | Yes — Gisin avoidance is not no-signaling |
| 5 | §2.4 Region prescription + worldline/surface dependence | Yes — covariance ≠ uniqueness; foliation dependence still hidden |
| 6 | §5.1–5.2 Concrete exclusion / threshold predictions | High — empirical content |
| 7 | §2.3 $I_0$ universality and composition | High — empirical falsifiability |
| 8 | §3.3 Concentration conjecture | High — single-outcome experience |
| 9 | §3.4 Lorentz covariance | Important — relativistic consistency |
| 10 | §5.4 Bell correlations quantitatively | Important — confrontation with experiment |
| 11 | §5.3 GRW/CSL discrimination | Important — empirical individuation |
| 12 | §2.5 State-space precision | Foundational hygiene |

Items 1-5 are blockers. Until they are resolved the rest cannot be addressed rigorously.

**Status after four passes** (`paper_strategy/34`–`37`):

| Item | Result |
|---|---|
| §2.1 | *Conditional theorem* — Connes cocycle preserves $N^\varepsilon_{\rm eff}$ modulo trace-normalization constant; physical Planck-area normalization open. |
| §2.2 | *Candidate variational principle* (Darwinism redundancy × Shannon − complexity − decoherence failure) over consistent history filtrations. Delegates to 5 sub-problems. |
| §3.1(2) | *Measure-theoretic bound* $|\nu - \mu| \le \delta$ proved; numerical lab-scale estimate circular without independent Bekenstein-on-branches theorem. |
| §3.2 | *Sufficient condition* identified + *concrete counter-example*: global $I_A + I_B \le S_{AB}$ formulation violates no-signaling. Bound must be regionally local. |
| §2.4 | *Concrete no-go*: $S_{\rm gen}$ not monotone under causal-diamond enlargement (entangled-pair counter-example); minimal-diamond capacity not well-defined without restrictions. |

**Net.** Two valid conditional theorems (§2.1, §3.1(2)). Two concrete no-go results (§2.4, §3.2). One candidate variational principle delegated to sub-problems (§2.2). The framework now has *real* technical constraints — not just "needs more work" labels. Some formulations have been *ruled out* (single global budget; naive capacity infimum). The framework is closer to evaluable as a research program; it is not yet a completed mathematical foundation.

---

## 7. What is *not* missing

For honesty, the following are *already in place* and do not need to be developed:

- Type III local QFT algebras (Buchholz, Wichmann, Borchers, Longo — rigorous).
- Tomita-Takesaki modular theory (rigorous).
- CPW/Witten crossed-product construction giving Type II$_\infty$ continuous core (rigorous, 2022).
- Generalized entropy $S_{\rm gen} = A/(4G\hbar) + S^{\rm ren}_{\rm matter}$ as semiclassical expression (well-established).
- Decoherence (Joos-Zeh) and einselection (Zurek) (established).
- Decoherent histories framework (Griffiths, Gell-Mann/Hartle, Omnès).
- Bekenstein-Bousso holographic bound on entropy (well-established as inequality).
- Algebraic relative entropy via Araki / Connes cocycle (rigorous, finite for Type III directly).

The borrowed mathematics is solid. The new mathematics — items §2-§5 above — is what is missing.

---

## Notes on scope

This document covers the *minimal mathematics that must exist before QIQT-H can be evaluated as a physical theory*. It is intentionally not a research agenda for any one author. Different items may require:

- Mathematical physics work (algebraic QFT, modular theory): §2.1, §3.4.
- Foundations work (typicality, Born-rule derivation, Bell): §3.1, §3.2, §5.4.
- Phenomenology (calibrate $I_0$, design exclusion experiments): §2.3, §5.1, §5.2, §5.3.

The natural collaboration boundary cuts across these.
