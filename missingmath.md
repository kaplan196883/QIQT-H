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

**Current state.** Schematic. Defined as "smoothed support entropy" without a basis-independent, coarse-graining-stable formula.

### 2.2 The admissible-history algebra $\mathcal{H}_{\rm adm}$

**What it must do.** Specify which formal decoherent histories count as *physically realizable* records.

**Required properties.**
1. **Closure.** $\mathcal{H}_{\rm adm}$ must be closed under the decoherent-histories sum-rule operations: if $h_1, h_2 \in \mathcal{H}_{\rm adm}$ and they are mutually exclusive in the medium-decoherence sense, then their coarse-grained union is in $\mathcal{H}_{\rm adm}$.
2. **Dynamical stability.** Under unitary evolution restricted to $D$, $\mathcal{H}_{\rm adm}$ must evolve consistently — admissible histories at $t_1$ must give rise to admissible histories at $t_2 > t_1$ via the standard decoherent-histories class operators.
3. **Born compatibility.** The induced probability measure restricted to $\mathcal{H}_{\rm adm}$ must reduce to Born weights $|c_i|^2$ in regimes where the holographic bound is far from saturated.

**Current state.** Underdetermined. The framework states the bound $I^\varepsilon_{\rm branch}(D) \le S_{\rm gen}(\partial D)$ but does not specify *which* of the formal decoherent histories are removed when the bound is approached.

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
- Causal diamond of the measurement event.
- The apparatus + environment region.
- The minimal enclosing screen of the macroscopic record.
- The environmental redundancy domain (where Quantum Darwinism makes the record objective).

**Required properties.**
1. **Covariance.** Two observers must agree on the region for the same physical measurement.
2. **Enlargement invariance.** Predictions must not change discontinuously when $D$ is replaced by a larger region $D' \supset D$ — only the bound becomes weaker.

**Current state.** Not specified. The bound $S_{\rm gen}(\partial D)$ depends on the chosen $D$; the framework needs a principled choice.

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

**Required input.** A precise definition of $\mathcal{H}_{\rm adm}$ (§2.2) and a typicality measure on microscopic initial conditions.

**Analogy.** Bohmian mechanics has its $|\psi|^2$-equivariance theorem (Dürr-Goldstein-Zanghì). QIQT-H needs the structural analogue.

**Difficulty.** Major open problem. Without this theorem, the framework either reproduces Born statistics by assumption (circular) or contradicts experiment.

### 3.2 No-signaling theorem

**Statement (target).** The renormalized conditional probabilities introduced by the admissibility constraint do not allow superluminal signaling.

**Required input.** Definition of $\mathcal{H}_{\rm adm}$ and its behaviour under spacelike-separated operations.

**Difficulty.** Nonlinear modifications of QM generically allow superluminal signaling unless carefully constrained (Gisin 1990). This theorem must rule that out.

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
| 1 | §3.1 Equivariance / Born compatibility theorem | Yes — without it the framework is either circular or contradicts experiment |
| 2 | §2.2 Precise definition of $\mathcal{H}_{\rm adm}$ | Yes — prerequisite for (1) |
| 3 | §2.1 Basis-independent $I^\varepsilon_{\rm branch}$ | Yes — prerequisite for (2) |
| 4 | §3.2 No-signaling theorem | Yes — relativistic consistency |
| 5 | §2.4 Region prescription | Yes — prerequisite for any quantitative claim |
| 6 | §5.1–5.2 Concrete exclusion / threshold predictions | High — empirical content |
| 7 | §2.3 $I_0$ universality and composition | High — empirical falsifiability |
| 8 | §3.3 Concentration conjecture | High — single-outcome experience |
| 9 | §3.4 Lorentz covariance | Important — relativistic consistency |
| 10 | §5.4 Bell correlations quantitatively | Important — confrontation with experiment |
| 11 | §5.3 GRW/CSL discrimination | Important — empirical individuation |
| 12 | §2.5 State-space precision | Foundational hygiene |

Items 1-5 are blockers. Until they are resolved the rest cannot be addressed rigorously.

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
