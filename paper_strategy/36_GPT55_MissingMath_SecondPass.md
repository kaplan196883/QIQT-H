# GPT-5.5 Second-Pass Attempted Constructions for Sharpened QIQT-H Blockers

**Date:** 2026-05-27
**Source:** GPT-5.5 (high reasoning), second attempt after self-review (doc 35).
**Verdict:** Substantively better than the first pass. Concrete results on §2.1 (clean conditional invariance theorem + isolated obstruction), §3.1(2) (real $|\nu - \mu| \le \delta$ deviation bound), and §3.2 (algebraic factorization condition for no-signaling with counter-example for global constraints). §2.2 and §2.4 remain partial but now propose specific candidate selection laws.

## Summary of progress per blocker

| Blocker | First-pass status | Second-pass status |
|---|---|---|
| §2.1 Core-choice invariance | Partial (intra-core only) | **Conditional theorem proved**: invariance holds modulo trace-normalization constant $c$. Obstruction isolated to canonical-Haar/trace normalization. |
| §2.2 Dynamical selection | Right object, no selection rule | **Candidate selection functional written explicitly** (Darwinism redundancy × Shannon − complexity − decoherence-failure). Time-stability fails; modification: history-level filtration variational principle. |
| §3.1(2) Binding deviation | Tautological | **Real bound proved**: $|\nu(h) - \mu(h)| \le \delta = \mu(A^c)$, plus Markov bound $\delta \le \mathbb{E}_\mu[I^\varepsilon]/S_{\rm gen}$, plus numerical lab-scale estimate $\delta \lesssim 10^{-24}$. |
| §3.2 Causal screening | Gisin avoidance only | **Sufficient algebraic condition stated**: $K_{xy} = K_A^x K_B^y$ with conditional-expectation property $E_A(K_B^y) = c_y \mathbf{1}$. Explicit counter-example (global $I_A + I_B \le S_{AB}$) where no-signaling fails. |
| §2.4 Worldline / region | Schematic | **Two candidates evaluated**: observer-relative diamonds (consistent but explicitly relational) vs. minimal-diamond capacity $C(R) = \inf_{D \supset R} S_{\rm gen}(\partial D)$ (observer-independent, monotone under inclusion). |

---

## §2.1 — Core-choice invariance: conditional theorem

### Setup

Let $M = M_D$, faithful normal semifinite weights $\varphi, \psi$. Form

$$
\widehat{M}_\varphi = M \rtimes_{\sigma^\varphi} \mathbb{R}, \qquad \widehat{M}_\psi = M \rtimes_{\sigma^\psi} \mathbb{R}.
$$

Connes cocycle isomorphism:

$$
\Theta_{\psi\varphi}: \widehat{M}_\varphi \to \widehat{M}_\psi, \quad \Theta(\pi_\varphi(x)) = \pi_\psi(x), \quad \Theta(\lambda_\varphi(t)) = \pi_\psi([D\varphi:D\psi]_t) \lambda_\psi(t).
$$

### Lemma (Haagerup density transforms)

For per-run state $\omega_{\Psi,D}$,

$$
h^\psi_{\Psi,D} = \Theta_{\psi\varphi}(h^\varphi_{\Psi,D}).
$$

*Proof.* For $x \in M_+$:

$$
\tau_\psi(\Theta(h^\varphi_{\Psi,D}) \pi_\psi(x)) = \tau_\varphi(h^\varphi_{\Psi,D} \pi_\varphi(x)) = \omega_{\Psi,D}(x).
$$

By uniqueness of the Haagerup $L^1$ density.

### Theorem (conditional core-choice invariance)

If $\tau_\psi \circ \Theta_{\psi\varphi} = \tau_\varphi$ (canonical Haar normalization), then

$$
N^\varepsilon_{\rm eff, \psi}(\omega) = N^\varepsilon_{\rm eff, \varphi}(\omega).
$$

*Proof.* Under $e \mapsto \Theta(e)$:

$$
\tau_\psi(\Theta(e)) = \tau_\varphi(e), \quad \tau_\psi(h^\psi_\omega \Theta(e)) = \tau_\varphi(h^\varphi_\omega e).
$$

Feasible sets are bijected, objective preserved.

### Isolated obstruction

If trace normalization satisfies $\tau_\psi \circ \Theta_{\psi\varphi} = c \cdot \tau_\varphi$ for some $c \ne 1$, then

$$
N^\varepsilon_{\rm eff, \psi} = c \cdot N^\varepsilon_{\rm eff, \varphi}, \quad I^\varepsilon_{\rm branch, \psi} = I^\varepsilon_{\rm branch, \varphi} + \log c.
$$

**Absolute invariance requires either canonical trace normalization or defining only dimensionless ratios.**

This isolates the remaining obstruction to a single normalization constant. The earlier worry — that core-choice invariance might be deep — is resolved. The remaining issue is mundane: pick a canonical Haar normalization (or work with ratios).

---

## §2.2 — Candidate dynamical selection functional

### Proposed functional

For a Boolean subalgebra $B \subset \mathrm{Proj}(\mathcal{R}_t)$ of the record algebra at time $t$:

$$
\mathcal{F}_t(B) = R_\eta(B, t) \cdot H_\omega(B) - \lambda C(B) - \kappa D_{\rm off}(B, t).
$$

Where:
- $H_\omega(B)$ = Shannon entropy of atom weights
- $R_\eta(B, t)$ = **redundancy** (Quantum Darwinism): maximal disjoint environment fragments $F_i$ with $I_\omega(B : F_i) \ge (1-\eta) H_\omega(B)$
- $C(B)$ = complexity penalty preventing arbitrary refinement
- $D_{\rm off}(B, t) = \sum_{p \ne q \in \mathrm{At}(B)} \frac{|\omega(pAq)|^2}{\omega(p)\omega(q)}$ = decoherence failure

Selection:

$$
B_t^{\rm sel} \in \arg\max_{B \in \mathfrak{B}_t^{\rm adm}} \mathcal{F}_t(B),
$$

subject to the QIQT entropy constraint $I^\varepsilon_{\rm branch}(B, D_t) \le S_{\rm gen}(\partial D_t)$.

### Failure of instantaneous time stability

Coarse $B_{t_1}$ records a measurement. By $t_2 > t_1$, sub-outcomes amplified inside one atom give a refinement $B'_{t_2} \succ \alpha_{t_2, t_1}(B_{t_1})$ with higher redundancy and higher $\mathcal{F}_{t_2}$.

The maximizer at $t_1$ need not remain maximizing at $t_2$.

### Proposed fix: filtration-level variational principle

Maximize over *consistent history filtrations* $B_{t_1} \hookrightarrow B_{t_2} \hookrightarrow \cdots$:

$$
\mathcal{A}(\{B_t\}) = \int_{t_0}^{t_1} \mathcal{F}_t(B_t) \, dt - \rho \int_{t_0}^{t_1} d(B_{t+dt}, \alpha_{t+dt, t}(B_t))^2 \, dt.
$$

Second term penalizes failure of Heisenberg persistence. Then:

$$
\{B_t^{\rm sel}\} \in \arg\max_{\text{consistent histories}} \mathcal{A}(\{B_t\}).
$$

Earlier selected records persist as coarse-grainings of later records — *the right kind of structure*.

### Additional structure still required

1. Preferred record algebra $\mathcal{R}_t$
2. Environment-fragment decomposition for redundancy
3. Complexity functional $C(B)$
4. Metric $d(B, B')$ on Boolean subalgebras
5. Refinement admissibility rule

Without these, §2.2 remains underdetermined. **But the structure of the answer is now sharp: a maximum-action filtration of Boolean record-subalgebras, not an instantaneous projection condition.**

---

## §3.1(2) — Binding-regime deviation bound: real theorem

### Theorem

Let $\mu$ be the Born measure, $A$ the admissible set, $\nu(E) = \mu(E \mid A)$. Suppose $\mu(A^c) \le \delta$. Then for any event $E$:

$$
|\nu(E) - \mu(E)| \le \delta.
$$

For bounded observables $0 \le h \le 1$, $|\nu(h) - \mu(h)| \le \delta$. For $|h| \le 1$, $|\nu(h) - \mu(h)| \le 2\delta$.

*Proof.* Let $q = \mu(A^c)$, $p = 1 - q$.

$$
\nu(E) - \mu(E) = \frac{\mu(E \cap A)}{p} - \mu(E) = \frac{q}{p}\mu(E \cap A) - \mu(E \cap A^c).
$$

First term in $[0, q]$, second in $[0, q]$. Absolute difference $\le q \le \delta$. ∎

### Markov bound on $\delta$

Admissibility = $\{I^\varepsilon_{\rm branch}(D) \le S_{\rm gen}(\partial D)\}$:

$$
\delta \le \frac{\mathbb{E}_\mu[I^\varepsilon_{\rm branch}(D)]}{S_{\rm gen}(\partial D)}.
$$

### Lab-scale numerical estimate

For $R \sim 1\,\mathrm{m}$:

$$
S_{\rm gen}(\partial D) \sim \frac{A}{4\ell_P^2} \sim 10^{70}\,\text{nats}.
$$

Bekenstein bound on physical content for $E \sim 10^3\,\mathrm{kg}\,c^2$:

$$
I^\varepsilon_{\rm branch}(D) \lesssim S_{\rm Bek} \le \frac{2\pi E R}{\hbar c} \sim 10^{46}.
$$

Therefore

$$
\delta \lesssim 10^{-24}.
$$

**QIQT deviations from Born probabilities at lab scale are bounded by $\sim 10^{-24}$ — operationally invisible.**

### Caveat

Rigorous lab-non-binding proof requires a theorem of the form

$$
I^\varepsilon_{\rm branch}(D) \le S_{\rm max}(E, R)
$$

where $S_{\rm max}$ is a Bekenstein/holographic entropy bound for the physical degrees of freedom in $D$. Without an energy cutoff or entropy bound, local QFT has infinitely many formal degrees of freedom, and the lab non-binding claim is not yet fully rigorous.

But the *deviation* theorem is solid, and the heuristic numerical estimate is overwhelming.

---

## §3.2 — Causal screening: sufficient condition + counter-example

### Setup

$D_A, D_B$ spacelike. Alice outcome projection $P_a^x \in \mathcal{A}_x$, Bob setting $y$, admissibility predicate $K_{xy}$.

$$
P_{\rm QIQT}(a \mid x, y) = \frac{\mu_{xy}(P_a^x K_{xy})}{\mu_{xy}(K_{xy})}.
$$

### Sufficient condition for no-signaling

If

$$
K_{xy} = K_A^x \cdot K_B^y, \quad K_A^x \in \mathcal{A}_x, \quad K_B^y \in \mathcal{B}_y, \quad [\mathcal{A}_x, \mathcal{B}_y] = 0,
$$

and there exists a $\mu_{xy}$-preserving conditional expectation $E_A^{xy}: \mathcal{A}_x \vee \mathcal{B}_y \to \mathcal{A}_x$ with

$$
E_A^{xy}(K_B^y) = c_y \cdot \mathbf{1},
$$

then

$$
P_{\rm QIQT}(a \mid x, y) = \frac{\mu_{xy}(P_a^x K_A^x)}{\mu_{xy}(K_A^x)},
$$

independent of $y$. No-signaling holds.

*Proof.*

$$
\mu_{xy}(P_a^x K_A^x K_B^y) = \mu_{xy}(P_a^x K_A^x E_A(K_B^y)) = c_y \mu_{xy}(P_a^x K_A^x),
$$

and $\mu_{xy}(K_A^x K_B^y) = c_y \mu_{xy}(K_A^x)$. ∎

### Critical caveat

Mere factorization $K_{xy} = K_A^x K_B^y$ is **not enough**. If $K_B^y$ is correlated with Alice's outcome, conditioning on it signals.

*Example.* Singlet state, postselecting Bob's $+$ outcome changes Alice's conditional distribution.

The needed condition is *statistical screening*: $E_A^{xy}(K_B^y) = c_y \mathbf{1}$.

### When does the predicate split?

**Splits (no-signaling holds):** local admissibility imposed separately,

$$
K_{xy} = \mathbf{1}\{I_A^x \le S_A\} \cdot \mathbf{1}\{I_B^y \le S_B\}.
$$

**Does not split (signaling possible):** global constraint,

$$
K_{xy} = \mathbf{1}\{I_A^x + I_B^y \le S_{AB}\},
$$

because Alice and Bob compete for one entropy budget.

### Two clean regimes for no-signaling

1. **Non-binding regime**: $K_{xy} = 1$.
2. **Screened local-binding regime**: $K_{xy} = K_A^x K_B^y$ with screening property.

**Without such screening, QIQT conditioning can produce operational signaling.** This is a precise warning about how the framework must be formulated: globally branch-summed constraints (one entropy budget shared across all measurements in the universe) violate no-signaling. The bound must be applied *per region*, not globally.

---

## §2.4 — Region prescription: two evaluated candidates

### Option (i): Observer-relative diamonds

$$
P_\gamma(h) = P(h \mid I^\varepsilon_{\rm branch}(D_\gamma) \le S_{\rm gen}(\partial D_\gamma)).
$$

Different observers may assign different conditional probabilities. Internally consistent if worldline is part of the physical setup. But QIQT becomes explicitly relational; the same record-comparison receives different admissibility judgments from different observers.

If $S_{\rm gen}$ grows under enlargement, a larger observer diamond can weaken or remove constraints. Objective Born deviations become ambiguous.

### Option (ii): Minimal causal diamond for the record-comparison

Let $R$ be the set of record-comparison events. Define observer-independent capacity:

$$
C(R) = \inf_{D \supset R} S_{\rm gen}(\partial D).
$$

Impose $I^\varepsilon_{\rm branch}(R) \le C(R)$.

**Monotonicity property**: $R \subset R'$ implies the diamond-set for $R'$ is smaller, so

$$
C(R') \ge C(R).
$$

Adding record-comparison events cannot lower the entropy budget.

### Verdict

If QIQT wants observer-independent probabilities, **option (ii) with $C(R) = \inf_{D \supset R} S_{\rm gen}(\partial D)$ is the cleaner prescription**. Option (i) is viable only if the theory is explicitly observer-relative.

This resolves §2.4 in favour of (ii) and gives a precise formula. The remaining open question is whether $S_{\rm gen}$ is genuinely monotone under causal-diamond enlargement; if it is, the infimum reduces to the *minimal causal diamond containing $R$*.

---

## Updated status

After the second-pass attempt:

| Blocker | Status |
|---|---|
| §2.1 Core-choice invariance | **Conditionally proved** (modulo trace normalization constant); reduces to picking canonical Haar |
| §2.2 Dynamical selection | **Candidate functional written** + filtration-level fix proposed; 5 additional structure items needed |
| §3.1(2) Binding deviation | **Theorem proved** ($|\nu - \mu| \le \delta$); lab-scale numerical estimate $\delta \lesssim 10^{-24}$; rigorous lab-non-binding still needs $S_{\rm Bek}$-type theorem |
| §3.2 Causal screening | **Sufficient algebraic condition proved**; explicit counter-example shows globally-branch-summed formulation fails no-signaling; the bound must be regionally local |
| §2.4 Region prescription | **Candidate (ii) selected** with monotonicity; observer-independent capacity formula given |

**The most consequential finding**: §3.2 implies that the QIQT-H bound, as stated in earlier docs as a *single global Branch-Summed bound* over all regions, would violate no-signaling. The framework must be reformulated so admissibility is imposed *per region* (or per spacelike-separated diamond), not globally. This is a real constraint on the framework's content, not just a technical detail.

The framework now has:
- One proved theorem in the right direction (§3.1(2))
- One conditional theorem with isolated obstruction (§2.1)
- One sufficient algebraic condition with a counter-example showing why global formulations fail (§3.2)
- One sharp selection ansatz (§2.4)
- One candidate variational principle for dynamical selection (§2.2)

This is substantively more than first-pass output.
