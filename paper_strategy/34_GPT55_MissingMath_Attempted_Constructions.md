# GPT-5.5 Attempted Constructions for QIQT-H Missing Math (Blockers §2.1, §2.2, §2.4, §3.1, §3.2)

**Date:** 2026-05-27
**Source:** GPT-5.5 (high reasoning), responding to `missingmath.md` priority blockers.
**Verdict:** Substantive technical attempts, not philosophy. Honest about what remains open. Three central open obstructions identified.

## Summary of central obstructions identified by GPT-5.5

1. **§2.1 — Branch information.** Basis-independence is *solved* by the Type II crossed-product core construction with Haagerup $L^1$ densities and Fack-Kosaki rearrangement. The obstruction is *physical matching* between the Type II trace volume and the generalized-entropy area unit (the $N_0(D)$ normalization).

2. **§2.2 — Admissibility.** Single-history admissibility is not closed under union (the *branch-summed* nature of the bound). The right object is a Boolean subalgebra of histories, jointly admissible. The central open obstruction: *construct a dynamical law selecting a projectively consistent admissible decoherent history algebra.*

3. **§2.4 — Region prescription.** The causal-diamond proposal is preferable to all four alternatives in the doc on covariance + record-locality + screen-finiteness grounds. But *exact enlargement invariance is not proved* — the required factorization theorem for Type II crossed-product cores is missing.

4. **§3.1 — Equivariance.** The *non-binding regime* Born theorem is immediate (proof in one line: $A^\Psi = \Omega$ implies $\nu = \mu$). The *binding regime* central open obstruction: *prove that admissibility-restricted Born measures form a projectively consistent family of history measures.*

5. **§3.2 — No-signaling.** Good news: QIQT-H does *not* directly trigger Gisin's nonlinear-reduced-density-matrix mechanism, because admissibility operates on whole histories, not on instantaneous states. Bad news: history-level admissibility can still signal via *global postselection*. Central open obstruction: *prove a causal screening theorem* — that admissibility weight has no setting-dependent effect on spacelike local marginals.

---

## §2.1 — Basis-independent $I^\varepsilon_{\rm branch}(D)$ — concrete construction

### Core construction

Let $M_D = \mathcal{A}(D)$ be the Type III local algebra. Choose a faithful normal semifinite reference weight $\varphi_D$ on $M_D$. Form the crossed-product core

$$
\widehat{M}_D := M_D \rtimes_{\sigma^{\varphi_D}} \mathbb{R},
$$

with canonical faithful normal semifinite trace $\tau_D$.

Independence of the reference weight: Connes' cocycle gives the canonical core isomorphism

$$
\Theta_{\psi\varphi}: M_D \rtimes_{\sigma^{\varphi_D}} \mathbb{R} \longrightarrow M_D \rtimes_{\sigma^{\psi_D}} \mathbb{R}
$$

with $\Theta_{\psi\varphi}(x) = x$ for $x \in M_D$ and $\Theta_{\psi\varphi}(\lambda_\varphi(t)) = [D\psi_D : D\varphi_D]_t \, \lambda_\psi(t)$. This transports the canonical trace: $\tau_{\psi,D} \circ \Theta_{\psi\varphi} = \tau_{\varphi,D}$.

The per-run regional state $\omega_{\Psi,D}$ has a Haagerup $L^1$ density $h_{\Psi,D} \in L^1(\widehat{M}_D, \tau_D)_+$ with $\tau_D(h_{\Psi,D}) = 1$.

### Smooth support size

For a projection $p \in \mathrm{Proj}(\widehat{M}_D)$, the trace volume is $\tau_D(p)$ and the mass in the per-run state is $\widehat{\omega}_{\Psi,D}(p) = \tau_D(p h_{\Psi,D})$.

Define the **$\varepsilon$-smooth effective support size**:

$$
N^\varepsilon_{\rm eff}(D; \Psi) := \inf\{ \tau_D(p) : p \in \mathrm{Proj}(\widehat{M}_D),\ \widehat{\omega}_{\Psi,D}(p) \ge 1 - \varepsilon \}.
$$

Then

$$
I^\varepsilon_{\rm branch}(D; \Psi) := \log N^\varepsilon_{\rm eff}(D; \Psi).
$$

### Continuous-spectrum formulation

Using the Fack-Kosaki generalized singular values $\mu_t(h_{\Psi,D})$:

$$
N^\varepsilon_{\rm eff}(D; \Psi) = \inf\left\{ t \ge 0 : \int_0^t \mu_s(h_{\Psi,D}) \, ds \ge 1 - \varepsilon \right\}.
$$

This expression is basis-independent and handles continuous spectra directly via the noncommutative Hardy-Littlewood / Fack-Kosaki formula.

### Finite-dim check

For $M_D = B(\mathcal{H})$ and $\rho_\Psi = \sum_i p_i |i\rangle\langle i|$ with $p_1 \ge p_2 \ge \ldots$:

$$
N^\varepsilon_{\rm eff} = \min\left\{ k : \sum_{i=1}^k p_i \ge 1 - \varepsilon \right\}.
$$

For equal-weight superposition over $N$ alternatives, $I^0_{\rm branch} = \log N$. The definition reduces to literal branch counting in the ideal discrete equal-weight case.

### Basis independence proof

Definition depends only on the triple $(\widehat{M}_D, \tau_D, h_{\Psi,D})$. Trace-preserving isomorphism preserves projections bijectively with their traces, and preserves mass evaluations. Hence $N^\varepsilon_{\rm eff}$ is invariant under trace-preserving algebra isomorphism.

### What remains schematic

1. **Local algebra in QG.** Quantum-gravity AQFT for finite causal diamonds is not fully constructed.
2. **Trace normalization $N_0(D)$.** Comparing $\log\tau_D(p)$ to $A/(4G\hbar)$ requires a fixed physical trace unit, not yet derived.
3. **State-lifting theorem.** Connecting decoherent records to finite-$\tau_D$ projections needs a precise theorem.
4. **Renormalized matter entropy compatibility.** $S^{\rm ren}_{\rm matter}$ must match the renormalization absorbed in the Type II core.
5. **Monotonicity under inclusion.** $D_1 \subset D_2$ implies useful monotonicity — not currently proved.

**The central obstruction in §2.1 is physical matching between Type II trace volume and the generalized-entropy area unit, not basis dependence.**

---

## §2.2 — Admissibility algebra $\mathcal{H}_{\rm adm}$ — candidate construction

### Conditioning on a history

For decoherent-histories class operator $C_E$ and initial state $\omega_0$:

$$
\omega_E(a) = \frac{\omega_0(C_E^* a C_E)}{\omega_0(C_E^* C_E)}.
$$

Restrict to $M_D$ and compute $I^\varepsilon_{\rm branch}(D; \omega_E)$ via §2.1.

Admissibility predicate (single region):

$$
\mathrm{Adm}_\varepsilon(E; D) \iff I^\varepsilon_{\rm branch}(D; \omega_E) \le S_{\rm gen}(\partial D; \omega_E).
$$

For multiple comparison regions $D \in \mathscr{D}(E)$, require admissibility at all of them.

### Closure under medium-decoherent unions

For disjoint $E, F$ with $\omega_0(C_F^* C_E) = 0$ and the stronger local condition $\omega_0(C_E^* a C_F) = 0$ for $a \in M_D$:

$$
\omega_{E \vee F, D} = q_E \omega_{E,D} + q_F \omega_{F,D}.
$$

Then **log-sum-exp closure bound**:

$$
I^{q_E\varepsilon_E + q_F\varepsilon_F}_{\rm branch}(D; \omega_{E \vee F}) \le \log\left( e^{I^{\varepsilon_E}_{\rm branch}(D; \omega_E)} + e^{I^{\varepsilon_F}_{\rm branch}(D; \omega_F)} \right).
$$

For finite disjoint unions:

$$
N^{\sum_i q_i \varepsilon_i}_{\rm eff}(D; \omega_U) \le \sum_i N^{\varepsilon_i}_{\rm eff}(D; \omega_{E_i}).
$$

### Why raw admissibility is not closed

If both $E$ and $F$ saturate the bound individually, their union generically violates it by up to $\log 2$. The **branch-summed nature of the bound** is exactly this: combining two separately admissible alternatives can exceed the total holographic branch budget.

### Candidate admissibility algebra

Correct object: a **Boolean subalgebra** $\mathfrak{B}_{\rm adm} \subseteq \mathfrak{B}$ of a medium-decoherent history algebra, such that for every nonzero $E \in \mathfrak{B}_{\rm adm}$ and every $D \in \mathscr{D}(E)$,

$$
I^\varepsilon_{\rm branch}(D; \omega_E) \le S_{\rm gen}(\partial D; \omega_E).
$$

Maximal such subalgebras exist by Zorn (modulo a normality/lower-semicontinuity argument for chain unions).

**Key insight**: QIQT-H admissibility should be imposed on decoherent **Boolean algebras** of histories, not only on single histories.

### Open problems

1. **Nonuniqueness** of maximal admissible subalgebras.
2. **Time extension** can invalidate previously-admissible coarse histories.
3. **Refinement instability** — coarse may be admissible while fine-graining is not.
4. **Approximate decoherence** — quantitative tolerances needed in closure estimates.
5. **Backreaction of conditioning** on $S_{\rm gen}$.

**Central open obstruction in §2.2: construct a dynamical law selecting a projectively consistent admissible decoherent history algebra.**

---

## §2.4 — Region prescription — causal diamond proposal

### Proposed prescription

For a record-comparison process by observer worldline $\gamma$ over proper-time interval $[\tau_-, \tau_+]$:

$$
D_{\gamma, [\tau_-, \tau_+]} := J^+(\gamma(\tau_-)) \cap J^-(\gamma(\tau_+)).
$$

Generalized entropy surface determined by the diamond boundary, optionally via a maximin or quantum-extremal-cut prescription:

$$
S_{\rm gen}(\partial D) := \inf_{\sigma \in \mathrm{Cuts}(\partial D)} \left[ \frac{A(\sigma)}{4G\hbar} + S^{\rm ren}_{\rm matter}(\sigma) \right].
$$

### Why the causal diamond beats alternatives

| Candidate | Problem |
|---|---|
| Entire Cauchy slice | Gauge/slicing dependent; spacelike inaccessible records; infinite $S_{\rm gen}$ |
| Instantaneous lab volume | Frame-dependent; not causally complete |
| Future light cone | Includes events after comparison; admissibility depends on future branches |
| QES region | Requires holographic dual; usually unavailable in cosmology; circularity risk |

Causal diamond is the smallest region with: record-local + causally complete + covariant + finite-screen.

### Covariance — solid

For diffeomorphism $f$ with covariant net $\alpha_f(\mathcal{A}(D)) = \mathcal{A}(fD)$, the crossed-product core is functorial, $\tau_{fD} \circ \widehat{\alpha}_f = \tau_D$, and $h_{\Psi, fD} = \widehat{\alpha}_f(h_{\Psi,D})$. Hence

$$
I^\varepsilon_{\rm branch}(fD; \Psi) = I^\varepsilon_{\rm branch}(D; \Psi).
$$

### Enlargement invariance — NOT proved

For $D \subset D'$, exact invariance requires a Type II core factorization

$$
\widehat{M}_{D'} \cong \widehat{M}_D \,\bar\otimes\, \widehat{M}_K
$$

with $h_{\Psi, D'} = h_{\Psi,D} \otimes h_K$ and $N^\varepsilon_{\rm eff}(K) = 1$. In Type III AQFT there is generally no literal tensor factorization $M_{D'} \cong M_D \,\bar\otimes\, M_{D' \setminus D}$, and crossed-product cores have no automatic conditional expectation implementing the decomposition.

**Honest statement: exact enlargement invariance is not proved.**

The prescription should therefore use the **minimal record-comparison diamond**, not arbitrary enlargement. Missing theorem:

> If $D \subset D'$ and the inclusion adds no new decoherent records relevant to the comparison, then the inclusion-induced core map preserves the $\varepsilon$-smooth support volume of the conditioned regional state.

---

## §3.1 — Equivariance / Born compatibility

### Bohmian template

DGZ equivariance: if $\rho_t = |\psi_t|^2$ initially and configuration evolves by guiding equation while $\psi$ evolves by Schrödinger, then $\rho_{t'} = |\psi_{t'}|^2$ for all $t' > t$.

### QIQT-H analogue

For events $E$ in decoherent history algebra $\mathfrak{B}_t$, formal Born measure:

$$
\mu_t^\Psi(E) = \omega_\Psi(C_E^* C_E).
$$

QIQT-H admissibility set $A_t^\Psi$ defined by branch-bound predicate. Renormalized measure:

$$
\nu_t^\Psi(E) = \frac{\mu_t^\Psi(E \cap A_t^\Psi)}{\mu_t^\Psi(A_t^\Psi)}.
$$

### Equivariance condition

For prefix map $\pi_{t \to s}: \Omega_t \to \Omega_s$:

$$
(\pi_{t \to s})_* \nu_t^\Psi = \nu_s^\Psi.
$$

### Born compatibility in the non-binding regime — *solved*

**Theorem (vacuous-bound Born compatibility).** On any decoherent history algebra for which every nonzero history satisfies the branch bound with positive margin $\Delta > 0$ larger than accumulated tolerances (decoherence approx, $\varepsilon$-smoothing, $S_{\rm gen}$ semiclassical uncertainty, $S^{\rm ren}_{\rm matter}$ renormalization), the QIQT-H renormalized history measure equals the ordinary decoherent-history Born measure.

*Proof.* Immediate from $A^\Psi = \Omega$, hence $\nu = \mu$.

**Operationally: for ordinary laboratory experiments, where $I^\varepsilon_{\rm branch}(D) \ll S_{\rm gen}(\partial D)$, the admissibility constraint removes no histories and hence changes no weights.**

### The hard regime

When $I^\varepsilon_{\rm branch}(D) \sim S_{\rm gen}(\partial D)$, projective consistency can fail:

$$
\mu_t^\Psi(A_t^\Psi \mid \pi_{t \to s}^{-1} h_s)
$$

must depend on past prefixes only through admissibility already visible at the earlier time. This is *not automatic*.

**Central open obstruction in §3.1: prove that admissibility-restricted Born measures form a projectively consistent family of history measures.** If false, QIQT-H needs a new dynamical law replacing the naive renormalized measure.

---

## §3.2 — No-signaling

### Gisin's mechanism (standard nonlinear QM)

Nonlinear pure-state evolution $|\psi\rangle\langle\psi| \mapsto \mathcal{N}_t(|\psi\rangle\langle\psi|)$ leads to ensemble-decomposition-dependent reduced states:

$$
\sum_i p_i \mathcal{N}_t(|\psi_i\rangle\langle\psi_i|) \ne \sum_j q_j \mathcal{N}_t(|\phi_j\rangle\langle\phi_j|).
$$

Hence Bob's choice of measurement basis changes Alice's later reduced state — superluminal signal.

### Why QIQT-H sidesteps Gisin directly

QIQT-H does **not** postulate instantaneous nonlinear evolution of $\rho_A$. It postulates a *predicate on whole conditioned histories*, with weights renormalized history-globally:

$$
\nu(E) = \frac{\mu(E \cap A)}{\mu(A)}.
$$

There is no map taking $\rho_A$ to a nonlinear evolved $\rho_A'$ depending on its ensemble decomposition. The admissibility condition is global in history space, not local in instantaneous density-matrix space.

### Residual risk: postselection signaling

For spacelike-separated $M_A$, $M_B$ with class operators $C^{A,x}_a$, $C^{B,y}_b$:

$$
P_{\rm QIQT}(a, b \mid x, y) = \frac{\mu(a, b \mid x, y) \, w(a, b, x, y)}{Z(x, y)},
$$

with admissibility weight $w(a, b, x, y) = \mathbf{1}_{\mathrm{Adm}(a, b, x, y)}$.

Alice's marginal:

$$
P_{\rm QIQT}(a \mid x, y) = \frac{\sum_b \mu(a, b \mid x, y) w(a, b, x, y)}{\sum_{a',b'} \mu(a', b' \mid x, y) w(a', b', x, y)}.
$$

Born no-signaling cancellation survives only if $w$ satisfies a conditional-independence condition. **There is no automatic reason for this to hold for an arbitrary global history constraint.**

### Required causal screening theorem

**Sufficient condition (not proved).** For Alice's record-comparison diamond $D_A$ and Bob's spacelike setting region, the admissibility predicate relevant to Alice's observed frequencies must be measurable in $M_{D_A}$ alone:

$$
\mathbf{1}_{A_{x,y}}|_{D_A} = \mathbf{1}_{A_x}^{D_A}, \quad \text{independent of } y.
$$

Required theorem:

> For any two spacelike-separated local instruments in commuting algebras $M_A$ and $M_B$, the admissibility restriction associated to Alice's record-comparison diamond has conditional expectation independent of Bob's choice of instrument.

**Central open obstruction in §3.2: prove that the admissibility weight has no setting-dependent effect on spacelike local marginals.**

In the non-binding regime $w = 1$, no-signaling reduces to ordinary algebraic no-signaling. In the binding regime, no-signaling is an additional nontrivial theorem, not yet established.

---

## Status assessment

After this attempt, the missing-mathematics situation looks like:

| Blocker | Status after attempt |
|---|---|
| §2.1 basis-independent $I^\varepsilon_{\rm branch}$ | **Proposed definition is concrete.** Basis independence solved via Connes cocycle + Fack-Kosaki. Open: physical trace normalization. |
| §2.2 admissibility | **Right formal object identified** (Boolean subalgebra of histories). Closure bound proved. Open: dynamical selection law. |
| §2.4 region prescription | **Causal diamond solidly preferred.** Covariance proved. Open: enlargement invariance. |
| §3.1 equivariance | **Non-binding regime: theorem.** Binding regime: open. |
| §3.2 no-signaling | **Gisin mechanism does not directly apply.** Open: causal screening theorem. |

Three blockers (§2.2 dynamical law, §3.1 projective consistency in binding regime, §3.2 causal screening) are now sharply formulated rather than schematic. That is genuine progress: the questions are now *specific theorems that need proving*, not "we need to figure something out."

The framework is closer to being a research program with clear technical targets, not just a philosophical position.
