# GPT-5.5 Elegant Resolution to Open Problem 10: Modular-Local Admissibility

**Date:** 2026-05-27
**Source:** GPT-5.5 (high reasoning), responding to a request for the most elegant resolution to the no-signaling problem in QIQT-H.
**Verdict:** A fifth option exists, more elegant than the previous four: reformulate admissibility as a **modular-local superselection constraint** on each $(\mathcal{A}(D), \omega_D)$ separately, using Araki / Type II core relative entropy as the intrinsic information functional. Spacelike-separated regions are combined by the *meet of local predicates*, not by a hard cutoff on the joint algebra. Under this reformulation, no-signaling follows automatically from AQFT microcausality — it is not an extra axiom.

## The reformulation in one sentence

> **QIQT-H admissibility is a modular-local superselection constraint on the algebra-state pair $(\mathcal{A}(D), \omega_D)$, defined via Araki / core relative entropy, with spacelike-separated regions combined by the meet of local predicates — never by a hard cutoff on the joint spacelike algebra.**

## The minimal postulate

For each causally complete region $D$, define the intrinsic information functional

$$
\chi_D(\omega) = S_{\mathcal{A}(D)}(\omega_D \| \Omega_D),
$$

the Araki relative entropy of the regional state with respect to a vacuum (or reference) state. This is **Type III-native**: no density matrix, no tensor factorization, no UV-divergent raw entropy. Equivalently, it can be computed from the Haagerup density $h_{\omega, D}$ in the Type II core:

$$
\chi_D(\omega) = \tau_D[h_{\omega, D}(\log h_{\omega, D} - \log h_{\Omega, D})] + \text{counterterms}.
$$

Admissibility is then:

$$
\omega_D \in \mathrm{Adm}(D) \iff \chi_O(\omega|_{\mathcal{A}(O)}) \le C(O) \quad \text{for all } O \subseteq D,
$$

with $C(O) \sim A(\partial O)/(4G\hbar)$ or the appropriate renormalized QIQT-H capacity.

For spacelike-separated regions:

$$
\mathrm{Adm}(D_A \sqcup D_B) = \mathrm{Adm}(D_A) \wedge \mathrm{Adm}(D_B).
$$

A state is admissible on the spacelike pair iff its restriction to *each* local algebra is admissible. The joint algebra $\mathcal{A}(D_A) \vee \mathcal{A}(D_B)$ may remain vacuum-entangled and Type III non-factorizing — the admissibility predicate doesn't impose anything on the joint structure beyond the two local restrictions.

Categorically: $\mathrm{Adm}$ is a **local subfunctor** of the AQFT state functor.

## Why no-signaling follows automatically

Let Alice's instrument be a normal CP instrument $\{\Phi_a^x\}_a$ localized in $D_A$, and Bob's $\{\Psi_b^y\}_b$ in $D_B$. Bob's non-selective channel is $\Psi^y = \sum_b \Psi_b^y$.

**By microcausality** $[\mathcal{A}(D_A), \mathcal{A}(D_B)] = 0$, Bob's non-selective Heisenberg dual acts as the identity on Alice's algebra:

$$
\Psi^{y*}(X) = X \quad \forall X \in \mathcal{A}(D_A).
$$

Alice's outcome effect is $E_a^x = \Phi_a^{x*}(\mathbf{1}) \in \mathcal{A}(D_A)$. Therefore:

$$
p(a \mid x, y) = \omega(\Psi^{y*}(E_a^x)) = \omega(E_a^x),
$$

**independent of $y$**.

Moreover, Alice's post-outcome local state restriction to $\mathcal{A}(D_A)$:

$$
\omega_{a,x}|_{\mathcal{A}(D_A)} = \frac{\omega \circ \Phi_a^{x*}|_{\mathcal{A}(D_A)}}{\omega(E_a^x)}
$$

is also independent of $y$, since Bob's non-selective operation does not change the restriction. Hence

$$
\chi_{D_A}(\omega_{a,x}) = S_{\mathcal{A}(D_A)}(\omega_{a,x} \| \Omega_{D_A})
$$

is independent of $y$. Alice's branch admissibility cannot depend on Bob's setting.

**No tensor factorization is used. Only microcausality.** This is the right structure for Type III local QFT.

## Critical caveat: do NOT use joint relative entropy as a hard cutoff

Imposing a hard cutoff on

$$
S_{\mathcal{A}(D_A) \vee \mathcal{A}(D_B)}(\omega \| \Omega)
$$

does **not** factorize, because the vacuum is not a product state across spacelike regions:

$$
S_{A \vee B}(\omega \| \Omega) \ne S_A(\omega_A \| \Omega_A) + S_B(\omega_B \| \Omega_B).
$$

The difference contains correlation / mutual-information terms — exactly the boundary entanglement structure that Type III preserves. Trying to bound the joint relative entropy with a hard cutoff would re-introduce the signaling problem of the original formulation.

The fix is to **use relative entropy locally only**, and combine spacelike regions by meet of predicates, not by joint constraint.

## Operational rule: instruments, not branches

The exclusion is at the level of **physically permissible instruments**, not at the level of postselected branches:

$$
\omega \in \mathrm{Adm}(D) \implies \frac{\omega \circ \Phi_a^*}{\omega(\Phi_a^*(\mathbf{1}))} \in \mathrm{Adm}(D)
$$

for every nonzero branch $a$. An instrument is admissible iff it preserves the admissible state cone branchwise. Inadmissible outcomes are not produced because the dynamics that would produce them is not a physical instrument — *not* because some branches are postselected away after the fact.

**This preserves QIQT-H's central flavor**: exclusion is kinematic (which states are physical) and dynamical (which instruments are allowed), not postselectional (filter applied to existing outcomes). The "superselection" interpretation is intact.

## Ranking of the five options

| Rank | Option | Pros | Cons |
|---|---|---|---|
| **1** | **Modular-local + meet of local predicates (this doc)** | No new axiom beyond holography; uses Araki entropy that exists in Type III; no-signaling automatic from microcausality; preserves kinematic-superselection flavor | Requires the framework to commit to relative-entropy-style information functional instead of branch-summed support counting; still owes a derivation of the per-region capacity $C(D)$ |
| 2 | Cylindrical consistency | Exact no-signaling; AQFT-compatible | Ad hoc additional axiom not motivated by holography |
| 3 | Outcome-symmetric costs | Simple; closes the Bell counter-example | Restrictive — many real records are outcome-asymmetric (Zurek complexity, redundancy) |
| 4 | Approximate operational no-signaling | Pragmatic | Concedes in-principle signaling; not foundationally clean |
| 5 | Soft exponential weights | Mathematically smooth; factorizes automatically | Changes QIQT-H from kinematic exclusion (superselection) to dynamical suppression (collapse-like) — substantive shift in framework character |

The modular-local option dominates the other four on every dimension that matters foundationally: minimality of postulates, naturalness in AQFT/Type III, automatic no-signaling, and preservation of framework character.

## What this means for the framework

QIQT-H needs to refactor:

1. **The Branch-Summed Bound** in the foundations paper currently reads "$I_\Sigma^\epsilon[\omega_R] \le Q_R$ for all bounded regions $R$." It should be re-expressed in terms of Araki relative entropy $\chi_R(\omega) \le C(R)$, where $C(R)$ is the renormalized capacity (Planck-area in physical units).

2. **The branch-summed support-counting** machinery — smooth active set, per-record cost $c_R(r)$, $I_0$ as experimental parameter — should be either:
   - **Reinterpreted** as a particular discretization of $\chi_R$ in the regime where the regional state is approximately classical-mixture, OR
   - **Replaced** with the relative-entropy formulation as the fundamental object.

3. **Spacelike combination** must be explicitly stated as the meet of local admissibility predicates. The framework must NOT impose joint-diamond capacity caps on $\mathcal{A}(D_A) \vee \mathcal{A}(D_B)$.

4. **Open Problem 10** is then **solved**: no-signaling is a theorem from microcausality + locality of admissibility, not an additional axiom or a lab-scale approximation.

## Implications for the foundations paper

§4 (FQ axiom): the holographic bound on renormalized entropy in part (ii) is already Araki-style. Strengthen it to Araki relative entropy with reference state $\Omega$. Drop any reading that imposes joint-region cutoffs.

§7.6 (Branch-Summed Bound): re-express as $\chi_R(\omega) \le C(R)$. The branch-summed support-counting machinery becomes a *derived approximation* in the macroscopic-classical-mixture regime, not the fundamental object.

§11.4 Open Problem 10: can be retired. Replace with a theorem statement: *Under modular-local admissibility, no-signaling follows from AQFT microcausality.* Proof one paragraph (the one above).

## Bottom line

The elegant resolution exists. It requires reformulating QIQT-H's central bound in **algebraic relative-entropy language** instead of **branch-counting language**. The two are equivalent in the relevant regime (classical mixtures of decoherent records) but the algebraic formulation is intrinsically local in the AQFT-net sense, which makes no-signaling automatic.

The cost is that the framework's working language shifts from "count surviving records, bound the count by area" to "constrain the algebra-state pair, bound its relative entropy by area." The first is more intuitive; the second is mathematically cleaner and physically consistent.

This is the most foundationally satisfying resolution available within the listed AQFT / Type II infrastructure.
