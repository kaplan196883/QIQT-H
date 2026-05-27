# GPT-5.5 Attack on Open Problem 10: No-Signaling Under Regional Admissibility

**Date:** 2026-05-27
**Source:** GPT-5.5 (high reasoning), attacking Open Problem 10 from the foundations paper.
**Verdict:** Exact no-signaling is *not* derivable from per-region caps alone. A concrete Bell-setup counter-example shows signaling explicitly. Exact no-signaling requires an *additional axiom* (cylindrical consistency / scalar-Bob-sum / additive factorization). Approximate operational no-signaling is available only if the lab-scale $\delta$-bound is established independently.

## Key result: explicit Bell-style signaling counter-example

Singlet state, binary outcomes $a, b \in \{\pm 1\}$, settings at angle $\theta_{xy}$:

$$
\mu_{xy}(a, b) = \tfrac{1}{4}(1 - ab \cos\theta_{xy}).
$$

Assign asymmetric information costs:

$$
I_A(+) = 0, \quad I_A(-) = 1, \quad I_B(+) = 0, \quad I_B(-) = 1,
$$

with joint-diamond capacity $Q_{D_{AB}} = 1$. The admissible joint branches are $(+,+), (+,-), (-,+)$; the branch $(-,-)$ is **excluded** by the joint cap.

Computing Alice's marginal:

$$
P_{\rm QIQT}(+\mid x, y) = \frac{\mu(++) + \mu(+-)}{1 - \mu(--)} = \frac{2}{3 + \cos\theta_{xy}}.
$$

This **depends on $y$**.

Concrete numerical example: Alice holds $x$ fixed; Bob chooses $y_0, y_1$ with $\cos\theta_{xy_0} = 0$, $\cos\theta_{xy_1} = 1/\sqrt{2}$:

$$
P_{\rm QIQT}(+ \mid x, y_0) = \tfrac{2}{3} \approx 0.667, \qquad P_{\rm QIQT}(+ \mid x, y_1) \approx 0.539.
$$

**Bob's choice of measurement axis shifts Alice's marginal by ~13%.** Operationally visible. **Operational signaling.**

## The structural lesson

The dangerous ingredient is **not** tensor factorization, **not** absence of conditional expectations, and **not** an instantaneous nonlinear evolution. It is *conditioning on a joint future predicate that is not cylindrically consistent*.

Per-region caps **do not enforce** the cylindrical consistency required for no-signaling. The framework must *add* it as an additional axiom, or rely on a softer admissibility mechanism.

## What CAN be proved: cylindrical-consistency theorem

### Theorem 1 (AQFT cylindrical-consistency sufficient condition).

Let $D_A, D_B$ be spacelike with $[\mathcal{A}(D_A), \mathcal{A}(D_B)] = 0$ and local class operators $C_{ab}^{xy} = C_a^x C_b^y$. Suppose the joint admissibility weight satisfies

$$
\sum_b k_{ab}^{xy} C_b^{y*} C_b^y = c_y \cdot h_a^x \cdot \mathbf{1},
$$

with $h_a^x$ independent of $y$. Then

$$
P_{\rm QIQT}(a \mid x, y) = P_{\rm QIQT}(a \mid x).
$$

*Proof.* Using microcausality, $[E_a^x, G_a^{xy}] = 0$ where $E_a^x = C_a^{x*}C_a^x$ and $G_a^{xy} = \sum_b k_{ab}^{xy} C_b^{y*}C_b^y$. If $G_a^{xy} = c_y h_a^x \mathbf{1}$, then $\omega(E_a^x G_a^{xy}) = c_y h_a^x \omega(E_a^x)$, and the $c_y$ cancels in the ratio. ∎

**This is a clean AQFT-compatible theorem** — it does *not* require tensor factorization or state-preserving conditional expectations. But the hypothesis is non-trivial.

## What FAILS: hard joint-capacity cutoff

A hard admissibility predicate

$$
k_{ab}^{xy} = \mathbf{1}\{I_A^{a,x} + I_B^{b,y} \le Q_{D_{AB}}\}
$$

does *not* satisfy the cylindrical-consistency condition. The Bell-style counter-example above is an explicit instance. So **the simplest formulation of QIQT-H's joint-diamond admissibility violates no-signaling**.

## Safe special cases identified

1. **Large-slack regime.** If $I_A^{a,x} + I_B^{b,y} \le Q_{D_{AB}}$ for *every* branch (i.e., the joint diamond is far from saturated for *all* outcomes), then $k = 1$ and Born no-signaling is recovered exactly. **This is the lab-scale regime** ($\delta \ll 1$ from `paper_strategy/36`).

2. **Outcome-independent costs.** If $I_A^{a,x}, I_B^{b,y}$ are independent of the outcome labels $a, b$ (depending only on settings), then $k$ is outcome-independent and cancels in the normalized marginal. This is the symmetric-cost case.

3. **Soft exponential admissibility.** If $g(I_A + I_B) = e^{-\lambda(I_A + I_B)} = e^{-\lambda I_A} \cdot e^{-\lambda I_B}$ factorizes, the conditional-expectation factorization is automatic. **A soft exponential admissibility weight would preserve no-signaling**; a hard threshold does not.

## Approximate operational no-signaling (Theorem 3)

If the lab-scale closeness bound $\|P_{\rm QIQT}^A - P_{\rm Born}^A\|_{\rm TV} \le \delta$ from `paper_strategy/36` holds for all $x, y$, then by triangle inequality and Born no-signaling:

$$
\|P_{\rm QIQT}^A(\cdot \mid x, y) - P_{\rm QIQT}^A(\cdot \mid x, y')\|_{\rm TV} \le 2\delta.
$$

Lab-scale $\delta \lesssim 10^{-24}$ ⇒ signaling amplitude bounded by $\sim 10^{-24}$, undetectable.

**Caveat.** A hard admissibility filter with small acceptance probability $Z_{xy} \ll 1$ can amplify tiny branch differences. So the $\delta$-bound requires *additional slack/non-extremality* hypotheses — it is not free.

## The four attacks: results table

| Attack | Result |
|---|---|
| **1. Microcausality** | Reduces problem to a sufficient cylindrical-consistency condition (Theorem 1); does NOT imply no-signaling alone |
| **2. Additive costs** | Hard cutoff $g$ does not factor; soft exponential $g$ does. Per-region caps with hard joint cutoff fail |
| **3. Bell example** | **Concrete signaling counter-example** with asymmetric costs and $\theta$-dependent marginal |
| **4. Operational** | Approximate no-signaling at $\le 2\delta$ if lab-scale closeness holds; requires independent slack assumption |

## Verdict

**Open Problem 10 is genuinely open** within the currently stated AQFT/Type II infrastructure.

To resolve it, QIQT-H must do one of the following:

1. **Add a cylindrical-consistency axiom.** Demand that joint-diamond admissibility predicates satisfy $\sum_b k_{ab}^{xy} C_b^{y*} C_b^y = c_y h_a^x \mathbf{1}$ as an additional foundational requirement. This is the cleanest route — it gives exact no-signaling — but it is a new axiom, not a consequence of holography.

2. **Replace hard thresholds with soft (exponential) admissibility weights.** Then the admissibility predicate factorizes across spacelike algebras automatically. This is a *change to the framework's formulation*: $K_{ab}^{xy}$ becomes $e^{-\lambda I_{AB}}$ rather than $\mathbf{1}\{I_{AB} \le Q\}$. The framework would no longer be a sharp superselection rule; it would be a weighted suppression. Mathematically cleaner; conceptually a substantive shift.

3. **Restrict to outcome-symmetric cost functions.** If $I_A(a)$ is independent of the outcome label $a$ (and similarly $I_B(b)$), the Bell counter-example evaporates. But this restricts the kinds of records the framework can handle: records that distinguish outcomes by *cost* (e.g., asymmetric Zurek complexity) re-introduce signaling.

4. **Accept approximate operational no-signaling.** Settle for the $|\nu - \mu| \le \delta$ bound from `paper_strategy/36`, which gives $\le 2\delta$ signaling. At lab scale this is unmeasurable. But this concedes that *in principle* QIQT-H can signal — just by a tiny amount in ordinary regimes.

## Implications for the foundations paper

The §11.4 Open Problem 10 entry should be updated to reflect:

(a) The exact theorem is provable only under an additional axiom (cylindrical consistency / scalar-Bob-sum / soft factorizing admissibility).

(b) The hard-threshold formulation of the Branch-Summed Bound, applied to joint comparison diamonds, **demonstrably signals** in a Bell setup with asymmetric record costs.

(c) The framework's options are explicit: add an axiom, soften the admissibility weight, restrict to symmetric costs, or accept approximate no-signaling.

This is a genuine constraint on what QIQT-H can be — analogous to the §2.4 non-monotonicity finding in `paper_strategy/37`. The framework is being forced into a more specific shape by these obstructions.

## Honest characterization

After four passes and four self-reviews, the *missing math* picture is:

| | Result |
|---|---|
| §2.1 Core invariance | Conditional theorem (modulo trace normalization) |
| §2.2 Dynamical selection | Candidate variational principle + 5 sub-problems |
| §2.4 Region monotonicity | **Concrete no-go** (entangled-pair counter-example) |
| §3.1(2) Lab Born compatibility | Measure-theoretic bound proved; numerical estimate circular |
| §3.2 Causal screening | **Concrete no-go** (Bell-setup signaling counter-example, this doc) |
| OP10 No-signaling | Provable under extra axiom; **demonstrably violated** with hard threshold |

Two conditional theorems, two concrete no-go results, one candidate variational principle. The framework's *kinematic shape* is now sharply constrained by the no-gos: it must be regional (rules out global budget), it must have soft or symmetric admissibility (rules out hard asymmetric threshold), and it must restrict to diamond families where $S_{\rm gen}$ behaves monotonically (rules out arbitrary inclusion).

These are real constraints — and identifying them is progress, even if the positive theorems are not yet in hand.
