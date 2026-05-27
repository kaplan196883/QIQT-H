# GPT-5.5-Pro Follow-up Audit: 7-Item Cleanup Verified, 6 Minor Residual Issues

**Date:** 2026-05-27
**Source:** GPT-5.5-Pro (high reasoning), follow-up audit of the propagated 7-item cleanup across all four documents.
**Verdict:** **The modular-local formulation is now substantially internally consistent.** The seven fixes remove the main contradictions identified in `paper_strategy/40`. Six residual technical issues remain — *minor precision/formalization*, not fatal.

## Status: substantially consistent

> The modular-local formulation is now substantially internally consistent. The seven fixes remove the main old contradictions.

## Each of the 7 fixes verified

| Item | Audit verdict |
|---|---|
| 1. $\mathcal{H}_{\rm phys}$ modular-local | ✓ Compatible, removes old branch-summed framing. Minor wording check on "normal" + reference state restriction-compatibility |
| 2. Theorem 6 effective form | ✓ Proof valid given probability normalization. $\|T_\delta\|$ bound correctly derived via Markov. $p_{\max} \ge e^{-H(p)}$ valid |
| 3. Algebraic dynamics + instruments | ✓ Algebraically well-posed. Heisenberg convention correct. Minor: "predual" applies only to vN algebras; "causal future of the outcome record" needs AQFT formalization |
| 4. Causal-application axiom | ✓ Conceptually consistent, fixes retroactive-pruning. Needs explicit *filtration by Cauchy slice/process stage* |
| 5. $S_{\rm ren} \equiv \chi_R$ | ✓ Mathematically clean *if* $\sigma_R$ specified |
| 6. Non-selective convention | ✓ Closes the postselection signaling loophole. Feed-forward not excluded (correctly: classically conditioned operations are causally ordered, not spacelike signaling) |
| 7. Modular Born-deviation $\delta_R \lesssim 10^{-27}$ | ✓ Markov step fine. Numerical ratio plausible. Caveat: modular-Hamiltonian estimate is generic only with extra hypotheses |

## 6 residual technical issues (minor, formalization-level)

These are *not* contradictions — they are precision items for a future polish pass.

### 1. Specify the reference state family $\sigma_R$

Araki relative entropy $S(\omega \| \sigma)$ depends on the choice of $\sigma$. The framework should specify whether $\sigma_R$ is:
- Minkowski vacuum
- KMS state
- Cosmological reference state
- Code-subspace reference state

Also, reference states should be **restriction-compatible**: $\sigma_{R'} = \sigma_R|_{\hat{\mathcal{A}}(R')}$ for $R' \subset R$. Otherwise the meet/isotony discussion becomes ambiguous.

### 2. Formalize local normality and the von Neumann net

"Normal" only makes sense after specifying the local von Neumann algebra / reference representation. If $\hat{\mathcal{A}}(R)$ is only a C*-algebra, the framework should say "extends to a normal state on the chosen local von Neumann algebra."

### 3. Add a causal/time-indexed filtration to avoid global-future tension

The axiom of causal application is conceptually consistent, but the current $\mathcal{S}_{\rm phys}$ definition imposes the constraint on $\omega$ at the global / spacetime-net level. There's a latent tension: if $\omega$ is treated as a single global state with constraints imposed for every future bounded region from the start, the causal axiom is in tension with the global state definition.

**Best fix:** introduce an explicit filtration by Cauchy slice / process stage / instantiated algebra. Then admissibility checks happen at each stage, and past separately-admissible branches are not retroactively deleted by future violations of $\chi_{D^+} > C(D^+)$ — instead, the *future* state/transition is inadmissible from $D^+$ onward.

### 4. Formalize "causal future of the outcome record"

The instrument-level branchwise admissibility condition is stated as: $\omega_a$ admissible "on every region in the causal future of the outcome record." This should be sharpened in AQFT terms:

- The outcome record should be localized in a bounded diamond $O_a$
- Branchwise admissibility should be checked for bounded regions $R \subset J^+(O_a)$

### 5. State Theorem 6 with normalized record probabilities and finite-$\eta$ saturation

Two precision corrections:
- The $p_k$ must form a *normalized* probability distribution over record alternatives. If the active record set has leakage probability $1 - q$, the bound needs $q$-dependent corrections or must be stated conditionally on the active set.
- "At saturation $I_0 = C(R)$, $H(p) = 0$" is only true in the ideal $\eta_\epsilon = 0$ limit. With finite $\eta_\epsilon$, the conclusion is only $H(p) \le 2\eta_\epsilon$.

### 6. Qualify the modular-Hamiltonian / Born-deviation estimate

The Bisognano-Wichmann form $\Delta\langle K_R^\sigma\rangle \lesssim 2\pi L E_R/(\hbar c)$ is:
- *Exact* for a Rindler wedge
- *Exact* for a ball in a CFT vacuum (via conformal symmetry)
- *Not* generic for an arbitrary ball-shaped region in flat-spacetime QFT

For generic QFT balls the modular Hamiltonian is nonlocal and the simple bound needs:
- Extra hypotheses (conformal symmetry), OR
- An enclosing-wedge monotonicity argument

Also, $\chi_R = \Delta K - \Delta S$ bounded by $\Delta K$ requires control of $\Delta S$ (e.g., $\Delta S \ge 0$ or a separate entropy-difference bound). Otherwise $\Delta K$ alone is not a rigorous upper bound on $\chi$.

**So the $10^{-27}$ claim is acceptable only as a *conditional* estimate, not a theorem for arbitrary regions/states.**

## Cross-document consistency

All four documents (foundations, tutorial, position, math) are now aligned:
- ✓ Algebraic / modular-local state space
- ✓ Effective, not literal, definiteness
- ✓ Branchwise instruments
- ✓ Causal application
- ✓ Region- and energy-dependent $10^{-27}$-type estimate
- ✓ Double-slit bound $H(\{p_k\}) \le C(R_S) - I_0 + 2\eta_\epsilon$

**Wording checks to perform:**
- No document should still say "$\mathcal{H}_{\rm phys}$ is a Hilbert subspace"
- No document should still say "branch-summed cost is fundamental"
- No document should still say "saturation gives literal uniqueness at finite $\eta_\epsilon$"
- No document should still say "$10^{-27}$ is universal"

## Overall verdict

> The modular-local formulation is now substantially internally consistent. The seven fixes remove the main old contradictions.
>
> Residual issues needing further work are *technical rather than fatal*:
> 1. specify the reference state family $\sigma_R$;
> 2. formalize local normality and the von Neumann net;
> 3. add a causal/time-indexed filtration to avoid global-future constraint tension;
> 4. formalize "causal future of the outcome record";
> 5. state Theorem 6 with normalized record probabilities and finite-$\eta$ saturation;
> 6. qualify the modular-Hamiltonian/Born-deviation estimate.
>
> With those clarifications, the framework is internally coherent in its modular-local version.

## What this means

After:
- Round 1: branch-summed framework + Open Problem 10
- Round 2: Bell-style counter-example (paper_strategy/38)
- Round 3: modular-local refactor (paper_strategy/39)
- Round 4: Audit finds 7 inconsistencies (paper_strategy/40)
- Round 5: Apply 7 fixes + propagate to all 4 documents
- Round 6: Follow-up audit — *substantial consistency*, 6 minor precision items

**The framework's modular-local version is now structurally sound.** The remaining six issues are formalization items that a careful mathematical-physics paper would polish in a final pass before submission. None of them threaten the framework's basic consistency.

This is genuine progress: from "the framework has a fatal signaling bug" (Round 2) to "the framework's modular-local version is internally coherent with six formalization items pending" (Round 6).
