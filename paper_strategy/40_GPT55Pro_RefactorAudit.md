# GPT-5.5-Pro Audit: Internal Consistency of the Modular-Local Refactor

**Date:** 2026-05-27
**Source:** GPT-5.5-Pro (high reasoning), referee-level audit of the refactored foundations paper.
**Verdict:** The refactor fixes the specific no-signaling pathology, but is **not internally consistent as written**. Six concrete issues identified, requiring a follow-up cleanup pass. The modular-local *direction* is viable; the *implementation* is incomplete.

## Six concrete issues

### 1. §7.6 carries over the old branch-summed definition of $\mathcal{H}_{\rm phys}$

The §7.6 introduction states $\chi_R(\omega) \le C(R)$ as the *foundational* bound and demotes $I_\Sigma^\epsilon$ to a derived classical-mixture approximation. But the subsequent **Definition (Physical state space)** still reads:

$$\mathcal{H}_{\rm phys} = \{|\Psi\rangle : I_\Sigma^\epsilon[\omega_\Psi^R] \le Q_R \text{ for all bounded } R\}$$

— using the *branch-summed* cost as the defining constraint. This contradicts the refactor.

The correct refactored definition should be a state-space condition:

$$\mathcal{S}_{\rm phys} = \{\omega : \chi_R(\omega) \le C(R) \text{ for every bounded connected } R, \text{ spacelike unions handled by meet}\}.$$

A vector $\mathcal{H}_{\rm phys}$ exists only as the preimage of $\mathcal{S}_{\rm phys}$ modulo the (FQ)(iii) physical equivalence relation.

### 2. Theorem 6 (Macroscopic Definiteness) does NOT survive the refactor

The current proof uses $|\mathcal{A}_\epsilon| \cdot I_0 \le I_\Sigma^\epsilon \le Q_R$ — pure branch-counting logic.

Under the new classical-mixture formula $\chi_R(\omega_{\rm cm}) \approx \sum_r p_r c_R(r) + H_{\rm Shannon}(\{p_r\})$, the cost is probability-weighted, plus Shannon entropy. This **bounds average modular cost and effective entropy, not hard active-set cardinality.** For $k$ equiprobable records with $c_R(r) = I_0$:

$$\chi_R \approx I_0 + \log k.$$

So $k$ can scale like $e^{C(R)}$, not $C(R)/I_0$. **The old cardinality bound is not a theorem of the modular-local axiom.** Theorem 6 must be rewritten as a classical-mixture corollary with explicit hypotheses — likely in a weaker effective-entropy form.

### 3. No-signaling proof is overkill — only needs meet of local predicates

The proof of Theorem 7 (no-signaling) actually uses three facts:
1. Microcausality $[\hat{\mathcal{A}}(D_A), \hat{\mathcal{A}}(D_B)] = 0$
2. No state-dependent pruning/renormalization of Alice's marginal
3. Spacelike admissibility is the meet of local predicates

**The proof does NOT actually depend on the modular-local form of the bound.** *Any* truly local admissibility predicate — including a per-region branch-summed cost — gives no-signaling.

**Implication:** the entire modular-local refactor was not necessary just to recover no-signaling. The original branch-counting framework could have been rescued by simply abandoning the joint-diamond cutoff and using meet of local predicates. The modular refactor may still be preferable for other reasons (covariance, algebraic locality, monotonicity, avoiding basis-dependent branch counts), but it is **not necessary** for this no-signaling theorem.

### 4. Joint future diamonds: retroactive-pruning trap

§7.7 Remark 3 says joint comparison diamonds $D_{AB}$ carry their own capacity $C(D_{AB})$ and their own modular-local admissibility predicate. This is consistent with no-signaling ONLY IF the constraint is applied *causally*: any state-dependent compression/erasure must occur in the future and cannot retroactively prune earlier Bell branches.

**The paper does not explicitly state this causal restriction.** If the framework treats admissibility of the whole run as a global history condition and deletes/renormalizes earlier Bell branches because they would later violate $C(D_{AB})$, **the original signaling problem returns**.

Required addition: an explicit "no retroactive pruning by future joint diamonds" condition.

### 5. "Physical Hamiltonian" notion no longer fits cleanly

The old "physical Hamiltonian preserves $\mathcal{H}_{\rm phys}$" language used a linear Hilbert subspace. Under the modular-local refactor, the physical state space is NOT naturally a Hilbert subspace — it's a nonlinear set of algebraic states satisfying regional entropy inequalities.

Correct reformulation:

- For dynamics: $\alpha_t^*(\mathcal{S}_{\rm phys}) \subseteq \mathcal{S}_{\rm phys}$ for physical automorphisms.
- For instruments: $\omega \in \mathcal{S}_{\rm phys} \implies \omega \circ \Phi_a^* / \omega(\Phi_a^*(\mathbf{1})) \in \mathcal{S}_{\rm phys}$ for every nonzero outcome.

The branchwise instrument rule is **stronger** than preservation of the non-selective state. A measurement unitary could preserve admissibility on average while some conditional outcome violates it.

Also: the condition should apply to **all relevant regions**, not merely the local measurement diamond. Otherwise an outcome could be admissible in $D_A$ and $D_B$ separately but inadmissible in a later $D_{AB}$.

### 6. Born compatibility numerical estimate must be rederived

The measure-theoretic bound $|\nu - \mu| \le \delta = \mu(A^c)$ carries over directly (it's independent of how admissibility is defined).

**But the lab-scale numerical estimate $\delta \lesssim 10^{-24}$ does NOT automatically carry over.** The old estimate used a Bekenstein-style cap on branch counts. The new estimate needs:

$$\delta_R = \mu\{r : \chi_R(\omega_r) > C(R)\} \le \frac{\mathbb{E}_\mu[\chi_R(\omega_r)]}{C(R)}$$

or a sharper tail bound. The numerical claim $\delta \lesssim 10^{-24}$ must be **rederived in modular-relative-entropy terms** — it cannot simply be imported from the old branch-counting argument.

## Additional consistency issues

- **§4.1 vs §7.6 entropy mismatch.** §4.1(ii) uses $S_{\rm ren}$; §7.6 uses Araki relative entropy $\chi_R$. These are not generally identical. The paper must state whether $S_{\rm ren} = \chi_R$, whether both are bounded, or whether one supersedes the other.

- **Classical-mixture formula requires conditions.** For block-diagonal states, relative entropy gives a classical term $D(p \| q)$, not automatically $+H(p)$, unless reference weights are specified appropriately. The decomposition $\chi_R \approx \sum_r p_r c_R(r) + H_{\rm Shannon}$ needs explicit hypotheses.

- **Region category needs precision.** "Every bounded $R$" conflicts with "spacelike unions are handled by meet" unless disconnected spacelike unions are explicitly excluded from the single-diamond capacity rule.

- **No-signaling proof implicit assumption.** The proof assumes physical instruments are trace-preserving non-selectively and do not remove inadmissible outcomes by postselection. This must be stated explicitly.

## Overall verdict

> The refactor fixes the specific no-signaling pathology if the meet-of-local-predicates rule is enforced and no future joint-diamond cutoff is used to retroactively prune Bell branches. However, the paper is not internally consistent as written. §7.6 still defines the physical state space and proves macroscopic definiteness using the old branch-summed cost as though it were fundamental. That must be removed or demoted to a derived approximation. Theorem 6 must be reproved in the modular-relative-entropy regime, likely in a weaker effective-entropy form.
>
> The modular-local direction is viable, but the current refactor is incomplete and needs a follow-up cleanup.

## Required follow-up cleanup pass

1. **Redefine $\mathcal{H}_{\rm phys}$ (or $\mathcal{S}_{\rm phys}$) in modular-local terms** via $\chi_R(\omega) \le C(R)$ — remove the residual branch-summed definition.

2. **Re-prove (or demote) Theorem 6.** The macroscopic definiteness claim must be reformulated as a classical-mixture corollary with explicit probability-weighted hypotheses. The framework will likely deliver "average modular cost is bounded" rather than "active-set cardinality is bounded" without an extra smoothing condition.

3. **Reformulate the "Physical Hamiltonian" notion** as admissibility-preserving automorphisms / channels at the algebraic level, including the branchwise instrument condition.

4. **Add explicit causal-application condition** on joint-future diamonds: admissibility constraints apply causally in the future and do not retroactively prune earlier branches.

5. **Reconcile $S_{\rm ren}$ vs $\chi_R$** in §4.1(ii) and §7.6: state explicitly which is the fundamental quantity.

6. **Rederive the numerical $\delta \lesssim 10^{-24}$** lab-scale Born deviation bound in modular-relative-entropy terms.

7. **State explicitly** that the no-signaling proof requires non-selective instruments (no postselection on outcomes).

## Important meta-finding

The audit reveals that the modular-local refactor was **not necessary** for no-signaling — meet-of-local-predicates *plus* the original branch-summed cost would have sufficed. The modular-local refactor is justified by *other* virtues:
- AQFT-native (works directly in Type III without coarse-graining)
- Basis-independent (no choice of record subalgebra needed)
- Connects to Araki / Connes / CPW machinery already in use
- Monotone under inclusion (relative entropy data-processing)

But the framework could have been saved by a less ambitious change: keep the branch-summed cost, but state it as a per-region predicate combined by meet, with explicit causal restriction. The fact that the framework went further and adopted the modular-local form is a matter of mathematical elegance, not logical necessity.

This is useful to know: the framework has flexibility about *which* informational quantity sits inside the bound, as long as the meet-of-local-predicates structure is preserved.
