# Third-Pass External Review and Impact Analysis by GPT-5.5

**Date:** 2026-05-23
**Paper version reviewed:** "One Wave Function, One World: A Finite-Information Axiom for Quantum Mechanics" (rewritten 2026-05-23 with explicit single-world realism + Proposition 6)

## Verdict (one paragraph)

> "The rewrite is a significant improvement rhetorically and dialectically. It no longer pretends that finite information solves collapse. But the paper's central thesis remains unsupported. ... The paper can be salvaged as a speculative metaphysical proposal: finite information may provide a cleaner setting for a one-world reading of quantum mechanics. But it should stop claiming that it has proven a structural necessity."

## A. The six fatal criticisms

### A.1 φ_i is misdefined (CRITICAL technical error)

The paper defines `φ_i := "observer is in record state |O_i⟩"` and identifies it with `⟨Ψ|P_i|Ψ⟩ = 1`. But for the entangled post-measurement state `|Ψ⟩ = Σ_i c_i |s_i⟩|A_i⟩|O_i⟩`,

```
⟨Ψ|P_i|Ψ⟩ = |c_i|²
```

which is generally not 1. So the formal proposition `⟨Ψ|P_i|Ψ⟩ = 1` is **false** (not undecidable) in $T_{QM}$ for non-trivial superpositions. The paper equivocates between:
- (a) a state-vector property (which is definitely false when stated as `⟨Ψ|P_i|Ψ⟩ = 1`), and
- (b) an actuality predicate ("this outcome was actually experienced") which is not part of the quantum formalism at all.

**Implication:** Theorem 1 is not the result the paper thinks it is. The honest statement is closer to "the formalism does not contain an actuality predicate" — which is the measurement problem in standard form, not a new undecidability theorem.

### A.2 The Gödel/Peano analogy overreaches

Gödel undecidability concerns formally expressible propositions independent of a recursively axiomatized theory. The situation in QM is different: "this outcome is actual" is not part of the quantum formalism *at all* unless one adds interpretive structure. That is **semantic incompleteness**, not Gödel-style undecidability. The analogy is rhetorically powerful but technically misleading.

### A.3 Single-world realism does add extra ontology, despite disclaimers

The paper insists it adds no hidden variables, no ontology, no collapse. But:

> "If exactly one branch is actual, and the wave function alone does not specify which branch, then there is an extra fact about the world not contained in the wave function. That extra fact may be primitive, stochastic, perspectival, modal, or indexical, but it is still extra structure. Calling it 'not hidden variables' does not remove the problem."

The paper's central rhetorical move — "we have only the wave function plus a brute fact about which outcome is realized" — *is* an additional ontological commitment by any reasonable definition. The "no extra ontology" claim is sleight of hand.

### A.4 (FQ) slides between four readings, none fully defensible

The four candidate readings of (FQ):

1. **Finite experimental precision** — harmless but trivial; doesn't imply probabilities are dyadic.
2. **Finite-dimensional Hilbert space (holographic)** — a finite-dim complex Hilbert space still contains a continuum of pure states, observables, amplitudes, and Born probabilities. It does *not* imply dyadic probabilities.
3. **Exact dyadic probability discreteness** — this *is* substantive but conflicts with ordinary QM. For generic spin measurement angle θ, `cos²(θ/2)` is irrational. To preserve (FQ), the paper must restrict either the allowed angles, the allowed states, or the allowed times. "Schrödinger evolution is preserved" then becomes false in any operationally meaningful sense.
4. **Holographic entropy bound** — the Bekenstein/Bousso bound constrains *entropy*, not the probability simplex. It does not derive dyadic discreteness.

The paper acknowledges multiple readings but slides between them; the strongest reading (3) modifies the physical content of QM, contradicting the "we modify nothing" claim.

### A.5 Algorithmic compactness (Theorem 5) is overstated

Finite representability of probability values ≠ computability of the map from physical setup to probability value. The paper proves only the first; it claims the second. Four distinct notions need to be separated: finite representability, computability, efficient computability, physical constructibility.

### A.6 Proposition 6 (well-formulation theorem) does not follow

The strongest single technical objection. The proposition is not rigorous as stated:

- **Cardinality does not determine well-formulation.** Bohmian mechanics is a single-world theory over a *continuum* configuration space. GRW flash ontology uses continuous spacetime locations. Classical mechanics has continuous outcome spaces. None is ill-formulated.
- **Finite probability values do not imply finite outcome sets.** Many outcomes can share the same probability; (FQ) on probabilities doesn't induce a finite outcome partition without additional structure.
- **"Empirically distinct" is not formalized.** The proposition's central term has at least six plausible definitions, each giving a different result.
- **Necessity is not established.** Corollary 6.1 claims (FQ) is *necessary* for single-world realism to be well-formulated. This is too strong — counterexamples (Bohm, GRW, classical SM) are direct.
- **Risk of being tautological.** If "well-formulated" is defined as "finite-set selection," the proposition is nearly trivial. If "well-formulated" has independent meaning, the paper hasn't established that continuum-based single-world realism fails it.

The defensible reading is much weaker:

> "A finite-information restriction may make a primitive single-outcome postulate less metaphysically extravagant by replacing continuum actuality with finite record actuality."

That is interesting but it is not necessity, and it is not a theorem.

## B. Impact analysis by audience

### B.1 Foundations journals (*Foundations of Physics*, SHPMP, PhilSci-Archive)

**Likely reception: mixed to negative.**

- *Foundations of Physics*: might consider if framed as speculative interpretive proposal, but **not** as proving a new measurement-problem theorem.
- *SHPMP*: harder. Philosophers will demand sharper modal/metaphysical semantics and will notice that "one outcome is actual but not derivable" is an extra actuality postulate.
- *PhilSci-Archive*: open venue; the paper might attract discussion but its strongest claims will be challenged.

**Best case:** "Interesting finite-information metaphysics, but not a solution to the measurement problem."
**Worst case:** "A dressed-up restatement of the measurement problem plus an unmotivated discreteness axiom."

### B.2 Quantum information / axiomatic reconstruction (Hardy, Chiribella, Masanes)

**Likely reception: not impressed.**

The Hardy/Chiribella/Masanes program is operationally precise. (FQ) is not a reconstruction principle — it doesn't derive Hilbert space, Born rule, purification, local tomography, tensor product structure. "All probabilities are dyadic rationals with bounded denominator" disrupts the convex structure central to generalized probabilistic theories.

The community will demand: *what are the allowed preparations? what are the allowed effects? how does composition work?* Without those operational specifications, (FQ) reads as a constraint slogan, not an axiom of a physical theory.

### B.3 Modal interpretations (Vermaas, Bub, Dieks)

**Likely reception: family resemblance acknowledged, incompleteness flagged.**

Modal interpretations supply a modal semantics — rules for which observables have definite values. This paper doesn't supply such a rule. The Vermaas/Dieks/Bub-style reader will say: "you are gesturing toward a modal interpretation while refusing to do the modal work." Finite probabilities do not give a value-state assignment by themselves.

### B.4 Working physicists outside foundations

**Likely reception: ignored or regarded as philosophical.**

The paper's own disclaimers ("no new dynamics," "no new predictions," "no operational restriction at lab scales") make the proposal empirically inert. The neutrino section will attract negative attention because the damping formula is not derived. Working physicists are allergic to speculative phenomenology without a model.

### B.5 Public-facing foundations audience (Carroll, Wallace, Bohm debate)

**Likely reception: rhetorically attractive headline; sophisticated critics will attack.**

The slogan "one wave function, one world, finite information" is strong. It positions cleanly against Many-Worlds excess and Bohmian hidden variables.

But sophisticated public-facing commentators will attack:

- **Everettians (Carroll, Wallace):** "You have not explained what selects one branch, so you have merely reintroduced collapse or hidden variables verbally while denying it formally."
- **Bohmians:** "If you want one world, add a primitive ontology and be honest about it."
- **Collapse theorists:** "If you want one outcome, you need dynamics."
- **Copenhagen/QBism:** "If you do not solve the outcome problem, you are just repackaging instrumentalism."

**Danger:** the broader audience may misread the paper as "holography solves the measurement problem" despite the disclaimers. The conclusion's closing slogan invites this misreading.

## C. The honest path forward

GPT-5.5's recommended retreat:

> "The defensible thesis is weaker: 'A finite-information restriction may make a primitive single-outcome postulate less metaphysically extravagant by replacing continuum actuality with finite record actuality.' That is interesting. It is not yet a theorem, not yet an interpretation, and not yet a physical theory."

Three specific repairs required:

1. **Fix φ_i definition.** Either (a) define it as an actuality predicate explicitly outside the formal language (a *meta*-proposition), or (b) abandon the "undecidability" framing entirely and present the result as "the formalism lacks an actuality predicate" — which is the measurement problem in standard form.

2. **Acknowledge the extra ontological commitment.** Single-outcome realism *is* an extra commitment beyond the wave function. The paper should say so rather than hide it under "no hidden variables."

3. **Retreat Proposition 6 from "necessary" to "useful."** Reformulate as: "(FQ) provides a finite-set framing under which the single-outcome commitment is more parsimonious," not as a necessity theorem.

These three repairs cost the paper its strongest rhetorical claims but make it defensible.
