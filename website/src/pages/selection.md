---
layout: ../layouts/Deep.astro
title: Φ and λ — constitution and actuality
eyebrow: The interpretation
description: The (Φ, λ) account — the global wave function Φ constitutes everything that exists, and λ selects which admissible record is actual. No external observer, no fundamental collapse, no branching. The observer is the wave function.
---

There is an apparent paradox at the heart of the [conditional theorem](/theory): the global dynamics is
unitary, yet each run yields *one* outcome. Unitary evolution and a single result sound incompatible — it
is exactly the tension that pushed the textbook to a collapse postulate and pushed Everett to many worlds.

QIQT-H aims to dissolve it — not with a new law, but by separating two questions the measurement problem
usually runs together: **what is constituted** and **what is actual**. The first is answered by $\Phi$,
the second by $\lambda$. To be honest about it, this *relocates* the tension into $\lambda$ rather than
making it vanish; whether the relocation succeeds turns on the open problems below.

## Φ — the global wave function constitutes everything

$\Phi$ is the universal state. It evolves unitarily, always; there is no term in its dynamics that collapses
it, and there is no observer standing outside it. Apparatus, environment, record, and experimenter are all
patterns *within* $\Phi$ — there is no external vantage from which a measurement is performed on it.

This is the literal reading of the formalism taken seriously: **the observer is the wave function**. What we
call "an observer" is a macroscopic, decohered, redundantly-recorded substructure of $\Phi$ — the very kind
of *record* the [theory](/theory) is about. We do not look at $\Phi$ from outside; we are realizations of it.

## λ — which admissible record is actual

Granting the finite-capacity postulate and the [Macroscopic Definiteness Conjecture](/theory), a bounded
region cannot *instantiate* two macroscopic records at once. So after decoherence the admissible regional
content is single-record: the unitarily-evolved $\Phi$ offers several mutually-exclusive records, but only
one of them *fits* the region's information budget at a time.

$\lambda$ is the **selection** of which admissible record is the actual one. It is the move the textbook
misnames "collapse" — but here it is not a dynamical event. $\lambda$ adds nothing to the Schrödinger
equation, exerts no force, and leaves $\Phi$ untouched. It is a fact about *which* of the constituted,
unitarily-evolved alternatives we find realized, not a physical process that edits the state.

<div class="note"><strong>Two layers.</strong> $\Phi$ is constitution — what there is, evolving unitarily.
$\lambda$ is actuality — which admissible record obtains. This is one dynamical law <em>plus</em> an
actuality postulate, not a cost-free relabeling: keeping the layers apart is what lets "exact unitarity"
and "one outcome" coexist, but giving $\lambda$ a precise, dynamically-consistent form is still open.</div>

## No fundamental probability, no chooser

$\lambda$ is not a random draw made by a privileged agent, and it is not an extra stochastic law bolted on.
There is no fundamental chance and no fundamental choice in QIQT-H. Probability is meant to *emerge*: across
many runs, the actual records distribute with frequency $|c_k|^2 = \omega_\Phi(P_k)$ for *typical*
microscopic initial conditions. What looks like a probability is the typicality of which realization a
record like us finds itself to be — not a die that $\Phi$ rolls.

That this typicality reproduces the Born weights is **not yet derived**; it is the
[Born-from-typicality problem](/open-problems). And it carries a real risk of circularity: until the
typicality measure $\mu$ — over uncontrolled microscopic initial conditions, or over admissible
$\lambda$-histories — is specified *independently* of the Born weights, this is a target, not a derivation.
Likewise, making $\lambda$ precise as a selection compatible with the unitary dynamics — that exactly one
admissible record obtains, not zero, and that the admissible space is dynamically invariant — is the
[dynamical-realization problem](/open-problems). The ontology here is coherent; these pieces of it are open.

<div class="note"><strong>How far this is pinned down.</strong> The Born-from-typicality claim above is
backed by a machine-checked reduction (the <a href="/papers">Born-rule formalization paper</a>): records
give definite outcomes but no weights; among rules <em>p</em>&nbsp;&prop;&nbsp;<em>f</em>(<em>w</em>),
refinement-additivity, no-signalling under remote refinement, and Born are <em>equivalent</em>; and a
<em>no-go</em> proves the squared-weight family <em>w</em><sup>2</sup> obeys every Born-free premise — so an
extra principle is unavoidable, which is the circularity worry made precise rather than waved away. A finite
H-theorem then reduces the residual to a Born-agnostic typicality postulate (reversibility over a uniform
bath, plus mixing) instead of to <em>|Ψ|</em><sup>2</sup> itself. It sharpens the open problem; it does not
yet close it.</div>

## How this differs from the usual answers

- **Collapse interpretations** make the selection a *dynamical* event that breaks unitarity. Here $\lambda$
  is not dynamical and breaks nothing; $\Phi$ stays exactly unitary.
- **Many-worlds** keeps every decohered branch as an existing world. Here the unselected components of
  $\Phi$ are *not* actual worlds: a region admits only one macroscopic record, so the alternatives are
  mutually-exclusive *candidates* for actuality that remain unactualized, not coexisting worlds.
- **Bohmian mechanics** adds hidden particle trajectories as the actual configuration. In the broad
  (Bell / modal) sense $\lambda$ is *also* an extra actuality variable beyond $\Phi$ — but it is not
  Bohmian: it is a record-valued selector over decoherence-defined alternatives, not a trajectory in
  configuration space.

## Locality and Bell — and why this is not superdeterminism

A single-world ontology has to face Bell. QIQT-H is **not superdeterministic**: it does not correlate the
measurement settings with $\lambda$, and it does not deny measurement independence. The Bell correlations
come from the *nonlocal global state* $\Phi$ — entanglement — exactly the source they have in Everett,
together with a **contextual** actuality selection (which record is actual can depend on what is actually
measured). The settings stay free; the price for Bell is contextuality and a global consistency condition
on $\lambda$ across overlapping regions, **not** a conspiracy between past and future. The one place
superdeterminism could sneak in is the typicality measure — so it must be over the *uncontrolled*
microstate in the ordinary, setting-independent sense (as in Bohmian quantum equilibrium or Everett
typicality), never a measure tuned to the settings.

## Honest scope

This page is the **interpretive layer** of QIQT-H, and it is more speculative than the
[machine-verified substrate](/formalization). The $(\Phi, \lambda)$ reading is a coherent ontology that
removes the external observer and the collapse law — but $\lambda$ is only as well-defined as the
[open problems](/open-problems) that pin it down. Treat it as the program's proposed picture of what a
single world *is*, not as a result.

In the broad hidden-variable sense, $\lambda$ *is* an additional actuality variable beyond $\Phi$ — but it
is not a local, noncontextual preassignment of all outcomes. A completed version must define $\lambda$ only
on decoherence-selected record algebras, keep it consistent across overlapping regions, recover the Bell
correlations without signalling, and justify a typicality measure not secretly chosen to encode the Born
rule. Those are the bills the program still has to pay.
