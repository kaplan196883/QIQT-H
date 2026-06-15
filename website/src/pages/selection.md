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

The unitarily-evolved $\Phi$ offers several mutually-exclusive macroscopic records; $\lambda$ marks exactly
one as *actual*. Decoherence first makes those records non-interfering and redundantly objective — but that
removes interference, it does not make one of them actual. The single actual record is $\lambda$'s doing.

<div class="note"><strong>Correction (2026).</strong> An earlier version said the finite capacity itself
<em>forbids</em> two actual records (their classical contents "would together exceed the budget"). That is a
<strong>category error</strong>: the holographic bound counts independent degrees of freedom, not a sum of
redundant classical records, and ordinary record entropy is capped at ~A<sup>3/4</sup> (~10<sup>91</sup>)
far below the bound (~10<sup>122</sup>) — a permanent ~31-order gap. So capacity does <em>not</em> exclude a
second actual record; "two actual records can't coexist" reduces to a classical carrier holding one value,
which is itself supplied by λ. Q<sub>max</sub>'s honest role is the finite record <em>stage</em> (how many
distinguishable records exist, $\le e^{Q_R}$), not the single-outcome selection.</div>

$\lambda$ is the **selection** of which admissible record is the actual one. It is the move the textbook
misnames "collapse" — but here it is not a dynamical event. $\lambda$ adds nothing to the Schrödinger
equation, exerts no force, and leaves $\Phi$ untouched. It is a fact about *which* of the constituted,
unitarily-evolved alternatives we find realized, not a physical process that edits the state.

<div class="note"><strong>Two layers.</strong> Φ is constitution — what there is, evolving unitarily.
λ is actuality — which admissible record obtains. This is one dynamical law <em>plus</em> an
actuality postulate, not a cost-free relabeling: keeping the layers apart is what lets "exact unitarity"
and "one outcome" coexist, but giving λ a precise, dynamically-consistent form is still open.</div>

## No fundamental probability, no chooser

$\lambda$ is not a random draw made by a privileged agent, and it is not an extra stochastic law bolted on.
There is no fundamental chance and no fundamental choice in QIQT-H. Probability is meant to *emerge*: across
many runs, the actual records distribute with frequency $|c_k|^2 = \omega_\Phi(P_k)$ for *typical*
microscopic initial conditions. What looks like a probability is the typicality of which realization a
record like us finds itself to be — not a die that $\Phi$ rolls. For the plain-language account of how this
yields $|c_k|^2$, see [How the Born rule emerges](/born).

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

## The λ construction, made precise

Stated sharply, $\lambda$ is **a single sample from a Lorentz-covariant probability law on record
histories** — four pieces:

1. **Stage** — the causal-diamond poset; for each region a finite set of decohered, redundantly-broadcast
   **candidate record alternatives** (not yet "actual"). The capacity bound is *posited* to limit their
   number — an actuality-layer assumption, not something the holographic entropy bound proves on its own.
2. **Histories** — compatible global assignments (one record per region, agreeing on overlaps), each a
   complete 4D history with no preferred time-slice.
3. **Law** — the Born weight $\mu_\Phi(\alpha)=\lVert C_\alpha\Phi\rVert^2$ (Born is **input** here),
   $\sigma$-additively extended, and *covariant as a law*: $\mu_{U_g\Phi}(g\alpha)=\mu_\Phi(\alpha)$.
4. **λ** — one history drawn from $\mu_\Phi$.

The key move: **a covariant measure is not a covariant selector.** Just as the rotation group has an
invariant measure on the sphere but no invariant point, the *law* $\mu_\Phi$ is Poincaré-covariant while a
*sampled* $\lambda$ generally is not a fixed point of the symmetry — ordinary sample non-invariance, not a
hidden preferred frame. So $\lambda$ need not be (and cannot be) an equivariant function of $\Phi$; it is a
contingent draw.

<div class="note"><strong>Now machine-checked (free-field sector).</strong> For the 1+1D free field this
covariant Born law is verified in Lean: a <em>σ-additive</em> measure exists (finite-fiber Kolmogorov
extension — the finiteness is the capacity bound), it is the same in <em>every Lorentz frame</em>, and it
satisfies the decoherent-histories <em>consistency</em> condition <em>Re D(α,β) = 0</em> exactly (this is
what makes the Born weights obey the probability sum rules). For <em>orthogonal</em> records the full
off-diagonal <em>D = 0</em> (strong), with an exact overlap-correction formula off orthogonality and a
redundancy law by which broadcasting drives <em>D → 0</em> (Quantum Darwinism). See the
<a href="/formalization">theorem index</a>. Born itself remains an <em>input</em>, not a derivation.</div>

<div class="note"><strong>Realm selection — the honest status.</strong> Picking <em>which</em> consistent
set of records (the realm) is the classic decoherent-histories gap (Dowker–Kent). Machine-checked:
capacity <em>alone</em> does <strong>not</strong> select a unique realm (distinct capacity-maximal record
bases exist); capacity <em>plus einselection</em> (the decoherence-selected pointer basis) does. Einselection
is an input, not yet derived — so realm uniqueness is reduced to it, not closed.</div>

## The λ-law, now machine-checked

What was, a year ago, a bare actuality postulate is now a *law whose every checkable piece is machine-verified*
(Lean&nbsp;4&nbsp;/&nbsp;Mathlib, axiom-free), at the **finite**, the **one-particle continuum** (the bounded
modular flow $\Delta^{it}$), *and* the **second-quantized free-field** ($\Gamma(\Delta^{it})$, a unitary group)
levels. The crossed-product "Type&nbsp;II dressing" idea for λ is retired as a category error; λ is
**Type-III-native**, riding the standard form and the modular automorphism. The verified law:

1. **Which records (kinematics).** *Which* pointer algebra carries λ's records is fixed by **Takesaki's
   criterion** — the modular flow fixes a pointer projection iff it commutes with the state ($[\rho,P]=0$),
   i.e. iff there is no coherence between the pointer sectors: *exact decoherence*. The decoherence map is then
   the state-preserving conditional expectation onto that algebra.
2. **Born weights.** Each record's weight is the algebraic state value $\omega(P_\alpha)=\lVert P_\alpha\Phi\rVert^2$
   — via the natural cone / vacuum state, *no trace* — and over a record family these are a genuine probability
   (on the genuine Fock vacuum state the single-mode record gives $(1\pm e^{-\lVert u\rVert^2/2})/2$).
3. **Persistence.** The decoherence map **commutes with the modular flow for all time**: a records-definite
   state stays definite, coherence never regenerates, the selected record is a fixed point of the dynamics. The
   selection does not un-select under evolution — the first genuinely dynamical result.
4. **The selection event.** An explicit constructor takes an actuality "seed" $s\in[0,1)$ to **exactly one**
   record (not zero, not two — single-world consistency), and the uniform seed measure of a record equals its
   Born weight, so the selection *realizes* Born as an across-run frequency.

<div class="note"><strong>The honest residual.</strong> The constructor reduces the whole selection to one
datum — <em>which seed is actual</em> — and that seed <strong>is</strong> λ: the single primitive a
non-dynamical single-world theory must take as given. Its dynamical origin is not derived (and arguably cannot
be, λ being non-dynamical by construction). Beyond the free-field sector the remaining mathematics is two cited
research walls — the Haagerup natural-cone <em>existence</em> in Mathlib, and the interacting case. So λ's law
is precise and verified where it can be; what is left is either <em>provably irreducible</em> (the seed; the
strong Born premise) or <em>genuine multi-year mathematics</em>.</div>

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

A single-world ontology has to face Bell. To be explicit: QIQT-H **is Bell-nonlocal** — like every
single-world theory that reproduces quantum statistics, the global law on $\lambda$ violates Bell *local
causality* ($P(a,b\mid x,y,\lambda_{\text{past}})\ne P(a\mid\dots)\,P(b\mid\dots)$). No-signalling and
microcausality *do* hold, but those are weaker, *operational* constraints; they do **not** rescue local
causality, and treating them as if they did would be a category error.

What QIQT-H is **not** is superdeterministic: it does not correlate the measurement settings with $\lambda$,
and it does not deny measurement independence. The Bell correlations come from the *nonlocal global state*
$\Phi$ — entanglement — exactly the source they have in Everett, together with a **contextual** actuality
selection (which record is actual can depend on what is actually measured). Assigning values only to the
records that are actually decohered in the actual context is also what dodges Kochen–Specker / Fine (no
noncontextual value-map over all counterfactual settings) — but it does *not* make Bell go away; the model
is irreducibly global/contextual. The settings stay free; the price for Bell is contextuality and a global
consistency condition on $\lambda$ across overlapping regions, **not** a conspiracy between past and future. The one place
superdeterminism could sneak in is the typicality measure — so it must be over the *uncontrolled*
microstate in the ordinary, setting-independent sense (as in Bohmian quantum equilibrium or Everett
typicality), never a measure tuned to the settings.

## Honest scope

This page is the **interpretive layer** of QIQT-H, and the *reading* of the machinery — what a single world
*is* — is more speculative than the [machine-verified substrate](/formalization). But $\lambda$ is no longer
just a picture: as recorded above, its **kinematic law, persistence, Born form, and single-outcome selection
are machine-checked** (finite through free-field, axiom-free). What stays genuinely open is narrower than it
once was — the *dynamical origin* of the actuality datum (the seed, which is λ itself; arguably irreducible for
a non-dynamical selector) and the cited continuum walls beyond the free field. Treat the *ontological reading*
as the program's proposed picture; treat the *law* as verified where it can be.

In the broad hidden-variable sense, $\lambda$ *is* an additional actuality variable beyond $\Phi$ — but it
is not a local, noncontextual preassignment of all outcomes. A completed version must define $\lambda$ only
on decoherence-selected record algebras, keep it consistent across overlapping regions, recover the Bell
correlations without signalling, and justify a typicality measure not secretly chosen to encode the Born
rule. Those are the bills the program still has to pay.
