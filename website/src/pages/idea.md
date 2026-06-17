---
layout: ../layouts/Deep.astro
title: The idea
eyebrow: In plain language
description: The measurement problem, finite information, and why a single world follows from a bounded region holding only finitely many bits.
---

Quantum mechanics, taken literally, predicts that a measuring device ends up in a superposition of
outcomes: the cat both alive and dead, the pointer at every reading at once. We never see that. The
textbook patch is the *collapse postulate*, where at measurement the state jumps to one outcome, by hand,
outside the unitary law. The many-worlds picture keeps unitarity but pays with an unobservable branching
multiverse. Both are answers to the same question: why one world?

## The hypothesis

QIQT-H starts from a single physical premise drawn from black-hole thermodynamics and holography:
**a bounded region of space has only a finite amount of operational information capacity**, on the order of
its boundary area in Planck units, $Q_R = A/4\ell_P^2$ (in natural entropy units). Finite, as a postulate
of the program.

Here is the sharp point — and getting it right took the program a while. Finite capacity *by itself* does
**not** forbid a superposition in the wave function $\Phi$: a superposition of two records is one vector in
the same finite-dimensional space, costing no more room than either record alone, and $\Phi$ evolves
exactly unitarily, keeping every branch. So $Q_{\max}$ is **not** a constraint on the wave function — but
(a correction we make honestly, 2026) it does **not force a single outcome either**. Decoherence makes the
macroscopic records non-interfering and redundantly objective, yet that removes *interference*; it does not
make one record *actual*. The single actual record is supplied by a non-dynamical selector $\lambda$ — an
Everett-like selection in which $\Phi$ keeps every branch and $\lambda$ marks exactly one as the actual
world. $Q_{\max}$'s honest role is the finite record **stage**: it bounds how *many* distinguishable records
a region can hold ($\le e^{Q_R}$), not whether two of them can be actual.

<div class="note">

<strong>The move.</strong> Collapse is not added as a new law and the wave function is
never touched: Φ stays exactly unitary, and a non-dynamical λ marks the one actual record.
<strong>Correction (2026).</strong> An earlier framing claimed the capacity bound <em>forbids</em> two
actual records because "classical record-contents add up" — that is a <strong>category error</strong>. The
holographic bound counts <em>independent</em> degrees of freedom, not a sum of redundant classical records
(R redundant copies of one fact carry H(X), not R·H(X)); and ordinary record entropy is capped at
~A<sup>3/4</sup>, about 10<sup>91</sup> for the observable universe against ~10<sup>122</sup> for the bound
— a permanent ~31-order gap (only black holes saturate A/4, and a black hole has no records). So capacity
never counts records out of existence; the single outcome is λ's, and "two actual records can't coexist"
reduces to a classical carrier holding one value (local single-valuedness) — itself supplied by λ, not by
the bound. The genuinely hard open piece is stitching the per-region actualities into one global,
Lorentz-covariant λ.

</div>

## What this buys, and what it doesn't

If the hypothesis holds, definiteness of the macroscopic world becomes a *consequence* of finite
information rather than a separate postulate. No collapse term, no branching ontology.

It does not, by itself, hand you the **probabilities**. That a given run yields outcome $k$ with frequency
$|c_k|^2$, the Born rule, is argued separately from the typicality of microscopic initial conditions
across runs, and that argument is [still open](/open-problems). Until it is settled, QIQT-H is an account
of *definiteness* — why there is one outcome — not yet a complete interpretation that also says with what
frequency.

## Where it stands

This is a research program with a sharp core, not a finished interpretation. An earlier version leaned on a
*capacity-exclusion* conjecture — that a region cannot hold two macroscopically distinct *actual* records
because their information would overflow its holographic budget. We now regard that as a **category error**
(see the correction above), and the numbers make the point vivid: the budget is so vast — about $10^{66}$
bits for a cm² boundary, $\sim 10^{122}$ for the cosmological horizon — against ordinary record entropy of
$\sim 10^{25}$ bits and a structural ceiling of $\sim A^{3/4}\approx 10^{91}$ (for the whole observable
universe), parametrically below the $\sim 10^{122}$ bound, so the budget is never even remotely approached.
Even the universe's *total* realized entropy — black-hole-dominated, $\sim 10^{104}$ bits, which carries no
records — is only $\sim 10^{-18}$ of its holographic capacity. So capacity is *not* what gives single
outcomes; **λ is**. What survives — and is genuinely distinctive — is the no-collapse single-world ontology:
Φ exactly unitary, one non-dynamical actuality selector λ, the holographic bound supplying only the finite
record stage. Absent an *additional* dynamical law (a new postulate with a free parameter), the framework is
**empirically equivalent to standard quantum mechanics** — an interpretation, not new physics, stated
plainly. The mathematical *substrate* it borrows — modular theory and relative entropy, the bookkeeping of
regional information cost — is [machine-verified in Lean&nbsp;4](/formalization). Read on for the
[mathematics](/theory) or the [open problems](/open-problems).
