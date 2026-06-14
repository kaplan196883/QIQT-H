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
exactly unitarily, keeping every branch. So $Q_{\max}$ is **not** a constraint on the wave function. What it
constrains is **actuality**. Two rival macroscopic records being *actual at once* would be two definite,
classical configurations — and classical, distinguishable contents **add up**, so realizing both would
exceed the region's budget $Q_R$. Hence at most one record can be *actual* per region; the actuality
selector $\lambda$ picks which one. The unrealized records remain in $\Phi$ — they are simply not actualized.

<div class="note"><strong>The move.</strong> Collapse is not added as a new law, and the wave function is
never touched. Q<sub>max</sub> constrains <em>actuality</em>, not Φ: because realizing two rival macroscopic
records would exceed the region's information budget, at most one is actual — and λ selects which.
This capacity exclusion is machine-checked at the actuality layer; Φ stays exactly unitary, with no
collapse term. What remains a conjecture — the <strong>Macroscopic Definiteness Conjecture</strong>, the
crux of the program — is that a genuine macroscopic record really costs near the full budget (so two rival
ones overflow); and the genuinely hard open piece is stitching the per-region actualities into one global,
Lorentz-covariant λ.</div>

## What this buys, and what it doesn't

If the hypothesis holds, definiteness of the macroscopic world becomes a *consequence* of finite
information rather than a separate postulate. No collapse term, no branching ontology.

It does not, by itself, hand you the **probabilities**. That a given run yields outcome $k$ with frequency
$|c_k|^2$, the Born rule, is argued separately from the typicality of microscopic initial conditions
across runs, and that argument is [still open](/open-problems). Until it is settled, QIQT-H is an account
of *definiteness* — why there is one outcome — not yet a complete interpretation that also says with what
frequency.

## Where it stands

This is a research program with a sharp core, not a finished interpretation. Its central physical conjecture
— that a region cannot hold a coherent superposition of two macroscopically distinct records once
instantiating them would exceed its holographic budget — is *in principle* falsifiable. Honestly, though,
that budget (the boundary area in Planck units) is so vast — about $10^{66}$ bits for a cm² boundary,
against record costs of perhaps $10^{25}$ bits — that it is never approached at accessible scales. Absent an
*additional* dynamical law with a much smaller effective capacity (a new postulate with a free parameter,
not a consequence of the bound), the framework is **empirically equivalent to standard quantum mechanics** —
an interpretation, not new physics, which we state plainly rather than advertise a near-term test. The
mathematical *substrate*
it borrows — modular theory and relative entropy, the bookkeeping of regional information cost — is
[machine-verified in Lean&nbsp;4](/formalization). The load-bearing physical conjecture, that two records
genuinely overflow the bound, is stated precisely and remains to be proved. Read on for the
[mathematics](/theory) or the [open problems](/open-problems).
