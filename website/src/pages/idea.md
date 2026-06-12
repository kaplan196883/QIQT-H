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

A wave function that recorded two macroscopically distinct outcomes at once, pointer-left *and*
pointer-right with all their correlated environmental traces, would be a far richer object than one
recording a single outcome. Now, finite capacity *by itself* does **not** forbid the superposition — a
finite-dimensional space still contains plenty of superposed distinguishable states. The load-bearing,
nonstandard claim is sharper: *physically instantiating* two macroscopic records in a region would cost
more information than its bound allows, so the two-record state is inadmissible there. That claim — the
**Macroscopic Definiteness Conjecture** — is the crux of the whole program, and it is unproven.

<div class="note"><strong>The move.</strong> Collapse is not added as a new law. Conditional on the
conjecture, multi-record regional states are inadmissible because they would exceed the region's
information capacity. After ordinary decoherence has made the records redundant and stable, only
single-record content fits — so the per-run *actual* content is single-record, one world, with no collapse
term added to the global dynamics.</div>

## What this buys, and what it doesn't

If the hypothesis holds, definiteness of the macroscopic world becomes a *consequence* of finite
information rather than a separate postulate. No collapse term, no branching ontology.

It does not, by itself, hand you the **probabilities**. That a given run yields outcome $k$ with frequency
$|c_k|^2$, the Born rule, is argued separately from the typicality of microscopic initial conditions
across runs, and that argument is [still open](/open-problems). Until it is settled, QIQT-H is an account
of *definiteness* — why there is one outcome — not yet a complete interpretation that also says with what
frequency.

## Where it stands

This is a research program with a sharp core, not a finished interpretation. It stakes itself on a
falsifiable claim: that a region cannot be held in a coherent superposition of two macroscopically
distinct records once instantiating them would exceed its holographic budget. The mathematical *substrate*
it borrows — modular theory and relative entropy, the bookkeeping of regional information cost — is
[machine-verified in Lean&nbsp;4](/formalization). The load-bearing physical conjecture, that two records
genuinely overflow the bound, is stated precisely and remains to be proved. Read on for the
[mathematics](/theory) or the [open problems](/open-problems).
