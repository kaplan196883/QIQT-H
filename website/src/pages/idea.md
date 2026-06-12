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
**a bounded region of space holds only a finite amount of physical information**, on the order of its area
in Planck units, $Q_R = A/4\ell_P^2$. Not approximately finite. Finite, full stop.

A wave function that recorded two macroscopically distinct outcomes at once, pointer-left *and*
pointer-right with all their correlated environmental traces, would be a far richer object than one
recording a single outcome. The claim is that the two-record object is simply too large to be
*instantiated* in the region's finite ledger. It does not get to exist there.

<div class="note"><strong>The move.</strong> Collapse is not added as a new law. Multi-record states are
excluded because they would exceed a region's information capacity. After ordinary decoherence has made
the records redundant and stable, only single-record content fits, so the per-run state is already a
single world, with the global dynamics left exactly unitary.</div>

## What this buys, and what it doesn't

If the hypothesis holds, definiteness of the macroscopic world becomes a *consequence* of finite
information rather than a separate postulate. No collapse term, no branching ontology.

It does not, by itself, hand you the **probabilities**. That a given run yields outcome $k$ with frequency
$|c_k|^2$, the Born rule, is argued separately from the typicality of microscopic initial conditions
across runs, and that argument is [still open](/open-problems).

## Where it stands

This is a research program with a sharp, falsifiable core, not a finished interpretation. The mathematical
*substrate* it borrows, modular theory and relative entropy, the bookkeeping of regional information cost,
is [machine-verified in Lean&nbsp;4](/formalization). The load-bearing physical conjecture, that two
records genuinely overflow the bound, is stated precisely and remains to be proved. Read on for the
[mathematics](/theory) or the [open problems](/open-problems).
