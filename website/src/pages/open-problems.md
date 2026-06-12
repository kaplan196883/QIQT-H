---
layout: ../layouts/Deep.astro
title: Open problems
eyebrow: The frontier
description: The four gaps between a research program and a theory — the H2 crux, dynamical realization, Born from typicality, and FQ grounding — and what closing each one buys.
---

QIQT-H is a coherent, *conditional* research program. The [formalization](/formalization) strengthens the
floor it stands on; it closes none of the gaps below. There are four, in load-bearing order. The first is
decisive: the no-collapse conclusion has no bite until it holds.

## Gap 1 — Macroscopic definiteness (H2): the crux

**Claim to establish.** A regional content carrying two or more operationally distinct macroscopic records
has cost $\chi_R > Q_R$, exceeding the holographic capacity of any region that would host it.

**Why decisive.** Finite capacity *alone* does not forbid two-record superpositions: a finite-dimensional
Hilbert space happily contains superpositions of many distinguishable vectors. H2 is the nonstandard extra
claim that physically *instantiating* a two-record state costs strictly more than $Q_R$. Until this holds,
the conclusion is empty.

**What is done toward it.** Essentially nothing direct. The CGP calculus gives a *calculable* cost for
coherent excitations but no macroscopic lower bound. A data-processing / readout-channel route yields only
about $\log 2$ of classical information, not an area-scale violation.

**What it buys.** This turns the thesis from a conditional program into a genuine no-collapse *result*. It
is the headline.

**Difficulty.** Hard — genuine new physics. Likely a distinguishability-volume or modular-Hamiltonian
estimate rather than a data-processing argument. Formalizable only once a concrete cost model exists.

## Gap 2 — Dynamical realization

**Claim to establish.** Even granting H2, actual *unitary* measurement evolution produces exactly one
admissible record (not zero), and the admissible-state space is invariant under the dynamics.

**Why it matters.** The conditional theorem is a *static exclusion*: it rules out two-record states, but it
does not show the measurement dynamics *lands on* a single-record state, nor that one rather than zero
records appears, nor that a concrete interaction maps microscopic initial conditions to a single record.

**What is done toward it.** The finite-dimensional no-collapse representation and the record-net skeleton
are the finite shadow; $U_t\,\mathcal{K}\subseteq\mathcal{K}$ (`modUnitary_mapsTo_K`, the modular flow
preserves the standard subspace) is a continuum invariance fragment.

**What it buys.** Closes the loop from *constraint* to *mechanism* — makes "no collapse" a dynamical
statement, not just a kinematic exclusion.

**Difficulty.** Medium–hard, and **partly formalizable in finite dimensions now** — the best near-term Lean
target.

## Gap 3 — Born from typicality

**Claim to establish.** Among admissible microscopic initial conditions, the outcome-$i$ subset carries
Born weight $|c_i|^2 = \omega_\Phi(P_i)$.

**Why it matters.** H2 and Gap 2 give *single outcomes* but no *statistics*, so the theory is not yet
empirically adequate. This is logically independent of H2 — single-outcome exclusion does not need Born —
but it is mandatory for predictions.

**What is done toward it.** A finite typicality skeleton (`BornTypicalityFinite`: a finite weak law of
large numbers / Chebyshev bound) plus the finite Born representation, machine-checked. But the bare
*existence* of a recorded-history net is trivially true; the genuine problem is the **realization**: a
measure extracted from a fixed relativistic field theory and geometry, Born-pinned to an actual global
state, equivariant under a genuine Poincaré action, and Lorentz-invariant.

**What it buys.** Makes the theory predictive. This is the prize-aligned continuum track.

**Difficulty.** Hard (continuum). The finite track is done; the continuum realization is the cited frontier.

## Gap 4 — FQ grounding and the continuum

**Claims.** (a) *Ground* the bound $S_{\mathrm{ren}}\le Q_R$ rather than postulate it; (b) extend the
modular and entropy results from free-field coherent states to *general* states and the Type III $\to$
Type II continuum.

**Why it matters.** (FQ) is currently a postulate — the crossed-product construction gives the Type II
*entropy*, not the *bound* — and the formalization is free-field and coherent only.

**What it buys.** Weakens the central assumption; the Type III / unbounded-modular formalization would be a
Mathlib-grade contribution in its own right.

**Difficulty.** Very hard — it needs unbounded operator theory that Mathlib currently lacks (general
two-state relative modular operators require unbounded GNS). The cited frontier; not a blocker for the
conditional paper.

---

## In one paragraph

QIQT-H becomes a *theory*, rather than a conditional program, exactly when three things land: **H2**, that
a $\ge 2$-record regional content exceeds the holographic capacity, is quantitatively established; the
**dynamical realization** connects that static exclusion to actual single-outcome unitary evolution; and
**Born statistics** are derived from typicality. The [machine-checked substrate](/formalization)
strengthens the floor; it closes none of these.
