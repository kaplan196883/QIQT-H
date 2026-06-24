---
layout: ../layouts/Deep.astro
title: Papers
eyebrow: Read the work
description: The QIQT-H foundations paper, the formalization companion in preparation, and the machine-checked Lean corpus.
---

## Foundations paper

**One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from
Holographic Constraint.** Paweł Kapłański.

The primary statement of the program: the $(\Phi,\lambda)$ single-world no-collapse ontology, the
finite-information premise as a record *stage*, the regional cost functional $\chi_R$, and an honest account
of what remains [open](/open-problems). It includes the **retirement of the Macroscopic Definiteness
Conjecture** (capacity does not forbid records — a category error) and reframes the single outcome as λ's, with
the machine-checked covariant Born-*reduction* (to a single typicality premise, with a no-go that some premise is unavoidable) and consistency results as the substantive contribution. Prepared for arXiv
(quant-ph; cross-listed math-ph, gr-qc).

**[Read the PDF](/QIQT_Foundations_Paper.pdf)**
&nbsp;·&nbsp; arXiv-ready preprint. The arXiv link will be posted here on submission; for now the current
build is served directly from this site.

## Methods paper — the way in

**Trustworthy AI for Foundational Science: An Audited Human-AI Loop that Machine-Checks a Conditional
Derivation of the Einstein Field Equations from a Finite-Information Bound.** Paweł Kapłański.

The shortest way into the program. This is a cs.AI methods paper, not a physics paper: it describes the
human-directed, two-model loop (a coding agent that formalizes against the Lean compiler, an independent
model that adversarially reviews the design, a human who controls scope) and the soundness audit that
holds the project-axiom budget at zero. Running that loop on QIQT-H produced its headline artifact: a
machine-checked, project-axiom-free Lean theorem deriving, *conditionally*, the Einstein field equations
$a\,T_{\mu\nu}=G_{\mu\nu}+\Lambda g_{\mu\nu}$ from a finite-information (Bekenstein-type) capacity bound,
by a Jacobson-style equation of state. It is deliberately honest about scope — the cited physics inputs
are labelled hypotheses, the capacity postulate stays open — and it is the natural entry point for a
reader who wants to see *how* the program is built and checked before reading the
[foundations paper](#foundations-paper) above for *what* it claims.

**[Read the PDF](/QIQT_AI_Methodology.pdf)**
&nbsp;·&nbsp; arXiv-ready (cs.AI; cross-list quant-ph, math.LO). The arXiv link will be posted here on
submission.

## Formalization companion

**A machine-checked modular and relative-entropy calculus for the free-field coherent sector.** In
preparation.

A focused companion documenting the Lean&nbsp;4 / Mathlib development — the bounded Tomita–Takesaki
objects, the one-particle CGP relative entropy and its positivity, the free-field modular flow, and the
coherent-state entropy-reduction identity — with the full theorem index and the reproducible build. See the
[formalization](/formalization) page for the result list.

## Born-rule formalization

**Machine-Checked Reductions of the Born Rule: Conditional Theorems, a No-Go, and a Finite H-Theorem.**
Paweł Kapłański.

The rigorous companion to the [Φ&nbsp;and&nbsp;λ](/selection) account of Born-from-typicality. It isolates,
as Lean&nbsp;4 theorems, exactly what the Born rule needs beyond a no-collapse, single-record dynamics: the
record layer gives definite outcomes but no weights; among rules $p_k \propto f(w_k)$, refinement-additivity
$\Leftrightarrow$ Born $\Leftrightarrow$ no-signaling under remote refinement; a **meta no-go** shows the
power-law family $w^\alpha$ satisfies every Born-free premise, so some extra input is unavoidable; and a
finite **H-theorem** derives the residual measure-preservation from reversibility over a uniform bath plus
mixing. An honest reduction to a sharply-stated typicality postulate — not a derivation from nothing.

**[Read the PDF](/QIQT_Born_Reduction.pdf)**
&nbsp;·&nbsp; No `sorry`; depends only on the standard classical foundations (`propext`, `Classical.choice`,
`Quot.sound`).

## The Lean corpus

The machine-checked substrate lives in the project repository. Every theorem is audited with
`#print axioms` and depends only on the standard classical foundations (`propext`, `Classical.choice`,
`Quot.sound`); the development carries no `sorry`.

- **Repository:** [github.com/kaplan196883/QIQT-H](https://github.com/kaplan196883/QIQT-H)
- **Build:** `lake build QIQTH` · **Audit:** `lake build QIQTH.AxiomAudit`

## How to cite

Until the preprint is live, cite as: P. Kapłański, *One Wave Function, One World*, preprint, 2026. A
DOI and arXiv identifier will be added here on release.
