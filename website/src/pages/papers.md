---
layout: ../layouts/Deep.astro
title: Papers
eyebrow: Read the work
description: The QIQT-H foundations paper, the formalization companion in preparation, and the machine-checked Lean corpus.
---

## Foundations paper

**One Wave Function, One World: Finite-Information Regional Algebras and the Macroscopic World from
Holographic Constraint.** Paweł Kapłański.

The primary statement of the program: the finite-information premise, the regional cost functional
$\chi_R$, the Macroscopic Definiteness Conjecture, the conditional single-record theorem, and an honest
account of what remains [open](/open-problems). Prepared for arXiv (quant-ph; cross-listed math-ph, gr-qc).

> *Status:* arXiv-ready preprint. The link will be posted here on submission.

## Formalization companion

**A machine-checked modular and relative-entropy calculus for the free-field coherent sector.** In
preparation.

A focused companion documenting the Lean&nbsp;4 / Mathlib development — the bounded Tomita–Takesaki
objects, the one-particle CGP relative entropy and its positivity, the free-field modular flow, and the
coherent-state entropy-reduction identity — with the full theorem index and the reproducible build. See the
[formalization](/formalization) page for the result list.

## The Lean corpus

The machine-checked substrate lives in the project repository. Every theorem is audited with
`#print axioms` and depends only on the standard classical foundations (`propext`, `Classical.choice`,
`Quot.sound`); the development carries no `sorry`.

- **Repository:** [github.com/kaplan196883/QIQT-H](https://github.com/kaplan196883/QIQT-H)
- **Build:** `lake build QIQTH` · **Audit:** `lake build QIQTH.AxiomAudit`

## How to cite

Until the preprint is live, cite as: P. Kapłański, *One Wave Function, One World*, preprint, 2026. A
DOI and arXiv identifier will be added here on release.
