---
layout: ../layouts/Deep.astro
title: About
eyebrow: The program
description: What QIQT-H stands for, who is behind it, and the discipline of honest scope that governs the project.
---

**QIQT-H** stands for *Quantized Information Quantum Theory — Holographic*. It is a foundational research
program proposing that the definiteness of the macroscopic world is a consequence of one physical premise —
that bounded regions hold only finite physical information — rather than a separate collapse postulate or a
branching multiverse.

The program is the work of **Paweł Kapłański**. The mathematical substrate is developed and machine-checked
in Lean&nbsp;4 / Mathlib.

## The discipline

This site is written to a standard of honest scope. Three commitments govern it:

- **Label every link.** The argument is a five-step chain; each step is marked as postulate, verified
  calculus, conjecture, conditional theorem, or open. Nothing is presented as settled that is not.
- **Don't over-credit the formalization.** What is machine-verified is the modular and relative-entropy
  *calculus* for the free-field coherent sector — the bookkeeping behind the regional cost $\chi_R$. It is
  not the holographic axiom, not the central conjecture, not the Born rule. See
  [formalization](/formalization) and [open problems](/open-problems).
- **Standard axioms, named.** "No axioms" means no *project* axioms. The Lean proofs use only the standard
  classical foundations every Mathlib proof uses (`propext`, `Classical.choice`, `Quot.sound`) and add
  nothing of their own; they carry no `sorry`.

## Contact

Paweł Kapłański — [pawel.kaplanski@cognitum.eu](mailto:pawel.kaplanski@cognitum.eu).
Source and issues: [github.com/kaplan196883/QIQT-H](https://github.com/kaplan196883/QIQT-H).
