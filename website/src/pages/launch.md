---
layout: ../layouts/Deep.astro
title: "Anyone can claim they solved the measurement problem. Almost no one lets you check."
eyebrow: The launch
description: Why I built a foundations-of-physics theory and then made a computer verify every step — the verification capsule, the single-world idea, the honest ledger, and an invitation to break it.
---

Physics foundations has a credibility problem, and it's not hard to see why. The field is a
magnet for grand, untestable claims: someone announces they've dissolved the measurement
problem, or derived gravity, and there's no practical way for a reader to check — so the sensible
default is to ignore it. I've spent the last stretch building a foundations program, **QIQT-H**,
that tries to earn attention the only way I think a solo, unaffiliated researcher can: by making
it **checkable**.

## Don't trust me — run the proofs

The entire deductive substrate is formalized in **Lean 4 / Mathlib**, and the repository ships a
**verification capsule**. On your own machine, with minimal trust in me, it wipes the compiled
proofs, rebuilds them from source so the Lean kernel re-checks every step, replays an independent
kernel checker, and audits that the *complete* transitive dependency set is only Lean's three
standard axioms — no `sorry`, no hidden axiom.

```bash
git clone https://github.com/kaplan196883/QIQT-H && cd QIQT-H
bash verify/verify.sh   # → verify/out/claim_card.md
```

Out comes a **[claim card](/claim-card)**: the exact formal theorem, the complete trusted base,
and a ledger of every *physical* assumption still assumed rather than proven. All the mechanical
trust in the project collapses to three things — the Lean kernel, your reading of the rendered
statement, and the explicitly-listed physical inputs. Nothing else about me matters.

## The idea, in one breath

Quantum physics lets a system be in many possible states at once, yet every measurement shows
just one. The textbook patch — "collapse" — is bolted on by hand, outside the unitary law. QIQT-H
drops the patch. The wave function (**Φ**) is the whole of reality and never collapses; a single
extra, non-dynamical fact — **λ** — just marks *which* of the many decohered records is the one
we actually experience. No collapse, no parallel universes, no built-in dice. Because any bounded
region of space can hold only a *finite* amount of entropy (a holographic bound from black-hole
physics), the same picture also grows a conditional, Lean-checked version of Einstein's gravity
for the free field.

## The honest part

Here's what I am **not** claiming, stated as loudly as the rest: I have not proved the universe
works this way, and I have not solved quantum gravity. The gravity chain is *conditional* on named
inputs; the value of Newton's constant is a labelled frontier; whether the Lean definitions
faithfully model the physics is an adequacy judgment I leave to you (which is why the claim card
renders the precise statement). Two adversarial red-team reviews landed the verdict I now stand
behind: this is a **single-world interpretation, plus a holographic *entropy* bound, plus a
conditional induced-gravity chain** — machine-verified where it can be, with the residue named.
Not a theory of everything. A program you can audit.

## What actually got built

Along the way the formalization produced results that, to my knowledge, existed in **no proof
assistant** before: the **first complete Tomita–Takesaki modular theory** for an inductive-limit
state, an **unbounded Stone theorem** and spectral machinery beyond current Mathlib, and the **von
Neumann double-commutant theorem** — plus the headline physics chain, **Einstein's equations from
a finite-entropy bound**, conditional and free-field, end to end. Over 4,400 theorems, zero axioms
beyond Lean's standard three.

## The ask

I'd genuinely value scrutiny — especially the one thing the capsule can't mechanize: *does the
Lean statement mean what the prose says?* Read a [claim card](/claim-card), poke at the
[open problems](/open-problems), or just [run `verify.sh`](/verify) and tell me what breaks. If
you find something formalized earlier, or a hole in an argument, I want to know.

- **Site:** [qiqt.org](https://qiqt.org)
- **Code:** [github.com/kaplan196883/QIQT-H](https://github.com/kaplan196883/QIQT-H)
- **Read the idea:** [qiqt.org/idea](/idea) · **The suspicious reader's FAQ:** [qiqt.org/faq](/faq)

*— Pawel Kaplanski*
