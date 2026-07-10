---
layout: ../layouts/Deep.astro
title: The skeptic's FAQ
eyebrow: Read this first if you're suspicious
description: Honest answers to the objections a hostile reader brings — is this crank physics, what is actually claimed, why trust a solo researcher, isn't "machine-checked" overselling it, and what would change my mind.
---

If you landed here suspicious, good. A foundations-of-physics project claiming to touch the
measurement problem *and* gravity is exactly the profile that should trigger your alarm.
Here are the objections, answered straight.

## "Isn't this crank / crackpot physics?"

The reliable tell of crank work is **unfalsifiable overclaiming** — grand conclusions, no way
to check them, no acknowledgement of what's missing. This project is built to be the opposite:

- **Every mathematical step is checked by the Lean kernel**, and you can [re-run the whole
  thing yourself](/verify) — the claims are *checkable*, not asserted.
- The scope is stated in the negative as loudly as the positive: it does **not** claim to have
  solved quantum gravity or proved the universe works this way (see below).
- The open problems are [named and public](/open-problems), and the [claim card](/claim-card)
  lists every physical assumption still assumed rather than proven.

You don't have to trust the conclusions. You have to check the kernel and read the statements.
That's the point.

## "What do you actually claim — and not claim?"

**Claimed:**

- The *mathematics* is correct and rests on **no hidden axiom** (only Lean's standard three) —
  machine-verified, `sorry`-free, independently auditable.
- A coherent **single-world** interpretation: one exactly-unitary wave function Φ, plus a
  non-dynamical selector λ that marks one record actual. No collapse, no many-worlds.
- The Born rule is **reduced** to a single equilibrium postulate (P5), with machine-checked
  no-go theorems showing some such premise is unavoidable.
- A **conditional** chain from a finite-entropy bound to an **Einstein-form equation** for the
  free field.

**Not claimed:**

- **Not** that general relativity, or this interpretation, is physically true of our universe.
- **Not** that quantum gravity is solved — the gravity chain is conditional on named inputs
  (the Clausius/area law where not discharged, the value of *G*, the continuum limit,
  interacting matter).
- **Not** that the finite bound "forbids superpositions" or selects outcomes — that reading is
  **retired as a category error**; single outcomes are λ's doing.

## "Why should I trust a solo, unaffiliated researcher with no institution?"

**You shouldn't — and you don't have to.** That's the entire design. The [verification
capsule](/verify) collapses all *mechanical* trust to the Lean kernel: it rebuilds the proofs
from source on *your* machine and audits the axioms. My credentials, my institution, my
honesty — none of it enters. The one thing no proof script can settle for you is **adequacy**:
do the Lean statements actually mean what the prose says? That's exactly why the
[claim card](/claim-card) renders the *precise formal statement* — so you can judge that
yourself, in one place.

## "Isn't 'machine-checked' overselling it? Lean can't verify physics."

Correct — and I say so everywhere. Lean checks that the **mathematics** is valid and
axiom-free; it says **nothing** about whether the physical postulates hold in nature. Those are
scientific arguments in the paper, not theorems. The value of the formalization is precisely
that it **separates the two, in public**: what's *proven* (a conditional entailment) and what's
*assumed* (the labelled physical inputs) can't be quietly blurred together.

## "Isn't this just repackaging known results — Sakharov, Jacobson, Everett?"

Partly, and that's stated honestly. The 1/4 coefficient and the Einstein-equation-of-state step
are **re-derivations** of Sakharov induced gravity and Jacobson's argument; the single-world
picture sits in the modal / relationalist family alongside Everett. What is genuinely new:

- the **machine-verified substrate** — including formalization firsts like the first
  Tomita–Takesaki modular theory in any proof assistant;
- the specific **(Φ, λ)** architecture with a machine-checked Born *reduction*; and
- the **honest, fully auditable packaging** — a foundations program you can check line by line.

If someone shows a result was formalized earlier, priority is ceded gladly.

## "Doesn't a finite information capacity break Lorentz invariance?"

This is the sharpest objection to any "finite information" program, and it's a fair one: a
frame-dependent cutoff generically produces an observable speed-of-light splitting at one loop (the
CPSUV problem). QIQT-H faced it head-on with three machine-checked "Lorentz gates," and the result is a
single, sharp conclusion.

**Every frame-anchored reading of the capacity is *falsified*** (each a Lean theorem): sharp *and all
smooth* spatial cutoffs hit the unsuppressed CPSUV constant `g²/12π²` (`cpsuv_gate_sharp_fails`);
diamond-rest-frame ("tip-anchored") truncations fail at *first* order (`tipSplit_hasDerivAt_one`);
boost-averaging is not a regulator because the boost group is noncompact (`boostAvg_diverges`); and no
local Lorentz-invariant finite-capacity *cutoff* exists at all (`|k²| < Λ²` has infinite rapidity
volume).

**Exactly one reading survives:** the capacity as a **covariant, state/algebra-level *entropy*
constraint** — `Q_D` bounds the renormalized entropy of the diamond algebra in the covariant vacuum
(modular, frame-free, covariance built in *before* any loop), never a mode-count regulator in any frame.
Crucially, this surviving reading makes **no low-energy Lorentz-violation prediction** at all
(`stateLevel_noDeltaC2`) — it constrains *states*, not *dynamics*, so there's nothing to falsify. The
only door left open is the dynamical-realization gap (a *non-equivariant* enforcement mechanism could in
principle reopen it — `equivariant_enforcement_preserves_invariance`), which is listed among the
[open problems](/open-problems).

So the honest answer is the strong one: not only does finite capacity *not* break Lorentz invariance in
the surviving reading — the one-loop stress test **forces** "finite capacity" to mean finite *entropy*
(state-level, covariant), which is exactly [the reframe](/idea) the rest of the site states. The
frame-anchored / finite-matter reading a critic would attack is the one QIQT-H itself proves dead.

## "Was this written by an AI?"

The formalization was developed with heavy AI assistance, human-directed. This changes nothing
about the guarantee: **the Lean kernel checks every proof regardless of who or what wrote it** —
that's the whole reason verification matters here. An AI (or a human) that writes a wrong proof
gets rejected by the kernel. The methodology is itself documented in a companion paper.

## "What would change your mind? What's still open?"

The [open problems](/open-problems) are listed without hedging: the canonicity of the P5
typicality measure, the dynamical/Lorentz-covariant law of λ, the numerical value of *G* (pinned
to a Seeley–DeWitt coefficient behind a Riemannian-heat-kernel gap), the continuum Type III₁
limit, and interacting matter. Any of these could break, and the framework says so up front. The
honest verdict — including two adversarial red-team reviews — is that this is a **single-world
interpretation plus a holographic entropy bound and a conditional induced-gravity chain**, all
machine-verified where it can be, with the residue named. Not a theory of everything. A program
you can audit.

---

Still skeptical? [Run the proofs yourself.](/verify)
