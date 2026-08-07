---
layout: ../layouts/Deep.astro
title: "Anyone can claim they solved the measurement problem. Almost no one lets you check."
eyebrow: The launch
description: A Physical Review Letters paper derived the semiclassical Einstein equations from quantum relative entropy. I formalized that exact conditional chain in Lean, so you can re-run it — with every physical assumption printed in a claim card. The verification capsule, the single-world idea, the honest ledger, and an invitation to break it.
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
cat verify/verify.sh          # read it first — it's short
bash verify/verify.sh         # → verify/out/claim_card.md
```

(Don't want to run a stranger's shell script? A pinned **Docker** recipe rebuilds the whole
stack — Lean, Mathlib, the project — from source in a container; see
[`verify/README.md`](https://github.com/kaplan196883/QIQT-H/blob/main/verify/README.md). Toolchain
`leanprover/lean4:v4.30.0`; the clean-room build takes a while — that's the point.)

Out comes a **[claim card](/claim-card)**: the exact formal theorem, the complete trusted base,
and a ledger of every *physical* assumption still assumed rather than proven. All the mechanical
trust in the project collapses to three things — the Lean kernel, your reading of the rendered
statement, and the explicitly-listed physical inputs. Nothing else about me matters.

## The flagship: a holographic duality — in flat spacetime

The headline result is a **flat-space holographic duality**
(`FlatSpaceRecordGravityCorrespondence`): in the continuum limit, one finite-capacity information
system — the region-by-region bookkeeping of the wave function Φ — turns out to be, at once, two
things that looked separate: (i) free quantum matter, and (ii) the gravity that curves around it.
The sharp content is a single equality with three faces, holding for every region:

> micro record entropy  =  one-loop conical (heat-kernel) entropy  =  Area / 4·*G*<sub>ind</sub>

where *G*<sub>ind</sub> is the Sakharov-*induced* Newton constant of the **same** field content. The
same *G* computes both sides — the states of matter *and* the gravitational coupling — with no
calibration between them. That shared *G* is what makes it a **duality** (two independently defined
descriptions provably the same physics), not merely a dictionary.

It reaches the *shape* of AdS/CFT's holographic statement — one system, two descriptions, S = A/4*G*
with a shared *G* — but **in flat spacetime (our universe's local structure), from finite quantum
information (postulate P4) rather than branes and flux, and machine-checked.** It needs no
anti-de Sitter box and no string theory, and it does *not* claim to reproduce AdS/CFT's full
machinery.

**Honest status, because this is the crux.** The **finite evidence is proven** (stationary records,
ladder rotation, finite KMS, region entropy = mode-entropy sum, the calibration-free saturated
Sakharov cross-check — all axiom-free), and the **five continuum rungs are proven term by term**
(continuum entropy, the heat-kernel form, the exact conical coefficient, the Susskind–Uglum identity,
the saturation bridge). The **entailment is machine-checked**: the still-cited physical inputs,
carried as *explicit hypotheses* (never axioms), imply the correspondence — and *non-vacuously*, since
the middle area-law equality is **derived**, not assumed. What is **not** proved is the unconditional
statement: it remains a **conditional theorem** whose open assumptions are three named inputs
(a₁ = R/6, same-regulator, cutoff identification) plus the continuum-limit assembly. So the correct
reading, everywhere, is: *a machine-verified substrate plus a conditional-theorem correspondence — a
holographic duality for flat spacetime whose remaining inputs are named* — never "the duality is
proven."

## There's a Physical Review Letters paper for the gravity chain

You don't have to take the gravity claim on faith from a stranger, either. In 2026 Dorau & Much
published *"From Quantum Relative Entropy to the Semiclassical Einstein Equations"* in **Physical
Review Letters** ([arXiv:2510.24491](https://arxiv.org/abs/2510.24491)) — a clean argument that
Einstein's equations follow from the relative entropy of a quantum field across a horizon (a
quantum-information upgrade of Jacobson's 1995 derivation). It's a *paper*: "arguments indicating."

I formalized that **exact chain** in Lean, for the free field. Their derivation maps step for step
onto machine-checked theorems here — modular flow = geometric boost (`Fock.OneParticleBW`), relative
entropy = horizon energy flux (`ModularEnergyBound`), area variation via Raychaudhuri
(`DifferentialAreaLaw`), and the Einstein equations by stress-energy conservation (the
[claim card](/claim-card)) — and it even re-derives the 1/4 they assume.

Two honesties, stated up front. **Their paper came first** — public October 2025, PRL 2026, before my
GR chain was formalized — so I claim **no priority**. And on the load-bearing input: the PRL
*bare-assumes* the entropy–area relation `S = δA/4`. QIQT-H does more — it **proves `S = A/4G` as a
theorem** for its own induced area (one weight family carries both capacity and geometry; the separate
area label is deleted), reducing the physical input to a **single calibration**, machine-checked, with a
guard proving that calibration is load-bearing (without it the count is unbounded at fixed area). But
that one calibration is still *carried*, not derived from nothing — so their Letter vindicates the
shared **derivation chain** (relative entropy → modular theory → Jacobson → Einstein), not QIQT-H's
finiteness reading. What I add is that a computer checks every line, and you can re-run it. In one
sentence: **a top-journal result exists for this — I formalized its free-field chain in Lean, and
reduced its one entropy–area assumption to a single, guarded calibration.**

**What's new here, and what isn't** — stated plainly, because conflating them is what lets a skeptic
dismiss the work:

- *Not new:* the Dorau–Much relative-entropy route, the physical insight, and the claim that
  semiclassical gravity can be motivated from horizon relative entropy. That's their published result,
  and it came first.
- *New:* the **Lean 4 formalization** of the corresponding free-field theorem chain; an **explicit
  assumption ledger** (the claim card) so every physical premise is visible; a **machine-checked
  dependency** from those premises to the conclusion; the reusable operator-algebra / spectral /
  modular-theory infrastructure it needed; and the finding that the A/4G relation is *derived* for the
  induced-area construction, with a guard isolating exactly which calibration input is load-bearing.

This is a formalization contribution on top of a published physics result — not a physics priority
claim, and not a proof that gravity is emergent. See the full
[**PRL equation → Lean theorem mapping**](/prl-mapping) for the step-by-step correspondence.

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
assistant** before (pointers and corrections welcome): a complete **Tomita–Takesaki modular theory**
for an inductive-limit state, an **unbounded Stone theorem** and spectral machinery beyond current
Mathlib, and the **von Neumann double-commutant theorem** — plus the flat-space **record-code /
gravity correspondence** (the flagship duality above) and the **semiclassical Einstein equations from
a finite-entropy bound**, both conditional and free-field, end to end. Even the old coefficient wall
has moved: there is now a machine-checked **conditional a₁ = R/6** — the genuine Ricci scalar in the
short-time heat expansion, reduced to four named geometric inputs (one being actively closed), not yet
an unconditional value. Over **8,000 theorems** across **~1,100 files**, with **no project-specific
axioms and no `sorry`** — the final theorems depend only on Lean's three standard classical axioms.

## The ask

I'd genuinely value scrutiny — especially the one thing the capsule can't mechanize: *does the
Lean statement mean what the prose says?* Read a [claim card](/claim-card), poke at the
[open problems](/open-problems), or just [run `verify.sh`](/verify) and tell me what breaks. If
you find something formalized earlier, or a hole in an argument, I want to know.

- **Site:** [qiqt.org](https://qiqt.org)
- **Code:** [github.com/kaplan196883/QIQT-H](https://github.com/kaplan196883/QIQT-H)
- **Read the idea:** [qiqt.org/idea](/idea) · **The suspicious reader's FAQ:** [qiqt.org/faq](/faq)

*— Pawel Kaplanski*
