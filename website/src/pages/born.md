---
layout: ../layouts/Deep.astro
title: How the Born rule emerges
eyebrow: The interpretation, in plain language
description: Probabilities |c_k|² as typicality, not a dice-roll — the one ingredient Born needs, why it cannot be avoided, and why it is nonetheless unique and forced. The honest version.
---

There is one wave function, it never collapses, and it just keeps evolving smoothly. The twist that lets a
*single* world survive: a bounded region of space holds only finite information, so it physically cannot
carry two macroscopically distinct records at once. After decoherence, only one record fits. So each run,
**you** — who are just a large, redundant record inside the wave function — end up *being* one outcome. Not
because the universe reached in and picked one, but because there is only room for you to be one. (That this
finite-capacity bound really forbids the two-record state is the program's [open crux](/theory), the
Macroscopic Definiteness Conjecture — assumed here.)

## So what is a "probability"?

If nothing collapses and there is no dice-roll, where does "70% chance" come from? The answer is
**typicality** — the same move that makes ordinary statistical mechanics work.

Think of a gas. The microscopic laws are reversible and have no arrow of time, yet a gas always spreads out.
Why? Because you add *one* ingredient — a way of counting microscopic states (the uniform measure) — and then
*almost every* starting configuration leads to spreading. "The gas spreads" is not derived from the laws
alone; it is "almost all microscopic ways of starting do this." That is Boltzmann's H-theorem.

The Born rule is the exact quantum version. The probability of outcome $k$ is not a chance the universe
takes — it is **the fraction of microscopic ways things could have started that make a record like you end up
as outcome $k$.** Across many runs, typical starting conditions show outcome $k$ a fraction $|c_k|^2$ of the
time. That fraction *is* the Born probability. What looks like a die is the typicality of which realization a
record like us finds itself to be.

## The one ingredient you have to add

To count "the fraction of ways things could be," you need a measure — a notion of which microscopic
configurations carry how much weight. The single ingredient Born needs is this:

<div class="note"><strong>The one posit.</strong> The natural weight of a microscopic configuration is its
<em>squared amplitude</em> — the |Ψ|² (Hilbert-space) measure. That is the entire input. Everything else
is a theorem.</div>

## Why you cannot get around adding it

This is what the machine-checked work pinned down. Two hard impossibility results say the squared-amplitude
weight genuinely has to be *put in*, not derived from cheaper stuff:

- **You cannot squeeze Born out of structure alone.** Any rule that respects all the obvious facts — definite
  records, decoherence, no faster-than-light signalling — could equally well be "probability $\propto$
  amplitude to the power $\alpha$" for some other power. The structure does not see the exponent. So
  decoherence and records, by themselves, *cannot* give you the "2" in $|c|^2$.
- **You cannot get it by counting copies.** The tempting idea — a louder branch must leave *more* environment
  imprints, so just count imprints — is provably false. A loud branch and a faint branch leave the **same
  number** of distinct records; the amplitude scales each record, it does not multiply how many there are.
  Counting is discrete and blind to the amplitude; the weight is continuous. Counting can never reproduce it.
  (This is also why the answer cannot be "count the worlds.")

So the weight must be assumed. Here is the part that makes that honest rather than embarrassing.

## Why it is nonetheless unique and forced

Granting that single, minimal assumption, the rule is **not arbitrary** — it is the *only* one possible.
**Gleason's theorem** (wired into the formalization) says: the moment you ask for any sensible probability
assignment at all — every yes/no question gets a probability, and compatible questions add up — squared
amplitude is the *unique* possibility. You do not get to choose the power $\alpha$. Asking for a coherent
probability *at all* already forces Born.

And it is stable on top of that: even if you started with the *wrong*, non-Born weighting, the dynamics
relaxes it back to Born — the same way a gas out of equilibrium settles down (a finite **H-theorem**, also
machine-checked). Born is not a fragile choice; it is the equilibrium the dynamics is pulled toward.

## The bottom line, honestly

Born emerges like this:

1. No collapse — each run, you can only *be* one record.
2. "Probability" means **typicality**: the fraction of microscopic possibilities that make you that outcome.
3. You weight those possibilities by **squared amplitude** — the one irreducible ingredient.
4. That ingredient is **not optional and not derivable from less** (both proved), **but it is unique** the
   instant you ask for any consistent probability at all (Gleason), and it is the **attractor** the dynamics
   relaxes to (H-theorem).
5. So across many runs, typical starting conditions show frequencies exactly $|c_k|^2$. That is Born.

In one sentence: **Born is what "typical" looks like when you measure microscopic possibilities with the
squared-amplitude yardstick — and that yardstick is the single thing every single-world version of quantum
mechanics must assume, which, the moment you assume any sensible probability at all, is forced to be exactly
squared amplitude and nothing else.**

<div class="note"><strong>Honest scope.</strong> This is a <em>reduction</em>, not a derivation from nothing.
The squared-amplitude measure is an irreducible posit — and we <em>prove</em> it has to be one. That is not a
weakness peculiar to this program: Everett, Bohmian mechanics, and the decision-theoretic approaches all need
exactly this one ingredient. What the <a href="/papers">machine-checked work</a> adds is precision — that this
single, natural assumption is <em>all</em> you need, that nothing weaker works, and that it makes Born unique.
The status on the chain is <a href="/open-problems">open · reduced</a>, not closed.</div>
