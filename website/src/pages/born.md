---
layout: ../layouts/Deep.astro
title: How the Born rule emerges
eyebrow: The interpretation, in plain language
description: Probabilities |c_k|² as typicality, not a dice-roll — the one ingredient Born needs, why it cannot be avoided, and why it is nonetheless unique and forced. The honest version.
---

There is one wave function, it never collapses, and it just keeps evolving smoothly. Decoherence makes the
macroscopic records non-interfering and redundantly objective — but that does **not** make one of them
*actual*. What does is a single non-dynamical fact, $\lambda$: of the many records the wave function carries,
$\lambda$ marks exactly one as the actual world. So each run, **you** — a large, redundant record inside the
wave function — *are* one outcome. Not because the universe reached in and collapsed it, and not (a 2026
correction we make honestly) because finite capacity *forbids* the others: the holographic bound only limits
how *many* distinguishable records a region can hold, not whether two can be actual — it is vastly too loose
for that (the universe runs at $\sim 10^{-18}$ of its capacity; see [the idea](/idea)). The "finite capacity
forbids two records" conjecture is **retired** as a category error. The single outcome is $\lambda$'s; the
wave function keeps every branch, exactly unitarily.

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

There is an even more visceral way to see *why the exponent is 2*. Quantum evolution **mixes** amplitudes —
it continuously rotates one into another (that is what a superposition is). Now ask: which power
$\sum_k |c_k|^\alpha$ stays fixed under that mixing? Only the square. Rotate the simplest pair $(1,0)$ by
$45°$ and you land on $(\tfrac{1}{\sqrt2},\tfrac{1}{\sqrt2})$; the total $|c|^\alpha$ comes out
$2^{\,1-\alpha/2}$, which equals the original $1$ **only when $\alpha=2$**. Every other exponent is *rigid* —
it tolerates relabelling and rephasing, but the instant amplitudes genuinely blend it changes. This is the
finite core of the Banach–Lamperti theorem, and it is the deepest "why 2": **the square is the only weight
the existence of continuous quantum evolution allows.** (It is also why, in every wave theory, energy goes
as amplitude *squared* — same conserved quadratic.) This is [machine-checked](/papers) too.

And it is stable on top of that: even if you started with the *wrong*, non-Born weighting, the dynamics
relaxes it back to Born — the same way a gas out of equilibrium settles down (a finite **H-theorem**, also
machine-checked). Born is not a fragile choice; it is the equilibrium the dynamics is pulled toward.

## The same square as the bell curve

You have met this square before — in the **bell curve**. Maxwell's 1860 derivation of how gas velocities are
distributed used exactly one assumption beyond independence: that the distribution looks the same in every
direction (rotational symmetry). Rotational symmetry *plus* independence forces the Gaussian
$e^{-(x^2+y^2)/2\sigma^2}$ — and the quantity sitting in the exponent is the rotation-invariant
$x^2+y^2$, the **very same square**. So the bell curve's square and Born's square are not a coincidence: both
are the unique quantity left unchanged by rotation/mixing. (Machine-checked: a rotation-invariant product
measure is forced to be Gaussian, the multiplicative mirror of the additivity that forces Born.) The honest
caveat is the same as always — "rotational symmetry" already carries the quadratic; it explains why the
Gaussian and Born wear the *same* square, not where the square ultimately comes from.

A footnote worth keeping: the law of large numbers (many runs converging to $|c_k|^2$) is a *consequence* of
the square, not its source. The bell-curve fluctuations around the Born frequencies presuppose the Born
probabilities; they don't create them.

## What about relativity? The boost

A natural worry: relativity mixes space and time with a **Lorentz boost**, which is itself a kind of rotation
— by an *imaginary* angle. Does that change the exponent? The answer is sharp, and it reveals something:
**Born must be quantum, not geometric.** A boost preserves the spacetime interval $t^2-x^2$ — but that carries
a minus sign, so it *vanishes on the light cone* and cannot be a probability (a probability can't be zero on a
real state). In fact any boost-invariant weight is forced to vanish on the light-cone direction
(machine-checked). So relativity does **not** carry Born through spacetime geometry. It carries it through a
different fact: in quantum theory a boost acts as a *unitary* rotation on the **state**, which still preserves
the positive $\sum|c|^2$. Born survives relativity precisely because it lives on the (positive-definite)
Hilbert space, never on the (indefinite) spacetime. Compact rotation *forces* the square; the non-compact
boost *forbids* any positive weight but the square — two sides of one coin.

## What is forced, and what is free — the exact split

The 2026 work pushed the posit one level deeper and then drew a sharp line through it. State-supervenience —
"the typicality of an outcome depends only on the state" — comes in two strengths, and they **come apart**
(this is now [machine-checked](/papers), axiom-free):

- **The weak half — naturality — is *blind*.** If the rule reprocesses the weights through *any* fixed function
  $f$ (probability $\propto f(|c_k|^2)$), relabelling the outcomes always permutes the weights the same way.
  Naturality holds for **every** $f$ — so by itself it cannot pick out the square. We prove the witness: the rule
  with $f(w)=w^2$ is a perfectly good natural, normalized probability, and it **disagrees** with Born on a
  concrete state (on $(\tfrac34,\tfrac14)$ it gives $\tfrac9{10}$, not $\tfrac34$). Weak supervenience does
  *not* force Born.
- **The strong half — refinement-additivity — is what bites.** Demand instead that splitting one outcome into
  sub-outcomes whose weights add be consistent — $f(a+b)=f(a)+f(b)$ — and the witness $f(w)=w^2$ is killed
  immediately ($(1{+}1)^2\neq 1^2{+}1^2$), while the identity ($f(w)=w$, i.e. Born) passes. And additivity
  *linearizes* — $f(n\,x)=n\,f(x)$ — which on a refinement into $n$ equal sub-records forces them to share
  weight equally. That equiprobability, run through the orthonormality bridge, **is** Born.

Is even the *weak* half forced by the bare ontology? The honest answer is that it depends on what you take a
"state" to *be* — and that dependency is the answer, not a dodge. On a **thin** reading (only $\Phi$ has
dynamics; $\lambda$ is a bare actuality fact), the weak half is **not** forced: the typicality measure is extra
structure, and because $\lambda$ has no guidance law there is no Bohm-/Liouville-style equivariance to single
one out. On a **thick** reading ($\Phi$ = a ray in Hilbert space with its inner product and symmetries, no
primitive labels), the weak half is essentially **built in** — constitutive, not a free lunch. But in **neither**
reading do you get Born: the **strong**, Born-selecting half — refinement-additivity — is unforced regardless,
and the no-go proves you cannot do without it. *That* is the whole irreducible content of Born, isolated and
named; the rest is a question about how much you pack into the word "state."

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
<strong>2026 update.</strong> The posit has now been driven one level deeper, axiom-free, and then split
exactly (see "What is forced, and what is free" above): the squared-amplitude weight reduces to
<em>state-supervenience</em>, whose <em>weak</em> half (naturality) is machine-checked to be blind to the
exponent — it cannot force Born — while the <em>strong</em> half (refinement-additivity) is the genuine
Born-selecting content, proved to discriminate the square and to linearize into equiprobability. A no-go (you
cannot get Born from nothing) shows that strong half is <em>unavoidable</em>. Whether even the <em>weak</em>
half is forced turns out to depend on how rich a notion of "state" you assume (thin vs thick ψ-monism; see
above) — but the irreducible premise is the <em>strong</em> half either way. The status on the chain is
<a href="/open-problems">open · reduced</a>, not closed.</div>
