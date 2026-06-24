---
layout: ../layouts/Deep.astro
title: Cosmology, gravity, and the reach of the idea
eyebrow: What it does and doesn't explain
description: Does finite holographic capacity solve dark matter, or tame the infinities of quantum gravity? Honestly — it lives in the right neighborhood, but a counting principle is not a theory of dynamics.
---

A finite-information idea naturally invites the big questions: does it explain the *dark universe* — dark
matter, dark energy? Does it remove the *infinities* that plague attempts to quantize gravity? Both are worth
answering plainly, because the honest answer is the same in each case, and it comes down to one clean idea.

## Does it explain dark matter?

No — and it matters not to pretend otherwise. QIQT-H is an interpretation of quantum *measurement*: it
reproduces every prediction of ordinary quantum mechanics ([why](/idea)) — the selector λ is non-dynamical and
unobservable, so the framework is **operationally equivalent to Everett**, with no new measurable claim; its
content is ontological (one actual world), not empirical. Dark matter is the opposite kind of
problem — a stubborn anomaly in *gravity*: galaxies spin too fast, light bends too much, and the early-universe
pattern only fits with about five times more gravitating stuff than we can see. Fixing that needs new *matter*
or a new law of *gravity* — exactly the sort of new, measurable claim an empirically-equivalent interpretation
does not make.

What is *true* is gentler, and more interesting: QIQT-H's founding premise — that information in a region is
**holographically finite** (bounded by surface area, not volume) — is shared by serious programs that *do* take
aim at the dark universe.

<div class="note">

<strong>The right neighborhood.</strong> Erik Verlinde's <em>emergent gravity</em> treats
gravity itself as an entropy/information effect; in a universe with dark energy, the holographic bookkeeping
leaves an extra pull that mimics dark matter, reproducing flat galaxy rotation curves with no dark-matter
particle. And <em>holographic dark energy</em> uses the same finite-information premise to get a dark-energy
density of roughly the observed size.

</div>

But two honest catches. Those are theories of *gravity*; QIQT-H is a theory of *measurement* — the same
building, a different floor. And even the best holographic attempt (Verlinde's) is **contested**: it struggles
with galaxy clusters, with the Bullet Cluster — where the lensing mass is clearly separated from the visible
gas, strong evidence for actual dark *stuff* — and with the detailed cosmic-microwave-background peaks, all of
which the standard dark-matter-particle picture fits beautifully. So the holographic family has not *solved*
dark matter either. If anything, dark *energy* is the more natural thematic fit than dark *matter*.

## Does it remove the infinities of quantum gravity?

Also no, in the deep sense — but here a sharp paradox is worth meeting head-on: *if the idea is "finite," how
can it carry infinities at all?*

The intuition behind that question is mostly right. The infinities of quantum field theory are an **artifact of
the continuum over-counting** degrees of freedom — a whole volume's worth of vibrating modes, when holography
says only a surface-area's worth physically exist. A genuinely finite theory would not have them. The trouble
is that **QIQT-H does not actually implement its own finiteness**: it asserts a finite capacity but does all its
computing on top of ordinary infinite-mode continuum field theory — so it *inherits* the very infinities it
says should not be there.

And there is a catch even if you fixed that: **finite information is not finite dynamics.** The infinities come
from how fields *interact at short distance* (products of fields at a point, high-energy loops), not from how
many *records* you store. A ceiling on storage does not tame a force at short range. Counting is not
regulating.

There is also a genuine theorem in the way of the naive fix. In real relativistic field theory you simply
*cannot* place finitely many degrees of freedom in a region — the Reeh–Schlieder theorem (the "Type III"
nature of local observables): acting on the vacuum with operators from any small region already reaches the
entire infinite space. So "just make each region finite-dimensional" is not merely hard; in the continuum it is
forbidden.

<div class="note">

<strong>One real win — borrowed.</strong> Recent work (Chandrasekaran–Longo–Penington–Witten)
shows that including gravity and an observer turns a region's algebra of observables from "Type III" (no
well-defined entropy — everything divergent) into "Type II" (finite, well-defined entropy). That genuinely
removes <em>one</em> infinity — the divergence in regional <em>entropy</em> — and QIQT-H is built on it. But it
makes <em>entropy</em> finite; it does not renormalize gravity or cure singularities. And it is their result,
not QIQT-H's.

</div>

<div class="note">

<strong>"But you machine-checked the Einstein equations — isn't that quantum gravity?"</strong> No, and it is
worth being exact, because the <a href="/formalization">showcase theorem</a>
(<code>qiqt_gr_ppwave_showcase</code>) makes the gap precise rather than closing it. That result is a
<em>Jacobson "equation of state"</em> derivation: the <em>classical</em> Einstein field equations emerge as the
<em>thermodynamics</em> of a horizon, for a free field on a fixed background, <em>conditional</em> on three
carried inputs — the matter equation of motion, the holographic capacity law <strong>P4</strong>
(<em>S = A/4ℓ<sub>P</sub><sup>2</sup></em>), and a localization map. It supports exactly one claim:
<strong>the metric need not be a fundamental quantum field</strong> — gravity can be emergent, like a
temperature, so quantizing <em>g<sub>μν</sub></em> (gravitons, a path integral over geometries, the
perturbative infinities) may be the wrong problem. It does <em>not</em> support "no quantum gravity needed."
Two reasons. (i) The coefficient <em>η = 1/4ℓ<sub>P</sub><sup>2</sup> = 1/4ℏG</em> <strong>is Newton's
constant</strong> — so postulating P4 inserts the gravitational coupling through the entropy density; the
derivation has the <em>equation of state</em> but not the <em>statistical mechanics</em> (the microstates whose
counting would <em>give</em> <em>S = A/4</em>). (ii) The hard cases — singularities, the Planck regime,
black-hole microstates and information, and the lab tests of <em>gravitationally-induced entanglement</em> —
are <em>deferred</em> to exactly that undelivered micro-theory, not solved. So the problem is <strong>relocated,
not removed</strong>: from "quantize the metric" to "find the quantum degrees of freedom whose entanglement
yields <em>S = A/4</em> and the localization flux" — and QIQT-H currently <em>assumes</em> (P4) the very thing
such a theory would have to <em>derive</em>. The honest slogan: <strong>QIQT-H can remove the need to quantize
the metric as fundamental; it does not remove the need for a quantum statistical micro-theory of spacetime.</strong>

</div>

To actually quantize gravity you would have to *add* a real **holographic dynamics** — a covariant law for
finite regions, a short-distance mechanism replacing the usual field products, and the right low-energy limits
(Einstein's gravity plus the Standard Model). The frameworks that *do* UV-complete gravity (AdS/CFT, matrix
models) achieve it with **nonlocal** holographic degrees of freedom — never a finite-dimensional local box.

## Where the finite budget actually bites

It is worth making this quantitative, because the conclusion is sharp and easy to mis-state. Holography gives
a region of area $A$ a finite record budget $Q_R = A/4\ell_P^2$ bits; a system only *feels* that ceiling when
the information it wants to lay down approaches $Q_R$. Place real systems on that plane — what they demand
versus what the horizon allows — and a clean pattern appears.

<div class="note">

<strong>Everything observable is slack; only horizons saturate.</strong> A trapped-ion qubit, a cubic
centimetre of gas, the Earth, the Sun, the cosmic microwave background — every ordinary system sits
<strong>30–60 orders of magnitude below</strong> its holographic budget. Even the <em>whole observable
universe</em> runs far below the ceiling: its <em>total</em> entropy, dominated by supermassive black holes
($\sim 10^{104}$ bits), is about <strong>$10^{-18}$ of capacity</strong> ($\sim 10^{122}$ bits) — and its
ordinary <em>record</em> content is smaller still ($\sim A^{3/4}\approx 10^{91}$, a $\sim$31-order gap; see
<a href="/idea">the capacity argument</a>). The only systems that reach the ceiling $S = A/4\ell_P^2$ are
<strong>black holes and cosmological horizons</strong> — the maximal-entropy gravitational objects, which sit
on the line <em>by construction</em>.

</div>

And here is the honest punchline. We modelled the finite budget in concrete continuous systems — a particle in
a box, a harmonic oscillator in coherent, squeezed, thermal, and Fock states — to see whether the selector λ
leaves any fingerprint. It does not. The budget caps phase-space resolution exactly as ordinary semiclassical
state-counting already does; there is **no λ-specific correction anywhere**, and reading the energy-level
cutoff as "Bekenstein–Hawking" only re-labels the holographic bound rather than deriving a new effect. On the
one line where the budget *is* saturated — the horizon — the physics is **standard black-hole thermodynamics
(Bekenstein–Hawking)**, which every approach shares, not λ. Because λ is non-dynamical and Born-transparent, it
cannot produce a resolution cap, a cooling, or a deviation. So the map says, cleanly: **slack everywhere you
can measure, standard quantum gravity where it saturates, and λ inert throughout — operationally Everett across
the whole chart.**

<div class="note">

<strong>The relativistic rungs — Dirac and Klein–Gordon.</strong> The study extends cleanly to the relativistic
case. A particle in a box has <em>no</em> position floor (you can localise it arbitrarily); the oscillator has
a floor in <em>phase space</em> (the $2\pi\hbar$ cell); the <strong>Dirac equation</strong> — the richest in
structure — has a floor in <em>position itself</em>, set by the mass: the Compton wavelength
$\lambda_C = \hbar/mc$. Try to localise an electron below it and the energy cost exceeds $2mc^2$, so the vacuum
makes electron–positron pairs and the single-particle position <em>record</em> dissolves. The resolution
saturates at $\lambda_C$ ($\sim$35 bits in a centimetre), and the 4-spinor adds a clean <em>2-qubit internal</em>
record (spin ⊗ particle/antiparticle) — the <a href="/ladder">bit → qubit ladder</a> realised in a real
relativistic equation. Strikingly, that handoff is not arbitrary: in limited bit space the non-relativistic
Schrödinger equation already acquires a maximum signal speed $v_{\max} = \hbar/ma$ on its position grid (a
lattice 'light cone'), and that speed reaches the true light speed $c$ <em>exactly</em> at $a = \lambda_C$ — so
the bit-limited Schrödinger picture runs out of room and gives way to Dirac and Klein–Gordon precisely at the
Compton wavelength.

<strong>Klein–Gordon</strong>, the spin-0 case, is the minimal rung — and the one that teaches the most. It
shares the same Compton floor but strips the record to its smallest: no spin, just a single charge/sign qubit
(and <em>zero</em> for a neutral scalar). It also exposes an obstruction Dirac avoids — its conserved density
is <em>indefinite</em> (it can go negative), so $|\phi|^2$ is not a record law at all and single-particle
position records are ill-defined. The honest fix is the field: Klein–Gordon is a <em>tower of oscillators</em>
(one per mode), whose records are particle-occupation numbers — looping the relativistic ladder straight back
to the oscillator rung.

Yet for both the verdict is identical: the floor is <strong>particle creation</strong> (set by the mass —
standard relativistic QFT), not λ and not holography (the budget stays $\sim$70 orders slack); λ inert ⇒ still
operationally Everett. The richest rung and the minimal one teach real physics and add no λ — thesis-empty,
like the rest.

</div>

## The one wall, every time

Notice the pattern. Dark matter, the infinities of quantum gravity, decoherence rates, a quantum-computing
ceiling — every one of these is about **dynamics**: forces, rates, short-distance behaviour. QIQT-H's
finiteness is **kinematic**: a counting principle, about how much information a region can hold.

<div class="note">

<strong>Counting is not dynamics.</strong> Finiteness of <em>information</em> tells you how
much can be stored; it does not, by itself, give you a force, a rate, or a short-distance cutoff. Turning the
premise into any of those means <em>adding</em> a holographic dynamics — a new theory of gravity, and the
genuine unsolved problem.

</div>

But it is worth being concrete about what that *added* dynamics would actually do — because in genuinely
limited bit space the effects are sharp and computable, and they pinpoint exactly what QIQT-H would have to
become to be testable.

<div class="note">

<strong>What a <em>dynamical</em> bit-limit would do — and why we don't see it.</strong> Make the finiteness
<em>dynamical</em> (a genuine cutoff $Q_{\text{eff}}$, a real minimum length) rather than an inert tag, and the
impact is concrete: the canonical commutator $[x,p]=i\hbar$ becomes <em>impossible</em> — a finite Hilbert
space forces $\operatorname{Tr}[x,p]=0\neq\operatorname{Tr}(i\hbar\mathbf{1})$, so the Heisenberg algebra
<em>must</em> deform; position turns <em>discrete and bounded</em> (a finite lattice with a hard edge — a
built-in UV cutoff); and a minimum length gives a <em>generalized uncertainty principle</em> that shifts every
bound spectrum. But the size of each is the ratio $(\Delta x_{\min}/L)^2$, so it is order one only when the
floor is comparable to the system — a tiny-budget toy, or a <em>saturated horizon</em> (where it simply
<em>is</em> Bekenstein–Hawking). For an atom the only real floor is the Compton length, and its impact —
$\alpha^2$, the fine structure — is plain relativistic QM; anything Planckian is $\gtrsim$45 orders below
measurement. Crucially, <strong>QIQT-H's λ is inert and produces none of this</strong>: to predict any of it you
must <em>add</em> the dynamical $Q_{\text{eff}}$ — a free parameter, not a consequence of the bound. That added
postulate is exactly what would turn the interpretation into testable physics, and exactly what it does not yet
contain.

</div>

There is, however, one reading of the finiteness that *is* falsifiable — and it is worth stating plainly, with
its price.

<div class="note">

<strong>The one falsifiable version — λ as a finite-information generator.</strong> Instead of an inert tag, let
λ be a finite-information deterministic <em>generator</em> of the actual history — a finite rule, in the spirit
of 't Hooft's deterministic quantum mechanics. Then the finiteness has teeth. A generator with a budget of $B$
bits can reproduce Born statistics only up to a data size $\sim 2^B$: beyond that its output must repeat or
reveal structure, so quantum 'randomness' would carry finite-information signatures — periodicity,
compressibility, faint correlations — at large enough scales. Unlike the inert reading, this is a
<strong>concrete, falsifiable prediction</strong>: quantum randomness is pseudo-random. So far every test of
quantum random-number generators finds <em>no</em> such structure — fully consistent with a very large budget,
but a genuine ongoing test.

Two honest catches keep it grounded. The break is at $\sim 2^{Q_R}$; for the holographic budget
$Q_R \sim 10^{70}$ that is $2^{10^{70}}$ events — never reached (the observable universe holds
$\sim 10^{120}$), so it stays <em>operationally = QM</em> in practice, becoming observable only near a horizon,
or if quantum randomness is far more information-limited than holography suggests. And it is a <em>different,
deterministic</em> ontology: it must pay Bell's price (nonlocality or superdeterminism — the generator's seed
correlating with measurement settings) and still owes an account of <em>why</em> the generator reproduces the
Born measure. So it is not a free prediction — but it is the one place the finite-information idea becomes a
genuine, testable-in-principle claim rather than an interpretation.

<strong>Pushed to its end — the wall is the Poincaré recurrence.</strong> A sharper look closes the testability
question with a <em>fact</em>, not a free parameter. The generating <em>code</em> — the laws of physics plus a
simple initial state — can be tiny, so the universe may well be a <em>simple</em> deterministic program. But a
program's repeat-time is set by the <em>state</em> it evolves, not by the size of its code: it cycles only when
its full microstate recurs. That state carries the universe's realized <em>entropy</em>, $\sim 10^{104}$ bits,
and ordinary thermalizing dynamics wanders through all of it — so the generator would only "repeat" at the
<strong>Poincaré recurrence time</strong>, $\sim 2^{10^{104}}$, longer than the age of the universe by some
$10^{103}$ orders of magnitude. Nothing shrinks that: the universe's high entropy is a measured fact. So "the
world is a simple generator" can be <em>true and holographically motivated</em>, yet its one fingerprint — the
randomness eventually repeating — is buried at the recurrence time, forever out of reach. What is left is then
not an experiment but a <em>choice of picture</em>: a simple deterministic program whose randomness is the
ergodic unfolding of a low-complexity seed, versus an inert λ on Everett — two descriptions of exactly the same
observations.

</div>

So the honest verdict across cosmology and quantum gravity is one sentence: **QIQT-H lives in the right
neighbourhood — holography, finiteness, the very premises serious people use to attack the dark universe and
the infinities — but a counting principle is not a theory of dynamics, and turning it into one is exactly the
work that remains undone.** That is not a dead end; it is a clear marker of where the real frontier is, and of
what the idea honestly is today: a deep *re-telling* of quantum mechanics, not yet a rival to general
relativity. See the [open problems](/open-problems) for what would have to be built.
