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

<strong>The relativistic rung — the Dirac equation.</strong> The study extends cleanly to the relativistic
case, and it is the richest of the three. A particle in a box has <em>no</em> position floor (you can localise
it arbitrarily); the oscillator has a floor in <em>phase space</em> (the $2\pi\hbar$ cell); the Dirac equation
has a floor in <em>position itself</em>, set by the mass — the Compton wavelength $\lambda_C = \hbar/mc$. Try
to localise an electron below it and the energy cost exceeds $2mc^2$, so the vacuum makes electron–positron
pairs and the single-particle position <em>record</em> dissolves. The record resolution saturates at
$\lambda_C$ ($\sim$35 bits in a centimetre), and the 4-spinor adds a clean <em>2-qubit internal</em> record
(spin ⊗ particle/antiparticle) — the <a href="/ladder">bit → qubit ladder</a> realised in a real relativistic
equation. Yet the verdict is identical: the floor is <strong>pair production</strong> (set by the mass —
standard relativistic QFT), not λ and not holography (the budget stays $\sim$70 orders slack); λ inert ⇒ still
operationally Everett. The richest case, and still thesis-empty.

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

So the honest verdict across cosmology and quantum gravity is one sentence: **QIQT-H lives in the right
neighbourhood — holography, finiteness, the very premises serious people use to attack the dark universe and
the infinities — but a counting principle is not a theory of dynamics, and turning it into one is exactly the
work that remains undone.** That is not a dead end; it is a clear marker of where the real frontier is, and of
what the idea honestly is today: a deep *re-telling* of quantum mechanics, not yet a rival to general
relativity. See the [open problems](/open-problems) for what would have to be built.
