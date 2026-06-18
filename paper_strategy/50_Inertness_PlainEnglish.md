# Why finite information stays hidden — and what that actually buys us

*A plain-English account of the inertness result. Companion to the technical note `49_Inertness_Theorem.md`.*

---

## The question we kept asking

QIQT-H says two things about the world. First, the wavefunction Φ evolves exactly as ordinary quantum
mechanics says — nothing is added to the equations, every branch survives. Second, a non-dynamical
"actuality selector" λ quietly marks **one** of those branches as the one that actually happened — the
single world we experience. And there's a third ingredient in the background: space can only hold a
**finite** amount of information. A region of the universe has a budget — the holographic bound — a
largest number of bits it can possibly contain.

That finiteness is the part that *feels* like it should do something. If information is genuinely
limited, surely somewhere, at some scale, we should be able to *see* the limit — the universe running
out of bits, a tiny deviation from textbook quantum mechanics, a fingerprint of finiteness. We spent a
long time hunting for that fingerprint. This note records, in plain terms, what we found.

## The short answer

**There is no fingerprint — and that's not a failure of imagination, it's a theorem.**

Finite information cannot produce any observable difference from ordinary quantum mechanics, anywhere a
human (or any conceivable experiment) could look. Not because we haven't been clever enough, but because
of *where* the finiteness sits in the mathematics. Once you see where it sits, the invisibility is
forced. And we can now prove it three different ways.

## Why finiteness hides: it lives in the exponent

Here is the heart of it, and it's a single idea.

Information, in physics, almost never appears as a number you measure directly. It appears as an
**exponent**. The number of possible states of a region isn't its information *S* — it's *e* raised to
the power *S*. The time it would take for a system to repeat itself isn't its entropy — it's *e* raised
to (roughly) its entropy. The accuracy you'd need to detect a finite cap isn't the cap — it's *e* raised
to *minus* the cap.

Now put in the actual numbers. The information budget of a one-metre region of space is about 10⁷⁰ bits.
For the whole observable universe it's about 10¹²² bits. These are not big numbers in the ordinary
sense — they are big numbers in the *exponent*. And *e* raised to a power like 10⁷⁰ is not "a very large
number." It is a number so large that the difference between "finite" and "infinite" vanishes for every
practical purpose. Any effect that depends on the finiteness shows up multiplied by something like *e*
to the *minus* 10⁷⁰ — which is not "small." It is **zero**, for any purpose, forever.

This is the whole story in one line: **the things you could observe grow like a power of size (gently);
the finiteness hides in an exponential of the information (violently).** A gentle power law and a violent
exponential never meet at a scale you can reach. That mismatch is *why* finite information is invisible —
and it's exactly why the only way we ever found to get a real, observable effect was to *abandon* the
finiteness idea entirely and switch to a completely different kind of theory (one where the wavefunction
actually collapses). That's a different theory with its own problems, not a consequence of finite
information.

## Three ways of checking, all saying the same thing

A good theorem should survive being approached from different directions. This one survives three.

**1. The "any experiment at all" check.** Take *any* laboratory procedure — any sequence of
preparations, evolutions, and measurements. Ask: could it ever tell apart a universe with a finite
information budget from one with an infinite budget? The answer is no, unless the experiment somehow
marshals more information than the budget itself (which means building a black hole) or runs for longer
than the age of the universe raised to an astronomical power. Ordinary matter in a lab uses a
laughably tiny fraction of the budget, so the cap simply never comes into play. The mathematical tool
here is a standard result called the "gentle measurement" lemma, which says that if your experiment
only ever touches the states that fit comfortably inside the budget, then truncating everything above
the budget changes your results by an amount too small to matter — and those tiny errors add up slowly,
they don't snowball.

**2. The "information cost of an excitation" check.** There's a precise quantity — the relative entropy
of a region — that measures how distinguishable a disturbed region is from empty space. It's one of the
few things in this whole framework that we've actually verified by machine-checked proof. We computed
how much of a region's information budget a physical object's disturbance actually uses. The answer is
beautifully simple: it uses a fraction equal to the object's **compactness** — how close it is to being
a black hole. An atom uses about 10⁻⁴³ of its budget. The Earth, about 10⁻⁹. The Sun, about 10⁻⁶. A
neutron star — the densest thing short of a black hole — gets up to about a third. Only an actual black
hole uses the whole budget. So the finiteness can only "bite" right at the edge of forming a black hole,
and nowhere else.

**3. The "shared entanglement" check.** Pick the cleanest possible measure of how two separated regions
are quantum-mechanically linked — their mutual information. (It's the cleanest because it doesn't depend
on the messy short-distance details that plague other measures.) This is the single best place a finite
budget could leave a mark on the structure of empty space itself. It leaves none: the actual shared
entanglement between two regions is about one bit, while the budget would allow something like 10⁵⁰ bits.
The realized amount is a fraction of about (Planck length / region size)² of what's permitted — again,
astronomically slack.

Three different questions — about experiments, about energy, about entanglement — three different small
numbers (the entropy ratio, the compactness, the squared Planck-to-size ratio), and the same verdict
every time. **Finite information is invisible below the threshold of black-hole formation.** The only
place it could ever matter is at horizons — black holes and the edge of the observable universe — where
the numbers finally reach order one. But a horizon is not a laboratory.

## Why this is not a disappointment

It would be easy to read all this as "the finiteness idea does nothing, so the theory is empty." That
reading is wrong, and seeing why is the real point.

Every interpretation of quantum mechanics makes exactly the same experimental predictions. Copenhagen,
Everett's many-worlds, Bohm's pilot wave, QIQT-H — they all reproduce textbook quantum mechanics in the
lab. That's what makes them *interpretations* rather than rival theories. So "makes no new predictions"
is not a flaw unique to QIQT-H; it is the entry ticket for the whole subject. Judging an interpretation
by new predictions is judging it by a standard *none* of them meet.

What separates interpretations is something else: **how rigorously, and how completely, they can write
themselves down.** And here QIQT-H is genuinely ahead, in three concrete ways.

- **The finiteness is doing real *mathematical* work, even though it does no *physical* work.** A finite
  collection of records is what makes the single-world story *definable* — you can build a clean,
  well-behaved probability rule on it. An infinite one is a mathematical swamp. So the finiteness isn't
  decoration; it's the scaffolding that lets the whole construction exist. It is an unusual and honest
  situation: a postulate that is essential to the mathematics and undetectable in the world.

- **There's a genuinely new technical result hiding in here.** Making the "one actual world" idea
  compatible with Einstein's relativity is notoriously hard — many-worlds struggles with it, the pilot
  wave struggles with it, and collapse theories struggle with it (their relativistic versions tend to
  produce infinite energy). QIQT-H has a relativistically consistent, machine-checked construction of
  the probability rule for single outcomes, together with a theorem showing that no rule can pick the
  actual world as a tidy *function* of the wavefunction — it can only be a *sample* drawn from a fair,
  relativistically-respectable lottery. That clean separation, between the *law* (which respects
  relativity) and the individual *draw* (which can't), is a real contribution.

- **The whole thing is being verified, not just argued.** Large parts of this — the probability rule,
  the consistency conditions, the information calculus — are checked by a proof assistant, line by line,
  with no hidden assumptions. No other interpretation of quantum mechanics has been put on that footing.

## The honest bottom line

We went looking for a way to *see* finite information, and instead we proved that you can't — three
times over. That sounds like a dead end, but it's the opposite. We turned a vague hope ("maybe
finiteness does something measurable") into a sharp, defensible statement ("finiteness is provably
invisible below the scale of black holes, and here is exactly why"). A clean impossibility result is
worth more than a fuzzy possibility.

So the substance of QIQT-H was never going to be a number on a dial that ordinary quantum mechanics gets
wrong. The substance is that it is the most rigorous, most complete, and most carefully verified way yet
written down to say: *the wavefunction is everything, it never collapses, and exactly one of its
branches is the world we actually live in.* The finite information budget is the quiet mathematical
backbone that lets that sentence be made precise — not a new prediction, but the reason the old picture
can finally be stated without hand-waving.

That is a real thing to have built. It just isn't the kind of thing you find in a laboratory — it's the
kind of thing you find in a proof.
