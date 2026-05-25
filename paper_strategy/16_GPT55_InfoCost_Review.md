# GPT-5.5 Review of Info-Cost Framework (Sixth Pass)

**Date:** 2026-05-24
**Recommendation: REJECT** in current form. Multiple required major revisions.

## The killer finding

The information-cost theorem — the core new claim that macroscopic superpositions cost ~2Q_R bits and exceed the Bekenstein budget — is **mathematically wrong** as stated.

GPT-5.5's specific objections:

### Objection 1: The bound is on Hilbert dimension, not description length

> "The holographic bound is not a bound on the number of classical bits required by an external observer to describe a quantum state. It is a bound on entropy/information content in a gravitational region. ... It is not a bound on Kolmogorov complexity, nor on the number of symbols in a classical description of a wave function."

The user's intuition (and mine) treated the wave function representation as if it were stored in classical memory, with separate "slots" for each component. That's not what the holographic bound is.

### Objection 2: Superpositions live in the same Hilbert space as basis states

> "A pure quantum state in a Hilbert space of dimension D can be a superposition of arbitrary basis states while still living inside that same D-dimensional Hilbert space. Superposition does not double the Hilbert-space dimension."

If region R has Hilbert space of dim D, then |R_1⟩, |R_2⟩, and (|R_1⟩ + |R_2⟩)/√2 are all vectors in the same D-dim space. The superposition doesn't require "two regions' worth" of anything.

### Objection 3: The entropy calculation goes the wrong way

This is the technical killer. For a decohered superposition:

$$\rho_R \approx |c_1|^2 \rho_{R_1} + |c_2|^2 \rho_{R_2}$$

The entropy bound is:

$$S(\rho_R) \le H(|c_i|^2) + \sum_i |c_i|^2 S(\rho_{R_i})$$

For two equal branches: $S(\rho_R) \le 1 + S_{\rm avg}$. That's **one extra bit**, not 2Q_R bits. The mixture entropy is only marginally higher than a single branch's entropy.

So even if individual records saturate the bound (which they don't), the superposition would only require S_avg + 1 bit — well within the budget.

### Objection 4: Ordinary records don't saturate the bound

> "Ordinary laboratory records are nowhere near saturating the holographic bound. A pointer, detector, or brain state may contain an enormous number of microscopic degrees of freedom, but the holographic capacity of a macroscopic laboratory region is fantastically larger."

A 1-meter region has Q_R ~ 10^70 bits available. An apparatus pointer uses maybe ~10^25 bits (Avogadro-scale particles, each needing tens of bits to specify). Vast headroom for any superposition.

### Objection 5: FQ alone doesn't select single-record states

> "An entanglement-entropy bound constrains the reduced density matrix of a region. It does not select a preferred basis. It does not identify 'record states.' It does not say that coherent superpositions of macroscopically distinct configurations are forbidden. A cat state can have low global entropy."

A pure Schrödinger cat state has entropy 0. FQ trivially permits it. The framework imports the single-record condition as a hidden additional axiom, not as a consequence of FQ.

## Other major problems

### The dynamics is unspecified and contradictory

> "Standard unitary dynamics produces entangled macroscopic superpositions from microscopic superpositions. If the per-trial state avoids that, the theory must explain how."

The framework wants all of:
1. Per-trial wave functions are real
2. They evolve unitarily
3. Macroscopic superpositions never occur per-trial
4. Microscopic superpositions do occur
5. Measurements produce one outcome

> "Those commitments are mutually unstable."

You can't have all of these without additional structure (collapse, hidden variables, branches, modified dynamics). The paper picks "Ballentine + hidden microscopic per-trial structure" but doesn't specify the hidden-variable dynamics.

### Theorem 4 (typicality) is a promissory note, not a theorem

> "The claim is: If the measure μ on microscopic initial conditions is appropriately chosen, then relative frequencies match Born weights. This is close to saying: if one chooses a probability measure that yields the Born rule, then the Born rule is obtained. That is not a derivation."

Bohmian mechanics has a genuine typicality story because |ψ|² is equivariant under the guidance dynamics. This framework has no analogous structure — no phase-space, no guidance law, no equivariance theorem.

### The Mandelbrot analogy is misleading

> "Finite-precision rendering limitations concern an external computation of a mathematical object. They do not imply that the mathematical object itself lacks the fine structure. ... A holographic entropy bound on a region does not imply that the physical state is 'rendered' as one classical macroscopic configuration."

The analogy conflates "representability by us" with "physical realizability in nature." The Mandelbrot set has infinite detail even though our renderings are finite-precision. Similarly, the wave function can have macroscopic-superposition structure even if our classical description is bounded.

## Comparison verdict

> "Substantively, the framework is very close to Ballentine's ensemble interpretation. ... The claimed novelty is the holographic explanation for why the formal wave function cannot be a per-trial universal wave function. But because the holographic argument fails, the novelty is mostly rhetorical."

The framework reduces to "Ballentine + hidden microscopic per-trial structure + an unsupported holographic gloss." The "holographically explained" part doesn't actually work.

## Required revisions

1. **Remove or radically weaken the information-cost theorem.** It's false as stated.
2. **Give a correct entropy calculation for record superpositions** — acknowledge that mixing adds ~1 bit, not 2Q_R bits.
3. **Justify (or drop) the claim that macroscopic records saturate holographic capacity.** They don't.
4. **Define the per-trial state space rigorously.** Currently underspecified.
5. **Specify the dynamics.** Show how unitary evolution produces single-record per-trial states without collapse. (Or admit this can't be done.)
6. **Provide a real typicality theorem or stop calling it one.**
7. **Address no-go theorems** (Bell, Kochen-Specker, PBR).
8. **Clarify empirical status.**
9. **Drop the Mandelbrot analogy** or mark clearly as heuristic.

## Bottom line

> "The paper's ambition is clear and the target is important, but the central mechanism does not work. Holographic entropy bounds do not imply that macroscopic superpositions require twice the information capacity of a single record. FQ, even if accepted, does not select one outcome. Born typicality is undeveloped. The result is essentially an ensemble interpretation with an unsupported holographic gloss and an implicit hidden-variable layer. It does not presently resolve the measurement problem."
