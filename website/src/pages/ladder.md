---
layout: ../layouts/Deep.astro
title: Bits → qubits — the finite-λ ladder
eyebrow: The construction, made concrete
description: A ladder of toy universes — one bit, two bits, three qubits, and the coarse-grained combinations — that makes the finite-information λ construction concrete, shows what the metaselector selects at each scale, and shows where the holographic horizon sets the boundary. Single-basis pedagogy, machine-checked, operationally Everett.
---

The [finite-information λ](/selection) thesis says λ is a finite **index** over a finite set of
record-histories, carrying the *exact* Born weights, with **holography bounding the index**. The cleanest way
to see what that means is to build it at the smallest scales — one bit, two bits, three qubits — each
machine-checked in Lean. This page is the ladder.

<div class="note">

<strong>Read these as toys, not new physics.</strong> Every model below lives in a single fixed basis and is
deliberately simple — its job is to make the *construction*, the *metaselector*, and the *holographic boundary*
concrete and checkable. Because Born stays exact and λ stays inert, all of it is <em>operationally Everett</em>.
"Entanglement" here means single-basis correlation (not a Bell/contextuality witness), and "Born emerges"
assumes the iid variance (it packages Chebyshev, it does not derive Born). Everything is verified in the
<a href="/formalization">Lean development</a> (`TinyUniverse`, `TwoBitUniverse`, `ThreeQubitUniverse`).

</div>

## One bit — a single qubit

The smallest universe is a single qubit. $\Phi$ has two basis records; $\lambda \in \{0,1\}$ names which one
is **actual**. Three things are machine-checked:

- **The bit names the world.** The selection map sends the actual bit to a record (the pointer state $e_k$),
  and $\Phi = \sum_k \Phi_k\, e_k$ is exactly the superposition of the records λ ranges over
  (`actualRecord`, `phi_eq_superposition`).
- **λ's weight is fixed by Φ, not free.** The bias is the squared amplitude: $\mu(0)=\lVert\Phi_0\rVert^2$,
  $\mu(1)=1-\mu(0)$ (`qubitBorn_eq_oneBitBorn`). A one-bit λ is consistent only with a two-dimensional Φ — the
  finiteness of λ and the dimension of Φ are the same fact.
- **Pre-statistical → statistical.** With $K$ actual records the empirical frequency concentrates,
  $\Pr(\lvert\hat p-p\rvert\ge\varepsilon)\le \tfrac{1}{4K\varepsilon^2}\to 0$ as $K\to\infty$
  (`born_finite_sample_bound`, `statistical_emergence`). *Caveat:* this assumes the iid variance — it is
  Chebyshev, not a derivation of Born. At small $K$ the world is genuinely pre-statistical.

## Two bits — two qubits

Now $\lambda=(\lambda_A,\lambda_B)$ over four records. The new thing is **correlation**:

- **Product Φ → independent bits.** A product state factorizes: the joint Born law is the product of the
  marginals (`product_independent`).
- **Bell Φ → correlated bits.** The state $c(\lvert00\rangle+\lvert11\rangle)$ has *uniform* marginals yet a
  joint law that does **not** factor (`bell_correlated`): the two bits are perfectly correlated
  (`bell_perfect_correlation`) while each is individually random.

<div class="note">

<strong>Honest caveat on "entanglement."</strong> `bell_correlated` is a <em>single-basis</em> fact: the
separable mixture $\tfrac12\lvert00\rangle\langle00\rvert+\tfrac12\lvert11\rangle\langle11\rvert$ has the
identical computational-basis distribution. So this is <em>classical correlation in one basis</em>, not an
entanglement witness — a genuine witness needs multiple incompatible measurement contexts (CHSH/Mermin), which
these toys do not have.

</div>

## One bit in a two-qubit world — coarse-graining

What if the actuality budget is *smaller* than the record structure — one bit in a four-record world? Then λ
cannot name a record; it names a binary **coarse-graining** (a yes/no question), and that coarse law *is* a
one-bit universe (`coarseBorn`, `coarse_is_oneBit`). Spending the bit on a local outcome gives one party's
marginal (`coarse_fstBit_eq_marginalA`). And here correlation bites: on the Bell state the **parity** bit is
*definite* (`bell_parity_zero`/`_one`) while a **local** bit is *uniform* (`bell_local_uniform`) — *which*
binary question you actualize interacts with Φ's correlations.

## Three qubits — the resolution hierarchy and the entropy ceiling

Eight records. A $k$-bit λ resolves a $2^k$-block coarse-graining with exact partial-Born weights
(`blockBorn`); at three bits it is the full per-record law (`blockBorn_full_eq_triBorn`). The budget is a
**resolution dial**: 1 bit → 2 blocks, 2 bits → 4 blocks, 3 bits → 8 records.

The lesson is the **entropy ceiling**. The GHZ state $c(\lvert000\rangle+\lvert111\rangle)$ lives in 8 records
but only $000$ and $111$ carry weight (`ghz_supported_on_diagonal`): its computational-basis Born entropy is
**1 bit, not $\log\dim = 3$**. So no budget reveals more than one bit — a two-bit reading never even separates
A from B (`ghz_2bit_collapse`). In short, **$H(R)$ can sit far below $\log\dim$** — record information is the
*support entropy* of the Born distribution, not the Hilbert dimension.

<div class="note">

<strong>What this is and isn't (honest scope).</strong> This is a <em>standard Shannon / data-processing</em>
fact — a sparse Born distribution has $H(R)<\log\dim$ — and it is <strong>basis-fixed</strong>: GHZ's "1 bit"
is the <em>computational-outcome</em> entropy (in the GHZ's own basis it is 0; in the $X$ basis it is $\sim$2
bits), and the <em>incoherent</em> mixture $\tfrac12\lvert000\rangle\langle000\rvert+\tfrac12\lvert111\rangle\langle111\rvert$
gives the <em>identical</em> table. So this is <strong>not</strong> a coherence/entanglement effect, and it is
<strong>not evidence for holography</strong>: it illustrates the trivial $H(R)\le\log\dim$, not the holographic
$H(R)\le S$ (which stays a postulate — see below). This whole ladder is a sanity-check / pedagogy tool, not
evidence: every number here is what any Everettian computes from the same Born distribution.

</div>

## The metaselector — what fixes the framework

The ladder fixes a basis by hand and shows what λ selects *among*. The separate question — *which* record
framework $\{P_\alpha\}$ is the right one (the **metaselector**) — is answered, machine-checked, as a **no-go
trilogy plus a positive selector**: neither **capacity** (`capacity_underdetermines_realm`), nor **symmetry**
(the unitary group is transitive on frameworks, so any invariant score is constant), nor the **state Φ alone**
(it generates only the trivial framework) selects it — but **einselection** does (Zurek's commutativity
criterion: a record commuting with the monitored observable $A$ commutes with the interaction $A\otimes B$, so
it is decoherence-free). The framework is the spectral algebra of the interaction Hamiltonian. See the
[theorem index](/formalization).

## Where the horizon creates the boundary

This is where **holography** enters the ladder. The Bekenstein–Bousso bound, attached to a **causal diamond**,
caps how many distinguishable record-histories a region can hold — the finite **stage** on which λ is an index.
Concretely, the holographic entropy $S$ of the diamond bounds the record information, and λ's information is
exactly that:

$$
H(\lambda) \;=\; I(\lambda; R) \;\le\; H(R) \;\le\; S_{\text{horizon}} \;\sim\; \frac{A}{4\ell_P^2}.
$$

So the **horizon area is the boundary condition on λ's finiteness**: it bounds the cardinality of the index
(how many actual records can coexist, $\le e^{S}$), per causal diamond — *not* Φ's superpositions (that was
the retired "capacity forbids records" error), and *not* the probability law (the retired "grid"). The
quantity the bound caps is $H(R)$, **not** $\log\dim$ — a sparse Born distribution can have $H(R)\ll\log\dim$
(the entropy ceiling above), so a region can carry a high-dimensional Φ while its actual record content stays
within the horizon budget. Two honest qualifications: the **$H(R)\le S$ step is the postulate** (the only place
holography enters — the enumeration neither tests nor supports it; it shows only the trivial $H(R)\le\log\dim$),
and $H(\lambda)=I(\lambda;R)$ holds because λ *is* the record (a deterministic function of $R$).

<div class="note">

<strong>Honest status of the boundary.</strong> The horizon bound is a <em>postulate</em> — a one-sided
capacity boundary condition supplied by the bounding area of a causal diamond, not derived. Two strengths are
kept distinct: the entropy form $H(R)\le S$ (Bousso, on the decohered record) and the strictly stronger
cardinality form $\log\lvert R\rvert\le S$. The contract that threads it is machine-checked and category-error-proof
(`RecordContract`, Born-from-projectors `‖P_r Φ‖²`); the area value itself is physics input.

</div>

## In one line

> The ladder makes the finite-information λ construction concrete: λ is a finite index over records (exact
> Born), **einselection** fixes the framework, and the **horizon** bounds the index's cardinality — the place
> where "Quantized Information" and "Holographic" meet the selector. It is single-basis pedagogy, machine-checked,
> and — because Born stays exact and λ is inert — **operationally Everett**.
