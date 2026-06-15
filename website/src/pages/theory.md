---
layout: ../layouts/Deep.astro
title: The theory
eyebrow: The mathematics
description: The finite-information axiom (FQ), the regional cost functional χ_R as Araki relative entropy, Type II regional algebras, and the conditional single-record theorem.
---

The framework has three moving parts: a capacity axiom (the finite record *stage*), a cost functional for
regional information, and a non-dynamical actuality selector λ that draws the single-world conclusion. (A
fourth, earlier part — a conjecture tying *two actual records* to a capacity *overflow* — has been withdrawn
as a category error; see below. Capacity bounds the *number* of records, not whether two can be actual.)
Only the cost functional's underlying calculus is [machine-verified](/formalization); the rest is stated
honestly as postulate or open.

## 1. Finite regional capacity (FQ)

A bounded region $R$ with boundary area $A$ carries a finite information capacity

$$ Q_R \;=\; \frac{A}{4\ell_P^2}, $$

the holographic / Bekenstein–Hawking bound, with $A$ the boundary area of the region and $Q_R$ in natural
entropy units (divide by $\ln 2$ for bits). In QIQT-H this enters as a **postulate** about physically
instantiable content, not merely about thermodynamic entropy: the renormalized information of any state the
region actually realizes obeys $S_{\mathrm{ren}} \le Q_R$. Grounding this bound from a more primitive
principle, and stating it cleanly in the continuum, is one of the [open problems](/open-problems).

## 2. The cost of regional content: $\chi_R$

To compare "how much information" two regional states carry, QIQT-H uses the **Araki relative entropy**
$S(\omega \,\|\, \omega_0)$ of a state $\omega$ against a reference $\omega_0$ (the local vacuum). For a
bounded region the local algebra is not the familiar Type I factor of ordinary quantum mechanics; in
relativistic field theory it is a **Type III$_1$** von Neumann algebra. Araki relative entropy is already
well defined there. The **Type II** "dressed" algebras — which carry a trace-like *generalized* entropy —
come from the gravitational crossed-product construction of Chandrasekaran–Penington–Witten and Witten;
QIQT-H borrows that picture as motivation, it is not something established here. The regional cost
functional is

$$ \chi_R(\omega) \;=\; S\big(\omega \,\|\, \omega_0\big), $$

computed through Tomita–Takesaki modular theory: the modular operator $\Delta$, the modular conjugation
$J$, and the modular flow $\Delta^{it}$ of the reference state. (Identifying this vacuum-relative
distinguishability functional with the *cost to instantiate* regional content is itself part of the
QIQT-H hypothesis, not a theorem.) For coherent excitations $W(f)\Omega$ of a free field this reduces to an
explicit one-particle expression, the Casini–Grillo–Pontello entropy $S_{\mathrm{CGP}}(f)$, and **this
coherent-state reduction is what the Lean development checks**, end to end, from the bounded modular
operators to the entropy-reduction identity.

<div class="note"><strong>Scope.</strong> What is verified is the modular and relative-entropy
<em>calculus</em> for the free-field coherent sector, the bookkeeping machine for <em>χ<sub>R</sub></em>. The verified
part does <strong>not</strong> include the Type&nbsp;II regional construction itself, the (FQ) axiom, or
the conjecture below.</div>

## 3. The crux: macroscopic definiteness (H2)

Here is the load-bearing physical claim. Let a "record" be a stable, redundantly-copied, macroscopically
distinguishable pointer state of the form decoherence leaves behind. The **Macroscopic Definiteness
Conjecture** states:

> Two or more distinct macroscopic records being *actual* together in a region would have joint cost
> $\chi_R$ exceeding the region's capacity $Q_R$. (This bounds the region's *actual* content — not the wave
> function $\Phi$, which keeps every branch; a superposition of records is one vector and costs no extra.)

This is the step that does the real work, and it is a **conjecture**. It asserts that the information cost
of genuine macroscopic multiplicity is not merely large but specifically larger than the holographic
ledger allows. One subtlety is load-bearing: the cost in this inequality need not be the same $\chi_R$ the
Lean development computes. A plain relative-entropy or data-processing estimate of two readable records
yields only about $\log 2$ of classical information, not an area-scale $Q_R$. The conjecture is precisely
that the right *instantiation* cost of genuine macroscopic multiplicity is area-scale — and identifying
that cost measure is itself part of the problem. Establishing H2, even in a model, is the central
[open problem](/open-problems).

## 4. Single record — by selection, not by capacity

After decoherence has stabilized and proliferated the macroscopic records (making them non-interfering and
redundantly objective), the content the region *realizes* is one definite macroscopic world — while $\Phi$
keeps all branches and evolves exactly unitarily, with no collapse term. **The single record is supplied by
the non-dynamical selector $\lambda$**, an Everett-like selection among the unitarily-evolved alternatives.

<div class="note"><strong>Correction (2026): the "capacity forbids two records" exclusion is withdrawn.</strong>
An earlier version drew the single-record conclusion from a capacity <em>exclusion</em> — two actual records
"exceeding $Q_R$." That is a <strong>category error</strong>: the holographic bound counts independent
degrees of freedom, not a sum of redundant classical records (R copies of one fact carry H(X), not R·H(X)),
and ordinary record entropy is capped at ~$A^{3/4}$ (~$10^{91}$) versus ~$10^{122}$ for the bound — a
permanent ~31-order gap; the universe runs at ~$10^{-18}$ of capacity. So capacity does not exclude a second
actual record. The exclusion of two <em>actual</em> records reduces to local single-valuedness (a classical
carrier holds one value), itself supplied by λ. What the Lean development machine-checks is a finite,
additive-cost <em>counting</em> bound (at most one member of a saturating family) — an honest <em>finite
stage</em>, not a derivation that capacity overflows on two macroscopic records.</div>

This is worth stating carefully, because "one outcome" and "unitary evolution" sound contradictory. The
global wave function evolves unitarily throughout; the single *actual* record is a [selection](/selection)
by λ among the unitarily-evolved alternatives, not a dynamical modification of the Schrödinger equation — the
[(Φ, λ) account](/selection). Making that selection precise, and deriving its statistics, is the
dynamical-realization and Born problem below. Q<sub>max</sub>'s role is the finite record *stage* (how many
distinguishable records exist), not the selection.

Two honest caveats. First, the theorem as formalized is a **static exclusion**: it says two-record content
is not instantiable, not yet that the unitary dynamics *drives* an initial superposition to a single
realized record. Closing that "dynamical realization" gap is open. Second, the theorem yields *that* there
is one outcome, not *which*, and with what frequency.

## 5. Born statistics

That outcome $k$ occurs across runs with frequency $|c_k|^2$ is the **Born rule**. QIQT-H aims to recover
it from typicality: over the measure of microscopic initial conditions compatible with a given preparation,
the realized single-record outcome has frequency $|c_k|^2$ for *typical* initial data. A Lorentz-covariant
such measure for free fields is the linchpin, and it is **open**. Born statistics are not assumed, but they
are not yet derived either.

---

The four-link status, at a glance: **(FQ)** postulate · **$\chi_R$ calculus** machine-verified ·
**H2 conjecture** the crux, open · **single record** conditional theorem (+ dynamical-realization gap) ·
**Born** open. The [formalization](/formalization) page documents exactly which pieces are checked; the
[open problems](/open-problems) page lays out the four gaps and what each one buys.
