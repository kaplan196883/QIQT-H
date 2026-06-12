---
layout: ../layouts/Deep.astro
title: The theory
eyebrow: The mathematics
description: The finite-information axiom (FQ), the regional cost functional χ_R as Araki relative entropy, Type II regional algebras, and the conditional single-record theorem.
---

The framework has four moving parts: a capacity axiom, a cost functional for regional information, a
conjecture that ties two records to an overflow of that capacity, and a conditional theorem that draws the
single-world conclusion. Only the cost functional's underlying calculus is
[machine-verified](/formalization); the rest is stated honestly as postulate, conjecture, or open.

## 1. Finite regional capacity (FQ)

A bounded region $R$ with boundary area $A$ carries a finite information capacity

$$ Q_R \;=\; \frac{A}{4\ell_P^2}, $$

the holographic / Bekenstein–Hawking bound. In QIQT-H this enters as a **postulate** about physically
instantiable content, not merely about thermodynamic entropy: the renormalized information of any state the
region actually realizes obeys $S_{\mathrm{ren}} \le Q_R$. Grounding this bound from a more primitive
principle, and stating it cleanly in the continuum, is one of the [open problems](/open-problems).

## 2. The cost of regional content: $\chi_R$

To compare "how much information" two regional states carry, QIQT-H uses the **Araki relative entropy**
$S(\omega \,\|\, \omega_0)$ of a state $\omega$ against a reference $\omega_0$ (the local vacuum). For a
bounded region the local algebra is not the familiar Type I factor of ordinary quantum mechanics; in
relativistic field theory it is a **Type III$_1$** von Neumann algebra, and after dressing it becomes
**Type II**, where a renormalized entropy is well defined. The regional cost functional is

$$ \chi_R(\omega) \;=\; S\big(\omega \,\|\, \omega_0\big), $$

computed through Tomita–Takesaki modular theory: the modular operator $\Delta$, the modular conjugation
$J$, and the modular flow $\Delta^{it}$ of the reference state. For coherent excitations $W(f)\Omega$ of a
free field this reduces to an explicit one-particle expression, the Casini–Grillo–Pontello entropy
$S_{\mathrm{CGP}}(f)$, and **this entire calculus is what the Lean development checks**, end to end, from
the bounded modular operators to the entropy-reduction identity.

<div class="note"><strong>Scope.</strong> What is verified is the modular and relative-entropy
<em>calculus</em> for the free-field coherent sector, the bookkeeping machine for <em>χ<sub>R</sub></em>. The verified
part does <strong>not</strong> include the Type&nbsp;II regional construction itself, the (FQ) axiom, or
the conjecture below.</div>

## 3. The crux: macroscopic definiteness (H2)

Here is the load-bearing physical claim. Let a "record" be a stable, redundantly-copied, macroscopically
distinguishable pointer state of the form decoherence leaves behind. The **Macroscopic Definiteness
Conjecture** states:

> A regional state carrying two or more distinct macroscopic records has $\chi_R$ exceeding the capacity
> $Q_R$ of any region that would have to host it.

This is the step that does the real work, and it is a **conjecture**. It asserts that the information cost
of genuine macroscopic multiplicity is not merely large but specifically larger than the holographic
ledger allows. Establishing it, even in a model, is the central [open problem](/open-problems).

## 4. The conditional theorem: single record

Granting (FQ) and the conjecture, the conclusion follows as a **conditional theorem**. If a $\ge 2$-record
state cannot be instantiated in $R$, then the only regional content compatible with the bound is
single-record. After decoherence has stabilized and proliferated the records, the per-run state the region
realizes is therefore one definite macroscopic world, with no collapse term added to the dynamics and
global unitarity exactly preserved.

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
