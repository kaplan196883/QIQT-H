---
layout: ../layouts/Deep.astro
title: The idea
eyebrow: In plain language
description: The measurement problem, finite information as a bounded record stage, and why the single actual world is λ's doing — not the wave function's, and not the capacity bound's.
---

Quantum mechanics, taken literally, predicts that a measuring device ends up in a superposition of
outcomes: the cat both alive and dead, the pointer at every reading at once. We never see that. The
textbook patch is the *collapse postulate*, where at measurement the state jumps to one outcome, by hand,
outside the unitary law. The many-worlds picture keeps unitarity but pays with an unobservable branching
multiverse. Both are answers to the same question: why one world?

## The hypothesis

QIQT-H's entry hook is a physical premise drawn from black-hole thermodynamics and holography:
**a bounded region of space has only a finite amount of operational information capacity** — a finite number
$N_R$ of distinguishable records ($N_R<\infty$). *Finiteness is the postulate* (the "Quantized Information"
core). This is one of **five postulates**, not the whole program: it is **(P4)**, and it sits alongside the
$(\Phi,\lambda)$ ontology **(P1)** and the quantum-equilibrium typicality premise **(P5)** — the irreducible
new physics being **P4 + P5, on the P1 ontology** (P2–P3 are the standard quantum-relativistic arena). This finiteness has **two machine-checked layers** (and they are *provably different*): in the
finite-dimensional model it is a literal record **count** ($\mathrm{card}\,R \le e^{Q_R}$); in the continuum —
where the matter algebra is the *infinite* Type III$_1$ of relativistic QFT — it is the corresponding finite
**entropy** bound $S_{\mathrm{vN}}+S_{\mathrm{rel}}\le Q_R$, which is machine-checked (`EntropyNotCardinality`)
to be strictly *weaker* than a count. The finiteness is always on the **records/entropy**, never on the matter
Hilbert space. That the capacity then takes the holographic **area form** $Q_R = A/4\ell_P^2$ — scaling with boundary
*area*, not volume — is **not** part of the postulate: it is *derived* in a conditional Sakharov / induced-gravity
bridge (with the value of $G/\ell_P$ carried as a datum, not derived). **(2026 — the *relation* $G = 1/(N\Lambda_s^2)$ promoted to derived; the numerical value stays carried.)** That
last carried datum can itself be reduced: positing a fundamental **record-granularity scale** $\Lambda_s$ (the
finite-information "pixel size", $a_0 = 1/\Lambda_s$) *in place of* $\ell_P$ delivers $G = 1/(N\Lambda_s^2)$ — the
Sakharov/Dvali species bound, machine-checked axiom-free (`InducedNewtonConstant`) — collapsing P4-MICRO's carried
inputs to a *single* scale $\Lambda_s$, from which the finite capacity *and* $G$ both follow. The *numerical value*
of $G$ still needs the species accounting (a frontier), and $\Lambda_s$ stays the one carried scale (a length
cannot come from a count). With this induced $G$ the granularity capacity also **maps onto the holographic
dictionary** — the boundary Cardy microstate count of a BTZ horizon *equals* QIQT-H's bulk capacity exponent
$(A/4)N\Lambda_s^2$ (machine-checked, `HolographicBridge`) — a *correspondence* under the shared $G$, not an
import of a boundary CFT or AdS/CFT's cross-check. More broadly, this bridge is one face of the program's
central result — a **flat-space holographic duality** (`FlatSpaceRecordGravityCorrespondence`): in the
continuum limit one finite-capacity record system is provably *both* free quantum matter *and* the gravity
that curves around it, with the *same* induced $G$ computing both sides — an AdS/CFT-*shaped* correspondence
but in flat spacetime, from the postulates, with no string theory and no anti-de Sitter box. Its finite
evidence and continuum skeleton are machine-checked; the *unconditional* statement is **not** proven — it is
a *conditional theorem* whose remaining inputs (the $a_1 = R/6$ heat-kernel coefficient, a shared regulator,
the cutoff identification) are named rather than assumed away. Finiteness *alone* gives only
$S_{\mathrm{vN}}(\rho_R)\le\log N_R$; the area floor $S_{\mathrm{vN}}(\rho_R)\le Q_R$ is then a *theorem*
(given the capacity postulate), and the $1/4$ a separate machine-checked *theorem* — but a *conditional* one,
resting on the Sakharov bridge, not on finiteness alone.

Here is the sharp point — and getting it right took the program a while. Finite capacity *by itself* does
**not** forbid a superposition in the wave function $\Phi$: a superposition of two records is one vector in
the same finite-dimensional space, costing no more room than either record alone, and $\Phi$ evolves
exactly unitarily, keeping every branch. So $Q_{\max}$ is **not** a constraint on the wave function — but
(a correction we make honestly, 2026) it does **not force a single outcome either**. Decoherence makes the
macroscopic records non-interfering and redundantly objective, yet that removes *interference*; it does not
make one record *actual*. The single actual record history is supplied by a non-dynamical **primitive-actuality** selector $\lambda$:
$\Phi$ keeps every branch, and $\lambda$ *actualizes* exactly one globally-consistent record *history*, the
other components staying present in $\Phi$ as real wave structure but *unactualized* — not actual events or
observers. This is a **primitive-actuality, single-history modal** reading (the picture — one actualized
history, the rest real-but-empty wave structure — is *Bohm-inspired*, his empty waves), though $\lambda$ is
non-dynamical, marking a record-history rather than a guided configuration. $Q_{\max}$'s honest role is the finite record **stage**: it bounds how *many* distinguishable records
a region can hold ($\le e^{Q_R}$), not whether two of them can be actual.

<div class="note">

<strong>The move.</strong> Collapse is not added as a new law and the wave function is
never touched: Φ stays exactly unitary, and a non-dynamical λ marks the one actual record.
<strong>Correction (2026).</strong> An earlier framing claimed the capacity bound <em>forbids</em> two
actual records because "classical record-contents add up" — that is a <strong>category error</strong>. The
holographic bound counts <em>independent</em> degrees of freedom, not a sum of redundant classical records
(R redundant copies of one fact carry H(X), not R·H(X)); and ordinary record entropy is capped at
~A<sup>3/4</sup>, about 10<sup>91</sup> for the observable universe against ~10<sup>122</sup> for the bound
— a permanent ~31-order gap (only black holes saturate A/4, and a black hole has no records). So capacity
never counts records out of existence; the single outcome is λ's, and "two actual records can't coexist"
reduces to a classical carrier holding one value (local single-valuedness) — itself supplied by λ, not by
the bound. The genuinely hard open piece is stitching the per-region actualities into one global,
Lorentz-covariant λ.

</div>

## What this buys, and what it doesn't

If the hypothesis holds, finite information supplies a bounded, decoherence-selected *record stage* — but
definiteness itself is the work of **decoherence + the non-dynamical selector λ**, not of the capacity bound.
(Capacity bounds *how many* distinguishable records a region can hold; it does **not** forbid a multi-record
superposition or *select* the actual one — that "capacity forbids records" reading is retired as a category
error. λ makes exactly one record actual.) No collapse term, no branching ontology.

It does not, by itself, hand you the **probabilities**. That a given run yields outcome $k$ with frequency
$|c_k|^2$, the Born rule, is *reduced* to a single typicality premise (P5) about microscopic initial conditions
across runs — provably underivable from unitarity alone; what stays [open](/open-problems) is justifying that
premise as forced (Born itself is reduced, not open). Until that is settled, QIQT-H is an account
of *definiteness* — why there is one outcome — not yet a complete interpretation that also says with what
frequency.

## Where it stands

This is a research program with a sharp core, not a finished interpretation. An earlier version leaned on a
*capacity-exclusion* conjecture — that a region cannot hold two macroscopically distinct *actual* records
because their information would overflow its holographic budget. We now regard that as a **category error**
(see the correction above), and the numbers make the point vivid: the budget is so vast — about $10^{66}$
bits for a cm² boundary, $\sim 10^{122}$ for the cosmological horizon — against ordinary record entropy of
$\sim 10^{25}$ bits and a structural ceiling of $\sim A^{3/4}\approx 10^{91}$ (for the whole observable
universe), parametrically below the $\sim 10^{122}$ bound, so the budget is never even remotely approached.
Even the universe's *total* realized entropy — black-hole-dominated, $\sim 10^{104}$ bits, which carries no
records — is only $\sim 10^{-18}$ of its holographic capacity. So capacity is *not* what gives single
outcomes; **λ is**. What survives — and is genuinely distinctive — is the no-collapse single-world ontology:
Φ exactly unitary, one non-dynamical actuality selector λ, the holographic bound supplying only the finite
record stage. Absent an *additional* dynamical law (a new postulate with a free parameter), the framework is
**empirically equivalent to standard quantum mechanics** — an interpretation, not new physics, stated
plainly. The mathematical *substrate* it borrows — modular theory and relative entropy, the bookkeeping of
regional information cost — is [machine-verified in Lean&nbsp;4](/formalization). Read on for the
[mathematics](/theory) or the [open problems](/open-problems).
