---
layout: ../layouts/Deep.astro
title: Open problems
eyebrow: The frontier
description: The honest frontier after H2 was retired — λ's law (the central problem), Born from typicality (reduced to one premise), and the continuum (Type III₁). What is closed, what is reduced, and what is a wall.
---

QIQT-H is a coherent, *conditional* single-world interpretation. This page is current as of the **2026-06-15
correction**, in which the program's original headline — that finite holographic capacity *forbids* two
macroscopic records — was **retired as a category error** (see the note below). The remaining gaps are about
giving the actuality selector **λ** a precise law and reaching the continuum. The
[formalization](/formalization) is now axiom-free and settles several pieces; the rest is named honestly.

<div class="note"><strong>Retired: H2 / "capacity forbids two records" (the former crux).</strong> The old
Gap 1 — that a $\ge 2$-record content costs more than $Q_R$, so finite capacity selects a single outcome —
is <strong>withdrawn as a category error</strong>. A holographic bound counts <em>independent</em> degrees of
freedom (joint entropy / code dimension), not a sum of redundant classical records ($R$ copies of one fact
carry $H(X)$, not $R\,H(X)$ — machine-checked); ordinary record entropy is capped at $\sim A^{3/4}$,
parametrically below $A/4$ (the universe runs at $\sim 10^{-18}$ of capacity); and finite capacity with exact
unitary linearity cannot select a branch. The single outcome is supplied by <strong>λ</strong>, not by
capacity; $Q_R$ is the finite record <em>stage</em> (a cardinality bound), and is even
<a href="/formalization">machine-checked</a> to be optional for λ's measure (which needs only finiteness, not
the area-bound). So H2 is no longer an open problem to establish — it is a resolved (negative) result.</div>

## Gap 1 — λ's law: the central open problem

**Claim to establish.** Give the non-dynamical actuality selector λ a precise *law*: a Poincaré-covariant
typicality measure on record histories, together with a *dynamical realization* showing that actual unitary
measurement evolution yields exactly one admissible record (not zero, not two), with the admissible space
dynamically invariant.

**Why decisive.** With H2 retired, λ *is* the single-outcome mechanism. As a bare primitive it makes QIQT-H a
single-world hidden-variable/modal *completion* of QM, genuine only once λ has a law — otherwise it is
"Everett minus the unrealized branches, via a primitive λ."

**What is done toward it.** A great deal, and machine-checked (axiom-free):

- The covariant **typicality measure exists** — a Poincaré-covariant, σ-additive, decoherent-histories-*consistent*
  Born measure on the free-field record net (`weylBit_typicalityMeasure_exists`, Lorentz-invariant).
- **OP3b (covariant gluing) resolved conceptually**: a covariant *measure* exists but no covariant *selector*
  (the S² obstruction) — so λ is necessarily a symmetry-breaking *sample*, not an equivariant function; and the
  construction is **contextuality-safe** with **state-independent no-signaling** (holds for entangled states).
- **λ is Type-III-native** (a 2026-06-15 correction, after a red-team that checked the operator algebra): the
  earlier idea of "dressing" the Type III₁ local algebra into a Type II algebra via the gravitational crossed
  product to recover atoms and a trace was a **category error** for the selection problem — Type II factors
  *also* have no minimal projections, so the records λ selects come from a chosen abelian *pointer* subalgebra
  𝔄, which already lives inside Type III₁. λ needs no forced trace: the Born weights are the algebraic
  $\omega(P_\alpha)=\lVert P_\alpha\Phi\rVert^2$ (the natural-cone state, Type-independent).
- **λ's kinematic law is now machine-checked** (finite/Type I shadow, `LambdaPointer.lean`): *which* pointer
  algebra is fixed by **Takesaki's criterion** $\sigma_t^\omega(\mathfrak A)=\mathfrak A \Leftrightarrow [\rho,P_\alpha]=0$
  (exact decoherence — `modAut_fixes_iff_commute`); the decoherence map $E(x)=\sum_\alpha P_\alpha x P_\alpha$ **is**
  the unital, $\omega$-preserving conditional expectation onto 𝔄 (`dephase_preserves_state`); and the Born
  weights are a genuine probability (`bornWeights_sum`).
- **Dynamical persistence is machine-checked** — the first real piece of the dynamical realization: $E$ commutes
  with the genuine real-time modular flow $\sigma_t$ for **every $t$** (`dephase_sigmaDiag_commute`; unconditional
  in the einselected basis, `dephase_sigmaDiag_commute_diagonal`). So a dephased, records-definite state **stays**
  dephased for all time — coherence between pointer sectors never regenerates, and the selected record is a fixed
  point of the dynamics with constant Born weights.

**What is open.** Two residuals, both honestly hard. (i) The **selection event** itself — persistence shows the
actual record does not *un*-select, but not *why one* (rather than zero or two) becomes actual; there is still
no constructor that *produces* the single history. (ii) The derivation of the stable weights as genuine
**across-run frequencies**, which the Born no-go (Gap 2) shows must rest on an irreducible premise.

**Difficulty.** The covariance/contextuality structure *and* the kinematic + persistence law are now done
(finite); the selection-event constructor and the continuum realization (Gap 3) are the medium-to-hard residual.

## Gap 2 — Born from typicality (reduced, not closed)

**Claim to establish.** Among admissible microscopic initial conditions, the outcome-$i$ subset carries Born
weight $|c_i|^2$.

**What is done toward it.** This is now **reduced to a single premise**, axiom-free: the Born weight is derived
from **state-supervenience** via the Zurek envariance symmetry (*proved*, not assumed) and an orthonormality
bridge that forces the branch count to track the amplitudes (`StateSupervenience`, `EnvarianceJustification`,
`BornEquiprobable`), with a finite law of large numbers (`BornTypicalityFinite`). And the premise has now been
**split exactly** (`WeakStrongSplit`): its *weak* half — naturality / state-supervenience — is machine-checked
to be **blind to the exponent** (`weight_naturality` holds for *every* reprocessing $f$; the $f=w^2$ rule is a
natural, normalized probability that disagrees with Born — `weak_underdetermines_born`), so it cannot force Born;
its *strong* half — **refinement-additivity** — is what discriminates the square (`sq_not_refinementAdditive`)
and *linearizes* into equiprobability (`refinementAdditive_nsmul`), hence Born. A **no-go** (`NoBornFromNothing`)
proves that strong half is unavoidable.

**What is open.** Only one thing, now sharply isolated: whether the **weak** half (state-dependence) is itself
*forced* by the (Φ,λ) ontology rather than merely motivated — a genuine philosophical question (the reasoned
case: the ψ-monist ontology contains nothing but the state for the law to depend on). The **strong** half is
proven *not* forcible (the no-go), so it is the named irreducible premise, not an open gap. Plus the
continuum/interacting realization of the measure.

**Difficulty.** The finite reduction *and* its forced/free split are done; the residual is one philosophy-of-the-premise
question + the continuum.

## Gap 3 — The continuum (Type III₁) and FQ grounding

**Claims.** (a) Extend the modular/entropy and record-measure results from the free-field coherent sector to
*general* states and the Type III $\to$ Type II continuum; (b) *ground* the bound $S_{\mathrm{ren}}\le Q_R$
rather than postulate it.

**What is done toward it.** The finite and free-field constructions are complete and axiom-free; the Type II
crossed-product *entropy* (CLPW) is the borrowed substrate.

**What is open.** The interacting / general-state Type III₁ realization. Two notes on what changed. (a)
Holography is now machine-checked to be **scaffolding**: λ's covariant measure needs only *finiteness*, not the
area-bound, so a genuinely load-bearing role for the holographic *grading* would have to be demonstrated. (b)
For **λ specifically** the continuum target is now the **standard form / natural cone** (the Type-independent
state↦vector correspondence carrying the algebraic Born rule) together with the modular $\sigma_t^\omega$ via
Connes cocycles — *not* the Type II crossed product, which the red-team retired as doing no work for selection.
That is a more tractable continuum entry point than the abandoned crossed-product tower, though still a wall.

**Difficulty.** Very hard — a multi-year Mathlib-grade wall (unbounded operator theory, Type III classification
that Mathlib lacks). Not a blocker for the conditional interpretation; the honestly-cited frontier.

---

## In one paragraph

The original crux (H2 — capacity forbids records) is **retired as a category error**; the single outcome is
λ's. λ is now **Type-III-native** (no forced trace), and its *kinematic* law is machine-checked: Takesaki's
criterion fixes which pointer algebra carries the $\omega$-preserving conditional expectation, the Born weights
are a genuine probability, and — the first dynamical piece — that selection **persists for all time** under the
real-time modular flow (coherence never regenerates). What remains for λ to make QIQT-H a *theory* rather than
a conditional completion: a constructor for the **selection event** (why *one* record becomes actual) and the
derivation of the weights as **across-run frequencies**. **Born** is reduced (axiom-free) to a single
state-supervenience premise with a no-go that some premise is unavoidable. The **continuum** (Type III₁,
now via the standard form for λ) is the honestly-cited multi-year wall. The
[machine-checked substrate](/formalization) is axiom-free and settles the covariance/contextuality/Born and
λ-kinematics/persistence pieces; it does not close the selection event or the continuum.
