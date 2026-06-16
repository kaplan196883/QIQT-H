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

<div class="note">

<strong>Retired: H2 / "capacity forbids two records" (the former crux).</strong> The old
Gap 1 — that a $\ge 2$-record content costs more than $Q_R$, so finite capacity selects a single outcome —
is <strong>withdrawn as a category error</strong>. A holographic bound counts <em>independent</em> degrees of
freedom (joint entropy / code dimension), not a sum of redundant classical records ($R$ copies of one fact
carry $H(X)$, not $R\,H(X)$ — machine-checked); ordinary record entropy is capped at $\sim A^{3/4}$,
parametrically below $A/4$ (the universe runs at $\sim 10^{-18}$ of capacity); and finite capacity with exact
unitary linearity cannot select a branch. The single outcome is supplied by <strong>λ</strong>, not by
capacity; $Q_R$ is the finite record <em>stage</em> (a cardinality bound), and is even
<a href="/formalization">machine-checked</a> to be optional for λ's measure (which needs only finiteness, not
the area-bound). So H2 is no longer an open problem to establish — it is a resolved (negative) result.

</div>

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
- **λ's kinematic criterion is machine-checked** (finite/Type I shadow, `LambdaPointer.lean`): *which* record
  context is consistent is fixed by **Takesaki's criterion** $\sigma_t^\omega(\mathfrak A)=\mathfrak A \Leftrightarrow [\rho,P_\alpha]=0$
  (exact decoherence — `modAut_fixes_iff_commute`); the dephasing map $E(x)=\sum_\alpha P_\alpha x P_\alpha$ is the
  $\omega$-preserving conditional expectation onto the (generally nonabelian) block-diagonal algebra
  (`dephase_preserves_state`); and the Born weights are a genuine probability (`bornWeights_sum`). ($\rho$ here is
  faithful/reduced, not the global pure $\Phi$; exact $[\rho,P]=0$ is an idealization.)
- **Modular invariance is machine-checked** — a *consistency* result, not physical dynamics: $E$ commutes with
  the modular flow $\sigma_t$ for **every $t$** (`dephase_sigmaDiag_commute`; unconditional in the einselected
  basis). So there is no *modular* recoherence in the chosen invariant algebra — but the **modular flow is not the
  physical Hamiltonian evolution** (they agree only in special KMS / Bisognano–Wichmann cases), so this is *not* a
  proof that real records never recohere under the actual dynamics, and is essentially a functional-calculus fact.
- **The selection event has an explicit constructor** (`SelectionEvent.lean`): an **inverse-CDF** selector from
  an "actuality seed" $s\in[0,1)$ that picks **exactly one** record per seed (`selects_exists_unique` — totality +
  uniqueness of a sampling map), with the *single-shot* seed measure of record $k$ equal to its Born weight $p_k$
  (`volume_selects`). It adds no actualization *mechanism*, and a single-shot measure is *not yet* an across-run
  frequency (that needs a product measure + a law of large numbers). The selector is order-dependent, not
  equivariant (as the no-covariant-selector result requires); the seed measure is order-blind.

**What is open.** The residuals, honestly. (i) The selection is a *representation*, not a mechanism — its content
reduces to *which seed is actual*, and the seed **is** λ, the one primitive a non-dynamical single-world theory
must take as given (its origin is not, and arguably cannot be, derived). (ii) The weights enter as an input; an
across-run **frequency** theorem (and the strong Born premise it rests on, Gap 2) is separate and unavoidable.
(iii) "Modular invariance" is not physical irreversibility; an *approximate* version and a **global
decoherent-history** selector (one coherent world, not one atom of one finite resolution) are the genuine
content-adding next targets. The scheme is, as it stands, operationally equivalent to standard QM.

**Difficulty.** The covariance/contextuality structure, the kinematic criterion + modular-invariance, *and* the
inverse-CDF selection representation are now done (finite → free field); what is left is genuinely irreducible
(the seed = λ; the strong Born premise), or genuine content-adding work (an across-run frequency theorem; a
global-history selector; approximate decoherence), or the continuum walls (Gap 3).

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

**What is open.** One philosophical question, now sharply isolated and resolved into a *dependency*: whether the
**weak** half (state-dependence) is forced turns on how rich a notion of "state" one assumes. On **thin**
ψ-monism (only Φ has dynamics; λ a bare actuality fact) it is *not* forced — the measure is extra structure, and
because λ has no guidance law there is no Bohm-/Liouville-style equivariance to single one out (a DGZ-typicality
disanalogy). On **thick** Hilbert-space ψ-monism (inner product + symmetries + no primitive labels) it is
essentially *constitutive*. Either way the **strong** half (refinement-additivity) is proven *not* forcible (the
no-go) — it is the named irreducible premise, in every reading. Plus the continuum/interacting realization of
the measure.

**Difficulty.** The finite reduction *and* its forced/free split are done; the residual is one philosophy-of-the-premise
question + the continuum.

## Gap 3 — The continuum (Type III₁) and FQ grounding

**Claims.** (a) Extend the modular/entropy and record-measure results from the free-field coherent sector to
*general* states and the Type III $\to$ Type II continuum; (b) *ground* the bound $S_{\mathrm{ren}}\le Q_R$
rather than postulate it.

**What is done toward it.** The finite and free-field constructions are complete and axiom-free; the Type II
crossed-product *entropy* (CLPW) is the borrowed substrate. And, as of **2026-06-16**, the **continuum λ
selection schema is machine-checked for the free-field / standard-subspace sector**: lifted onto the genuine
continuum modular flow $\Delta^{it}$ (the Rieffel–Van Daele bounded `modUnitary`), the modular automorphism
$\sigma_t=\mathrm{Ad}(\Delta^{it})$, the **continuum Takesaki criterion**, **continuum modular-invariance** (the
dephasing map commutes with $\sigma_t$ for every $t$ — a consistency fact, *not* physical persistence: the
modular flow ≠ physical time), the **Type-independent algebraic Born rule**, and the **inverse-CDF selection
event** (one record per seed; single-shot seed-measure = Born weight) are all axiom-free (`ContinuumLambda`,
`NaturalConeBorn`, `ContinuumSelection`). And the whole schema is also lifted to the **second-quantized free
field**: $\Gamma(\Delta^{it})$ as a unitary one-parameter group on Fock, with the field-level automorphism,
modular-invariance, Born rule (on the genuine Fock *vacuum state* — the Weyl-bit record gives
$(1\pm e^{-\lVert u\rVert^2/2})/2$), and selection event all axiom-free (`SecondQuantCLM`, `ContinuumLambdaField`,
`FieldBorn`, `FieldSelection`).

**What is open.** With the continuum schema now built (above), the residual walls are sharply two: the
**Haagerup natural-cone existence** in Mathlib (we state the Born rule directly on vector states; the canonical
state↦vector identification is cited, not yet formalized) and the **interacting / general-state** case (the free
field is done). Two further notes. (a) Holography is machine-checked to be **scaffolding**: λ's covariant measure
needs only *finiteness*, not the area-bound, so a genuinely load-bearing role for the holographic *grading* would
have to be demonstrated. (b) For **λ specifically** the continuum target is the **standard form / natural cone**
(the Type-independent state↦vector correspondence carrying the algebraic Born rule) together with the modular $\sigma_t^\omega$ via
Connes cocycles — *not* the Type II crossed product, which the red-team retired as doing no work for selection.
That is a more tractable continuum entry point than the abandoned crossed-product tower, though still a wall.

**Difficulty.** Very hard — a multi-year Mathlib-grade wall (unbounded operator theory, Type III classification
that Mathlib lacks). Not a blocker for the conditional interpretation; the honestly-cited frontier.

---

## In one paragraph

The original crux (H2 — capacity forbids records) is **retired as a category error**; the single outcome is
λ's, by stipulation. λ's *selection schema* is machine-checked (not a law): Takesaki's criterion fixes which
record context admits the conditional expectation, the Born weights are a genuine probability, the dephasing map
is **modular-invariant** (a consistency fact — *not* physical irreversibility; the modular flow is not physical
time), and the **selection event has an explicit inverse-CDF constructor** (exactly one record per seed,
single-shot seed-measure = Born weight). What is verified is a consistency scaffold *conditional on a primitive
seed and a Born premise*: the seed itself **is** λ (the one primitive a non-dynamical single-world theory must
take as given), and the weights-as-**across-run-frequencies** rest on a premise the no-go proves unremovable —
so, as it stands, the scheme is operationally equivalent to standard QM. **Born** is reduced (axiom-free) to a single
state-supervenience premise with a no-go that some premise is unavoidable. The **continuum** (Type III₁,
now via the standard form for λ) is the honestly-cited multi-year wall. The
[machine-checked substrate](/formalization) is axiom-free and settles the covariance/contextuality/Born and
λ-kinematics/persistence pieces; it does not close the selection event or the continuum.
