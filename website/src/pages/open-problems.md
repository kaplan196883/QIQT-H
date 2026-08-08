---
layout: ../layouts/Deep.astro
title: Open problems
eyebrow: The frontier
description: The honest frontier — λ's law (the central problem), Born from typicality (reduced to one premise), the continuum (Type III₁), and Lorentz naturalness (does finite capacity survive radiative Lorentz violation?). What is closed, what is reduced, and what is a wall.
---

QIQT-H is a coherent, *conditional* single-world interpretation. This page is current as of **2026-08-07**;
it incorporates the **2026-06-15 correction**, in which the program's original headline — that finite
holographic capacity *forbids* two macroscopic records — was **retired as a category error** (see the note below). The remaining gaps are about
giving the actuality selector **λ** a precise law and reaching the continuum. The
[formalization](/formalization) is now axiom-free and settles several pieces; the rest is named honestly.

<div class="note">

<strong>Retired: H2 / "capacity forbids two records" (the former crux).</strong> The old
Gap 1 — that a $\ge 2$-record content costs more than $Q_R$, so finite capacity selects a single outcome —
is <strong>withdrawn as a category error</strong>. A holographic bound counts <em>independent</em> degrees of
freedom (joint entropy / code dimension), not a sum of redundant classical records ($R$ copies of one fact
carry $H(X)$, not $R\,H(X)$ — machine-checked); ordinary record entropy is capped at $\sim A^{3/4}$,
parametrically below $A/4$ (and even the total black-hole-dominated entropy, $\sim 10^{104}$, is only
$\sim 10^{-18}$ of capacity); and finite capacity with exact
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
- **The metaselector — *which* framework 𝔄 — is substantially resolved** (a machine-checked no-go trilogy + a
  positive selector): neither **capacity** (`capacity_underdetermines_realm`), nor **symmetry** (the unitary
  group acts transitively on frameworks, so any invariant typicality score is constant —
  `SymmetryNoGo.unitary_invariant_score_constant`), nor the **state Φ alone** (a single projection generates
  only the trivial $\{0,P,1-P,1\}$ — `StateAloneNoGo.state_records_trivial`) selects the framework; **einselection**
  does (Zurek's commutativity criterion — a record commuting with the monitored observable $A$ commutes with the
  interaction $A\otimes B$ — `MetaselectorSelection.pointer_commutes`). So the framework is the spectral algebra
  of the interaction Hamiltonian; this is the classic decoherent-histories set-selection question (Dowker–Kent)
  answered up to its one residual input (below).
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
- **The boundary is now a dynamical open system (RC1–RC3 + IC1, 2026-07; axiom-free)** — upgrading several of
  the above from *kinematics* to *dynamics*. **Records dynamically form:** a dissipative dephasing semigroup
  drives every state to its record readout (`tendsto_Tsem_dephase` — decoherence as a semigroup theorem, with a
  second law and a Lyapunov theorem). **Einselection is derived:** for the pure-dephasing coupling
  $H_{\rm int}=A\otimes B$, the *time-average* of the interacting dynamics converges to that dephasing map
  (`timeAvg_reduced_tendsto_dephase`), so the pointer basis **emerges from the coupling** — deleting the "one
  residual input" above, at the time-averaged level (finite environments recur, so pointwise $t\to\infty$ is
  impossible; the self-Hamiltonian pointer competition is a named follow-on). And the selection event gets a
  **dynamical realization:** the channel is the λ-average of a jump process (exponential clock + Born-selected
  record), whose Born weights are **forced** — *any* record-diagonal unraveling must use exactly the Born weights
  (`unraveling_weights_unique`, no positivity hypothesis — a finite answer to the circularity risk). So λ = the
  jump time + selected record; single-world actuality = one sample path. **Still carried:** this is a finite
  two-time law, not a continuum stochastic process; Born is forced *given* the channel, not derived ab initio
  (P5 not eliminated); and the covariant/continuum law of λ — Gap 1's core — remains the frontier.

**What is open.** The residuals, honestly. (i) The selection is a *representation*, not a mechanism — its content
reduces to *which seed is actual*, and the seed **is** λ, the one primitive a non-dynamical single-world theory
must take as given (its origin is not, and arguably cannot be, derived). (ii) The weights enter as an input; an
across-run **frequency** theorem (and the strong Born premise it rests on, Gap 2) is separate and unavoidable.
(iii) "Modular invariance" is not physical irreversibility; an *approximate* version and a **global
decoherent-history** selector (one coherent world, not one atom of one finite resolution) are the genuine
content-adding next targets. (iv) The metaselector reduces *which* framework to **einselection**, which itself
presupposes a system–environment factorization / Heisenberg cut — the residual **Dowker–Kent** input; einselection
is the empirically-correct but *conditional* selector, so the framework problem is answered up to that cut, not
from nothing. The scheme is, as it stands, operationally equivalent to standard QM.

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

**Toward grounding the bound (claim b) — the area-operator crossed product.** Separately from selection, the
FQ-grounding use of the Type II crossed product (CLPW's gravitational dressing, where the *area* enters as a
trace shift) now has its **operator layer machine-checked and axiom-free**: the modular automorphism $\sigma_t$,
the covariant representation $\pi(a)$/$\lambda_t$ on $L^2(\mathbb{R};H)$, the **clock energy $A_{\mathrm{edge}}$ as
a genuine self-adjoint operator** (via the now-built Stone's theorem), and the **dressed modular Hamiltonian
$\tilde K = K_{\mathrm{bulk}} + A_{\mathrm{edge}}$ proved self-adjoint** (`CrossedProduct*`,
`dressedModularGen_isSelfAdjoint`). With these, P4's holographic floor $S\le A/4\ell_P^2$ is **reduced to a single,
non-vacuous inequality** — the `Phase5Master` certificate, proved equivalent (both directions) to the JLMS master
inequality $S_{\mathrm{vN}} + D \le \langle A_{\mathrm{edge}}\rangle/4\ell_P^2$ — whose slack positivity
($D\ge 0$, `cgpEntropy_nonneg`) is *proved*. The lone remaining input is the **Type II dual-weight trace** that
supplies that one inequality; the coefficient $1/4$ stays the carried UV datum. This is the *area-operator* use of
the crossed product — distinct from selection, where the red-team retired it.

**What is open.** With the continuum schema now built (above), the residual walls are sharply two: the
**Haagerup natural-cone existence** in Mathlib (we state the Born rule directly on vector states; the canonical
state↦vector identification is cited, not yet formalized) and the **interacting / general-state** case (the free
field is done). Two further notes. (a) Holography is machine-checked to be **scaffolding**: λ's covariant measure
needs only *finiteness*, not the area-bound, so a genuinely load-bearing role for the holographic *grading* would
have to be demonstrated. (b) For **λ specifically** the continuum target is the **standard form / natural cone**
(the Type-independent state↦vector correspondence carrying the algebraic Born rule) together with the modular $\sigma_t^\omega$ via
Connes cocycles — *not* the Type II crossed product, which the red-team retired as doing no work for selection.
That is a more tractable continuum entry point than the abandoned crossed-product tower, though still a wall.

**Difficulty.** Very hard — a multi-year Mathlib-grade wall. Three external walls, outside the program's own
control, are cited honestly: the **Riemannian heat-kernel / Seeley–DeWitt** machinery (the $a_1=R/6$ front —
now a *conditional* theorem, see Gap 4's Route-1 note); the **von Neumann type-III₁ classification API**
(Mathlib has no factor/type invariant — only the operator-level III₁ *signature*, $\sigma((1+\Delta)^{-1})=[0,1]$
with the tower limit a factor, is proven; the Connes $S$-invariant / type classification proper is *not*); and
**general interacting matter** (scope stays free fields, linearized gravity, flat / asymptotically-flat). Not a
blocker for the conditional interpretation; the honestly-cited frontier.

## Gap 4 — Lorentz naturalness: is finite capacity compatible with *exact* Lorentz invariance?

This is the **sharpest current frontier**, and the result is honest and sobering. We stress-tested the
finite-capacity postulate (P4) against **radiatively-induced Lorentz violation** — the
Collins–Perez–Sudarsky–Urrutia–Vucetich (CPSUV) one-loop speed splitting $\Delta c^2 = Z_s/Z_t - 1$. The chain
(scripts + Lean under `scripts/qg/`, `QIQTH/QG/`):

- **A naive "finite capacity = local Lorentz-violating cutoff" is dead** (machine-verified numerics): a sharp
  3-momentum cutoff radiatively generates $\Delta c^2 \to \tfrac43\cdot g^2/16\pi^2 \neq 0$, an *unsuppressed*
  dimension-4 Lorentz violation. A Lorentz-invariant regulator gives $0$. The violation is sourced purely by the
  regulator's frame anisotropy; the escape condition is machine-checked to be a single scalar ($\Delta c^2 = 0
  \Leftrightarrow$ the matter kernel is Lorentz-scalar).
- **QIQT-H's *actual* capacity is not such a cutoff.** It is a holographic bound on the **distinguishable-record /
  entropy** content per causal diamond ($\mathrm{card} \le e^{Q_D}$, $Q_D = A(\partial D)/4\ell_P^2$), with no
  field-momentum or modular-energy truncation — so the naive CPSUV failure **does not directly apply**.

<div class="note">

**The honest dilemma (adversarial review, 2026-06-30).** Whether this constitutes a genuine *escape* is **not
established**, and a deliberate red-team puts the strong claim — *literal finite per-region capacity together with
exact Lorentz invariance* — at only **≈10–20%**. The crossed-product (Type II) construction that would reconcile
them faces a fork: either **(A)** matter stays ordinary covariant (Type III₁) field theory and "finite capacity"
is a finite *renormalized entropy* in a trace — consistent, and the "finite information" framing means finite
*entropy*, not a finite matter Hilbert space; or **(B)** the finiteness is made literal for matter — which
collides with structural facts (Type III₁ has no atoms or finite trace; non-compact Lorentz has no non-trivial
finite-dimensional unitary representations). **This is now settled: QIQT-H is on fork (A).** The literal
finite-*matter* reading (fork B) is **retired as untenable** — "finite information" means finite *entropy*, never
a finite matter Hilbert space. The (Φ, λ) record-selection ontology and the holographic *entropy* bound are
untouched: both are entropy-level and Lorentz-safe.

A sharper consequence (adversarial review, 2026): the finite-record-*count* layer is **not derivable** from the
entropy/area bound — the machine-checked `EntropyNotCardinality` no-go forbids it. The only sound *operational*
count is a **Holevo capacity**, $\log M_\epsilon \le (Q + h_2(\epsilon))/(1-\epsilon)$, for records
$\epsilon$-decodable under a relative-entropy bound $Q$; it becomes a finite *number* only under an **imported
energy cutoff**, where it is just the **Bekenstein / microcanonical** bound — standard holography, *not* new
physics. This operational bound is now itself **machine-checked, axiom-free** (`QIQTH/OperationalCapacity.lean`:
`record_capacity`, and the Bekenstein `gibbs_entropy_bound`), built straight on the `EntropyNotCardinality`
guardrail. So QIQT-H's "finite information" is distinctive here **only** via a capacity $Q_R$ *different* from
standard generalized entropy $S_{\rm gen}=A/4G+S_{\rm bulk}$ — and such a $Q_R$ **cannot be derived** from the
program's principles (a conditional no-go: area/JLMS use $S_{\rm vN}$, the finite *count* is independent of
$S_{\rm vN}$, and $\lambda$ is inert). It is possible **only** by *adding* the explicit **max-entropy bridge
postulate** — gravity's capacity is $S_{\max}$ (the finite record **count**), not $S_{\rm vN}$. That postulate
(a new assumption, **not** a derivation) makes the one genuinely-falsifiable distinctive prediction
$Q_R-S_{\rm gen}=S_{\max}-S_{\rm vN}$, governed by the **capacity of entanglement** $\sqrt{V_{\rm gen}}$ —
finite-size Page-time / quantum-extremal-surface shifts; the coefficient and the value of $G$ are open frontiers.
This is the honest edge of the program: *not* a hidden derivation waiting to be found, but a single sharp
*postulate* with a checkable consequence. The no-go (that the area does not fix the count), the gap, the
capacity of entanglement, and the conditional prediction under the postulate are all **machine-checked,
axiom-free** (`QIQTH/MaxEntropyCapacity.lean`: `svn_underdetermines_smax`, `gap_nonneg`, `capEnt_nonneg`,
`distinctive_gap`; `QR_FRONTIER_PLAN.md`).

**The honest verdict, on first contact with real holography (2026).** We tested it. Against a genuine
holographic spectrum — a two-fixed-area-sector state (Dong–Harlow–Marolf), the canonical Page-transition
density matrix — the universal $\sqrt{V_{\rm gen}}$ prediction is **falsified**: the *exact* one-shot shift
saturates while $z_\epsilon\sqrt{V_{\rm gen}}$ overshoots by $\sim\!2.3\times$ and exceeds the physical ceiling
(predicting more records than the Hilbert space holds). $\sqrt{V_{\rm gen}}$ turns out to be a *Gaussianity*
approximation — it "works" only in the Haar / many-copy regime, where it says nothing new. And the surviving
content — *gravity's capacity is the smooth one-shot / max-entanglement-wedge entropy* — is already
**known holography** (Akers–Penington, [arXiv:2008.03319](https://arxiv.org/abs/2008.03319)): distinctive
relative to the naive "RT always uses $S_{\rm vN}$," but **not new physics, and not a new $Q_R$**. So
QIQT-H's one distinctive frontier, honestly tested, **reduces to known one-shot entanglement-wedge physics**
(`scripts/qr/twosector_killtest.py`). That is the calibrated end of the line: no quantum gravity, no value of
$G$, no surviving novel prediction — but a precise, machine-checked map of exactly where the program stands.

</div>

<div class="note">

**"Route 1" (derive the capacity law via the JLMS modular identity) — reframed, and what it *does* deliver
(2026-07-01).** The tempting route to *deriving* the area law is the JLMS identity
$K_{\partial R} = A/4\ell_P^2 + K_{\rm bulk}$. For a fixed-background **free scalar** this is **not achievable**,
and we do not claim it: the free theory has **no Newton constant $G$** and **no geometric area operator**; the
cutoff wedge-entropy coefficient is matter/scheme-dependent, not universally $1/4G$; and the
$\delta A/4G = 2\pi\!\int\!\delta T_{kk}$ step **uses the Einstein equations**, not pure Bisognano–Wichmann
kinematics. So BW supplies the Unruh $2\pi$ but **not** the $1/4G$ *via this route* — along the JLMS modular
identity the $A/4G$ identification stays a *gravitational input*, and the continuum Type III$_1\!\to$II
crossed-product dual-weight trace where it would live is a multi-year cited frontier. **This is a statement about
the JLMS *modular route*, not about the $1/4$'s derivability.** The Bekenstein–Hawking $1/4$ *is* machine-checked
— but through a *different* mechanism, the **Sakharov / induced-gravity bridge**
(`SakharovRatio.sakharov_ratio`: $S_{\rm ent}\,G_{\rm ind}/A = (4\pi)/(16\pi) = 1/4$, with the matter coefficient,
regulator, area and $\pi$ **all cancelling** — matter- and regulator-independent, circularity-clean; this is the
**P4-MICRO** story, where finiteness is postulated, the area *floor* and *form* are theorems, and the $1/4$ ratio
is derived). What *neither* route computes is the **numerical value of $G$** — though even that is now reframed:
positing a fundamental **record-granularity scale** $\Lambda_s$ in place of $\ell_P$ makes the *relation*
$G = 1/(N\Lambda_s^2)$ a machine-checked theorem (`InducedNewtonConstant`), so $G$ moves from *carried* to
*derived-from-$\Lambda_s$* (P4-MICRO's inputs collapse to one scale); the *value* still needs the species
accounting, and $\Lambda_s$ becomes the one carried scale. That species accounting turns on the curved-space
**Seeley–DeWitt coefficient** $a_1 = R/6$ — and *that* has now advanced from *nobody-has-any-of-it* to a
**machine-checked _conditional_ theorem** (`a1_R6_from_data`, `A1R6FromData.lean` — the consolidated capstone
of the ~48-brick J4-363…410 window): the diagonal short-time heat expansion carrying the *genuine* Ricci
scalar $(\sum_i \mathrm{Ric}_{ii})/6 = R/6$ in the $O(t)$ coefficient at the constant-radius gate, with the
whole analytic tower that *was* the wall (van-Vleck parametrix, Levi/Duhamel algebra, delta-family, sliver
cancellations, interchange, resolvent-Lipschitz) discharged into **four semantic input groups** (base
geometry/gauge, the assembly carries, one bundled slot-census package, and the single Gauss identity
$\mathtt{hGauss}$); three of the four are now discharged, satisfiable, or derived in-bank, leaving one
genuinely deep residue: the **Duhamel / convergence-trio** parabolic-PDE convergence wall. This is **not**
unconditional $a_1=R/6$ — that deep residue and the true-kernel analytic Seeley–DeWitt identification stay a
Mathlib-wide frontier. With this
induced $G$ the granularity capacity **maps
onto the holographic dictionary**: the boundary Cardy microstate count of a BTZ horizon *equals* QIQT-H's bulk
capacity exponent $(A/4)N\Lambda_s^2$ (machine-checked, `HolographicBridge.btz_cardy_eq_qiqth_capacity`; the AdS
radius cancels) — a *correspondence* showing the two holographic bookkeepings agree under the shared $G$, **not**
an import of a boundary CFT, the Cardy formula, or AdS/CFT's cross-check. Assembled, these rungs are the
**flat-space record-code / gravity correspondence** (`FlatSpaceRecordGravityCorrespondence`, DY7) — a
holographic duality *in flat spacetime*, from the postulates, with no string theory and no anti-de Sitter box:
for every region, *micro record entropy $=$ one-loop conical (heat-kernel) entropy $=$ Area$/4G_{\rm ind}$*, the
**same** induced $G$ on both faces (matter states *and* gravitational coupling — no calibration). Its honest
status is the crux of the whole program. The **finite evidence is proven** (`finiteEvidence_holds`) and the
**five continuum rungs are proven** term by term; the *entailment* is machine-checked
(`flatSpaceCorrespondence_of_constructive`) — the still-cited physical inputs, carried as **explicit
hypotheses, never axioms**, imply the correspondence **non-vacuously** (the middle area-law equality is
*derived* from the Susskind–Uglum `induced_product`, not assumed), with two of its five inputs already
discharged as finite theorems. But the **unconditional `Prop` is *not* proved**: it is a **conditional
theorem** whose remaining assumptions are three named inputs ($a_1=R/6$ above, a same-regulator condition, a
cutoff identification) plus the continuum-limit assembly. So the correct phrasing is a *machine-verified
substrate $+$ a conditional-theorem duality with named remaining inputs* — never "the duality is proven."
**What *is* now machine-checked**
along the modular route is the honest, derivable content — the
free-field **modular-energy bound**: the entropy variation is bounded by (and, at the reference, equals) the
modular-energy variation, $\Delta S \le \Delta\langle K_\sigma\rangle$ and $\delta S = \delta\langle K_\sigma\rangle$,
which with the one-particle BW identification $K_\sigma = 2\pi B_{\rm boost}$ reads $\Delta S \le 2\pi\,\Delta\langle
B_{\rm boost}\rangle$ (the Unruh modular bound). All four rungs are axiom-free theorems in
`QIQTH/ModularEnergyBound.lean` — the Umegaki identity `modular_relEnt_identity`
($D(\rho\|\sigma)=\Delta\langle K_\sigma\rangle-\Delta S$), the Casini bound `modular_casini_bound`, the
Bisognano–Wichmann rewrite `finiteCorner_wedge_Casini_BW` (the modular-invariant-corner / BW identification
carried as an **explicit hypothesis**), and the first law `finiteCorner_firstLaw`. This upgrades the *modular*
pieces of the carried `Phase5Master` hypothesis from an assumption to derived results — **formalized modular
QFT, not a derivation of the holographic $A/4G$ bound** (`ROUTE1_MODULAR_PLAN.md`).

</div>

## Exploratory — is λ a *fact* or a *generator*? (a falsifiable alternative)

This is a distinct, **speculative** direction, separate from Gaps 1–3, and it *changes the ontology* — so it is
flagged as exploration, not a claim of the program.

**The question.** In the main thesis λ is a *fact*: a placeless, non-dynamical stamp of actuality — *which*
complete branch of Φ is real — Born-typical and inert ($=$ Everett). The alternative is to ask whether that fact
is *raw* or *generated*: whether the actual history is the output of a **finite-information deterministic
generator** (a small seed + a rule), in the spirit of 't Hooft's deterministic quantum mechanics.

**The fork (a proved distinction).** The two readings differ on one provable property — *is the actual history
compressible?* A Born-typical history is algorithmically **incompressible** (Martin–Löf random; machine-illustrated).
So a *truly* random history has **no** finite generator (no short description) ⇒ inert λ, exact Born forever,
**unfalsifiable**, $=$ Everett; a *pseudo*-random history **is** a generator (a seed of $B$ bits) ⇒ it can fake
Born only up to $\sim 2^B$ outcomes, then reveals finite-information structure (periodicity, compressibility).

**Why interesting.** Unlike the inert reading, the generator version is **falsifiable** — a concrete prediction
that quantum randomness is pseudo-random and would show structure in long datasets at $\sim 2^B$. Every test of
quantum random-number generators so far finds *none*, consistent with a large (or absent) seed.

**What it costs.** (i) **Bell** — a finite *local* generator is capped at CHSH $=2$, so reproducing the quantum
$2\sqrt2$ forces it to be nonlocal or **superdeterministic** (its seed correlated with the measurement settings).
(ii) **A location** — λ stops being placeless and must live *somewhere* (a physical substrate / the causal past).
(iii) **The budget** — the **Bekenstein** (energy × size) bound gives a small budget (~10–100 bits) only for the
*toy* case of a generator confined to a bare quantum; a real apparatus / causal-past budget is enormous and
untestable. (An earlier claim that single-quantum data already *excludes* the small case was **withdrawn** as an
overclaim — it mis-assigned the budget to the bare particle.)

**The decisive question — and its resolution (two steps).** *Why would the seed be small?* Faking $N$ outcomes
needs only $\sim\log_2 N$ bits, so a small seed is information-theoretically *sufficient* — the question is whether
anything *forces* the used information far below the holographic capacity, down to a testable level.

*Step 1 — the holographic flow (a partial rescue + a motivation).* Grow a region and its information grows with
the boundary **area** ($\propto R^2$), not the **volume** ($\propto R^3$): the bulk is the *hologram* of its
boundary. So the **boundary** carries the incompressible (Born-random) information and the **bulk is its
compressible image**. This **dissolves the Martin–Löf wall** — the incompressible randomness lives on the
boundary, and the bulk is *generated* from it — and gives the generator a physical identity: it **is** the
holographic boundary, with budget $=Q_R$ now *motivated* (sub-volume, by holography) rather than assumed. Its
observable face is the entanglement **area law** (Ryu–Takayanagi) — already standard physics, not a new signature.

*Step 2 — but the seed still cannot be forced small (the real wall).* A distinction settles it: the generating
**code** (the laws + a simple initial state) *can* be tiny — $\sim$ a few thousand bits; the universe is
plausibly algorithmically simple. But a deterministic program's faking window is $2^{M}$, where $M$ is the
**state** entropy it evolves — *not* $2^{\text{code}}$. For the universe $M\approx$ the realized entropy
$\sim 10^{104}$ bits, and generic (ergodic / thermalizing) dynamics explores the full state space, so the period
is the **Poincaré recurrence** $\sim 2^{10^{104}}$ — beyond the age of the universe by $\sim 10^{103}$ orders. No
principle makes $M$ small: the universe's high entropy is a *physical fact*, and thermalization excludes confining
the actual trajectory to a testable ($\sim 50$-bit) subspace.

**Net (status).** "The universe is a simple deterministic generator" is **viable and motivated** (small code,
holographically grounded) — but it is **observably indistinguishable from true randomness**, not because the seed
is large, but because its only deviation (the generator repeating) sits at the **Poincaré recurrence time**, set
by the universe's entropy, not its code. So the *testability* question is closed by a **fact, not a free
parameter**; what remains is purely **ontological** — whether one prefers "a simple deterministic program whose
randomness is ergodic unfolding" to "inert λ on Everett," two empirically identical pictures. Speculative, a
*different* (deterministic/superdeterministic) ontology from Gaps 1–3; included as an honest exploration, not a
claim of the program. See the [reach](/reach) page for the same idea in plain language.

**A concrete realization, and what survives.** Made concrete, the few-bit generator is a *fractal machine* — an
elementary cellular automaton, where an 8-bit rule is the "fact" and its unfolding is λ. The 256-rule space spans
simple → fractal (Rule 90 = Sierpiński) → chaos (Rule 30, a known pseudo-random generator) → universal computation
(Rule 110, Turing-complete). This *sharpens* the wall rather than evading it: a fractal is the *compressible*
extreme (low Kolmogorov complexity) — the **opposite** of a Born-random record — so a few-bit machine can supply
the **scaffold** of λ (self-similar record geometry) and **pseudo-random frequencies** (chaotic rules), but not the
incompressible Born **content**. Rule 110's universality does not rescue the idea — but the honest reason is more general than universality
(14th–15th GPT-5.5-pro consults). For *any* fixed computable rule $R$ and decoder, a finite decoded history
$h_n$ from initial data $i$ obeys $K(h_n) \le K(i) + K(n) + O(1)$: a fixed deterministic map cannot add more than
a constant to the algorithmic complexity. The **invariance theorem** ($K_U = K_V + O(1)$) then makes the *choice*
of universal rule irrelevant, and universality only lets Rule 110 act as an *interpreter* once the input is
supplied — it does not remove the need for that input. So *if* the actual single branch is Born / Martin–Löf
random — its prefixes having complexity of order their Born *surprisal* (Levin–Schnorr) — that information must
live in the **initial condition** (or some other counted boundary/selection datum), and an incompressible branch
needs an incompressible IC. A few-bit rule plus a *genuinely few-bit* input can yield only a *computable or
pseudo-random-looking* history, never an algorithmically random one. (The pseudo-random / bounded-observer escape
is exactly the untestable generator fork above, not a refutation; and $K(\text{IC})$ is an uncomputable lower
bound, not a certifiable count.) The one genuinely suggestive residue is a *texture* observation, not a generator:
the actual world (persistent structure in a quasi-random background) resembles Wolfram **Class 4, the "edge of
chaos"**; whether the record net being critical / Class-4 *constrains* admissible Born content is the single open
lead this opened.

**A horizon contrast (where stable records are expected — not which is actual).** Pushing the edge-of-chaos lead
toward the [Bekenstein flow](/theory) gives a physically-grounded *organizing contrast* (qualitative, **not** a
theorem — GPT-5.5-pro referee, 2026-06-17). A black-hole horizon jointly realizes two **distinct** sharp limits:
its Bekenstein–Hawking entropy $A/4\ell_P^2$ saturates the holographic *capacity* bound, and — in semiclassical
Einstein gravity — its chaotic dynamics saturate the **Maldacena–Shenker–Stanford** chaos bound, with the
Schwarzschild rate $\lambda_L = 2\pi k_B T_H/\hbar = c/2R_s$ and scrambling time $t_*\sim\lambda_L^{-1}\ln S$
(Sekino–Susskind fast scramblers). These are different quantities (an entropy vs. a Lyapunov *rate*) tied to the
same horizon thermodynamics — a juxtaposition, **not an identity** (larger holes have *more* capacity yet a
*slower* $\lambda_L$). At the maximally-scrambling horizon the fine-grained microstate information is delocalised —
unitarily preserved and (Page / Hayden–Preskill) decodable only from large radiation subsystems by nontrivial
decoding — **not** redundantly broadcast as Quantum-Darwinism pointer records (though macroscopic $M,Q,J$ records
remain). So stable redundant classical records — what λ indexes — are *expected* in ordinary **sub-holographic,
non-maximally-scrambling** open-system environments (the realized-entropy bulk), where decoherence + einselection
+ Quantum Darwinism operate. This is a qualitative contrast organizing *where* records arise (the record stage,
Gap 3, and the einselection metaselector, Gap 1) — there is **no** proven link from $S/S_{\rm holo}<1$ to
$\lambda_L/(2\pi T/\hbar)<1$ to redundancy, it does **not** touch the Born *content* (which record is actual),
and it selects no Everett branch. λ stays inert; $=$ Everett. (Machine-illustrated:
`scripts/holographic_scrambling_records.py`, `einselection_vs_criticality.py`.)

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
