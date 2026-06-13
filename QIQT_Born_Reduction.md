---
title: "Machine-Checked Reductions of the Born Rule: Conditional Theorems, a No-Go, and a Finite H-Theorem"
author: "Paweł Kapłański"
date: "June 13, 2026"
---

## Abstract

We report a Lean 4 formalization that isolates, with full machine-checked rigor, exactly what the Born
rule requires beyond a no-collapse, single-record dynamics. Working in a finite setting where each run
realizes one macroscopic record (the QIQT-H setting), we prove a chain of conditional representation
theorems: redundant records force a definite, context-independent pointer outcome but carry no
quantitative weights; among rules $p_k = f(w_k)/\sum_j f(w_j)$ with $w_k=\lVert P_k\psi\rVert^2$, the rule
is Born if and only if $f$ is additive under coarse-graining, equivalently if and only if the
selector marginals are invariant under remote refinement (no-signaling). We then prove a meta no-go: the
power-law family $f_\alpha(w)=w^\alpha$ satisfies every Born-free structural premise yet differs from Born,
so no premise invariant under $w\mapsto w^\alpha$ can entail it — a precise statement of why some extra
input is unavoidable. Finally we take the residual input — that the selection dynamics preserves a
Born-agnostic typicality measure — and derive it from a finite H-theorem: a reversible closed update
over a uniform bath induces a bistochastic selector kernel (column-stochasticity follows from the bijection,
not from any Born assumption), and an $\varepsilon$-mixing condition makes the Born measure the geometrically
attracting equilibrium. A reset-kernel no-go shows relaxation alone does not suffice. The development has
no `sorry` and no axioms beyond the standard classical foundations (`propext`, `Classical.choice`,
`Quot.sound`). The honest upshot: the Born rule is reduced to a sharply-stated finite Liouville plus
molecular-chaos typicality postulate, and we prove that nothing Born-free can replace it.

**Keywords:** Born rule, quantum measurement problem, typicality, Lean 4, formal verification, envariance, H-theorem, no-signaling, quantum Darwinism

## 1. Introduction

The Born rule — that an outcome with amplitude weight $w_k=\lVert P_k\psi\rVert^2$ occurs with probability
$p_k=w_k/\sum_j w_j$ — is the bridge between the deterministic, unitary state and observed frequencies. In
interpretations that add neither collapse nor branching as extra substance, the rule must be *recovered*
rather than postulated, and a long line of work (Gleason; Busch; Deutsch–Wallace; Zurek's envariance;
Dürr–Goldstein–Zanghì typicality) shows this is subtle: unitarity and the existence of definite records do
not, by themselves, fix the **exponent** $2$. For any $\alpha\neq 1$ the law $p_k^{(\alpha)}\propto w_k^{\alpha}$ is equally support- and certainty-preserving, so something beyond "no-collapse plus records"
is mathematically required.

This paper does not claim to derive Born from nothing. It does something we believe is more useful and that,
to our knowledge, has not been done with machine-checked rigor: it **isolates the exact extra input**,
proves a family of sharp conditional theorems pinning Born to that input, proves a no-go showing the input
cannot be weakened past a precise threshold, and then *derives* the input itself from a finite reversibility
plus mixing premise via an H-theorem. Every statement below is a theorem in a Lean 4 development that builds
with no `sorry` and depends only on the standard classical foundations.

The contribution is fourfold:

1. a Born-free **objectivity** layer: redundant records force one classical pointer variable, with no weights (§3);
2. the **exponent-fixer iff**: among rules $p\propto f(w)$, refinement-additivity $\Leftrightarrow$ Born $\Leftrightarrow$ remote-refinement no-signaling (§5), together with the $\alpha$-family countermodel (§4);
3. a **meta no-go**: any premise satisfied by the whole $\alpha$-family cannot entail Born (§6);
4. a **finite H-theorem** that derives the residual measure-preservation from reversibility over a uniform bath plus mixing, with a reset-kernel no-go showing relaxation alone is insufficient (§§7–9);
5. **three brackets on the exponent** (§10): a rank-count no-go (records can't count the weights), the rotation/Banach–Lamperti uniqueness (only the square survives unitary mixing — the same square as the Gaussian bell curve, while a Lorentz boost admits no positive norm), and Gleason (the noncontextual functionals are exactly the Born functionals).

We are explicit throughout about what is *not* done: this is a finite, non-relativistic combinatorial core;
no continuum field theory, no Type III algebra, and no QIQT-H physical postulate enters the theorems. The
residual premise (§11) is a genuine physical input, not a missing lemma.

## 2. Setting and reduction target

Fix a finite outcome set and weights $w_k\ge 0$ from a fixed prepared state, $w_k=\lVert P_k\psi\rVert^2$.
A **rule** is a normalized assignment $p_k = f(w_k)/\sum_j f(w_j)$ for some $f:\mathbb{R}_{\ge0}\to\mathbb{R}_{\ge0}$. Born is the case $f=\mathrm{id}$. We study which structural constraints on $f$ — or on the
underlying microstate dynamics that produces the actual record — force $f=\mathrm{id}$.

Two equivalent vantage points recur. The **rule level** treats $f$ abstractly. The **selector level** posits
a finite microstate space $\Omega$, a Born-agnostic *typicality measure* $\mu:\Omega\to\mathbb{R}$, and a
deterministic readout $\mathrm{sel}:\Omega\to K$; the probability of outcome $k$ is the marginal
$\mathrm{marg}\,\mu\,\mathrm{sel}\,k=\sum_{\omega}[\mathrm{sel}(\omega)=k]\,\mu(\omega)$. The selector level
is where "dynamics" lives, and where the residual input ultimately sits.

## 3. Records give definiteness, not weights

The first layer is Born-free. In a spectrum-broadcast / quantum-Darwinism structure, many environment
fragments redundantly encode the same system pointer. We formalize this with orthogonal projectors on a
module and prove that redundancy forces a single classical pointer variable.

> **Theorem (objectivity, `SBSBoolean.lean`).** A nonzero state cannot lie in two orthogonal record sectors
> (`record_unique`); hence redundant fragment readouts agree and are all functions of one classical pointer
> $K_0$ (`fragments_co_referential`).

This delivers the Boolean pointer algebra — definite, context-independent outcomes — with *no* probability
weights. It is exactly the qualitative "single world" content, and it is provably silent about the exponent.

## 4. The exponent is underdetermined: the $\alpha$-family

The decisive negative fact is that records, with all their structure, do not pin the exponent.

> **Theorem (records $\not\Rightarrow$ Born, `RefinementBorn.lean`).** The squared-weight rule
> $\mu_2(k)=w_k^2/\sum_j w_j^2$ satisfies definiteness, redundant-fragment agreement, support- and
> certainty-preservation, label-permutation symmetry, and product independence, yet for $w=(\tfrac13,\tfrac23)$
> returns $(\tfrac15,\tfrac45)\neq$ Born (`alphaSq_ne_born`).

The whole family $f_\alpha(w)=w^\alpha$ is a guardrail: any proposed "derivation of Born from record
structure" must fail on it, because it has all of that structure. The remaining sections each identify a
premise the $\alpha$-family violates, and prove it forces Born.

## 5. The exponent-fixers (an iff)

**Refinement-additivity.** Write the rule as $p_k\propto f(w_k)$ and demand that splitting an outcome of
weight $x+y$ into two exclusive sub-records of weights $x,y$ leaves the coarse event's probability unchanged.
This forces $f(x+y)=f(x)+f(y)$, hence (on the rationals) $f(t)=Ct$, hence Born.

> **Theorems (`RefinementBorn.lean`).** Additivity of $f$ implies Born on rational weights
> (`additive_fMeasure_eq_born`); the squared rule is *not* additive and exhibits the exact failing split
> (`alphaSq_refinement_violation`).

**No-signaling under refinement.** The least ad-hoc form of the premise is operational: a spacelike choice to
refine a remote ancillary record must not change a local coarse frequency. We define
`RefinementNatural f` (the coarse probability of a merged outcome equals the sum of the fine probabilities)
and prove the equivalence.

> **Theorems (`RefinementBorn.lean`).** No-signaling plus $f>0$ implies $f$ additive
> (`refinementNatural_additive`), hence Born; the squared rule is not refinement-natural — it would signal
> (`sq_not_refinementNatural`); and Born itself is refinement-natural (`id_refinementNatural`). Together:
> **among rules $p\propto f$, refinement-natural $\Leftrightarrow$ Born.**

So Born is equivalent to an independently-motivated relativistic principle (no remote-refinement signaling),
not merely to an algebraic ansatz. The same content at the integer/count level is the linearity of an
additive count, $F(n)=n\,F(1)$ (`BornRoutes.additive_nat_linear`), which yields Born weights $n_i/M$ on the
grid.

## 6. The meta no-go: no Born-free premise pins the exponent

Why can one never simply *invent* the missing premise as a consequence of structure alone? Because the
power-law family is a fixed point of every Born-free constraint.

> **Theorem (meta no-go, `BornRoutes.lean`).** With integer counts $[2,2]$ and their refinement $[1,1,2]$
> (one outcome split into two equal sub-records), Born gives $P=\tfrac12$ either way, while the $\alpha=2$
> rule gives $\tfrac12$ on the coarse context but $\tfrac13$ on the fine one (`sqRule_refinement_signals`).

Thus $f_2$ *signals under refinement* while satisfying normalization, positivity, permutation symmetry and
product independence. Any constraint set $\Gamma$ that the entire family $f_\alpha$ obeys is therefore
satisfied by a non-Born member, so $\Gamma$ cannot entail Born. The irreducible premise must be one that
breaks the $\alpha$-symmetry — refinement-additivity, no-signaling, equivariance, or martingale
conservation are exactly such premises, and they are all equivalent in strength.

## 7. The selector layer and the Bell guardrail

At the selector level the no-signaling premise becomes a statement about the marginal of the actual
selector, not about the already-Born trace functional. We isolate the load-bearing condition.

> **Theorems (`SelectorRefinement.lean`).** If a remote refinement $R$ preserves the typicality measure
> ($\mu$-equivariance, $(R)_*\mu=\mu$), then every local-readout marginal is invariant
> (`equivariant_marg_invariant`); a deterministic $\alpha=2$ selector over a uniform measure *does* signal
> (`Countermodel.alphaSq_selector_signals`, by `decide`), proving that ordinary operator-net microcausality
> does **not** already supply selector no-signaling.

The equivariance must be imposed at the level of *marginals*, not pointwise. This is forced by a Bell
guardrail already in the development: a pointwise-local deterministic selector is a local hidden-variable
model, hence obeys the CHSH bound $\lvert\mathrm{CHSH}\rvert\le 2$ (`Bell.chsh_pointwise`), which the quantum
value $2\sqrt2$ violates (`Tsirelson` module). So the selector is ontically contextual; only its marginals
are local — the same structure as quantum-equilibrium no-signaling in Bohm–DGZ.

We also note the bridge that unifies the routes:

> **Theorem (`SelectionDynamics.lean`).** In an equivariant selection model the $\mu$-expectation of every
> observable is conserved under the selection step, $\mathbb{E}_\mu[W\circ R]=\mathbb{E}_\mu[W]$
> (`SelectionModel.expectation_conserved`).

This is precisely the martingale-increment condition, so the no-signaling route and the
martingale/optional-stopping route to Born are two faces of one condition: $\mu$-equivariance.

## 8. Zurek envariance: both halves

Envariance gives Born over a Born-agnostic measure, in two complementary pieces.

> **Equal amplitudes (`Envariance.lean`).** A $\mu$-preserving bijection implementing the $a\leftrightarrow b$ label swap on the readout forces equal marginals, $\mathrm{marg}\,a=\mathrm{marg}\,b$
> (`envariance_equal_marg`). A swap of records undone by a $\mu$-preserving remote action cannot change a
> local marginal — pure no-signaling symmetry, no Born input. Consequently total transposition-envariance
> forces $\mu$ uniform (`envariance_forces_uniform`).

> **Unequal amplitudes (`SelectionDynamics.lean`).** Fine-grain outcome $k$ into $M\cdot w_k$ equal
> sub-records; all sub-records are pairwise swap-symmetric, hence equiprobable ($1/M$ each), and outcome $k$
> collects $M w_k\cdot(1/M)=w_k$ (`born_from_uniform`).

`envariance_forces_uniform` closes the "why uniform?" gap that the fine-graining argument otherwise leaves
open: uniformity is *derived* from swap-symmetry rather than assumed. The sole residual is that the global
state's dynamics furnishes these $\mu$-preserving swaps for genuinely equal-amplitude branches — Zurek's
envariance symmetry of the entangled state.

## 9. A finite H-theorem: deriving the measure-preservation

All routes bottom out at one residual: *the selection dynamics preserves a Born-agnostic measure*. We attack
this directly. The naive hope — "the dynamics is bistochastic, and a bistochastic map fixes the uniform
measure" — is dangerous, because bistochasticity on the Born fine-grid is just the assumed equivariance in
disguise. We resolve this with a no-go and an honest derivation.

**No-go (relaxation alone is Born-agnostic).** The reset kernel $K_\nu(x,y)=\nu(y)$ is row-stochastic,
strictly positive (primitive), and sends *every* measure to $\nu$ in one step.

> **Theorem (`Relaxation.lean`).** For any full-support $\nu$, one step of the reset kernel reaches $\nu$
> (`resetKernel_reaches`); and it is bistochastic iff $\nu$ is uniform (`resetKernel_colSum`).

So "Markov + positive + relaxes to a unique equilibrium" holds for *any* $\nu$ and does not select Born.
Relaxation must be supplemented by exactly the structure the reset kernel lacks: bistochasticity.

**The advance — reversibility forces bistochasticity.** Let a reversible closed update $F:S\times E\simeq S\times E$ act over a bath $E$, and define the induced selector kernel $T_F(s,s')=\#\{e:\mathrm{fst}\,F(s,e)=s'\}/\lvert E\rvert$.

> **Theorems (`Relaxation.lean`).** $T_F$ is row-stochastic (`inducedKernel_row`) and **column-stochastic**
> (`inducedKernel_col`), the latter because $F$ is a *bijection*: the bath states landing on $s'$, summed
> over sources, are the preimage of the fiber $\{s'\}\times E$, of size $\lvert E\rvert$. Hence the uniform
> (= Born-counting) measure is stationary (`uniform_stationary_of_colStochastic`).

Column-stochasticity — the property the no-go showed is exactly what relaxation lacks — is here *derived*
from reversibility (the finite shadow of unitarity / Liouville's theorem), not assumed.

**Relaxation half.** Stationarity is not attraction: the identity and permutations are bistochastic and do
not mix. A Doeblin minorization supplies the mixing.

> **Theorem (Doeblin contraction, `Relaxation.lean`).** If $T x y\ge\varepsilon$ for all $x,y$, then for any
> probability measures $\mu,\nu$ one has $\lVert \mu T-\nu T\rVert_1 \le (1-\lvert\Omega\rvert\varepsilon)\lVert\mu-\nu\rVert_1$ (`doeblin_contraction`). Combined with column-stochasticity, every $\mu$ relaxes
> geometrically to uniform $=$ Born (`relaxation_to_uniform`).

This is the finite H-theorem with **every premise explicit**: reversibility (column-stochastic), a uniform
bath, and mixing ($\varepsilon$-minorization).

## 10. Why the exponent is 2: counting, symmetry, and uniqueness

Granting that the weight must be assumed, the reader will press: *why the square*? Four further
machine-checked results sharpen this and bracket the Born posit from independent directions.

**Records cannot count the weights.** One might hope the multiplicity of environment records of a branch
scales with its weight, so uniform counting reproduces Born from the dynamics. It cannot: record multiplicity
is the rank of the orthogonal environment record subspace — fixed by the dynamics and *independent of the
amplitude* (scaling a branch by a nonzero scalar preserves its support rank), whereas the Born weight is
continuous in the amplitude. So no amplitude-independent multiplicity rule equals Born
(`RankCountNoGo.no_multiplicity_rule_is_born`). Decoherence delivers definite records, not their weights.

**Only the square survives mixing.** Unitary evolution continuously mixes amplitudes; ask which normalization
$\sum_k|c_k|^\alpha$ is preserved. Exactly $\alpha=2$: the elementary two-coordinate rotation preserves
$|c|^2$ (Pythagoras), while for $\alpha\ne2$ the $45°$ rotation of $(1,0)$ changes the total
($2^{1-\alpha/2}\ne1$). This is the finite core of the Banach–Lamperti theorem on $\ell^p$ isometries — for
$p\ne2$ the only isometries are permutations and phases; only $p=2$ admits the continuous rotation group
(`RotationBorn.rotation_invariant_iff_exponent_two`). The **same square** governs the bell curve: a
rotation-invariant product density is forced Gaussian with $|z|^2$ in the exponent (Maxwell–Herschel;
`SymmetrySquare.gaussian_profile_from_rotation`) — the Gaussian's square and Born's square are one and the
same rotation invariant. A **Lorentzian boost**, by contrast, preserves the indefinite $t^2-x^2$ and so admits
*no* positive probability norm — it must vanish on the light cone (`SymmetrySquare.no_boost_invariant_positive_norm`).
Relativistic Born therefore descends from the unitary Wigner representation on the positive-definite Hilbert
space, never from spacetime geometry (compact rotation *forces* $\alpha=2$; the non-compact boost *forbids*
any positive norm).

**Gleason makes the posit unique.** The irreducible input — a noncontextual probability assignment on effects
— is forced to the Born/trace form $\operatorname{Re}\operatorname{tr}(\rho E)$ and conversely realized by
every density matrix (`BornChain.noncontextual_forces_born`, `born_is_noncontextual`), so the noncontextual
functionals are *exactly* the Born functionals. With the meta no-go (§6) and the rank-count no-go above, this
is the honest ceiling: Born reduces to one maximally-natural posit, made unique by Gleason and proven
irreducible from three directions. *Honest caveat:* the rotation/symmetry results confirm the square is the
degree-2 invariant of the unitary group — they do not derive Born from nothing, since unitary invariance
already carries the quadratic form.

## 11. The irreducible residual and honest scope

After the H-theorem, the Born rule in this development follows from three finite premises about the
inaccessible degrees of freedom:

1. **reversibility** — the closed update is a bijection (the finite shadow of exact unitarity, which the
   no-collapse setting asserts globally);
2. **uniform bath** — the inaccessible degrees are uniform in counting measure;
3. **mixing** — the dynamics is $\varepsilon$-minorized.

Premise (1) is essentially given by exact unitarity. Premises (2)–(3) are a finite Liouville plus
molecular-chaos *typicality postulate*. This is not pure logic — but it is a far weaker and more physical
input than "assume $\mu=\lvert\Psi\rvert^2$," and the meta no-go of §6 proves that *nothing Born-free can
replace it*. That postulate is the genuine, sharply-localized residual; it is the same statistical-mechanical
input every typicality-based account of Born ultimately requires.

We stress the limits. The development is finite and combinatorial: it contains no continuum field theory, no
von Neumann algebra type classification, and no specific physical Hamiltonian. The selector models are
finite by construction. The claim is therefore a **conditional representation result**: Born holds given the
named premises, the premises are individually motivated, the meta no-go shows some such premise is
unavoidable, and the H-theorem reduces the measure-theoretic premise to reversibility plus mixing. It is not
a derivation of Born from no assumptions, and we make no such claim.

## 12. Verification and reproducibility

All theorems named above are part of a single Lean 4 aggregator (`QIQTH`). The development builds with no
`sorry`/`admit` (`sorryAx` count $0$) and a raw project-axiom count of $0$; every cited theorem carries a
`#print axioms` line in `QIQTH/AxiomAudit.lean` reporting only the standard classical foundations
`propext`, `Classical.choice`, `Quot.sound`. A CI guard (`scripts/axiom_budget_check.sh`) fails the build on
any `sorryAx` dependency or any reappearance of a retired axiom, and asserts the project-axiom budget of $0$.
We use the wording "no `sorry` and no axioms beyond the standard classical foundations" deliberately; we do
not claim the informal "axiom-free" externally, since classical logic axioms are present as in any standard
Mathlib development.

## Appendix A — Theorem ↔ Lean index

| Paper statement | Lean name | File |
|---|---|---|
| records ⇒ one pointer | `record_unique`, `fragments_co_referential` | `SBSBoolean.lean` |
| records ⇏ Born ($\alpha=2$) | `alphaSq_ne_born` | `RefinementBorn.lean` |
| additivity ⇒ Born | `additive_fMeasure_eq_born` | `RefinementBorn.lean` |
| no-signaling ⇒ additive | `refinementNatural_additive` | `RefinementBorn.lean` |
| Born is refinement-natural | `id_refinementNatural` | `RefinementBorn.lean` |
| additive count is linear | `additive_nat_linear` | `BornRoutes.lean` |
| meta no-go witness | `sqRule_refinement_signals` | `BornRoutes.lean` |
| martingale ⇒ Born | `born_from_martingale` | `BornRoutes.lean` |
| equivariance ⇒ no-signaling | `equivariant_marg_invariant` | `SelectorRefinement.lean` |
| selector α=2 signals | `Countermodel.alphaSq_selector_signals` | `SelectorRefinement.lean` |
| equivariance = martingale | `SelectionModel.expectation_conserved` | `SelectionDynamics.lean` |
| uniform ⇒ Born (fine-grain) | `born_from_uniform` | `SelectionDynamics.lean` |
| equal-amplitude Born | `envariance_equal_marg` | `Envariance.lean` |
| envariance ⇒ uniform | `envariance_forces_uniform` | `Envariance.lean` |
| relaxation no-go | `resetKernel_reaches` | `Relaxation.lean` |
| reversible ⇒ bistochastic | `inducedKernel_col` | `Relaxation.lean` |
| Doeblin contraction | `doeblin_contraction` | `Relaxation.lean` |
| relaxation to Born | `relaxation_to_uniform` | `Relaxation.lean` |
| records ⇏ Born by counting | `no_multiplicity_rule_is_born` | `RankCountNoGo.lean` |
| noncontextual ⇒ Born (Gleason) | `noncontextual_forces_born`, `born_is_noncontextual` | `BornChain.lean` |
| only α=2 survives mixing | `rotation_invariant_iff_exponent_two` | `RotationBorn.lean` |
| bell curve = Born's square | `gaussian_profile_from_rotation` | `SymmetrySquare.lean` |
| boost no-go (no positive norm) | `no_boost_invariant_positive_norm` | `SymmetrySquare.lean` |
| CHSH guardrail | `chsh_pointwise` | `Bell.lean` |

## Appendix B — Reproducibility

Build with a pinned Lean toolchain via `lake build QIQTH`; verify axioms with
`lake build QIQTH.AxiomAudit` and `bash scripts/axiom_budget_check.sh` (exit $0$, "raw axiom count: 0
(budget 0) — OK"). The named theorems exist with the signatures quoted; the index in Appendix A gives the
file for each.
