# 50 — Born Exponent: Attack Routes (GPT-5.5-pro consult, 2026-06-13)

This document records the three attack routes on the Born **exponent** (why `p_k ∝ w_k` and not
`w_k^α`), GPT-5.5-pro's assessment, the new routes it surfaced, and which pieces are now
machine-checked (`QIQTH/BornRoutes.lean`, axiom-free).

## The single open problem (restated)

Everything up to the exponent is machine-checked (records ⇒ definiteness; refinement-additivity ⇔
Born; no-signaling ⇔ Born; uniform typicality + weight-encoding ⇒ Born). The α-family
`f(w)=w^α` (α≠1) satisfies **every** Born-free structural premise yet is **not** Born — it is the
proven countermodel (`RefinementBorn.alphaSq_ne_born`). So closing Born = supplying exactly one
extra premise that **breaks the α-symmetry**. The whole question is: *can that premise be derived
from QIQT-H dynamics rather than assumed?*

## The three routes written down

- **Route A — capacity counting / MaxEnt.** Maximise entropy of the outcome distribution subject to a
  capacity/cost constraint; hope Born falls out. **Pro's verdict: obstruction, not a closure.** A flat
  MaxEnt gives uniform (dimension counting), not Born; any *additive* per-branch cost reproduces the
  whole `w^α` family (α = the cost's exponent). Best repurposed as a **no-go**: "no symmetric additive
  cost singles out α=1."

- **Route B — uniqueness of the equivariant measure.** Argue the only dynamics-invariant typicality
  measure is `|Ψ|²`. **Pro's verdict: only closes with Bohm-grade extra structure** (a guidance
  current + locality). For a bare finite deterministic selector, α-equivariant measures exist, so
  uniqueness fails without that structure. Best repurposed as a **guardrail/impossibility** (the
  `SelectionDynamics.uniformModel` honest-risk note).

- **Route C — no-signaling + capacity (count level).** *The closest positive route.* If every remote
  record split is a μ-preserving dynamics that leaves the local coarse basin invariant (remote-split
  **no-signaling**), the count functional `F` is forced additive: `F(a+b)=F(a)+F(b)`, hence
  `F(n)=n·F(1)`, hence `P_F(i)=n_i/M = w_i` — **Born on the rational grid**. ✅ The load-bearing
  `additive ⇒ linear` step is machine-checked: `BornRoutes.additive_nat_linear`.
  **Honest caveat (pro):** stating "F additive" *directly* is just refinement-naturality (already
  proven, `RefinementBorn.refinementNatural_additive`). The genuine new content is the **dynamical
  lemma** that every Bob-local split is implemented by a μ-preserving remote dynamics — that is the
  Born-strength input and remains open.

## New routes pro surfaced

- **Martingale / optional-stopping (pro's "best missing dynamical bridge").** If the squared branch
  weight `W_k(t)` is a μ-**martingale** (μ-expected squared weight conserved) with the final record
  **absorbing** (`W_k(T)∈{0,1}`) and initial value `w_k`, then by optional stopping
  `μ(outcome k) = E_μ[W_k(T)] = E_μ[W_k(0)] = w_k` — **Born**. This is exactly why GRW/CSL collapse
  models recover Born. ✅ Machine-checked: `BornRoutes.born_from_martingale`. The Born-strength premise
  is the martingale conservation; deriving it from QIQT-H unitary dynamics is the open step. This is a
  genuinely **different** Born-strength input from refinement/fine-graining — physically the most
  appealing (it is a conservation law), and the most promising frontier target.

- **Meta no-go (Lean-friendly).** "If a structural constraint set Γ is satisfied by every power-rule
  model `Fα(n)=n^α`, and `F₂` violates Born on some finite context, then Γ does **not** entail Born."
  ✅ Machine-checked witness: `BornRoutes.sqRule_refinement_signals` — counts `[2,2]` vs the
  refinement `[1,1,2]`: Born gives `1/2` either way; the α=2 rule gives `1/2` coarse but `1/3` fine,
  i.e. it **signals under refinement**. So no premise the whole power-family obeys can force Born —
  the formal statement of *why the exponent cannot be pinned for free*.

## Pro's ranking

1. **Route C** — best positive route (count-level additivity; Born on the grid). ✅ core checked.
2. **Martingale** — best missing dynamical bridge (conservation-law Born). ✅ implication checked.
3. **Route B α-no-go** — best guardrail/impossibility.
4. **Route A MaxEnt no-go** — obstruction theorem.

## What is now machine-checked (this round, `QIQTH/BornRoutes.lean`, axiom-free)

| theorem | content |
|---|---|
| `additive_nat_linear` | Route C core: additive count `F` ⇒ `F(n)=n·F(1)` ⇒ Born weights `n_i/M`. |
| `born_from_martingale` | Martingale + absorbing 0/1 + initial `w_k` ⇒ `μ(outcome k)=w_k`. |
| `sqRule_refinement_signals` | Meta no-go witness: α=2 signals under `[2,2]→[1,1,2]` (1/2 vs 1/3); Born invariant. |
| `SelectionModel.expectation_conserved` | **Bridge**: equivariance ⇒ `E_μ[W∘R]=E_μ[W]` for every `W` — the martingale-increment condition, *derived* not assumed in the equivariant model. |
| `Envariance.envariance_equal_marg` | **Zurek equal-amplitude Born**: a μ-preserving swap implementing the `a↔b` label swap ⇒ `marg a = marg b`. Equal-amplitude branches equiprobable, no Born assumption. |
| `Envariance.envariance_forces_uniform` | Total transposition-envariance ⇒ `μ` constant — *derives* the uniform Born-agnostic measure `born_from_uniform` had to assume. |

### The two halves of Born, both now machine-checked

Zurek's envariance route is now complete as a pair of axiom-free theorems over a **Born-agnostic** measure:
- **Equal amplitudes** → `envariance_equal_marg`: swap-symmetric branches are equiprobable (a system swap
  undone by a μ-preserving remote action cannot change the local marginal — pure no-signaling symmetry).
- **Unequal amplitudes** → `born_from_uniform`: fine-grain outcome `k` into `M·w_k` equal sub-records;
  all sub-records are pairwise swap-symmetric, so `envariance_forces_uniform` makes them equiprobable
  (`1/M` each), and outcome `k` collects `M·w_k·(1/M) = w_k` — Born on the rational grid.
`envariance_forces_uniform` closes the "why uniform?" gap that `born_from_uniform` left open: uniformity
is *derived* from swap-symmetry, not assumed. The sole remaining residual is unchanged and purely
physical — that the actual global state's `(Φ,λ)` dynamics furnishes these μ-preserving swaps for
genuinely equal-amplitude branches (the envariance symmetry of the entangled state, established by Zurek).

### The bridge that unifies the routes

`SelectionModel.expectation_conserved` (in `SelectionDynamics.lean`) shows the **martingale conservation
and the equivariance condition are the same thing**: for an equivariant typicality measure, the
μ-expectation of every observable is conserved under the selection step `R`. This discharges
`born_from_martingale`'s Born-strength premise (`hmart`) *inside the equivariant model class* — so the
no-signaling route (equivariance) and the martingale route are two faces of one condition. The entire
open problem then collapses to a single physical claim: **the actual `(Φ,λ)` dynamics preserves a
Born-agnostic typicality measure `μ`** (the Valentini-style relaxation hope, vs. the circularity risk
that the only equivariant `μ` is `|Ψ|²` itself).

## The swing at the physics (2026-06-13, `QIQTH/Relaxation.lean`)

Instead of restating the residual, an attempt to *derive* the measure-preservation from dynamics. Pro's
brutal verdict shaped it: naked "bistochastic ⇒ Born" is dressed-up equivariance, but reversibility over a
uniform bath genuinely *forces* bistochasticity. Two machine-checked theorems:

| theorem | content |
|---|---|
| `resetKernel_reaches` | **No-go**: the reset kernel `K_ν(x,y)=ν y` is row-stochastic, strictly positive, and sends every μ to `ν` in one step — so for ANY full-support `ν`, "Markov + positive + relaxes to a unique equilibrium" holds yet does *not* select Born. Relaxation alone is Born-agnostic. |
| `inducedKernel_col` | **The advance**: a reversible closed update `F : S×E ≃ S×E` over a uniform bath induces a *column*-stochastic selector kernel — bistochasticity is **derived from `F` being a bijection** (finite Liouville / unitarity shadow), not assumed. |
| `uniform_stationary_of_colStochastic` | column-stochastic ⇒ the uniform (= Born-counting, via `born_from_uniform`) measure is stationary. |
| `doeblin_contraction` | an ε-minorized kernel contracts ℓ¹ distance by `(1−|Ω|ε)`: the **relaxation** half (stationarity → attraction). |
| `relaxation_to_uniform` | **the finite H-theorem, all premises explicit**: reversibility (col-stochastic) + uniform bath + mixing (ε-minorization) ⇒ every μ relaxes geometrically to uniform = Born. |

**What this buys.** The irreducible input is sharpened from *"assume μ is |Ψ|²-equivariant"* to *"assume the
closed dynamics is reversible and the inaccessible bath is uniform in counting measure"* — a finite
Liouville + molecular-chaos premise, more structural and more physically forced. The no-go proves you
cannot drop it (relaxation alone gives any ν).

**The relaxation half is now also closed.** `doeblin_contraction` + `relaxation_to_uniform` supply the
mixing that turns "Born is a fixed point" into "Born is the *attracting* fixed point": an ε-minorized
(mixing) reversible-uniform-bath kernel drives every μ to Born geometrically, `‖μT−π‖₁ ≤ (1−|Ω|ε)‖μ−π‖₁`.
So the finite H-theorem is complete with **every premise explicit**: reversibility (column-stochastic, from
the bijection) + uniform bath + mixing (ε-minorization).

**Honest residual (pro), now sharply localised.** The Born rule, in this route, follows from three finite
premises about the inaccessible degrees of freedom: (i) the closed update is *reversible* (a bijection —
the finite shadow of unitarity, which QIQT-H asserts globally), (ii) the inaccessible *bath is uniform* in
counting measure, (iii) the dynamics is *mixing* (ε-minorized). (i) is essentially given by QIQT-H's exact
unitarity; (ii) and (iii) are a finite Liouville + molecular-chaos typicality postulate — not pure logic,
but a far weaker and more physical input than "assume μ = |Ψ|²". That postulate is the genuine irreducible
residual, and the meta no-go (`sqRule_refinement_signals`) proves nothing Born-free can replace it.

## The weight-encoding question — settled NO (GPT-5.5 consult, 2026-06-13)

The one way to upgrade "reduction" → "derivation" was Path A: derive the weight-encoding from the dynamics
(does decoherence make the Born-agnostic record multiplicity of branch `k` `∝ w_k`?). The consult verdict is
a clean **impossibility**, with a structural reason:

> Multiplicity is integer/discrete/**support-like** (the rank of the orthogonal environment record subspace,
> fixed by the interaction/bath); the Born weight `‖P_kψ‖²` is continuous/**amplitude-like**. Scaling a branch
> by a nonzero `c_k` changes its norm but **not** its support rank — so the count is locally constant in the
> amplitude and cannot be `∝ w_k` on any open set.

Mechanism by mechanism (none scale with `w_k` without smuggling `|Ψ|²`): einselection picks the basis not the
weights; quantum-Darwinism redundancy is set by the environment; ETH/typicality is defined w.r.t. a Hilbert
measure (already Born-type); large-deviation `e^{-ND}` needs a base measure that itself comes from amplitudes.

Machine-checked (`QIQTH/RankCountNoGo.lean`, axiom-free):

| theorem | content |
|---|---|
| `multRule_ne_born_of_differs` | a state-independent multiplicity rule can't match Born across two states with different Born values — the core obstruction. |
| `no_multiplicity_rule_is_born` | **no amplitude-independent record-multiplicity rule equals Born** (multiplicity state-independent, Born state-dependent). |

**So Path A is closed**, and that is a result: decoherence explains classical records, not why they are
weighted by squared amplitude. Born requires an **irreducible Hilbert-typicality axiom** — thinnest form
`μ(k)=⟨Ψ|P_k|Ψ⟩` (decoherent-history measure `‖C_hΨ‖²`), which Gleason then makes essentially unique. That is
**Path B, the honest ceiling**: Born reduced to one maximally-natural typicality posit, with machine-checked
no-gos proving (i) nothing Born-free can replace it and (ii) no amplitude-independent counting can supply it.

## The assembled Path-B chain (capstone, `QIQTH/BornChain.lean`)

The Gleason-uniqueness link is now wired into the chain end-to-end (axiom-free):

> **META NO-GO** (`sqRule_refinement_signals`) — nothing Born-free entails Born; some Born-strength input is
> forced. **⟹ RANK-COUNT NO-GO** (`no_multiplicity_rule_is_born`) — no amplitude-independent counting
> supplies it. **⟹ the input is irreducible**; its thinnest form is a **noncontextual probability assignment**
> on effects (the finite Hilbert-typicality axiom, an `EffectMeasure`). **⟹ GLEASON-UNIQUENESS**
> (`BornChain.noncontextual_forces_born` + `born_is_noncontextual`) — that axiom is forced to `μ(E)=Re tr(ρE)`
> and conversely every density matrix realizes it, so the noncontextual functionals are **exactly** the Born
> functionals: the axiom pins Born uniquely.

| theorem | content |
|---|---|
| `noncontextual_forces_born` | a noncontextual assignment (`EffectMeasure`) is forced to the Born trace form on every effect — Gleason, forward. |
| `born_is_noncontextual` | converse: every density matrix yields such a noncontextual assignment — the axiom is consistent and Born-unique. |

**Net (the ceiling, assembled).** Born is reduced to a single, maximally-natural typicality posit
(noncontextuality / Hilbert measure), made **unique** by Gleason, and **bracketed by two no-gos** proving (i)
nothing Born-free entails it and (ii) no amplitude-independent counting supplies it. This is the strongest
true statement available — the same posit every single-world program (Everett, Bohm–DGZ, Deutsch–Wallace)
ultimately needs.

## Why the exponent is 2 — the rotation/Banach–Lamperti core (GPT-5.5 consult, 2026-06-13)

The sharpest answer to "why $|c|^2$ and not $|c|^\alpha$" is the finite core of **Banach–Lamperti** (isometries
of $\ell^p$): for $p\neq2$ the only norm-preserving maps are permutations + phases (rigid relabelling); **only
$p=2$ admits the continuous rotation/mixing group** — and unitary dynamics *is* continuous amplitude-mixing.
So the square is the unique power-law normalization compatible with unitary evolution. Machine-checked
(`QIQTH/RotationBorn.lean`, axiom-free):

| theorem | content |
|---|---|
| `born_exponent_rotation_invariant` | α=2: the square is preserved by **every** rotation of two amplitudes (Pythagoras). |
| `lpow_rotation_invariant_forces_two` | α≠2: the 45° rotation of $(1,0)$ is an explicit witness — invariance there forces $2^{1-\alpha/2}=1$, i.e. α=2. |
| `rotation_invariant_iff_exponent_two` | the iff: $\sum|c_k|^\alpha$ is rotation- (mixing-) invariant **iff** α=2. |

This sharpens the picture past the two no-gos: the square is not merely the irreducible posit, it is the
**only** power-law normalization the existence of continuous unitary evolution permits. Honest caveat
(GPT-5.5): this is close to Gleason in symmetry language, not a deeper non-circular principle ("unitary"
already means inner-product-preserving) — but it is the cleanest statement of *where the 2 comes from*.

## Two more faces of the square — bell curve & boost (GPT-5.5-pro consult, 2026-06-13)

Pro confirmed both hypotheses and turned them into machine-checked theorems (`QIQTH/SymmetrySquare.lean`,
axiom-free):

**Aspect 1 — the bell curve's square IS Born's square (Maxwell–Herschel).** A product density invariant under
the rotation/unitary group is forced Gaussian, with the rotation-invariant quadratic `|z|²` in the exponent —
the same square Born uses. In squared-radius coordinates `U(2)`-invariance reads `P(a)P(b)=P(a+b)P(0)`, so the
radial profile is **multiplicative** and hence exponential: the exact multiplicative mirror of the additive
`f(x+y)=f(x)+f(y) ⇒ Born` bridge. Theorems: `rotation_product_multiplicative`, `multiplicative_pow`,
`gaussian_exponent`, `gaussian_profile_from_rotation`. (CLT governs *fluctuations* of already-Born
frequencies; it does not produce the Born weights — pro.)

**Aspect 2 — a Lorentzian boost cannot carry a probability (sharp no-go).** A boost is a rotation by
imaginary rapidity preserving the *indefinite* `t²−x²`; the light-cone vector `(1,1)` is an eigenvector with
eigenvalue `eᵡ`, so any homogeneous boost-invariant `F≥0` obeys `F(1,1)=e^{χα}F(1,1)` ⇒ `F(1,1)=0`. Hence
**no boost-invariant positive probability norm exists** (`no_boost_invariant_positive_norm`); relativistic
Born comes from the *unitary* (Wigner) rep preserving `Σ|c|²`, never from spacetime-boost invariance. The
mirror of `RotationBorn`: compact rotation *forces* α=2; non-compact boost *forbids* any positive norm.

**Unifying fact (pro, precise).** Born `Σ|z_i|²`, the Gaussian `e^{−‖x‖²}`, the free action `⟨φ,Aφ⟩`, and the
interval `t²−x²` are all the degree-2 invariant of their symmetry group; rotations (compact) and boosts
(non-compact) are real forms of one complexified group, Wick-related — but **only the positive-definite cases
support a probability norm.** Honest caveat: this confirms the square is the degree-2 invariant; it does not
derive Born from nothing (rotation/unitarity already imports the quadratic).

## Honest status

These are **conditional theorems**: each makes its one Born-strength premise fully explicit and
machine-checks the implication to Born, and the meta no-go proves no Born-free premise can replace
it. The remaining genuine research frontier is unchanged and now sharply localised: **derive one of
{remote-split no-signaling on counts, squared-weight martingale conservation, equivariance} from the
actual (Φ,λ) dynamics.** The martingale route is the recommended next target — a conservation law is
the most natural thing to seek a dynamical proof of.
