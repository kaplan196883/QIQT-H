# A Lean 4 formalization of a boost-covariant abelian Weyl-bit history measure on continuum bosonic Fock space

**Author:** Paweł Kapłański
**Status:** draft technical note (quant-ph / math.FA), 2026-06-09
**Artifact:** Lean 4 + Mathlib, axiom-free; repository <https://github.com/kaplan196883/QIQT-H> (directory `lean/mathlib/QIQTH/Fock/`).

---

## Abstract

We report a machine-checked construction, in Lean 4 with Mathlib, of a σ-additive,
Lorentz-boost-covariant *typicality measure* on the outcome histories of a commuting family of binary
Weyl observables on the continuum symmetric (bosonic) Fock space over `L²(ℝ)`. Concretely: we build the
bosonic Fock space from the exponential-vector positive-definite kernel `exp⟪f,g⟫`; the bounded Weyl
operators `W(u)` and prove they are unitary with adjoint `W(u)*=W(−u)`; the binary Weyl-bit operators
`A(u,s)=(I+sW(u))/2` and their effects `E(u,s)=A(u,s)*A(u,s)`, which form a two-outcome POVM
(`E(u,+1)+E(u,−1)=I`); and the joint Born weights `p_J(σ)=‖∏_{i∈J}A(u_i,σ_i)Ω‖²` of a symplectically
commuting (microcausal) mode family. We prove these weights are a genuine vacuum-state expectation of a
positive joint effect, are normalized and Kolmogorov-projective, and hence extend (via a finite-fiber
Kolmogorov theorem, also formalized) to a unique σ-additive probability measure `μ∞` on the history space
`∏_i {±1}`. Finally we prove `μ∞` is invariant under boosting the one-particle modes by any isometry of the
one-particle space — in particular under the 1+1-dimensional Lorentz boost realized as rapidity translation
on `L²(ℝ)` — and we package this as an abstract geometric-covariance interface. The entire development
depends only on Lean's three standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`); it
introduces no domain axioms and contains no `sorry`. We are careful to state precisely what is and is not
established: this is a boost-covariant *abelian Weyl-bit process*, not yet a fully spacetime-localized
relativistic field, the missing ingredient being a Poincaré-equivariant localization map satisfying
Pauli–Jordan microcausality.

---

## 1. Introduction

A recurring foundational question for "typicality"/Everettian and single-outcome accounts of quantum
mechanics is whether a canonical, Lorentz-covariant probability measure exists over the space of outcome
*histories* of a relativistic quantum field, reproducing Born statistics without a per-measurement
postulate. The hard part is *covariance*: producing one measure on histories that is invariant under the
spacetime symmetry group, rather than a frame-dependent family.

This note isolates and machine-checks the **measure-theoretic and operator-algebraic core** of that
question on the continuum free field, at the level of a commuting family of binary field observables. We do
*not* claim a full Wightman/Haag–Kastler localized net; we claim, and verify in Lean, the following chain of
statements on the genuine continuum bosonic Fock space:

1. the bosonic Fock space, coherent states, and quasifree vacuum *exist as a genuine Hilbert space*
   (Mathlib has no Fock-space theory; this is built from the `exp⟪f,g⟫` kernel);
2. the Weyl operators are unitary, satisfy `W(u)*=W(−u)`, and the spacelike/isotropic ones commute
   (microcausality);
3. the binary Weyl-bit effects form a two-outcome POVM and the joint Born weights are genuine vacuum
   expectations of positive joint effects;
4. those weights are normalized and projective, hence define a unique σ-additive history measure `μ∞`;
5. `μ∞` is invariant under boosting the modes by any one-particle isometry (Lorentz-frame independence).

Everything is axiom-free and reproducible. The deliberate, honest scope is discussed in §6.

### Relation to prior formalization work

To our knowledge Mathlib contains no symmetric Fock space, CCR/Weyl algebra, quasifree state, or
second-quantization functor; the present development builds these directly. The Kolmogorov extension we use
is the general (correlated, non-product) finite-fiber case, formalized as part of this program and built on
Mathlib's `IsProjectiveLimit` / `addContent` infrastructure.

---

## 2. The one-particle space and the bosonic Fock space

Let `H` be a complex inner-product space (the *one-particle space*). For the relativistic instance we take
`H = L²(ℝ)`, the one-particle space of the 1+1-dimensional free field written in rapidity coordinates, on
which the Lorentz boost acts as translation (see §5).

**Fock space (`Fock/ExpKernel`, `Fock/FockSpace`).** The kernel `K(f,g)=exp⟪f,g⟫` is positive-definite:
this follows from the Gram matrix being PSD, the Schur product theorem (Hadamard powers preserve PSD), and
the convergent series `exp`. (`expKernel_posSemidef`.) We realize the associated pre-Hilbert space directly
as `FockPre H := H →₀ ℂ` carrying the inner product
```
⟪φ, ψ⟫ = Σ_{f,g} conj(φ_f) · exp⟪f,g⟫ · ψ_g ,
```
the **exponential (coherent) vectors** `e(f)` with `⟪e(f),e(g)⟫=exp⟪f,g⟫`, and the **vacuum** `Ω=e(0)`,
`⟪Ω,Ω⟫=1`. The Fock space `Fock H` is its Hilbert completion. (`FockPre.inner_expVec`,
`Fock.inner_expVec`, `norm_vac_sq`.)

**Second quantization (`Fock/SecondQuant`).** For a one-particle isometry `A : H →ₗᵢ H`,
`Γ(A) e(f) = e(A f)`, fixing the vacuum (`Γ(A)Ω=Ω`) and preserving the Fock inner product
(`fockInner_secondQuant`); hence `Γ(A)` is an isometry of `Fock H`.

---

## 3. Weyl operators, unitarity, and microcausality

**Weyl operators (`Fock/Weyl`, `Fock/WeylOp`).** With `c(u,g)=exp(−½⟪u,u⟫−⟪u,g⟫)`,
```
W(u) e(g) = c(u,g) · e(g+u) .
```
The prescribed action preserves the coherent inner product (`weyl_isometry`, `fockInner_weyl`), so `W(u)`
is a linear isometry. We prove the two algebraic identities that make it a *unitary*:

- **Adjoint** (`weylCoeff_adjoint`, `fockInner_weyl_adjoint`): `⟪W(u)φ, ψ⟫ = ⟪φ, W(−u)ψ⟫`, i.e. `W(u)*=W(−u)`.
- **Inverse** (`weylCoeff_neg_cancel`, `weylPre_neg_cancel`): `W(−u)W(u)=I` exactly (not merely up to a
  phase), so `W(−u)` is the two-sided inverse of `W(u)`.

**Microcausality (`Fock/WeylCCR`).** Two Weyl operators commute when their modes are symplectically
orthogonal (`weyl_microcausality`):
```
Im⟪u,v⟫ = 0  ⟹  W(u)W(v) = W(v)W(u) .
```
For modes that arise from spacelike-separated localization regions this is the microcausality of the field;
at the present level of generality we use it as the algebraic hypothesis `Im⟪u_i,u_j⟫=0` for distinct modes.

**Quasifree vacuum state (`Fock/VacuumState`).** `ω₀(T)=Re⟪Ω,TΩ⟫` is a real Born-expectation functional on
operators (positive on `T*T`, `ω₀(I)=1`). It gives the correct probabilities for self-adjoint effects; we do
not claim it is a complex-linear C\*-state.

---

## 4. Weyl-bit effects, Born weights, and the typicality measure

**The bit and its effect (`Fock/WeylBit`, `Fock/WeylBitEffect`).** For `s ∈ {+1,−1}`,
```
A(u,s) = (I + s·W(u))/2 ,   E(u,s) = A(u,s)* A(u,s) .
```
Then `E(u,s)` is positive (`effOp_nonneg`), and the pair is a genuine two-outcome **POVM**:
```
⟪ψ, E(u,s) ψ⟫ = ‖A(u,s) ψ‖²        (bit_effect_expectation)
E(u,+1) + E(u,−1) = I              (effOp_sum_eq_id)
```
the completeness relation using `W(−u)W(u)=I`.

**Joint Born weights (`Fock/WeylBitMeasure`).** For a finite *commuting* context — a finite set `J` of
modes with `Im⟪u_i,u_j⟫=0` for `i≠j` — and an outcome `σ : J → {±1}`, the joint weight is
```
p_J(σ) = ‖∏_{i∈J} A(u_i,σ_i) Ω‖²
```
where the product is the order-independent `noncommProd` of the commuting bit operators. We prove:

- **POVM expectation** (`bornWeight_eq_joint_effect`): `p_J(σ) = ⟪Ω, E_σ Ω⟫` with
  `E_σ = (∏_i A(u_i,σ_i))* (∏_i A(u_i,σ_i))` a positive joint effect (so positivity is *free*: it is a
  norm-square / vacuum expectation of `T*T`);
- **Normalization** (`bornWeight_total`): `Σ_σ p_J(σ) = 1`;
- **Projectivity** (`bornWeight_coarse`): for `I ⊆ J`, `p_I(y) = Σ_{σ↾I=y} p_J(σ)` (Kolmogorov
  coarse-graining consistency).

**The measure (`StateNetMeasure`, `KolmogorovFiniteFiber`, `Fock/WeylBitMeasure`).** Positivity,
normalization, and projectivity are exactly the hypotheses of a (state-agnostic) `EffectStateNet`; together
with a formalized general finite-fiber Kolmogorov extension theorem they yield a unique σ-additive
probability measure on the history space:

> **Theorem (existence, `weylBit_typicalityMeasure_exists`).** For any commuting mode family there is a
> probability measure `μ∞` on `∏_i {±1}` whose finite marginals are the Born weights `p_J`.

This is, to our knowledge, the first machine-checked *non-deterministic* typicality measure on a continuum
field (the weights `p_J` are a genuine `2^{|J|}`-outcome distribution, not a point mass).

---

## 5. Lorentz-boost covariance

**Boost on the one-particle space (`Fock/OneParticle`).** A measure-preserving flow on `L²(μ)` induces a
one-parameter unitary group. For the 1+1-dimensional massive field, writing momenta in rapidity
coordinates `p=m·sinh θ` turns the invariant measure into a constant multiple of Lebesgue measure and the
boost into the translation `θ ↦ θ+t`; thus the Lorentz boost `U₁(t)` is realized as translation on `L²(ℝ)`
(`boostUnitary`), with no Jacobian.

**Covariance of the Born weights (`Fock/WeylBitMeasure`).** Boosting every mode `u_i ↦ A u_i` by a
one-particle isometry `A` is implemented on Fock space by `Γ(A)`, which is an isometry; since the Born
weight is a norm-square, it is invariant:
```
bornWeight (A∘u) J σ = bornWeight u J σ        (bornWeight_isometry_invariant)
```
(via the second-quantization push-through `Γ(A)(∏A(u_i,s_i)Ω) = ∏A(Au_i,s_i)Ω`,
`bornVecTot_secondQuant`). Hence the whole projective family is unchanged, and by uniqueness of the
Kolmogorov limit:

> **Theorem (boost-covariance, `weylBit_typicality_boost_invariant`).** If `μ` realizes the typicality
> family for modes `u` and `ν` for boosted modes `A∘u`, then `μ=ν`.
>
> **Corollary (`weylBit_typicality_lorentzBoost_invariant`).** Specializing `A=U₁(t)`, the Weyl-bit
> typicality measure is the same in every Lorentz frame.

**Abstract geometric-covariance interface (`Fock/WeylBitGeoCovariance`).** We package this as a reusable
datum `GeoCovariantModes`: a relabeling `π : ι ≃ ι` of the mode index by a symmetry, a one-particle
isometry `A` implementing it, the equivariance `u(π i)=A(u i)`, and the isotropy `Im⟪u_i,u_j⟫=0`. The
conclusion (`GeoCovariantModes.typicality_invariant`) is that the typicality measure for the
geometrically-relabeled family `u∘π` equals the one for `u`. A concrete spacetime localization map (§6) is
exactly what would supply `π`, `A`, the equivariance, and the microcausality from Poincaré covariance and
Pauli–Jordan vanishing.

---

## 6. Honest scope: what is and is not established

We are explicit about the boundary, following internal and external (GPT-5.5-pro) adversarial review.

**What is established.** A boost-covariant **abelian Weyl-bit process** on the genuine continuum bosonic
Fock space over `L²(ℝ)`: the Fock/coherent/quasifree construction; unitarity `W(u)*=W(−u)` and
`W(−u)W(u)=I`; algebraic microcausality; two-outcome POVM `{E(u,±1)}` with completeness; positive joint
effects and the POVM reading of the Born weights; normalization and projectivity; existence and uniqueness
of the σ-additive history measure `μ∞`; and its invariance under boosting the modes by a one-particle
isometry, specialized to the 1+1 Lorentz boost.

**What is *not* established (the boundary).**

1. **Spacetime localization.** The covariance proven is "boost the abstract one-particle modes
   `u_i ↦ U₁(t) u_i`," not "boost the spacetime region in which a measurement is localized." Bridging this
   requires a Poincaré-equivariant localization map `K : TestFun(Minkowski) → H` with
   `K(f∘Λ⁻¹)=U(Λ)Kf` and the **Pauli–Jordan** property `Im⟪Kf,Kg⟫=0` for spacelike-separated supports. The
   Pauli–Jordan commutator-support theorem is the genuine analytic obstruction and is a separate,
   substantially larger project (tempered distributions / propagation of singularities, or an explicit
   kernel-support argument).

2. **Single global measure vs. contextual family.** The global Kolmogorov measure `μ∞` is appropriate
   precisely because we fix a *commuting* (pairwise symplectically orthogonal, hence decoherent) mode
   family. For non-commuting observables a single classical history measure does not exist (Fine/Bell); we
   make commutativity an explicit hypothesis and do not violate it.

3. **State functional.** `ω₀=Re⟪Ω,·Ω⟫` is a real Born-expectation functional, sufficient for effect
   probabilities; we do not claim a complex-linear C\*-state, nor have we lifted the bit operators from the
   pre-completion space `FockPre` to bounded operators on the completed Hilbert space (a bounded but
   nontrivial functional-analytic step).

4. **Non-triviality of correlations.** The process is genuinely non-i.i.d. when `Re⟪u_i,u_j⟫≠0`: the
   pair correlations are determined by the quasifree Gram covariance, not a product law. We say the finite
   laws are *determined by* the quasifree two-point structure; we do not identify the bit law with the
   two-point function itself.

None of these gaps is hidden behind an axiom or a `sorry`: the formalization is complete for exactly the
statements claimed.

---

## 7. Reproducibility and the axiom audit

- **Toolchain.** Lean `leanprover/lean4:v4.30.0`; Mathlib at revision `c5ea003` (2026-05-26).
- **Build.** `lake build QIQTH` (the `Fock/*` modules build as part of it).
- **Axiom discipline.** Every theorem cited here is checked with `#print axioms` in
  `QIQTH/AxiomAudit.lean`; each depends on **only** Lean's three standard foundational axioms
  `propext, Classical.choice, Quot.sound`. The project introduces **no** domain-specific axioms in this
  development and contains **no** `sorry`. A budget script (`scripts/axiom_budget_check.sh`) enforces the
  axiom count and scans for `sorryAx`.

### Index of the main Lean results

| Statement | Lean name |
|---|---|
| `exp⟪f,g⟫` positive-definite | `expKernel_posSemidef` |
| coherent inner product; `‖Ω‖²=1` | `FockPre.inner_expVec`, `norm_vac_sq` |
| `Γ(A)` isometric, fixes `Ω` | `fockInner_secondQuant`, `secondQuantPre_vacuum` |
| `W(u)*=W(−u)` | `fockInner_weyl_adjoint` |
| `W(−u)W(u)=I` | `weylPre_neg_cancel` |
| microcausality | `weyl_microcausality` |
| `⟪ψ,E(u,s)ψ⟫=‖A(u,s)ψ‖²` | `bit_effect_expectation` |
| POVM completeness `E(u,+1)+E(u,−1)=I` | `effOp_sum_eq_id` |
| Born weight = joint effect expectation | `bornWeight_eq_joint_effect` |
| normalization `Σ_σ p_J(σ)=1` | `bornWeight_total` |
| projectivity `p_I(y)=Σ_{σ↾I=y} p_J(σ)` | `bornWeight_coarse` |
| existence of `μ∞` | `weylBit_typicalityMeasure_exists` |
| boost-covariance of `μ∞` | `weylBit_typicality_boost_invariant` |
| Lorentz-boost corollary | `weylBit_typicality_lorentzBoost_invariant` |
| geometric-covariance interface | `GeoCovariantModes.typicality_invariant` |

---

## 8. Outlook

The natural next increments, in increasing difficulty: (i) the literal single-measure pushforward
`Measure.map(history-relabel) μ∞ = μ∞` (needs a `noncommProd` reindex-by-bijection lemma and routine
measure plumbing); (ii) lifting the Weyl-bit operators to bounded operators on the completed Fock space with
the complex vacuum state; (iii) the concrete Poincaré-equivariant localization map `K` with Pauli–Jordan
microcausality, which would upgrade the present abelian Weyl-bit process to a genuinely spacetime-local free
field. Of these, (iii) is the real research program; (i)–(ii) are bounded.

---

## References (open access)

1. K. R. Parthasarathy, *An Introduction to Quantum Stochastic Calculus*, Birkhäuser (1992) — §§15, 19, 20,
   23 (positive-definite kernels, Fock space, Weyl operators, creation/annihilation).
2. The Mathlib Community, *Mathlib4*, <https://github.com/leanprover-community/mathlib4> — `IsProjectiveLimit`,
   `addContent`, continuous functional calculus, `StandardSubspace`.
3. Lean 4, <https://github.com/leanprover/lean4>.
4. (Background, for the localization map and microcausality) standard AQFT references: Pauli–Jordan
   commutator and the Reeh–Schlieder/Bisognano–Wichmann circle of ideas; cited as the analytic frontier, not
   used in the formalization.

*This note describes the `QIQTH/Fock/*` layer of the QIQT-H formalization program; the broader foundational
program is documented separately in the repository.*
