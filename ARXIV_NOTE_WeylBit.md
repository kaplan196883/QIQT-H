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
Pauli–Jordan microcausality. Toward that ingredient we additionally machine-check the *covariance half* of a
concrete mass-shell localization `K` for the 1+1D massive scalar — its boost-equivariance, volume-preserving
unit Jacobian, both-frequency reality relation, and the antisymmetry of the induced (Pauli–Jordan, not
Wightman) symplectic form — leaving the `L²` boundedness and the Pauli–Jordan support theorem as the
explicitly isolated analytic remainder.

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

**Literal single-measure pushforward.** The statements above equate the two measures realizing the `u` and
`u∘π` families. We additionally prove the textbook form — that the *one* measure `μ∞` is fixed by the
symmetry acting on the history space `∏_i {±1}` itself:

> **Theorem (`GeoCovariantModes.typicality_pushforward_invariant`).** Let `historyAct π : (g_i) ↦ (g_{π i})`
> be the relabeling of the history space induced by `π`. If `μ∞` realizes the Weyl-bit typicality family for
> an equivariant `GeoCovariantModes` datum, then `(historyAct π)_* μ∞ = μ∞`.

The proof reindexes the order-independent Born product along the index bijection — a `Finset.noncommProd`
reindex-by-bijection lemma (`bornVecTot_map`, `bornWeight_map`) we supply by induction, absent from the
present Mathlib — and shows the pushforward realizes the *same* projective family, so the conclusion follows
from uniqueness of the Kolmogorov limit.

---

## 5½. Toward the concrete localization map `K` (1+1D massive scalar, `Fock/Localization`)

The covariance above is stated for an *abstract* index symmetry. We have begun the concrete spacetime
localization that would instantiate it for the genuine free field, and the entire **covariance half** is now
machine-checked. In 1+1 Minkowski space `V = ℝ²` with pairing `η(p,x)=p₀x₀−p₁x₁`, mass shell
`p_m(θ)=(m cosh θ, m sinh θ)` (rapidity `θ`), and the localization

> `(K f)(θ) = 2^{−1/2}·f̂_M(p_m θ)`,  `f̂_M(p)=∫ e^{−iη(p,x)} f(x)\,dx`

(the `2^{−1/2}` is the invariant-measure normalization `dp/2ω = dθ/2`), we prove, axiom-free:

- **Geometry.** The boost `Λ_a` shifts the shell by rapidity, `Λ_a(p_m θ)=p_m(θ+a)` (`massShell_boost`), and
  the pairing is boost-invariant, `η(Λp,Λx)=η(p,x)` (`minkowskiDot_boost`).
- **Unimodularity + volume-preservation.** `det Λ_a = 1` (`det_lorentzBoost`) and `Λ_a` preserves the
  Lebesgue measure (`measurePreserving_lorentzBoost`) — the unit Jacobian for the Fourier change of
  variables.
- **Equivariance (keystone).** `(β_a f)^_M(p)=f̂_M(Λ_a p)` (`minkowskiFourier_boost`, where `β_a f = f∘Λ_a`),
  hence at the amplitude level `(K(β_a f))(θ)=(K f)(θ+a)` (`Krep_boost`): the spacetime Lorentz boost acts on
  the localized one-particle amplitude as the rapidity translation `θ↦θ+a` — exactly the one-particle unitary
  `U₁` of §5. So the localization *intertwines* the spacetime boost with the one-particle representation.
- **Reality / both frequencies.** `conj(f̂_M(p))=(\bar f)^_M(−p)` (`minkowskiFourier_conj`); for a real test
  function this is `conj(f̂_M(p))=f̂_M(−p)`, the relation that recovers the *full* (both-frequency) field from
  the positive-mass-shell amplitude.
- **Symplectic form is antisymmetric.** For the integral-level form `⟨Kf,Kg⟩=∫_ℝ \overline{(Kf)(θ)}(Kg)(θ)dθ`
  we prove Hermitian symmetry `conj⟨Kf,Kg⟩=⟨Kg,Kf⟩` (`Kform_conj`) and hence
  **`Im⟨Kf,Kg⟩=−Im⟨Kg,Kf⟩`** (`Kform_im_antisymm`) — the defining antisymmetry of the Pauli–Jordan
  *commutator* form, distinguishing it from the symmetric Wightman two-point function.

We also package the **L²-valued localization map** itself: a `LocalTest` is a spacetime test function whose
localized amplitude `Krep m f` lies in `L²(ℝ)` (the one-particle space), and `K : LocalTest → L²(ℝ)`
(`K L = (Krep m L.f).toLp`) is the Hilbert-space-valued localization the Stage-2 interface requires. The
square-integrability is carried as a domain field (the class is inhabited, `trivialLocalTest`).

What remains *not* yet formalized for a complete `K`: (i) that every Schwartz `f` is a `LocalTest`, i.e. the
boundedness `K f ∈ L²` from Schwartz decay (the Schwartz–Fourier convention-matching to Mathlib's `𝓕` plus
the mass-shell decay estimate — a bounded but multi-week exercise), and (ii) the analytic **Pauli–Jordan
support theorem** `Im⟪Kf,Kg⟫=0` for spacelike-separated supports (the `Δ_m` light-cone support — the genuine
multi-month wall). The latter is the single physics input the `SpacetimeLocalization` interface (§6) isolates
as a hypothesis.

---

## 6. Honest scope: what is and is not established

We are explicit about the boundary, following internal and external (GPT-5.5-pro) adversarial review.

**What is established.** A boost-covariant **abelian Weyl-bit process** on the genuine continuum bosonic
Fock space over `L²(ℝ)`: the Fock/coherent/quasifree construction; unitarity `W(u)*=W(−u)` and
`W(−u)W(u)=I`; algebraic microcausality; the two-outcome POVM `{E(u,±1)}` and the **joint** POVM `{E_σ}`
(positive bounded effects on the completed Hilbert space with operator completeness `∑_σ E_σ=I`) whose vacuum
expectations are the Born weights; normalization and projectivity; existence and uniqueness of the σ-additive
history measure `μ∞`; and its invariance under boosting the modes by a one-particle isometry, specialized to
the 1+1 Lorentz boost.

The finite weights are the **diagonal sequential-POVM (Weyl–Kraus) probabilities** `p_J(σ)=⟨Ω|C_σ†C_σ|Ω⟩`
with class operators `C_σ=∏ᵢA(uᵢ,σᵢ)`; their Kolmogorov consistency comes from POVM completeness *at each
mode* (`‖A(u,+)ψ‖²+‖A(u,−)ψ‖²=‖ψ‖²`), **not** from off-diagonal decoherence. We do **not** claim a
Gell-Mann–Hartle consistent/decoherent-histories functional: the off-diagonal `D(σ,τ)=⟨C_τΩ,C_σΩ⟩` is not
shown to vanish and generically does not when `Re⟪uᵢ,uⱼ⟫≠0`. The measure is thus the Kolmogorov extension of
a Weyl–Kraus sequential-measurement family, which is what makes its consistency unconditional.

**What is *not* established (the boundary).**

1. **Spacetime localization.** The covariance proven is "boost the abstract one-particle modes
   `u_i ↦ U₁(t) u_i`," not "boost the spacetime region in which a measurement is localized." Bridging this
   requires a Poincaré-equivariant localization map `K : TestFun(Minkowski) → H` with
   `K(f∘Λ⁻¹)=U(Λ)Kf` and the **Pauli–Jordan** property `Im⟪Kf,Kg⟫=0` for spacelike-separated supports.
   The *covariance half* of this concrete `K` is now machine-checked for the 1+1D massive scalar (§5½:
   equivariance, volume-preservation, and the antisymmetry of the localized symplectic form); what remains
   unformalized is the `L²` boundedness from Schwartz decay and the Pauli–Jordan *support* theorem. The
   Pauli–Jordan commutator-support theorem is the genuine analytic obstruction and is a separate,
   substantially larger project (tempered distributions / propagation of singularities, or an explicit
   kernel-support argument). We *do* package exactly these obligations as a reusable interface
   (`SpacetimeLocalization`: a localization map `K`, region family, boost, equivariance, and Pauli–Jordan
   microcausality as hypothesis fields) and prove that any such datum yields a `GeoCovariantModes`, hence the
   existence + boost-covariance + single-measure pushforward-invariance of `μ∞` over the spacelike-local
   field records (`SpacetimeLocalization.localized_typicality_pushforward_invariant`); a non-vacuity witness
   shows the interface is inhabited. We further give a *genuinely non-degenerate* continuum instance
   (`boostOrbitModes`): the discrete boost orbit `u_n = U₁(nτ)u₀` on `L²(ℝ)`, where the Lorentz boost of
   rapidity `τ` acts on the records by the **shift** `n ↦ n+1` (equivariance proven from the one-parameter
   group law), so `(historyAct (·+1))_* μ∞ = μ∞` (`boostOrbit_typicality_pushforward_invariant`). For this
   instance microcausality reduces to the *single* seed condition `Im⟪u₀, U₁(kτ)u₀⟫=0` (`k≠0`) — the residual
   Pauli–Jordan input. What remains is establishing that seed condition for a genuinely spacelike
   localization, i.e. the concrete `K`.

2. **Single global measure vs. contextual family.** The global Kolmogorov measure `μ∞` is appropriate
   precisely because we fix a *commuting* (pairwise symplectically orthogonal, i.e. compatible / jointly
   measurable) mode family — *not* a claim of dynamical decoherence (see the Weyl–Kraus remark above). For
   non-commuting observables a single classical history measure does not exist (Fine/Bell); we make
   commutativity an explicit hypothesis and do not violate it.

3. **State functional.** `ω₀=Re⟪Ω,·Ω⟫` is a real Born-expectation functional, sufficient for effect
   probabilities; we do not claim a complex-linear C\*-state. We *have* now lifted the Weyl operators from
   the pre-completion space `FockPre` to bounded operators on the completed Hilbert space `Fock H`
   (`weylCLM`, via `ContinuousLinearMap.extend`): `W(u)` is a CCR-unitary continuous linear map with the
   genuine Hilbert-space two-point function `⟪Ω,W(u)Ω⟫=exp(−½⟪u,u⟫)`, and the single-mode Born weight is a
   bona fide vacuum expectation of a bounded positive effect with operator POVM completeness
   `E(u,+1)+E(u,−1)=1` (`vacuumState_weylBitEffectCLM_true`, `weylBitEffectCLM_complete`). The full *joint*
   multi-mode effect `E_σ=(∏A(uᵢ,σᵢ))*(∏A(uᵢ,σᵢ))` is likewise a bounded *positive* operator on the completed
   Hilbert space, with both operator-level **completeness** `∑_σ E_σ=I` (`jointEffectCLM_complete`) and
   `vacuumState(E_σ)=bornWeight u J σ` (`jointEffectCLM_isPositive`, `vacuumState_jointEffectCLM`): the entire
   multi-mode Born law is a genuine bounded Hilbert-space **POVM** read in the vacuum state, not a collection
   of pre-completion gadgets. (This is the operator family; the *measure* `μ∞` is its Kolmogorov extension.)

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
| single-measure pushforward `(historyAct π)_* μ∞ = μ∞` | `GeoCovariantModes.typicality_pushforward_invariant` |
| `noncommProd` reindex-by-bijection | `bornVecTot_map`, `bornWeight_map` |
| spacetime-localization interface (Stage 2) | `SpacetimeLocalization`, `…toGeoCovariantModes` |
| localized pushforward covariance | `SpacetimeLocalization.localized_typicality_pushforward_invariant` |
| bounded Weyl unitary on `Fock H` | `weylCLM`, `weylCLM_neg_cancel` |
| Hilbert-space two-point function | `weylCLM_vacuum_inner` |
| Born weight = vacuum C\*-state expectation | `vacuumState_weylBitEffectCLM_true` |
| operator POVM completeness on `Fock H` | `weylBitEffectCLM_complete` |
| joint multi-mode effect, positive on `Fock H` | `jointEffectCLM_isPositive` |
| joint POVM completeness `∑_σ E_σ=I` on `Fock H` | `jointEffectCLM_complete` |
| joint Born weight = vacuum expectation | `vacuumState_jointEffectCLM` |
| concrete boost-orbit instance (`n↦n+1`) | `boostOrbitModes`, `boostOrbit_typicality_pushforward_invariant` |
| sharp single-mode range `(1/2,1)` | `weylBitWeight_mem_Ioo_half` |
| mass-shell geometry: boost shifts rapidity | `massShell_boost`, `minkowskiDot_boost` |
| boost unimodular + volume-preserving | `det_lorentzBoost`, `measurePreserving_lorentzBoost` |
| localization equivariance `(β_a f)^_M(p)=f̂_M(Λ_a p)` | `minkowskiFourier_boost`, `Krep_boost` |
| reality / both frequencies | `minkowskiFourier_conj` |
| symplectic form antisymmetric (Pauli–Jordan) | `Kform_im_antisymm` |

---

## 8. Outlook

The single remaining research program is the concrete Poincaré-equivariant localization map `K` with
Pauli–Jordan microcausality. Its *covariance half* is now machine-checked for the 1+1D massive scalar (§5½):
the mass-shell Fourier localization, boost-equivariance `(K(β_a f))(θ)=(K f)(θ+a)`, volume-preservation, the
both-frequency reality relation, and the antisymmetry of the localized symplectic form. Two analytic pieces
remain unformalized: (i) the `L²(ℝ)` boundedness `K f∈L²` from Schwartz–Fourier decay (a bounded
convention-matching-plus-decay exercise), and (ii) the **Pauli–Jordan support theorem** — `Im⟪Kf,Kg⟫=0` for
spacelike-separated supports, equivalently `supp Δ_m ⊆` the closed light cone (the `Δ_m` Bessel kernel
argument) — the genuine multi-month/multi-year frontier. For the discrete-boost-orbit instance (§6.1) the
latter reduces to the single seed fact `Im⟪u₀, U₁(kτ)u₀⟫=0` for `k≠0`. The bounded-operator lift of the Weyl
apparatus to the completed Hilbert space (including the *joint* multi-mode effect, §6.3), the literal
single-measure pushforward covariance (§5), a concrete non-degenerate boost-orbit realization (§6.1), and the
localization covariance scaffolding (§5½) are all now proven; everything downstream of the cited Pauli–Jordan
support input is machine-checked and axiom-free.

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
