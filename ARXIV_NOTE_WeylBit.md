# A Lean 4 formalization of a Poincaré-covariant, microcausal Weyl-bit history measure on the 1+1D free quantum field

**Author:** Paweł Kapłański
**Status:** draft technical note (quant-ph / math.FA), 2026-06-10
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
introduces no domain axioms and contains no `sorry`.

We then **close the spacetime-localization gap**. For the 1+1-dimensional massive scalar we construct the
concrete mass-shell localization map `K` from real smooth compactly-supported spacetime test functions into
`L²(ℝ,dθ)` and machine-check the two physics properties an Einstein-causal, Poincaré-covariant localization
must have. **(i) Microcausality (Pauli–Jordan):** `Im⟪Kf,Kg⟫ = 0` whenever the supports of `f` and `g` are
spacelike separated — the genuine light-cone commutator-support theorem, proved through an oscillatory
integration-by-parts keystone `|∫_a^b sin(c·sinh u)\,du| ≤ 3/(|c|\cosh a)`, a dominated-convergence limit and
a Fubini assembly, with the `L²`-integrability side-condition discharged internally (so the top-level
statement carries no analytic hypothesis). **(ii) Poincaré equivariance:** `K(τ_b β_a f) = U(a,b)\,Kf`, where
`U(a,b) = M_b ∘ U₁(a)` composes the rapidity-translation isometry `U₁(a)` (the boost) with the unimodular
multiplication isometry `(M_b ψ)(θ) = e^{-iη(p_m(θ),b)}ψ(θ)` (the spacetime translation); we prove the group
law `U(a,b)U(a',b') = U(a+a',\,b+Λ_{-a}b')`, exhibiting `(a,b)↦U(a,b)` as a unitary **representation** of the
connected Poincaré group `ℝ^{1,1}⋊SO⁺(1,1)`. **(iii) Non-triviality:** `K` is not the zero map (explicit
Gaussian witness), and there is a genuinely spacelike pair of localizable tests making (i) non-vacuous.
Consequently the σ-additive history measure `μ∞` for any pairwise-spacelike (microcausal) localized family is
invariant under the **whole connected Poincaré group**, not merely under abstract one-particle isometries.
The remaining boundaries are matters of scope (free/quasi-free vacuum sector, connected proper-orthochronous
group, the formalized Weyl-bit Born law, 1+1 dimensions), stated precisely in §6; there is no remaining
unformalized analytic input and no `sorry`.

---

## 1. Introduction

A recurring foundational question for "typicality"/Everettian and single-outcome accounts of quantum
mechanics is whether a canonical, Lorentz-covariant probability measure exists over the space of outcome
*histories* of a relativistic quantum field, reproducing Born statistics without a per-measurement
postulate. The hard part is *covariance*: producing one measure on histories that is invariant under the
spacetime symmetry group, rather than a frame-dependent family.

This note isolates and machine-checks the **measure-theoretic and operator-algebraic core** of that
question on the continuum free field, at the level of a commuting family of binary field observables, and
then **closes it onto genuine spacetime localization**. We do *not* claim a full Wightman/Haag–Kastler net
of von Neumann algebras with Type III₁ classification; we claim, and verify in Lean, the following chain of
statements on the genuine continuum bosonic Fock space:

1. the bosonic Fock space, coherent states, and quasifree vacuum *exist as a genuine Hilbert space*
   (Mathlib has no Fock-space theory; this is built from the `exp⟪f,g⟫` kernel);
2. the Weyl operators are unitary, satisfy `W(u)*=W(−u)`, and the spacelike/isotropic ones commute
   (algebraic microcausality);
3. the binary Weyl-bit effects form a two-outcome POVM and the joint Born weights are genuine vacuum
   expectations of positive joint effects;
4. those weights are normalized and projective, hence define a unique σ-additive history measure `μ∞`;
5. `μ∞` is invariant under boosting the modes by any one-particle isometry (Lorentz-frame independence);
6. the concrete 1+1D mass-shell localization map `K` realizes (2) from genuine spacelike separation — it
   satisfies the **Pauli–Jordan** support theorem `Im⟪Kf,Kg⟫=0` for spacelike-separated test supports;
7. `K` is **Poincaré-equivariant**, intertwining the spacetime boost-and-translation action with a unitary
   **representation** `U(a,b)=M_b∘U₁(a)` of the connected Poincaré group, so `μ∞` is invariant under the whole
   connected group; and `K` is non-trivial (Gaussian witness) with a non-vacuous spacelike instance.

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

## 5½. The concrete localization map `K` (1+1D massive scalar, `Fock/Localization`)

The covariance above is stated for an *abstract* index symmetry. We construct the concrete spacetime
localization that instantiates it for the genuine free field. This section records its covariance scaffolding
and `L²`-boundedness; the microcausality (Pauli–Jordan) and the full translation/Poincaré structure that
complete it are §5¾. In 1+1 Minkowski space `V = ℝ²` with pairing
`η(p,x)=p₀x₀−p₁x₁`, mass shell
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
  **`Im⟨Kf,Kg⟩=−Im⟨Kg,Kf⟩`** (`Kform_im_antisymm`). This antisymmetry is the *commutator*-type structure
  (as opposed to the symmetric Wightman two-point function); we are careful **not** to over-read it: `Im⟨·,·⟩`
  is antisymmetric for *any* complex inner product, so antisymmetry alone does not identify this as the
  Pauli–Jordan distribution. It is the mass-shell symplectic form; its identification as the field commutator
  is secured by the **spacelike-support (Pauli–Jordan) theorem of §5¾**, `Im⟪Kf,Kg⟫=0` for spacelike-separated
  supports, which is now proved.

We also package the **L²-valued localization map** itself: a `LocalTest` is a spacetime test function whose
localized amplitude `Krep m f` lies in `L²(ℝ)` (the one-particle space), and `K : LocalTest → L²(ℝ)`
(`K L = (Krep m L.f).toLp`) is the Hilbert-space-valued localization the Stage-2 interface requires.

**`L²` admissibility (the membership criterion).** We do **not** claim a uniform operator bound
`‖Kf‖_{L²} ≲ ‖f‖_{𝒮}`; what is machine-checked is an *admissibility criterion* plus a concrete inhabitant:

- *Reduction to a decay bound.* All the measure-theoretic content is discharged: `1/cosh ∈ L²(ℝ)`
  (`memLp_cosh_inv` — `cosh²θ ≥ 1+θ²` so `cosh⁻²` is dominated by the Cauchy density `(1+θ²)⁻¹`), whence
  `‖(K f)(θ)‖ ≤ C/cosh θ ⟹ K f ∈ L²` (`Krep_memLp_of_decay`). The boundedness of `K` thus rests on a single
  sharp pointwise estimate — that the Fourier transform of a smooth test decays like `1/cosh` on the mass
  shell — with everything else proven.
- *A concrete non-degenerate instance.* For the Gaussian `f(x)=exp(−‖x‖²)` we compute the localization
  explicitly: by Fubini over `ℝ²` and the complex Gaussian Fourier integral, `K f` is the real amplitude
  `(K f)(θ) = 2^{−1/2}·π·exp(−m²cosh(2θ)/4)` (`minkowskiFourier_gaussian`, `Krep_gaussian_eq`), so
  `‖(K f)(θ)‖² = (π²/2)·exp(−(m²/2)cosh 2θ)` is integrable and `K f ∈ L²(ℝ)` (`gaussian_Krep_memLp`).
  Hence `gaussianLocalTest` witnesses that `K`'s admissible domain is non-empty (the Gaussian's support is
  all of spacetime, so it witnesses domain non-degeneracy, **not** spacelike localization).
- *The general Schwartz bound (now machine-checked).* For **every** Schwartz test function `f` we prove the
  sharp decay `‖(K f)(θ)‖ ≤ C_f·(cosh θ)⁻¹` with `C_f = 4π(‖f‖₁+‖∂f‖₁)/(√2·|m|)`, hence `K f ∈ L²(ℝ)`
  (`schwartz_Krep_memLp`). The proof exhibits the bespoke (no-2π Minkowski-pairing) transform as a genuine
  `VectorFourier.fourierIntegral` for the continuous bilinear form `L v w = (v₀w₀−v₁w₁)/(2π)`
  (`minkowskiFourier_eq_fourierIntegral`) and applies Mathlib's Fourier-decay estimate
  (`VectorFourier.pow_mul_norm_iteratedFDeriv_fourierIntegral_le`) — which performs the integration by parts —
  with the test vector `v = (p₀,−p₁)` extracting `L v p = (p₀²+p₁²)/(2π)`; on the mass shell
  `p₀²+p₁² = m²(cosh²θ+sinh²θ) ≥ m²cosh²θ` gives the `1/cosh` decay. This yields a `LocalTest` for *every*
  Schwartz function (`schwartzLocalTest`) — the honest local test class.

So the localization map `K` has its covariance scaffolding machine-checked and is `L²`-bounded on the full
Schwartz class (with constant controlled by `L¹` norms of `f` and `∂f`, i.e. by Schwartz seminorms). What was
formerly the "single remaining input" — the analytic Pauli–Jordan support theorem — **is now proved**; we turn
to it next.

---

## 5¾. Microcausality, translations, and full Poincaré covariance of `K` (`Fock/PauliJordan`, `Fock/TranslationCovariance`)

Three further results promote `K` from a boost-equivariant `L²`-bounded map to a fully Poincaré-covariant,
microcausal localization. All are axiom-free.

**Pauli–Jordan microcausality (`Fock/PauliJordan`).** For real, smooth, compactly-supported tests `f, g` with
spacelike-separated supports and mass `m ≠ 0`,
```
Im⟪K f, K g⟫ = 0       (K_im_inner_eq_zero_smooth)
```
— the genuine Einstein-causality / commutator-support property, the `Δ_m` light-cone vanishing read on the
one-particle inner product. The analytic core is the oscillatory integration-by-parts keystone
`|∫_a^b sin(c·sinh u)\,du| ≤ 3/(|c|\cosh a)` (`abs_integral_sin_sinh_le`), feeding a pointwise vanishing for
spacelike separation, a dominated-convergence truncation limit, and a mixed Fubini step that assembles the
double-integral kernel `Im(\overline{Kf}\,Kg) = ½∬ sin η(p_m θ, x−y)\,(f x · g y)\,d(x,y)`
(`Kform_im_eq_zero_of_spacelike`, `Krep_prod_im`). The top-level form `K_im_inner_eq_zero_smooth` discharges
the `L²`-integrability side-condition internally (Cauchy–Schwarz on the Schwartz amplitudes), so the caller
sees no analytic hypothesis. A concrete spacelike pair of bumps makes the statement **non-vacuous**
(`localized_microcausality_nonvacuous`): this is not the degenerate `f=0` case.

**Translation equivariance and the multiplier isometry (`Fock/TranslationCovariance`).** A spacetime
translation `τ_b f(x)=f(x−b)` multiplies the localized amplitude by a `θ`-dependent unit-modulus phase
(`Krep_translate`):
```
K(τ_b f)(θ) = e^{-iη(p_m(θ),b)} · (K f)(θ) = (M_b (K f))(θ).
```
The multiplier `M_b` is a *genuine* `LinearIsometry` of `L²(ℝ)` (`multiplierIsometry`): although it is *not* a
translation, `|e^{-iη}|=1` makes the phase cancel in every inner product (`multiplier_inner`,
`⟪M_b φ, M_b ψ⟫ = ∫ \overline{φ_b}φ_b\,\overline{φ}ψ = ⟪φ,ψ⟫`), so it preserves the entire complex Gram
matrix. Hence `K(τ_b f) = M_b(Kf)` (`K_translate_equivariant`) and, by the same Gram-matrix/isometry-invariance
route used for the boost, `μ∞` is **translation-invariant** (`localized_typicality_translation_invariant`).

**The connected Poincaré representation (`Fock/TranslationCovariance`).** Setting `U(a,b)=M_b∘U₁(a)`
(`poincareIsometry`), the localization intertwines an arbitrary connected-Poincaré transformation:
```
K(τ_b β_a f) = U(a,b)(K f)        (K_poincare_equivariant)
```
and `(a,b)↦U(a,b)` is a genuine group **representation** — we prove the two subgroup laws
`U₁(a)U₁(a')=U₁(a+a')` (`boostUnitary_comp`), `M_b M_{b'}=M_{b+b'}` (`multiplierIsometry_comp`), the nonabelian
semidirect intertwining `U₁(a)M_b = M_{Λ_{-a}b}U₁(a)` (`boostUnitary_comp_multiplier`), and hence the full
group law
```
U(a,b)\,U(a',b') = U(a+a',\ b + Λ_{-a}b')        (poincareIsometry_comp)
```
of `ℝ^{1,1}⋊SO⁺(1,1)`. Since boosts and translations generate the connected Poincaré group of 1+1D Minkowski
space, the typicality measure `μ∞` for any pairwise-spacelike microcausal localized family is invariant under
the **whole connected Poincaré group** (`localized_typicality_poincare_invariant`). Non-triviality is secured
by `K_gaussian_ne_zero` (`K(\text{Gaussian})≠0`, its amplitude `2^{-1/2}π e^{-m^2\cosh(2θ)/4}` being everywhere
strictly positive).

This is the literal Open-Problem-3b deliverable: a microcausal, provably non-trivial, σ-additive typicality
measure on the 1+1D relativistic free field that is full connected-Poincaré covariant, with the covariance
realized by an honest unitary group representation. The remaining boundaries (§6) are scope statements, not
unformalized inputs.

---

## 6. Honest scope: what is and is not established

We are explicit about the boundary, following internal and external (GPT-5.5-pro) adversarial review.

**What is established.** A **microcausal, Poincaré-covariant Weyl-bit history measure** on the genuine
continuum bosonic Fock space over `L²(ℝ)`, with a *concrete spacetime localization*: the Fock/coherent/
quasifree construction; unitarity `W(u)*=W(−u)` and `W(−u)W(u)=I`; the two-outcome POVM `{E(u,±1)}` and the
**joint** POVM `{E_σ}` (positive bounded effects on the completed Hilbert space with operator completeness
`∑_σ E_σ=I`) whose vacuum expectations are the Born weights; normalization and projectivity; existence and
uniqueness of the σ-additive history measure `μ∞`; the concrete 1+1D mass-shell localization `K` with **(i)**
Pauli–Jordan microcausality `Im⟪Kf,Kg⟫=0` for spacelike-separated supports (§5¾, non-vacuous), **(ii)** full
connected-Poincaré equivariance `K(τ_b β_a f)=U(a,b)Kf` with `(a,b)↦U(a,b)` a genuine unitary **representation**
of `ℝ^{1,1}⋊SO⁺(1,1)`, and **(iii)** non-triviality (`K≠0`); and the resulting invariance of `μ∞` under the
whole connected Poincaré group.

The finite weights are the **diagonal sequential-POVM (Weyl–Kraus) probabilities** `p_J(σ)=⟨Ω|C_σ†C_σ|Ω⟩`
with class operators `C_σ=∏ᵢA(uᵢ,σᵢ)`; their Kolmogorov consistency comes from POVM completeness *at each
mode* (`‖A(u,+)ψ‖²+‖A(u,−)ψ‖²=‖ψ‖²`), **not** from off-diagonal decoherence. We do **not** claim a
Gell-Mann–Hartle consistent/decoherent-histories functional: the off-diagonal `D(σ,τ)=⟨C_τΩ,C_σΩ⟩` is not
shown to vanish and generically does not when `Re⟪uᵢ,uⱼ⟫≠0`. The measure is thus the Kolmogorov extension of
a Weyl–Kraus sequential-measurement family, which is what makes its consistency unconditional.

**What is *not* established (the boundary).** With the spacetime-localization gap now closed, the remaining
boundaries are *scope* statements, not unformalized analytic inputs. None is hidden behind an axiom or a
`sorry`.

1. **"Canonical," not "unique."** `μ∞` is the measure *canonically constructed* from the Born/Gram kernel and
   uniquely *extending its own finite-cylinder marginals* (Kolmogorov uniqueness). We do **not** prove it is
   the unique measure satisfying Born + covariance + microcausality; distinct measures can share one-bit
   marginals unless the full finite-dimensional law is part of the specification.

2. **Born-law scope and the commuting family.** The cylinder marginals are the *formalized Weyl-bit Born
   weights* `‖∏A(uᵢ,σᵢ)Ω‖²` for a *commuting* (pairwise symplectically orthogonal, hence compatible / jointly
   measurable, hence microcausal) family — *not* a claim of dynamical decoherence (see the Weyl–Kraus remark
   above), and *not* a joint law for non-commuting / sequential measurements. For incompatible observables a
   single classical history measure does not exist (Fine/Bell); we make commutativity an explicit hypothesis
   and do not violate it.

3. **Free / quasi-free, vacuum sector.** This is a vacuum (quasi-free) construction determined by the
   one-particle map `K`. The state functional `ω₀=Re⟪Ω,·Ω⟫` is a real Born-expectation functional sufficient
   for effect probabilities; we do **not** claim a complex-linear C\*-state, interacting fields, or
   state-independence. (We *have* lifted the Weyl apparatus to bounded operators on the completed Hilbert
   space `Fock H` via `ContinuousLinearMap.extend`: `weylCLM` is CCR-unitary with two-point function
   `⟪Ω,W(u)Ω⟫=exp(−½⟪u,u⟫)`, and the joint effect `E_σ` is a bounded positive operator with operator
   completeness `∑_σ E_σ=I` (`jointEffectCLM_complete`) and `vacuumState(E_σ)=bornWeight u J σ`
   (`vacuumState_jointEffectCLM`) — the multi-mode Born law is a genuine bounded Hilbert-space POVM read in
   the vacuum, not a collection of pre-completion gadgets.)

4. **Connected, proper-orthochronous only; global translation.** Covariance is under the connected Poincaré
   group generated by boosts and translations, with a *single* `b` translating spacetime once (we do **not**
   claim invariance under independent per-region translations, which would be false). We do **not** address
   parity, time reversal, or the disconnected components.

5. **Non-triviality is global; symplectic vanishing vs. commutator.** `K(\text{Gaussian})≠0` establishes that
   `K` is not the zero map; we do **not** yet prove the strictly-local `∃ f∈C_c^∞(ℝ^{1,1}),\ Kf≠0` (which
   would need a Paley–Wiener argument; the Gaussian is not compactly supported). And we prove
   `Im⟪Kf,Kg⟫=0`; the statement "the local Weyl operators commute" should be read as: *in any CCR
   representation*, vanishing of the symplectic form gives `W(Kf)W(Kg)=W(Kg)W(Kf)`.

6. **Dimension, and no Type III₁ net.** All of the above is 1+1-dimensional — the mass-shell rapidity
   parametrization that turns the boost into a translation is special to two dimensions. We do **not** claim a
   full Haag–Kastler net of von Neumann algebras with the Type III₁ classification (Buchholz–Wichmann); that
   is a separate, much larger program and is not needed for the typicality measure constructed here.

**Pair correlations.** The process is genuinely non-i.i.d. when `Re⟪uᵢ,uⱼ⟫≠0`: the pair correlations are
*determined by* the quasifree Gram covariance, not a product law; we do not identify the bit law with the
two-point function itself.

None of these boundaries is hidden behind an axiom or a `sorry`: the formalization is complete for exactly the
statements claimed, and each boundary above is a deliberate limitation of scope rather than an unproven step.

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
| mass-shell symplectic form antisymmetric (commutator-type) | `Kform_im_antisymm` |
| `L²`-valued localization `K : LocalTest → L²(ℝ)` | `LocalTest`, `Localization.K` |
| `L²`-admissibility criterion (`1/cosh` decay ⟹ `L²`) | `memLp_cosh_inv`, `Krep_memLp_of_decay` |
| explicit Gaussian Fourier on the shell | `minkowskiFourier_gaussian`, `Krep_gaussian_eq` |
| Gaussian inhabitant of the test class | `gaussian_Krep_memLp`, `gaussianLocalTest` |
| bespoke transform = `VectorFourier.fourierIntegral` (bridge) | `minkBilin`, `minkowskiFourier_eq_fourierIntegral` |
| **`L²`-bounded on ALL Schwartz tests** (`1/cosh` decay) | `schwartz_Krep_memLp`, `schwartzLocalTest` |
| oscillatory IBP keystone `\|∫sin(c·sinh u)\| ≤ 3/(\|c\|cosh a)` | `abs_integral_sin_sinh_le` |
| **Pauli–Jordan microcausality** `Im⟪Kf,Kg⟫=0` (spacelike) | `Kform_im_eq_zero_of_spacelike`, `K_im_inner_eq_zero_smooth` |
| non-vacuous spacelike witness | `localized_microcausality_nonvacuous` |
| **translation multiplier** `K(τ_b f)(θ)=e^{−iη(p_mθ,b)}Kf(θ)` | `Krep_translate` |
| multiplier isometry `M_b` (unimodular, inner-preserving) | `multiplierIsometry`, `multiplier_inner` |
| **translation equivariance** `K(τ_b f)=M_b(Kf)` | `K_translate_equivariant` |
| translation-covariance of `μ∞` | `localized_typicality_translation_invariant` |
| **Poincaré equivariance** `K(τ_b β_a f)=U(a,b)Kf` | `K_poincare_equivariant` |
| **Poincaré group law** `U(a,b)U(a',b')=U(a+a',b+Λ_{−a}b')` | `poincareIsometry_comp` |
| boost/translation subgroup + intertwining laws | `boostUnitary_comp`, `multiplierIsometry_comp`, `boostUnitary_comp_multiplier` |
| **full-Poincaré invariance of `μ∞`** | `localized_typicality_poincare_invariant` |
| non-triviality `K(Gaussian)≠0` | `K_gaussian_ne_zero` |

---

## 8. Outlook

The concrete mass-shell localization map `K` for the 1+1D massive scalar is now machine-checked end to end:
boost-equivariance and `L²`-boundedness on the full Schwartz class (§5½), the **Pauli–Jordan support theorem**
`Im⟪Kf,Kg⟫=0` for spacelike-separated supports (§5¾, via the oscillatory IBP keystone — the pointwise
`∫ sin(m(t\cosh θ − x\sinh θ))\,dθ` is *not* absolutely convergent, so the proof proceeds through truncation,
dominated convergence and a mixed Fubini, not naïve integration), translation equivariance through the
unimodular multiplier isometry `M_b`, and the full connected-Poincaré **representation** `U(a,b)=M_b∘U₁(a)`
with its semidirect group law (§5¾). The typicality measure `μ∞` is invariant under the whole connected
Poincaré group, the localization is non-trivial, and the spacelike microcausality is non-vacuous. Everything
above is axiom-free with no `sorry`.

What remains is *deliberate scope* (§6), not an unformalized analytic input: extension beyond the
free/quasi-free vacuum sector; the disconnected symmetries (P, T) and higher dimensions; a strictly-local
(compact-support) sharpening of non-triviality (a Paley–Wiener refinement); and — for the broader foundational
narrative, not for this measure — the Type III₁ classification of the associated local von Neumann algebras
(Buchholz–Wichmann), which is a separate research-grade program. The residual `𝒮(ℝ²)→L²` operator-norm
bundling of the Schwartz bound is likewise a packaging refinement, not a gap. To our knowledge this is the
first machine-checked, axiom-free construction of a Poincaré-covariant, microcausal, σ-additive typicality
measure on a relativistic free field, with the covariance realized by an honest unitary group representation.

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
