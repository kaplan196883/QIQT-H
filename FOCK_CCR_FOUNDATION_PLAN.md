# The Fock / CCR / quasifree foundation — the only path to the *literal* continuum prize

**Status:** committed program (decision taken 2026-06-08). This is the multi-year campaign that
replaces the finite-mode **shadow** in `QIQTH/FreeFieldTypicality.lean` with the genuine continuum
relativistic free field, and thereby earns the *literal* OP3b prize: a Lorentz-covariant typicality
measure μ∞ on a Type III₁ local net, Born marginals + boost-covariance machine-checked.

This is the **narrow, prize-aligned** sub-program of the broader Tomita–Takesaki tower
(`giggly-coalescing-scone.md` / `TOMITA_TAKESAKI_ROADMAP.md`). Where that plan formalizes the abstract
Connes Type-III classification top-down, **this** plan builds the one concrete object the prize needs
bottom-up: the symmetric Fock space over a one-particle Hilbert space with a Poincaré (at minimum
boost) representation, the CCR/Weyl algebra, the quasifree vacuum, the wedge-local net, its geometric
(Bisognano–Wichmann) modular flow, and finally the covariant μ∞ plugged into the **already-proven**
measure machinery. Type III₁-ness itself is **cited** (Buchholz–Wichmann), not proved — the honest
interface boundary.

---

## What we already have (build on, do not rebuild)

**Proven, axiom-free, in-repo (the measure/state/covariance apparatus is DONE):**
- `QIQTH/StateNetMeasure.lean` — `EffectStateNet`: *any* positive normalized linear functional ω on an
  effect net yields a Kolmogorov-consistent Born family. **This is the socket the field plugs into.**
- `QIQTH/KolmogorovFiniteFiber.lean` — `exists_isLimit`: σ-additive Kolmogorov extension, correlated
  (entangled) case, from compactness/FIP. The σ-additivity is solved.
- `QIQTH/FiniteMarginals.lean` — `FiniteMarginals`, `IsLimit`, `limit_unique`, projective-limit plumbing.
- `QIQTH/NormalState.lean` + `QIQTH/BHTypicalityMeasure.lean` — a genuine **normal state on B(H)**
  (diagonal density operator) feeding the loop end-to-end on infinite-dim B(H).
- `QIQTH/FreeFieldTypicality.lean` — the **finite-mode** free-field instance: boost = mode permutation
  `e : m ≃ m`, boost-covariance `freeFieldMeasure_boost_invariant` proven. **This is the shadow we are
  promoting to the continuum.** The continuum version must reproduce exactly this theorem with the
  finite mode-permutation replaced by a genuine one-parameter Lorentz boost.
- `QIQTH/StandardSubspaceModular.lean` — RvD bounded modular objects on Tanimoto `StandardSubspace`:
  `rvdR` (0≤R≤2, ℂ-linear, `rvdRC`), `rvdPmQ` (D conjugate-linear → J antiunitary). The **one-particle**
  modular Δ₁/J₁ machinery is started here; Phase F4 second-quantizes it.
- `QIQTH/AbsoluteValue.lean` — `|T| = √(T⋆T)` (sidesteps the `StarOrderedRing` wall).
- `QIQTH/Spectral/SpectralTheorem.lean`, `Spectral/PVM.lean` — bounded spectral theorem / PVM /
  `boundedFC`, `modFlowC` (Δ^{iz} entire flow), `modAutC` (σ_{-i}=ΔxΔ⁻¹). The continuum Δ^{it}
  generator infrastructure.

**Mathlib HAS (verified 2026-06-08):** `SymmetricAlgebra`/`Basis`, `TensorAlgebra`,
`ExteriorAlgebra`, Hilbert sums (`OrthogonalFamily`, `lp`/`HilbertSum`), `MeasureTheory.Lp` (= L²),
measure-preserving maps, `InnerProductSpace`/adjoint/positive, CFC, `VonNeumannAlgebra`+`.commutant`,
GNS, **`StandardSubspace`** (Tanimoto 2026: structural only; Δ/J/KMS are TODOs).

**Mathlib LACKS (we provide):** symmetric **Fock** space (the Hilbert completion — only the algebraic
`SymmetricAlgebra` exists), second quantization Γ/dΓ, creation/annihilation, **Weyl/CCR** operators and
the CCR C\*-algebra, **quasifree/coherent** states, exponential (coherent) vectors, the Lorentz-invariant
mass-shell measure + Poincaré one-particle rep, Haag–Kastler local nets, Bisognano–Wichmann.

---

## Progress (live)

- **F1 — DONE** (commit `822108b`, axiom-free): `QIQTH/Fock/OneParticle.lean`.  `MPFlow` →
  `MPFlow.unitary t : L²(μ) ≃ₗᵢ[ℂ] L²(μ)` (one-parameter unitary group); `boostUnitary` = the 1+1D
  massive Lorentz boost = translation on `L²(ℝ)` in rapidity coordinates (no Jacobian).
- **F2 keystone — DONE** (commit `6d5a515`, axiom-free): `QIQTH/Fock/ExpKernel.lean`.
  `expKernel_posSemidef` — `exp⟪f,g⟫` is a positive-definite kernel (Gram-PSD + Schur product theorem
  iterated over Hadamard powers + the exp series).  **The one hard analytic lemma of F2.**
- **F2 infinite-index lift — DONE** (commit `64037c9`, axiom-free): `expKernel_posSemidef'` for an
  arbitrary (infinite-dim) family — the form the exponential-vector inner product / `RKHS.OfKernel`
  consume.
- **F2 Fock space — DONE** (commits `8220e6c`, `0888726`, axiom-free): `QIQTH/Fock/FockSpace.lean`.
  Route (b) — direct scalar `PreInnerProductSpace.Core` on a `FockPre H` wrapper of `H₁ →₀ ℂ`
  (`re_inner_nonneg` = `expKernel_posSemidef'` verbatim).  `Fock H := UniformSpace.Completion (FockPre H)`
  is the genuine bosonic Fock Hilbert space; `Fock.expVec`/`Fock.vacuum` the coherent vectors and vacuum;
  `Fock.inner_expVec` proves `⟪e(f),e(g)⟫ = exp⟪f,g⟫`; `Fock.inner_vacuum` proves `⟪Ω,Ω⟫ = 1`.
- **F2 remaining (optional):** second quantization `Γ(A) e(f) = e(Af)` and its functoriality/unitarity
  (lift the F1 boost `U₁(t)` to `Γ(U₁(t))` on Fock space — the continuum `diagBoost`).  Not on the
  critical path to F6.
- **F3 vacuum state — DONE** (commit `038fae4`, axiom-free): `QIQTH/Fock/VacuumState.lean`.
  `vacuumState T = Re⟪Ω,TΩ⟫`, bundled `vacuumStateHom : (Fock H →L[ℂ] Fock H) →+ ℝ` with
  `vacuumState_nonneg` (≥0 on positives) and `vacuumState_one` (`ω₀(1)=1`) — **the ω₀ that
  `EffectStateNet` consumes for F6**, now on the genuine continuum free field.
- **F3 Weyl core — DONE** (commit `2f07473`, axiom-free): `QIQTH/Fock/Weyl.lean`.
  `weylCoeff u g = exp(−½⟪u,u⟫−⟪u,g⟫)`; `weyl_isometry` (the prescribed `W(u)` action preserves the
  coherent-state inner product → `W(u)` unitary — the CCR-unitarity core); `weylCoeff_vacuum`
  (`⟪Ω,W(u)Ω⟫ = exp(−½‖u‖²)` — the **quasifree** value).
- **F3 remaining (optional):** the bounded Weyl operator `W(u)` as an actual `Fock H →L Fock H`
  (linear map on `FockPre` + bounded extension to the completion) and the CCR composition law.  Not on
  the critical path to F6 (which needs the vacuum state ω₀, already done).
- **F2-Γ second quantization — DONE** (commit `d00c124`, axiom-free): `QIQTH/Fock/SecondQuant.lean`.
  `secondQuantPre A = Finsupp.lmapDomain A` (Γ(A)e(f)=e(Af)); `fockInner_secondQuant` (Γ(A) isometric);
  `secondQuantPre_vacuum`/`secondQuantPre_comp` (Γ(A)Ω=Ω, functoriality).  Specialized:
  **`boostFock t = Γ(boostUnitary t)`** = the Lorentz boost on the Fock space, with
  **`boostFock_vacuum`** proving `Γ(U₁(t))Ω = Ω` — the key input to boost-covariance.  The chain
  F1(one-particle boost) → F2(Fock) → boost-on-field is now complete with the vacuum fixed.
- **Bounded boost on the Fock HILBERT space — DONE** (commit `556c94d`, axiom-free): `boostFockₗᵢ`
  (boost as a `LinearIsometry` of `FockPre`), `boostFockH = Completion.map boostFockₗᵢ` (boost on the
  completed `Fock(L²ℝ)`), `boostFockH_isometry` (it is an isometry of the Hilbert space), `boostFockH_vacuum`
  (`Γ(U₁(t))Ω = Ω` in the completed space).  **The operator-side foundation is complete**: the Lorentz
  boost is a bounded isometry of the genuine Fock Hilbert space fixing the vacuum.
- **Genuine remaining gap to the literal prize:** the Haag–Kastler-style **local field-effect net** —
  smeared field observables per spacelike region as the typicality records, with the boost permuting
  regions, so `μ∞.map boost = μ∞`.  This (with Bisognano–Wichmann) is the multi-year remainder; the
  Fock/operator/state/boost apparatus it sits on is now machine-checked and axiom-free.
- **GPT-5.5-pro increments (2026-06-08) — ALL THREE DONE** (axiom-free; the review put the literal prize
  at ~20% and named the bounded Weyl operator the keystone):
  - **Increment 1 — bounded Weyl operator** (commit `ebac330`): `QIQTH/Fock/WeylOp.lean` — `weylPre`
    (`W(u)e(g)=weylCoeff u g·e(g+u)`), **`fockInner_weyl`** (the isometry — the keystone), `W(0)=id`,
    `weylH`/`weylH_isometry` (Hilbert-space isometry), `fockInner_vacuum_weyl` (`⟪Ω,W(u)Ω⟫=exp(−½‖u‖²)`).
  - **Increment 2 — first NON-VACUOUS boost-covariance** (commit `be40b78`): `QIQTH/Fock/WeylCovariance.lean`
    — `weyl2pt` (`⟪Ω,W(u)W(v)Ω⟫`), **`weyl2pt_boost_invariant`** (Lorentz-invariant two-point function —
    genuinely tests quasifree correlations, unlike the deterministic net), `weylBitWeight_mem_Ioo`
    (non-degenerate Weyl-bit Born weight `∈(0,1)`).
  - **Increment 3 — microcausality** (commit `821a87b`): `QIQTH/Fock/WeylCCR.lean` — **`weyl_microcausality`**
    (`W(u)∘W(v)=W(v)∘W(u)` when `Im⟪u,v⟫=0`): spacelike Weyl observables commute — Einstein causality.
  - **Genuine remaining gap to the literal `μ∞.map(boost)=μ∞`:** the **localization map** `K:TestFun→
    OneParticleH` (Pauli–Jordan: spacelike ⇒ `Im⟪Kf,Kg⟫=0`; Fourier/mass-shell construction) + bundling
    `W(u)` as a `ContinuousLinearMap` for a genuine POVM.  The algebraic spine is complete.
- **F4–F6:** unchanged below.

## The ladder (six phases F1–F6)

Each phase is a self-contained, axiom-free, green-building Lean checkpoint. The arc is bottom-up so the
**bottom rungs are independently Mathlib-contributable** (Fock space, Weyl algebra, coherent states are
wanted upstream) and value lands incrementally; the **top rung F6 is the prize**.

### Phase F1 — One-particle space + Poincaré (boost) representation  *(concrete, Mathlib L²)*
*New file `QIQTH/Fock/OneParticle.lean`.*
The continuum analogue of `FreeFieldTypicality`'s finite mode set `m` and mode-permutation `e : m ≃ m`.
1. **Mass-shell measure.** The Lorentz-invariant measure dΩ_m = d³p/(2ω_p) on the positive mass shell
   H_m = {p : p²=m², p⁰>0}, mass m ≥ 0. Build as a pushforward / weighted measure on ℝ³ (concrete,
   Mathlib `Measure` + density). Prove **boost-invariance** of dΩ_m under a one-parameter Lorentz boost
   χ_t acting on ℝ³ (the spatial momentum map of the boost). *This is the genuine continuum replacement
   for "mode permutation preserves counting measure."*
2. **One-particle space** H₁ := L²(H_m, dΩ_m; ℂ) (Mathlib `Lp 2`).
3. **Boost unitary** U₁(t) : H₁ → H₁, `(U₁(t)ψ)(p) = ψ(χ_{-t} p)` — unitary because χ_t is
   dΩ_m-preserving (Mathlib measure-preserving ⇒ Lp-isometry). Prove the **one-parameter group law**
   `U₁(s)∘U₁(t) = U₁(s+t)`, `U₁(0)=1`, and strong continuity (the Stone generator = the boost generator,
   feeding `Spectral` Phase 2).
   *Green checkpoint: a genuine continuum Lorentz boost as a strongly-continuous unitary group on H₁.*

### Phase F2 — Symmetric (bosonic) Fock space + second quantization  *(the keystone Mathlib lacks)*
*New file `QIQTH/Fock/FockSpace.lean`.* Two routes; build the **exponential-vector route first** (far
more Lean-tractable — never touches Sym^n explicitly), cross-check against the direct-sum route later.
1. **Exponential/coherent vectors (primary).** Free ℂ-vector space on symbols `e(f)`, f ∈ H₁, with the
   prescribed kernel `⟪e(f), e(g)⟫ = exp ⟪f,g⟫`. **Prove the kernel is positive semidefinite** (the one
   real analytic lemma: exp of a PD kernel is PD, via `∑ ⟪f,g⟫ⁿ/n!` and the Schur/Hadamard power of a PD
   Gram matrix staying PD — check Mathlib `PosSemidef.mul`/Schur product; provide if absent). Quotient by
   the null space, **complete** → bosonic Fock space `Fock H₁`. Vacuum `Ω := e(0)`, `‖Ω‖=1`.
2. **Second quantization Γ.** For a one-particle contraction/unitary `A : H₁ →L H₁`, define
   `Γ(A) : Fock H₁ →L Fock H₁` on exponential vectors by `Γ(A) e(f) = e(A f)`; prove well-defined
   (kernel respects A when A is a contraction), `Γ(A)` unitary when A is, **functoriality**
   `Γ(A)Γ(B)=Γ(AB)`, `Γ(1)=1`, `Γ(A)Ω=Ω`. Lift the **boost** `U(t) := Γ(U₁(t))` — a strongly-continuous
   unitary group on Fock space with the group law inherited from F1. *The continuum `diagBoost`.*
3. *(Cross-check, deferred)* the direct-sum picture `Fock H₁ ≅ ⊕ₙ Symⁿ H₁` and `dΓ` generators; only
   needed if a later phase wants particle-number / occupation observables explicitly.

### Phase F3 — Weyl operators, CCR C\*-algebra, quasifree vacuum  *(the bounded field algebra)*
*New file `QIQTH/Fock/Weyl.lean`.* Bounded (Weyl) route — **no unbounded operator domains**.
1. **Weyl operators** `W(f) : Fock H₁ →L Fock H₁`, unitary, acting on exponential vectors by
   `W(f) e(g) = exp(-‖f‖²/4 - ⟪f,g⟫/√2 · …) e(g + f/√2)` (Parthasarathy normalization; fix conventions
   once). Prove the **CCR / Weyl relation** `W(f)W(g) = exp(-i·Im⟪f,g⟫/2) W(f+g)` and `W(f)* = W(-f)`.
2. **CCR algebra** 𝒲(H₁) := the C\*-subalgebra of `B(Fock H₁)` generated by `{W(f)}` (Mathlib
   `StarSubalgebra` + closure / `elementalStarAlgebra`). Covariance `Γ(U₁(t)) W(f) Γ(U₁(t))* = W(U₁(t)f)`.
3. **Quasifree vacuum state** ω₀(x) = ⟪Ω, x Ω⟫; compute `ω₀(W(f)) = exp(-‖f‖²/4)` — a faithful normal
   state, **boost-invariant** (`ω₀∘Γ(U₁(t)) = ω₀` since Γ(U₁(t))Ω=Ω). *This is the ω that feeds
   `EffectStateNet` in F6 — the continuum replacement for `FreeFieldTypicality`'s per-region ν.*

### Phase F4 — Wedge-local net + geometric (Bisognano–Wichmann) modular flow
*New file `QIQTH/Fock/LocalNet.lean`.* Where Track B (`StandardSubspaceModular`) and the field meet.
1. **Local algebras.** For a region O ⊂ Minkowski space, A(O) := vN algebra generated by
   `{W(f) : supp f̂ ⊂ O}` (real test functions supported in O). Isotony A(O₁) ⊆ A(O₂) for O₁ ⊆ O₂;
   Poincaré covariance `Γ(U(g)) A(O) Γ(U(g))* = A(gO)`. Focus on **wedges** W_R (the right wedge) where
   everything is explicit.
2. **One-particle wedge subspace** is a **standard subspace** (cyclic+separating) → instantiate
   Tanimoto `StandardSubspace` and run `StandardSubspaceModular` (`rvdRC`, `rvdPmQ`) to get the
   one-particle Δ₁, J₁. **Bisognano–Wichmann (one-particle):** Δ₁^{it} = U₁(boost by −2πt), J₁ = the
   TCP/reflection — i.e. the modular flow of the wedge subspace **is the boost** (provable on the free
   field via the explicit U₁ of F1, not merely cited; cross-check the abstract BGL/Leyland–Roberts–Testard
   statement).
3. **Second-quantize to Fock modular data:** Δ = Γ(Δ₁), J = (second-quantized J₁); modular automorphism
   σ_t(x) = Δ^{it} x Δ^{-it} = Γ(U₁(−2πt)) x Γ(…)* — **a genuine continuum geometric σ_t** on A(W_R),
   and ω₀ is **KMS** for it at β=1 (free-field KMS, provable). *This delivers the continuum σ_t the OP3b
   linchpin needs, on the genuine field — retires the relevant interface axioms when fed back into
   `ModularAutomorphism`/`ArakiInterface` (budget ratchet down).*

### Phase F5 — Type III₁  *(cited — the honest interface boundary)*
*Documented in `AXIOM_CONTRACTS.md`, one clearly-labelled input.*
The wedge/double-cone algebras A(O) of the free field are **Type III₁** — **Buchholz–Wichmann
(CMP 1986), Fredenhagen (CMP 1985)**. Cited as an external interface input, **not proved** (proving it
is itself a Connes-classification campaign — that is the *other* plan's Phase 5). Logged as a single
named axiom with an audit note; the budget records it explicitly. Everything in F1–F4 and F6 is
axiom-free and does not depend on this beyond labelling the net's type.

### Phase F6 — The prize: covariant μ∞ on the continuum net

> **F6 first increment — DONE** (commit `340c724`, axiom-free): `QIQTH/Fock/FockTypicality.lean`.
> `fockVacuumNet` = an `EffectStateNet` on `B(Fock H)` driven by the quasifree vacuum state `ω₀`;
> `fock_typicalityMeasure_exists` proves a unique σ-additive probability **μ∞ EXISTS** on the history
> space (via `EffectStateNet` + the Kolmogorov extension) — the whole prize pipeline running on the
> genuine continuum free-field Fock space with the vacuum state.  The continuum analogue of
> `BHTypicalityMeasure.bh_typicalityMeasure_exists`.
> **Remaining for the full prize: boost-COVARIANCE of μ∞** — needs the boost acting on the Fock space,
> i.e. second quantization `Γ(U₁(t))` (the optional F2-Γ step) + `Γ(U₁(t))Ω = Ω` (vacuum invariance) +
> the field effects transforming covariantly.  This is the continuum analogue of
> `FreeFieldTypicality.freeFieldMeasure_boost_invariant`.

*New file `QIQTH/Fock/ContinuumTypicality.lean`.* The promotion of `FreeFieldTypicality` to the continuum.
1. **Effect net from the field.** Records = spectral data of a commuting family of smeared field
   observables in a spacelike region (a single **compatible/decoherent** framework per the Fine/Bell
   soundness gate already enforced in the XL step — the index must be one decoherent record framework,
   not arbitrary incompatible POVMs). Outcomes from the PVM (`Spectral/SpectralTheorem`) of the
   bounded field operators; finite-fiber per region.
2. **Plug ω₀ into `EffectStateNet`.** The quasifree vacuum ω₀ (F3) is the positive normalized
   functional; the field effects give the coarse-grain-consistent joint effects. Apply
   `StateNetMeasure.exists_typicalityMeasure` + `KolmogorovFiniteFiber.exists_isLimit` → **σ-additive
   continuum typicality measure μ∞** with Born marginals at every finite set of regions.
3. **Boost-covariance — THE prize theorem.** Prove `μ∞.map (continuumBoost t) = μ∞`, where the boost
   acts via Γ(U₁(t)) on records, given ω₀ boost-invariance (F3). The **exact continuum analogue** of
   `freeFieldMeasure_boost_invariant`, with the finite mode-permutation `e : m ≃ m` replaced by a
   genuine one-parameter Lorentz boost. Combined with F5's cited Type III₁ label: **a Lorentz-covariant
   typicality measure μ∞ on a Type III₁ local net, Born + no-signaling + covariance machine-checked.**
   *This is OP3b. The literal continuum prize.*

---

## Dependency graph

```
F1 one-particle + boost  ──┐
                           ├──► F2 Fock + Γ ──► F3 Weyl/CCR + ω₀ ──┬─► F4 local net + σ_t (uses StandardSubspaceModular)
StandardSubspaceModular ───┘                                       │
Spectral/SpectralTheorem (PVM) ────────────────────────────────────┴─► F6 μ∞  ◄── StateNetMeasure + KolmogorovFiniteFiber (DONE)
                                                                          ▲
                                                            F5 Type III₁ (cited) ─ labels only
```
F1, F2, F3 are a strict chain. F4 needs F3 + the existing `StandardSubspaceModular`. F6 needs F3 (ω₀) +
the existing measure machinery + `Spectral` PVM; F4's σ_t is needed only for the *modular/KMS* claim,
not for μ∞ itself — so **F6 can be reached without finishing F4**, and F4 retires interface axioms in
parallel.

---

## Near-term green increment (what to start NOW — independently valuable, axiom-free)

**Phase F1, step 1–3: `QIQTH/Fock/OneParticle.lean`.** The mass-shell measure dΩ_m, its boost-invariance,
H₁ = L²(H_m), and the boost unitary group U₁(t). Concrete, rides Mathlib L² + measure-preserving maps,
no Fock completion required, ships green on its own — and it is the genuine continuum upgrade of
`FreeFieldTypicality`'s mode set + permutation, so it is immediately prize-aligned. Lands as one commit
(`lake build` green, `AxiomAudit` `#print axioms` = `[propext, Classical.choice, Quot.sound]`, budget
check). Then F2's exponential-vector Fock space (the keystone), then F3 Weyl + ω₀.

---

## Files

**New:** `QIQTH/Fock/OneParticle.lean`, `QIQTH/Fock/FockSpace.lean`, `QIQTH/Fock/Weyl.lean`,
`QIQTH/Fock/LocalNet.lean`, `QIQTH/Fock/ContinuumTypicality.lean`.
**Extend:** `QIQTH/StandardSubspaceModular.lean` (one-particle BW Δ₁/J₁ for the wedge),
`QIQTH/AxiomAudit.lean` (`#print axioms` per new theorem), `AXIOM_CONTRACTS.md` (the one cited
Type III₁ input), `scripts/axiom_budget_check.sh` (ratchet **down** as F4 retires interface axioms),
docs (`TOMITA_TAKESAKI_ROADMAP.md`, `PROGRAM_STATUS.md`, `WRITEUP.md`, `FreeFieldTypicality` header note
pointing to its continuum promotion).

## Verification discipline (unchanged)

- `lake build` green after every increment (Windows/PowerShell, `lean/mathlib/`).
- `AxiomAudit` shows only `propext, Classical.choice, Quot.sound` for every new theorem — or the single
  named **Type III₁** cited input with an audit note. No `sorry`. Budget only ever **decreases** (F4
  retirements) except the one logged, justified Type III₁ entry.
- Each phase cross-checked against its reference: F1 vs the standard dΩ_m = d³p/2ω_p; F2 exp-vector
  positive-definiteness vs Parthasarathy/Guichardet; F3 Weyl relation + ω₀(W(f))=exp(−‖f‖²/4) vs
  Bratteli–Robinson Vol 2 §5.2; F4 Δ₁=boost vs Bisognano–Wichmann / Brunetti–Guido–Longo; F5 vs
  Buchholz–Wichmann; F6 vs `freeFieldMeasure_boost_invariant` (the finite-mode theorem it generalizes).

## Honest scale note

Symmetric Fock space, the Weyl/CCR algebra, coherent states, and the mass-shell Poincaré rep are each a
substantial Mathlib-grade build; together with the local net and Bisognano–Wichmann this is a
**multi-year campaign**, and Type III₁-ness is **cited, not proved**. But the structure pays off
incrementally — **F1 alone** delivers a genuine continuum Lorentz boost unitary; **F2 alone** is a
Mathlib-contributable bosonic Fock space; **F6** is the literal prize and depends only on F3 + the
already-proven measure apparatus, not on the full F4/F5 modular-classification tower. Nothing here is a
monolith that only pays off at the end.

## Open-access references

- **Parthasarathy, *An Introduction to Quantum Stochastic Calculus*** (in hand,
  `refs/books_papers/parthasarathy1992.pdf`; arabic page P ≈ PDF page P+12) — **the F2/F3 construction
  manual, section-for-section:** §15 *Positive definite kernels and tensor products* (p.91) = F2's one
  hard lemma (exp⟪f,g⟫ positive-definite); §19 *The Fock Spaces* (p.123) = F2 (symmetric Fock + second
  quantization Γ); §20 *The Weyl Representation* (p.134) + §23 *Creation, conservation and annihilation
  operators in Γₐ(ℋ)* (p.172) = F3 (Weyl/CCR + vacuum). Also §10 *Spectral integration and Stone's
  Theorem* (p.53) + §§11–12 *unbounded operators / von Neumann's spectral theorem* (p.60–65) feed the
  Stone-generator of the boost group U₁(t) (F1 / `Spectral/Unbounded.lean`).
- Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics* Vol 2 §5.2 — CCR, quasifree
  states, KMS (statements; reference, cross-check only).
- Brunetti–Guido–Longo, "Modular localization and Wigner particles" (arXiv math-ph/0203021,
  open access) — standard subspaces, one-particle modular = boost (F4).
- Bisognano–Wichmann (JMP 1975/76) — geometric modular flow of wedges (F4, cited statement).
- Buchholz–Wichmann (CMP 1986), Fredenhagen (CMP 1985) — free-field local algebras are Type III₁ (F5,
  cited input).
- Tanimoto, Mathlib `StandardSubspace` (2026) — the in-Mathlib standard-subspace API (F4 substrate).
