# QIQT-H: a machine-checked single-world quantum framework — master write-up

*Consolidated summary of the Lean 4 / Mathlib formalization (state as of 2026-06-08). Every result
called "machine-checked" below builds with `lake build` and depends only on Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) unless explicitly attributed to one of the 33
named project interface axioms (§7). Nothing here is a `sorry`; the axiom budget has only ratcheted
down. Honesty is the governing discipline: at every layer we distinguish **derived** from **assumed**,
**finite** from **continuum**, and **machine-checked** from **cited**.*

---

## 1. One-paragraph verdict

QIQT-H formalizes a single-world reading of quantum mechanics — an exactly-unitary global wavefunction
Φ, a primitive **actuality selector** λ (which macroscopic realization is actual), and a **typicality
measure** μ over λ — under a **finite information-capacity** bound. The load-bearing claim, *"finite
capacity removes the need for a collapse postulate,"* is a machine-checked theorem. The Born rule is
established as an honest **conditional representation theorem** (forced by a minimal, each-necessary set
of operational premises). The program's "prize" — a **canonical, Lorentz-covariant typicality measure
μ** yielding Born + no-signaling without per-measurement fiat — is now **built end-to-end as a
σ-additive, unique, covariant, no-signaling measure**, machine-checked for the correlated/entangled
case, shown state-agnostic, run on an infinite-dimensional `B(H)` normal state, and **instantiated on a
genuine free-field net with a real boost symmetry at finite mode number**. Beyond the finite-mode case,
the **continuum 1+1D bosonic free field is now itself machine-checked, axiom-free** (§6½): the symmetric
Fock space, coherent states, the **quasifree vacuum state**, the Weyl/CCR core, second quantization, the
**Lorentz boost as a Hilbert-space isometry fixing the vacuum**, and the **Lorentz-invariance of the
vacuum state** — with μ∞ existing on the Fock space. The single remaining frontier for the *literal
continuum (relativistic, Type III₁)* prize is now narrowed to one construction — the Haag–Kastler local
field-effect net — which lifts the proven operator-level vacuum covariance to measure-level μ∞
covariance; it sits atop a fully machine-checked field foundation and is downstream of nothing unproven.

---

## 2. The thesis

- **Φ** evolves unitarily; there is no collapse dynamics.
- **Finite capacity** `Q_R = A(∂R)/4ℓ_P²` (holographic) bounds the number of simultaneously realizable
  distinguishable records in a finite region.
- **λ** selects which macroscopic realization is actual; "collapse" is conditionalization on λ.
- **μ** is the typicality measure over λ; Born frequencies are typical under μ.

The contribution is to make this division of labour **precise and machine-checked**, and to pin down
exactly which premises each conclusion requires.

---

## 3. Layer A — the no-collapse mechanism (DONE, axiom-free, derived)

The chain establishing *single outcome from finite capacity*, each link **derived** from the previous:

- **`CoreNoCollapse`** — `coactual_subsingleton` (finite capacity forbids two coactual records),
  `exactly_one_actual`, `qiqth_single_outcome_no_collapse` (∃! actual record), and
  `condProb_eq_born_postState` (Lüders conditionalization = Born on the collapsed state). Collapse is
  recovered as conditionalization, not posited.
- **`CapacityModel`** — the capacity bound is a *theorem* `capacity_total` from orthonormality +
  `finrank` (∑ record-dimensions ≤ register dimension); `macroscopic_subsingleton`,
  `capacity_exactly_one`.
- **`OrthogonalCapacity`** — the pairwise-overflow premise `pair_exceeds` is *derived* from
  orthogonality of distinct records (span dimension); `orthogonal_single_outcome`.
- **`SBSBridge`** — the saturation premise `cost > Q_max/2` is *derived* from Spectrum-Broadcast-Structure
  redundancy (`redundancy_le_logStorage`, `R·log n ≤ storage`); `sbs_single_outcome`.
- **`CollisionalGamma`** — the one physical input, per-collision distinguishability `γ<1`, is *derived*
  from a toy QND Hamiltonian `H = g σ_z⊗σ_x` (`branch_overlap`, `gamma_lt_one`,
  `collisional_overlap_tendsto_zero`: `γ^L → 0`).
- **`ValueSelection`** — record-level single outcome lifts to pointer-**value** level:
  `existsUnique_actualValue`, `existsUnique_actualHistory`.

**Verdict.** The mechanism is in hand: finite capacity (itself derived from dimension/orthonormality/SBS
redundancy) ⇒ exactly one actual value history; collapse is conditionalization. Machine-checked,
non-vacuous (concrete witnesses), no project axioms.

---

## 4. Layer B — the Born rule (a CONDITIONAL representation theorem)

Born is **forced** by a minimal, independent, each-necessary set of operational premises — *not* derived
from nothing.

**Genuinely proved (axiom-free):**
- `EffectGleason.finite_effect_gleason` — finite Busch/effect-Gleason: a normalized, positive,
  coexistence-additive effect functional equals `Tr(ρ·)`.
- `GleasonSelector.born_is_forced` — Born forced from positivity + ray-certainty, with
  `naive_gleason_premises_insufficient` (a `Fin 2` counterexample proving positivity is irreducible).
- `OneSiteGleason.oneSite_forced` — non-contextuality ⇒ single-trial Born (via effect-Gleason), with
  `traceEffectMeasure` (every density matrix *is* a non-contextual effect measure).
- `RecordGleason.born_kron` (tensor multiplicativity), `decoherent_partition_additive`.
- `BornTypicalityFinite` — Chebyshev typicality (finite weak law): Born frequencies are typical.
- `BornJoin.finite_noCollapseBornRepresentation`,
  `BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality` — the join: capacity-selected actual
  histories have the Born product law and are typical.

**Proved NECESSARY (the honesty layer):**
- `EquivarianceGap` — support-preservation ≠ measure-preservation.
- `NoBornFromNothing` — any distribution is realizable by some μ; structure alone does not pick Born.
- `BornMinimalityTable` — three independent postulates, each with a kill-countermodel.

**Verdict.** The honest claim is: *Born is the unique admissible measure given positivity +
non-contextuality + tensor-independence + measure-equivariance, each provably necessary.* Making Born
**unconditional** (deriving those premises from deeper principles) is the shared open problem of every
single-world program — possibly a restatement of the measurement problem — and is **not** claimed.

---

## 5. Layer C — the covariant typicality measure μ (the "prize" measure)

### 5.1 Finite conditional interface (axiom-free, rigid)
- `LorentzSelection` — `RecordPresheaf`, `GlobalSection` (=λ), `PoincareAction`, `RecordedHistoryNet`;
  `evaluation_covariance`, `covariant_selection_exists`, `net_no_signaling`.
- `LorentzSelectionStrong` — a genuine `GroupAction` on global sections, `group_evaluation_covariance`,
  measure-covariance **derived from unitarity** (`ubornω_covariant`), `measure_pushforward_total`. An
  honest-scope caveat distinguishes Born-*kernel* covariance from the Layer-B equivariance premise.
- Non-trivial models: `LorentzWitness`, `FreeFieldNet` (no-signaling derived from the product Born
  measure), `DiamondSwapNet` (a genuine geometry-moving swap over a real orbit), `SheafSection`.

### 5.2 The continuum σ-additive measure (the "XL step", machine-checked)
The premeasure is upgraded to a genuine σ-additive measure on the projective limit of histories (=
global selectors λ). **Soundness gate (Fine/Bell):** the index ranges over a *single compatible/
decoherent record framework*, not arbitrary counterfactual settings — a joint law over incompatible
measurements is false by Fine's theorem, and this constraint is enforced.

- `NoSignalingGeneral` — `bipartite_no_signaling`, `local_marginal_indep_remote`: no-signaling for an
  **arbitrary (entangled)** state, not just product states.
- `CoarseGrainNaturality` — `born_coarse_grain` (Kolmogorov consistency, coarse Born = pushforward of
  fine), `bornW_unitary_invariant` (Born-kernel covariance), `sum_pushforward_eq`.
- `CylinderTypicality` — `BornProjSystem`: `consistent`, `μ_total`, `μ_nonneg`, `cylinder_refine`
  (stage-independence), `μ_covariant`.
- `FiniteMarginals` (`QIQTH.HistoryMeasure`) — the projective-family shape + `IsLimit`, `limit_unique`
  (uniqueness), `productMarginals` (product case via Mathlib `infinitePi`), and the limit properties
  `isLimit_marginal` (Born marginals), `isLimit_marginal_mono` (no-signaling at the limit),
  `isLimit_map_eq` (covariance via uniqueness).
- `KolmogorovFiniteFiber` — **`exists_isLimit`**: the general (correlated/entangled, **no product
  assumption**) finite-fiber Kolmogorov extension. Crux `projectiveFamilyContent_tendsto_zero` (content
  → 0 on antitone empty-intersection cylinders) proved from compactness of the finite-fiber product +
  the finite-intersection property; assembled via Mathlib `AddContent.measure`.
- `StateNetMeasure` — `EffectStateNet`: the construction is **state-agnostic** (`toFiniteMarginals`
  derives Kolmogorov consistency from linearity of any positive normalized state ω);
  `exists_typicalityMeasure`; `diracNet` (non-vacuity witness — the pipeline fires end-to-end).
- `QuantumHistoryMeasure` — `bornPMF`, `quantumHistoryMeasure`: the i.i.d. quantum continuum Born
  measure.

**Verdict.** μ∞ — σ-additive, **unique**, Born-marginal at every finite context, **no-signaling**,
**covariant** — exists and is machine-checked, **including the correlated/entangled case**, and is
state-agnostic.

---

## 6. Phase B — the normal state and the free-field instance (machine-checked)

The measure consumes a *normal state*; this is where μ meets genuine quantum/field structure.

- `NormalState` — a genuine **normal state on infinite-dimensional `B(H)`**: the diagonal density
  operator `ω(x) = Tr(ρ x) = ∑ pₙ⟨bₙ, x bₙ⟩` (`diagStateHom`), positive (`diagState_nonneg`), normalized
  (`diagState_one`), bypassing the (unbuilt) general Schatten theory.
- `BHTypicalityMeasure` — **the loop closed end-to-end on `B(H)`** (`bh_typicalityMeasure_exists`): a
  real normal state on `B(H)` → `EffectStateNet` → Kolmogorov extension → a unique σ-additive μ∞. The
  first fully infinite-dimensional instance of the whole pipeline.
- `AbsoluteValue` — the general-trace-class foundation: the operator absolute value `|T| = √(T⋆T)`
  (Simon, *Trace Ideals*, §1.1) via `cfc` on the nonnegative spectrum of `T⋆T`
  (`spectrum_star_mul_self_nonneg` — which sidesteps the missing `StarOrderedRing (B(H))` instance);
  `absOp_mul_self` (`|T|·|T| = T⋆T`), `norm_absOp_apply` (`‖|T|x‖ = ‖Tx‖`).
- `FreeFieldTypicality` — the **free-field, finite-mode covariant typicality measure**: outcomes are
  occupation sectors `m → Bool`, `freeFieldMeasure` is the σ-additive history measure, and
  **`freeFieldMeasure_boost_invariant`** proves μ∞ is **invariant under the geometry-moving
  mode-permutation boost** (the finite-mode Lorentz action) — genuine covariance instantiated by field
  structure.

**Verdict.** The measure/state/covariance apparatus runs on a genuine **free-field net with a real boost
symmetry at finite mode number (Type I)**. The prize is *proven for the finite-mode free field*.

---

## 6½. The continuum free field — the Fock/CCR foundation (machine-checked, axiom-free)

Mathlib has **no** Fock-space / CCR / second-quantization theory. This layer builds the genuine
**continuum 1+1D relativistic free field** from scratch — the operator/state/boost apparatus the
*literal* (Type III₁) prize sits on — entirely axiom-free (`QIQTH/Fock/*`, plan
`FOCK_CCR_FOUNDATION_PLAN.md`, grounded in Parthasarathy §§15/19/20):

- **F1 — one-particle space + boost** (`Fock/OneParticle`): a measure-preserving flow → a one-parameter
  **unitary group** on `L²`; the genuine 1+1D massive **Lorentz boost** `boostUnitary t` = translation
  on `L²(ℝ)` in rapidity coordinates (no Jacobian, since `dΩ_m = ½dθ`).
- **F2 — the symmetric (bosonic) Fock space** (`Fock/ExpKernel`, `Fock/FockSpace`): the **keystone**
  `expKernel_posSemidef` — `exp⟪f,g⟫` is a **positive-definite kernel** (Gram-PSD + the **Schur product
  theorem** iterated over Hadamard powers + the exp series) — the one hard analytic lemma. On it:
  `Fock H = Completion(FockPre H)` is a genuine Hilbert space, with **exponential (coherent) vectors**
  `e(f)`, the **vacuum** `Ω = e(0)`, and the defining identity **`⟪e(f),e(g)⟫ = exp⟪f,g⟫`**
  (`Fock.inner_expVec`), `⟪Ω,Ω⟫ = 1`.
- **F2-Γ — second quantization** (`Fock/SecondQuant`): `Γ(A) e(f) = e(Af)` (= `Finsupp.mapDomain A`),
  **isometric** (`fockInner_secondQuant`), **functorial** (`secondQuantPre_comp`), vacuum-fixing. The
  Lorentz boost lifts: `boostFockH t = Γ(U₁(t))` is a genuine **isometry of the Fock Hilbert space**
  (`boostFockH_isometry`) with **`boostFockH_vacuum`: `Γ(U₁(t)) Ω = Ω`**.
- **F3 — quasifree vacuum state + Weyl/CCR core** (`Fock/VacuumState`, `Fock/Weyl`): the **vacuum state**
  `ω₀(T) = Re⟪Ω,TΩ⟫` (`vacuumStateHom`, positive, `ω₀(1)=1`) — the `ω` `EffectStateNet` consumes; the
  **Weyl unitarity identity** `weyl_isometry` (the CCR-unitarity core) and the **quasifree value**
  `⟪Ω,W(u)Ω⟫ = exp(−½‖u‖²)`.
- **Vacuum covariance** — **`weylCoeff_vacuum_boost_invariant`: `⟪Ω,W(U₁(t)u)Ω⟫ = ⟪Ω,W(u)Ω⟫`** — the
  **quasifree vacuum state is Lorentz-boost invariant** (the boost preserves `‖u‖`). With
  `boostFockH_vacuum` this is the **operator-level boost-covariance of the vacuum state**.
- **F6 (first increment)** (`Fock/FockTypicality`): `fock_typicalityMeasure_exists` — the whole prize
  pipeline (`EffectStateNet` + Kolmogorov extension) runs **end-to-end on the genuine continuum Fock
  space driven by `ω₀`**: a unique σ-additive μ∞ exists.  *(Honest caveat, per the GPT-5.5-pro review:
  this net uses deterministic record effects, so it is a plumbing/sanity check, not yet a non-trivial
  field-history measure — see the non-vacuous results below.)*
- **The bounded Weyl operators** (`Fock/WeylOp`): the actual unitaries `W(u) : Fock H → Fock H` with
  `W(u) e(g) = weylCoeff u g · e(g+u)`, the **isometry** `fockInner_weyl` (the `weyl_isometry` identity
  summed over the coherent-vector expansion — the CCR-unitarity content), `W(0)=id`, the Hilbert-space
  extension `weylH_isometry`, and `⟪Ω,W(u)Ω⟫ = exp(−½‖u‖²)` as a genuine operator matrix element.
- **First NON-VACUOUS boost-covariance** (`Fock/WeylCovariance`): the vacuum two-point Weyl function
  `weyl2pt u v = ⟪Ω,W(u)W(v)Ω⟫` (`= weylCoeff v 0 · weylCoeff u v`) is **Lorentz-boost invariant**
  (`weyl2pt_boost_invariant`) — a genuinely non-trivial, quasifree-correlation-dependent covariance (it
  is *not* the deterministic-net triviality); plus the non-degenerate Weyl-bit Born weight
  `(1+exp(−½‖u‖²))/2 ∈ (0,1)` (`weylBitWeight_mem_Ioo`).
- **Microcausality** (`Fock/WeylCCR`): **`weyl_microcausality`** — `W(u) ∘ W(v) = W(v) ∘ W(u)` whenever
  `Im⟪u,v⟫ = 0` (symplectic orthogonality, as spacelike-separated smearings give): **spacelike Weyl
  observables commute** — Einstein causality / no-signaling, the locality mechanism of the local net.

**Verdict.** The entire *algebraic spine* of the relativistic free field is now machine-checked and
axiom-free: Fock space, coherent states, the **quasifree vacuum state**, the **bounded Weyl operators**
with CCR-unitarity, second quantization, the Lorentz boost as a Hilbert-space isometry fixing the vacuum,
**vacuum-state Lorentz-invariance**, a **non-vacuous boost-covariant two-point function**, and
**microcausality**.  A GPT-5.5-pro review (2026-06-08) put the *literal* continuum prize at ~20% and named
the bounded Weyl operator the keystone — that keystone and all three of its recommended increments are
done.  The two genuine remainders to *measure-level* boost-covariance (`μ∞.map boost = μ∞`): the spacetime
**localization map** `K : TestFun → OneParticleH` (Pauli–Jordan: spacelike ⇒ `Im⟪Kf,Kg⟫=0`; a separate
Fourier/mass-shell construction) and bundling `W(u)` as a `ContinuousLinearMap` for a genuine POVM — the
localization *geometry* + the measure/POVM bundling, atop a now-complete algebraic foundation.

---

## 7. The continuum operator-algebra infrastructure (built to / past the Mathlib frontier)

Supporting machinery, machine-checked, that the continuum realization would feed on:

- `Spectral/SpectralTheorem` — the **bounded spectral theorem** `PVM_of_selfAdjoint`, `T = ∫λ dE`
  (`re_inner_T_eq_integral`); the **bounded Borel functional calculus** `borelFC`; the **continuum
  modular flow** `modFlow` (`Δ^{it}`, a strongly-continuous unitary group), the modular automorphism
  `*`-group `modAut`, state-invariance, and the entire **complex-time flow** `modFlowC`/`modAutC` with
  `modAutC_neg_I` (`σ_{−i}(x) = Δ x Δ⁻¹`).
- `StandardSubspaceModular` (Rieffel–Van Daele) — `0 ≤ R ≤ 2`, `R` **ℂ-linear** and positive (`rvdRC`),
  `D = P−Q` **conjugate-linear** (`rvdPmQ_smul_I` ⇒ `J` antiunitary). Complete *up to* the analytic
  square root.
- `FiniteModularTheory`, `SpectralPVM`, `Spectral/PVM` — finite Tomita–Takesaki, the matrix spectral
  PVM, and the abstract PVM/bounded-FC scaffolding.

---

## 8. The axiom budget — 33 honest interface inputs

All 33 project axioms are **standard, clearly-labelled continuum/operator-algebra facts** beyond current
Mathlib, audited (2026-06-08) to be non-vacuous and not doing illegitimate load-bearing work:
- `ArakiInterface` (11), `Donald` (8), `DPI` (4), `EntropyBridge` (6), `RelEntPositivity` (2),
  `MarginalLocality` (1) — Araki relative entropy, Klein's inequality, DPI, Donald's identity, the
  modular bridge.
- Discharged to theorems (no longer axioms): `tsirelson_bound` (proved in `Tsirelson`),
  Goldstein–Struyve Steps 1 & 3, `FQEquivarianceUniqueness`.

`AxiomAudit.lean` carries a `#print axioms` entry for every result; `scripts/axiom_budget_check.sh`
enforces the budget and scans for vacuous `:= True` bodies and `sorry`.

---

## 9. The honest open frontiers

1. **Unconditional Born** (Layer B). Deriving non-contextuality / equivariance / independence from
   deeper principles — the shared open problem of all single-world programs. *Likely a restatement of
   the measurement problem; not claimed.*
2. **The continuum (Type III₁, relativistic) prize** (Layer C/Phase B). The **Fock / CCR /
   quasifree-vacuum field infrastructure is now built** (§6½, axiom-free): one-particle space + Lorentz
   boost → symmetric Fock space → coherent states + vacuum → quasifree vacuum state → Weyl/CCR core →
   second quantization → the boost as a Hilbert-space isometry fixing the vacuum → the **Lorentz-invariance
   of the vacuum state** → μ∞ exists on the Fock space. The **one genuine remainder** is the
   **Haag–Kastler local field-effect net** — bounded field operators per spacelike region as the
   typicality records, with the boost permuting regions — which lifts the (done) *operator-level* vacuum
   covariance to *measure-level* `μ∞.map boost = μ∞`. That net (with Bisognano–Wichmann) is a multi-year
   construction; it now sits on a fully machine-checked, axiom-free Fock/operator/state/boost foundation,
   so it is "build the local net," not "build the field."
   - *Cited, not needed for μ:* Type III₁-ness of local algebras (Buchholz–Wichmann 1986; Fredenhagen
     1985); Bisognano–Wichmann (modular flow = boost, 1975/76). These characterize the algebra *type*;
     μ only needs a normal state.

---

## 10. What is genuinely established (bottom line)

- A **machine-checked single-world mechanism**: finite capacity ⇒ unique actual value history;
  collapse = conditionalization. (Layer A.)
- A **machine-checked conditional Born theorem** with each premise proved necessary. (Layer B.)
- A **complete, machine-checked covariant typicality measure** μ∞ — σ-additive, unique, Born-marginal,
  no-signaling, covariant, correlated case included — that is **state-agnostic**, runs **end-to-end on
  infinite-dim `B(H)`** with a genuine normal state, and is **instantiated on a free-field net with a
  real boost symmetry at finite mode number**. (Layers C + Phase B.)
- All of the above **axiom-free**; the 33 remaining axioms are honest, audited continuum/entropy
  interface inputs.
- A **machine-checked, axiom-free construction of the continuum 1+1D bosonic free field** (§6½): the
  symmetric Fock space, coherent states, the **quasifree vacuum state**, the Weyl/CCR unitarity core,
  second quantization, the **Lorentz boost as a Hilbert-space isometry fixing the vacuum**, and the
  **Lorentz-invariance of the vacuum state** — with μ∞ existing on the Fock space.
- The continuum (relativistic, Type III₁) prize is now reduced to **one remaining construction** — the
  Haag–Kastler local field-effect net — which lifts the proven operator-level vacuum covariance to
  measure-level μ∞ covariance, atop a fully machine-checked field foundation.

---

## 11. File index

| Theme | Files |
|---|---|
| No-collapse core (A) | `CoreNoCollapse`, `CapacityModel`, `OrthogonalCapacity`, `SBSBridge`, `CollisionalGamma`, `ValueSelection` |
| Born layer (B) | `EffectGleason`, `GleasonSelector`, `OneSiteGleason`, `RecordGleason`, `BornTypicalityFinite`, `BornConcentration`, `BornJoin`, `BornJoinGleason`, `BornMeasureUniqueness`, `EquivarianceGap`, `NoBornFromNothing`, `BornMinimalityTable`, `QubitIC` |
| Lorentz/μ finite (C) | `LorentzSelection`, `LorentzSelectionStrong`, `LorentzWitness`, `FreeFieldNet`, `DiamondSwapNet`, `SheafSection`, `FreeFieldRecord` |
| Continuum measure (XL) | `NoSignalingGeneral`, `CoarseGrainNaturality`, `CylinderTypicality`, `FiniteMarginals`, `KolmogorovFiniteFiber`, `StateNetMeasure`, `QuantumHistoryMeasure` |
| Normal state / B(H) / free field | `NormalState`, `BHTypicalityMeasure`, `AbsoluteValue`, `FreeFieldTypicality` |
| Continuum Fock/CCR field (§6½) | `Fock/OneParticle`, `Fock/ExpKernel`, `Fock/FockSpace`, `Fock/SecondQuant`, `Fock/VacuumState`, `Fock/Weyl`, `Fock/FockTypicality`, `Fock/WeylOp`, `Fock/WeylCovariance`, `Fock/WeylCCR` |
| Continuum TT infra | `Spectral/SpectralTheorem`, `Spectral/PVM`, `StandardSubspaceModular`, `FiniteModularTheory`, `SpectralPVM` |
| Audit | `AxiomAudit`, `scripts/axiom_budget_check.sh` |
| Plans / status | `PRIZE_ROADMAP`, `PRIZE_EXECUTION_PLAN`, `XL_STEP_PLAN`, `PHASE_B_INFRASTRUCTURE_PLAN`, `TOMITA_TAKESAKI_ROADMAP`, `PROGRAM_STATUS`, `FINITE_BORN_REPRESENTATION` |

## 12. References (grounding; open / cited)

- B. Simon, *Trace Ideals and Their Applications* — trace-class/Schatten, `|A|=√(A⋆A)`, the trace,
  Lidskii (`refs/`).
- A. Conway, *A Course in Functional Analysis* (GTM 96) — bounded spectral theorem, functional calculus
  (`refs/`).
- Rieffel–Van Daele, *A bounded operator approach to Tomita–Takesaki theory*, PJM 69 (1977) (`refs/`).
- K. R. Parthasarathy, *An Introduction to Quantum Stochastic Calculus* — exponential vectors, Fock
  space, Weyl operators, the positive-definite kernel `exp⟪f,g⟫` (§§15/19/20; the §6½ construction;
  `refs/`).
- Buchholz–Wichmann (1986), Fredenhagen (1985) — Type III₁ of local QFT algebras (cited).
- Bisognano–Wichmann (1975/76) — modular flow of wedge algebras = boost (cited).
- Busch / Bunce–Wright–Christensen–Yeadon — effect-Gleason (grounding Layer B).
- A. Fine, *Hidden variables, joint probability, and the Bell inequalities* — the joint-distribution
  obstruction enforced as the soundness gate (§5.2).
