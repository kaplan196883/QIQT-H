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
genuine free-field net with a real boost symmetry at finite mode number**. The single remaining frontier
for the *literal continuum (relativistic, Type III₁)* prize is the Fock/CCR/quasifree field
infrastructure — a separate multi-year program that Mathlib does not yet support, but which is
*wall-free* (it bypasses Tomita–Takesaki/Type-III machinery) and downstream of nothing unproven.

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
2. **The continuum (Type III₁, relativistic) prize** (Layer C/Phase B). The only thing between the
   current state and the literal continuum prize is the **Fock / CCR / quasifree-vacuum field
   infrastructure**: real symplectic test space → Weyl/CCR algebra → quasifree vacuum → Fock space →
   local net → explicit second-quantized boost. Mathlib has none of this — a **multi-year,
   build-from-scratch program** (`PHASE_B_INFRASTRUCTURE_PLAN.md` Part-B route). It is **wall-free** (the
   explicit-boost route bypasses Tomita–Takesaki / Type-III / `StarOrderedRing`, never forming `Δ^{1/2}`),
   and **every downstream measure-theoretic piece is already proven** — so it is "build the field net,"
   not "redo the measure theory."
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
- The continuum (relativistic, Type III₁) prize is **fully reduced** to one large, wall-free, downstream-
  of-nothing-unproven infrastructure program.

---

## 11. File index

| Theme | Files |
|---|---|
| No-collapse core (A) | `CoreNoCollapse`, `CapacityModel`, `OrthogonalCapacity`, `SBSBridge`, `CollisionalGamma`, `ValueSelection` |
| Born layer (B) | `EffectGleason`, `GleasonSelector`, `OneSiteGleason`, `RecordGleason`, `BornTypicalityFinite`, `BornConcentration`, `BornJoin`, `BornJoinGleason`, `BornMeasureUniqueness`, `EquivarianceGap`, `NoBornFromNothing`, `BornMinimalityTable`, `QubitIC` |
| Lorentz/μ finite (C) | `LorentzSelection`, `LorentzSelectionStrong`, `LorentzWitness`, `FreeFieldNet`, `DiamondSwapNet`, `SheafSection`, `FreeFieldRecord` |
| Continuum measure (XL) | `NoSignalingGeneral`, `CoarseGrainNaturality`, `CylinderTypicality`, `FiniteMarginals`, `KolmogorovFiniteFiber`, `StateNetMeasure`, `QuantumHistoryMeasure` |
| Normal state / B(H) / free field | `NormalState`, `BHTypicalityMeasure`, `AbsoluteValue`, `FreeFieldTypicality` |
| Continuum TT infra | `Spectral/SpectralTheorem`, `Spectral/PVM`, `StandardSubspaceModular`, `FiniteModularTheory`, `SpectralPVM` |
| Audit | `AxiomAudit`, `scripts/axiom_budget_check.sh` |
| Plans / status | `PRIZE_ROADMAP`, `PRIZE_EXECUTION_PLAN`, `XL_STEP_PLAN`, `PHASE_B_INFRASTRUCTURE_PLAN`, `TOMITA_TAKESAKI_ROADMAP`, `PROGRAM_STATUS`, `FINITE_BORN_REPRESENTATION` |

## 12. References (grounding; open / cited)

- B. Simon, *Trace Ideals and Their Applications* — trace-class/Schatten, `|A|=√(A⋆A)`, the trace,
  Lidskii (`refs/`).
- A. Conway, *A Course in Functional Analysis* (GTM 96) — bounded spectral theorem, functional calculus
  (`refs/`).
- Rieffel–Van Daele, *A bounded operator approach to Tomita–Takesaki theory*, PJM 69 (1977) (`refs/`).
- Buchholz–Wichmann (1986), Fredenhagen (1985) — Type III₁ of local QFT algebras (cited).
- Bisognano–Wichmann (1975/76) — modular flow of wedge algebras = boost (cited).
- Busch / Bunce–Wright–Christensen–Yeadon — effect-Gleason (grounding Layer B).
- A. Fine, *Hidden variables, joint probability, and the Bell inequalities* — the joint-distribution
  obstruction enforced as the soundness gate (§5.2).
