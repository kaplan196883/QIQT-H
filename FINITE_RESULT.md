# QIQT-H — the finite result, consolidated for the paper

*Master consolidation of the complete **finite, machine-checked, axiom-free** QIQT-H
formalization (Lean 4 / Mathlib, `lean/mathlib/QIQTH/`).  Every module listed here depends only
on Lean's three standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — **zero
project axioms** — verified by `AxiomAudit.lean` and the CI guard `scripts/axiom_budget_check.sh`.
The project's 33 remaining named axioms are ALL continuum / operator-algebra interface theorems
(Araki, Donald, DPI, Tsirelson, …), none in the finite development below.  Two GPT-5.5-pro
adversarial verification passes are folded into the honest-scope statements.  Companion docs:
`FINITE_BORN_REPRESENTATION.md` (the Born-representation detail), `PRIZE_EXECUTION_PLAN.md`
(continuum roadmap), `AXIOM_CONTRACTS.md` (the 33 continuum axioms).*

---

## 0. One-paragraph result

> **A finite, machine-checked, axiom-free architecture for single-outcome quantum measurement
> without a collapse postulate.**  A finite information-capacity bound forces a *unique actual
> pointer value* per run (no collapse map); a *non-contextual* outcome assignment is forced by the
> finite effect-Gleason theorem to be the Born weight `tr(ρ Pₐ)`; *product preparation* gives
> independent trials; and the capacity-selected actual-value histories then carry the Born product
> law and are Chebyshev-typical.  This is realized on a Lorentz-covariant *recorded-history net*
> with marginalizing restriction, derived no-signaling, permutation-equivariance, an
> informationally-complete record family, a genuine diamond-permuting covariant action, and global-
> section (selector) existence/classification; the discrete spectral measure is a finite PVM and
> the modular flow preserves the Born state.  Everything is finite-dimensional and axiom-free; the
> continuum / Type III₁ realization is identified as the single open infrastructure problem.

---

## 1. Honest abstract (paper-ready)

We give a machine-checked (Lean 4 / Mathlib), axiom-free, finite-dimensional account of
single-outcome quantum measurement in the QIQT-H framework.  A finite record-capacity bound,
together with an actuality selector, forces exactly one actual pointer **value** per run with no
collapse map; collapse is recovered as Lüders conditionalization.  The single-trial Born weights
are *derived* from non-contextuality via a fully-formalized finite effect (Busch) Gleason theorem,
and the multi-trial product Born law and Chebyshev typicality follow from product preparation.  We
realize this on a finite recorded-history net carrying a marginalizing restriction whose
no-signaling marginal is a theorem about the product Born measure, a permutation-equivariant
typicality measure, an explicit informationally-complete qubit record POVM, a genuine
diamond-permuting Poincaré-style covariant action, and the existence and top-fibre classification
of global selectors (with the gluing cocycle vanishing in the finite/product case).  We further
formalize the finite spectral theorem as a projection-valued measure and the finite Tomita–Takesaki
modular flow with its state-invariance.  Born statistics are **not assumed** — only non-contextuality
and product preparation are.  The continuum (Type III₁ / bounded spectral theorem / Tomita–Takesaki)
is identified as the open infrastructure problem.

---

## 2. The complete claim → theorem map (all axiom-free)

### A. No-collapse core
| Claim | Lean (`QIQTH/…`) |
|---|---|
| Finite capacity ⇒ ≤1 coactual record (subadditivity-robust: monotone jointCost + pairwise overflow) | `CoreNoCollapse.joint_coactual_subsingleton` |
| Pairwise overflow DERIVED from orthogonality (distinguishability) | `OrthogonalCapacity.pair_exceeds` |
| Capacity + selector ⇒ EXACTLY one actual record (no collapse) | `CoreNoCollapse.qiqth_single_outcome_joint`, `OrthogonalCapacity.orthogonal_single_outcome` |
| Genuine PVM; Born normalization `∑‖Eᵣψ‖²=1` a theorem | `CoreNoCollapse.FinPVM`, `weight_sum_eq_one` |
| "Collapse" = Lüders conditionalization (operationally redundant) | `CoreNoCollapse.condProb_eq_born_postState`, `joint_eq_weight_mul_cond` |
| Capacity bound from orthonormality (Strasberg branch-counting) | `CapacityModel.capacity_total`, `macroscopic_subsingleton` |
| Redundancy ⇒ storage `R·log n` (Spectrum Broadcast Structure) | `SBSBridge.redundancy_le_logStorage`, `sbs_single_outcome` |
| Per-collision distinguishability `γ<1` from a toy QND Hamiltonian | `CollisionalGamma.gamma_lt_one` |

### B. Born from positivity / non-contextuality
| Claim | Lean |
|---|---|
| Finite effect (Busch) Gleason: normalized+positive+coexistent-additive functional = `tr(ρ·)` | `EffectGleason.finite_effect_gleason(_unique)` |
| Goldstein–Struyve Schur classification (Born uniqueness), fully proved | `GoldsteinStruyveStep1.schur_classification_real` |
| Single-trial Born **forced** by non-contextuality (effect-Gleason) | `OneSiteGleason.oneSite_forced` |
| Non-contextual assignments ARE the Born/trace forms (converse) | `OneSiteGleason.traceEffectMeasure` |
| One-site Born: vector valuation on a PVM effect = `‖Eᵣψ‖²` | `OneSiteBorn.vectorState_eq_weight` |

### C. Typicality and the product law
| Claim | Lean |
|---|---|
| Finite weak LLN (Chebyshev) `P(|freq−p|≥ε) ≤ p(1−p)/(Nε²)`; union bound `≤1/(Nε²)` | `BornTypicalityFinite.chebyshev_freq`, `chebyshev_freq_union_le` |
| Product preparation ⇒ trial independence | `BornTypicalityFinite.w_history_factorizes` |
| Born typicality measure is permutation-equivariant (mode relabeling) | `BornTypicalityFinite.w_perm_invariant` |
| Quantum bridge: `N`-copy product-measurement weight = product Born vector | `BornTypicalityQuantum.quantumWeight_eq_w` |
| Trace of product of PSD matrices ≥ 0 (Born nonneg) | `BornTypicalityQuantum.trace_mul_nonneg` |
| Product Born measure is the UNIQUE additive history measure with Born marginals | `BornMeasureUniqueness.product_born_measure_unique` |

### D. The join (record → value → Born) — the finite no-collapse Born representation
| Claim | Lean |
|---|---|
| One actual RECORD → one actual VALUE (redundant same-value records coexist) | `PointerValue.ValueSelection.existsUnique_actualValue`, `existsUnique_actualHistory` |
| Capacity-selected actual histories obey the Born product law + typicality | `BornJoin.finite_noCollapseBornRepresentation` |
| World-measure carries no observable freedom (history-observational equivalence) | `BornJoin.ActualEnsemble.history_law_unique` |
| Representation with `p` FORCED Born from non-contextuality | `BornJoinGleason.finite_noCollapseBorn_fromNoncontextuality`, `ensemble_p_isBorn` |
| Non-vacuity: a concrete i.i.d. Born ensemble realizes the hypotheses | `BornJoin.iidWitness` |

### E. Lorentz-covariant recorded-history net (finite case of the prize)
| Claim | Lean |
|---|---|
| Recorded-history net interface; covariant selector; no-signaling derived | `LorentzSelection.RecordedHistoryNet`, `covariant_selection_exists`, `net_no_signaling` |
| Non-toy net: marginalizing restriction + product Born ω + no-signaling theorem | `FreeFieldNet.bornNet`, `bornNet_no_signaling`, `bornNet_covariant_selection` |
| Diamond-permuting action: a genuine non-trivial net automorphism (moves geometry) | `DiamondSwapNet.swapIso`, `swapAction`, `swap_covariant_selection` |
| Unified diamond net: ω + BOTH no-signaling marginals + the swap action | `DiamondSwapNet.diamondBornNet`, `diamond_unified` |
| Informationally-complete qubit record POVM (record-completeness, finite case) | `QubitIC.qubitIC_separating`, `qubitIC_records_imply_all_effects`, `qubitIC_sum` |
| Global selectors λ exist + classified by the top fibre (gluing unobstructed) | `SheafSection.topSection`, `globalSection_eq_top`, `diamondSelector_classifies` |

### F. Spectral / modular groundwork (finite case of the continuum infrastructure)
| Claim | Lean |
|---|---|
| Spectral theorem as a PVM: eigenprojections, resolution of identity, projection algebra | `SpectralPVM.specProj_sum_eq_one`, `specProj_idem`, `specProj_orthogonal`, `specProj_selfAdjoint` |
| Finite Tomita–Takesaki: modular flow, KMS, and STATE-INVARIANCE of the modular flow | `FiniteModularTheory.modAut`, `kms_condition`, `modAut_stateOf_invariant` |

---

## 3. Derived vs assumed (the honest ledger)

**Derived** (machine-checked, axiom-free): unique actual record/value from capacity + selector (no
collapse map); pairwise overflow from orthogonality; single-trial **Born weights** from
non-contextuality (effect-Gleason); the **product law** from independence; Chebyshev typicality;
uniqueness of the product Born measure; no-signaling (as a product-measure marginal);
permutation-equivariance; global-section existence/classification; the finite spectral PVM; modular
state-invariance.

**Assumed** (named, motivated — not Born by hand): **non-contextuality** (the outcome assignment is
a normalized positive finitely-additive effect functional — strong, but effect-Gleason is the engine
that turns it into Born); **product preparation** (independent copies — irreducible: independence
cannot come from no-signaling); the system **is** in a state `ρ`.

**Honest caveats** (GPT-5.5-pro verification): the joint theorem is a *conditional representation
theorem*, not a derivation of Born from `Q_max` alone; `ActualEnsemble` still names `oneSite`/`indep`
as fields (the reduction theorems supply Born-forced `p` + product-derived independence around it);
the trace-path interface theorem is circular as a standalone derivation (use the non-trace path);
the no-collapse value-uniqueness is a wrapper relative to the probability layer.  None of these is a
soundness bug; all are interpretive and documented in-file.

---

## 4. What is NOT done (the open continuum)

Uniformly the infinite-dimensional operator-algebra infrastructure that Mathlib lacks:
- bounded spectral theorem / Borel functional calculus / PVM for Hilbert-space operators (3.1);
- infinite-dimensional Tomita–Takesaki (3.2);
- a Type III₁ free-field net realizing `RecordedHistoryNet` with unitary Poincaré transport (3.3);
- continuum Bunce–Wright Gleason (3.4);
- non-trivial Roberts–DHR net cohomology for posets without a global chart (Stage 2.3).

These are a multi-month Mathlib contribution (or honest cited interfaces), NOT conceptual gaps in
QIQT-H.  The finite result above stands on its own.

---

## 5. Suggested paper

**Title.** *Finite no-collapse quantum measurement in Lean 4: capacity-limited pointer values,
Born-typical histories, and a covariant recorded-history net.*

**Structure.**
1. Introduction — the measurement problem, the QIQT-H `(Φ,λ)` thesis, what "finite" buys.
2. The no-collapse core — capacity exclusion (subadditivity-robust) + selector ⇒ one outcome;
   Lüders = conditionalization (§2A).
3. Born from positivity — finite effect-Gleason; non-contextuality ⇒ Born (§2B).
4. Typicality and the product law — finite weak LLN, product preparation, uniqueness (§2C).
5. The join — finite no-collapse Born representation; the honest conditional scope (§2D).
6. Covariance — recorded-history net, no-signaling, equivariance, IC records, diamond-permuting
   action, global sections (§2E).
7. Spectral / modular groundwork; the open continuum (§2F, §4).
8. Formalization & reproducibility — Lean 4 / Mathlib, 0 project axioms in the finite core,
   `AxiomAudit.lean`, the 33 continuum interface axioms (§2 ledger, `AXIOM_CONTRACTS.md`).

**Claimable.** "A machine-checked, axiom-free, finite-dimensional no-collapse Born representation
+ covariant recorded-history architecture; Born statistics derived from non-contextuality + product
preparation, not assumed; continuum identified as the open infrastructure problem."

**NOT claimable.** "Born derived from `Q_max` alone / from nothing"; "the measurement problem is
solved"; "the continuum result is proved."

---

## 6. Reproducibility

`cd lean/mathlib && lake build QIQTH` builds the whole development; `bash
scripts/axiom_budget_check.sh` rebuilds `QIQTH.AxiomAudit` and verifies: no `sorryAx`, no
re-introduced deleted axioms, raw `axiom` count = 33 (budget 33).  Every theorem in §2 is verified
to depend only on `propext, Classical.choice, Quot.sound` (the standard three) by the corresponding
`#print axioms` line in `AxiomAudit.lean`.
