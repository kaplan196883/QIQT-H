# The Finite No-Collapse Born Representation — scope, theorems, honest claim

> *This document details the Born-representation layer.  For the **complete** finite result
> (no-collapse core + Born + typicality + the covariant recorded-history net + spectral/modular
> groundwork), paper-ready, see the master consolidation **`FINITE_RESULT.md`**.*

*Consolidation document for the finite, machine-checked core built 2026-06 (Lean 4 /
Mathlib, `lean/mathlib/QIQTH/`). Every result below is **axiom-free**: it depends only on
Lean's three standard foundational axioms `propext, Classical.choice, Quot.sound` (verified
by `AxiomAudit.lean`; project axiom budget **33**, all 33 being continuum /
operator-algebra interface axioms — NONE in this finite core). Two independent GPT-5.5-pro
adversarial verification passes are folded in; their honest caveats are kept verbatim in the
"Scope" rows so the result is not overstated.*

---

## 1. The one-sentence honest claim

> **A finite, axiom-free, machine-checked no-collapse Born representation theorem.**
> A finite information-capacity bound forces a *unique actual pointer value* per run (no
> collapse map); a *non-contextual* outcome assignment is forced by finite effect-Gleason to
> be the Born weight `tr(ρ Pₐ)` of a density matrix; *product preparation* gives independent
> trials; and the actual-value histories then carry the Born product law and are
> Chebyshev-typical. **Born statistics are not assumed** — only non-contextuality and product
> preparation are. The world-measure is shown to carry no observable freedom.

**NOT claimed** (guardrails): "Born derived from `Q_max` alone"; "Born derived from nothing";
"the measurement problem is solved." Non-contextuality and product preparation are genuine
(if motivated) inputs; the `(Φ,λ)` selector that picks the single run is physics, not a
formalized probabilistic posit. See §5.

---

## 2. The chain, claim → theorem

| # | Honest claim | Lean theorem (`QIQTH/…`) | Scope / what is assumed |
|---|---|---|---|
| A1 | Finite capacity forbids two coactual records | `CoreNoCollapse.coactual_subsingleton` / `joint_coactual_subsingleton` | capacity is a **monotone** joint cost ≤ `Q_max` + pairwise overflow (no additivity assumed) |
| A2 | Pairwise overflow is *derived* from distinguishability (orthogonality), not assumed | `OrthogonalCapacity.pair_exceeds` | distinct macroscopic records occupy **orthogonal** subspaces; joint cost = `finrank(span)` (subadditive) |
| A3 | Capacity + actuality selector λ ⇒ **exactly one** actual record (no collapse) | `CoreNoCollapse.qiqth_single_outcome_joint` | the selector supplies "≥ 1 active"; single-outcome is the theorem |
| A4 | "Collapse" = Bayesian conditioning (Lüders), operationally redundant | `CoreNoCollapse.condProb_eq_born_postState`, `joint_eq_weight_mul_cond` | genuine PVM (`FinPVM`); a Hilbert space |
| **C1** | One actual **record** → one actual **value** (redundant same-value records coexist) | `PointerValue.ValueSelection.existsUnique_actualValue`, `existsUnique_actualHistory` | two *different-valued* records overflow capacity (`pair_exceeds_value`) |
| **C2** | Single-trial vector valuation on a PVM effect **is** the Born weight `‖Eₐψ‖²` | `OneSiteBorn.vectorState_eq_weight`; `bornVec` (prob vector) | unit state ψ; PVM (self-adjoint idempotent, complete) |
| **b2** | Single-trial Born **forced** from non-contextuality (effect-Gleason) | `OneSiteGleason.oneSite_forced` | **non-contextual** assignment = an `EffectMeasure` (normalized, positive, finitely-additive on coexistent effects). *Strong premise; effect-Gleason is the engine.* |
| b2′ | Non-contextual assignments **are** the Born/trace forms (converse to Gleason) | `OneSiteGleason.traceEffectMeasure` | every density matrix ρ (PSD, unit trace) is such an `EffectMeasure` |
| b2″ | Ensemble's single-trial law `p` is **forced Born** (not a free parameter) | `BornJoinGleason.ensemble_p_isBorn`, `finite_noCollapseBorn_fromNoncontextuality` | `p` = an *independently given* non-contextual measure's values on `{Pₐ}` |
| **b1** | Product preparation ⇒ **trial independence** | `BornTypicalityFinite.w_history_factorizes` | independence = the world-measure is a **product** (i.i.d. copies); irreducible — not derivable from no-signaling |
| **C3/C4** | Actual-value histories carry the **Born product law** + are **Chebyshev-typical** | `BornJoin.ActualEnsemble.pushforward_eq_w`, `actualHistory_typical[_world]`, `finite_noCollapseBornRepresentation` | named inputs `oneSite` + `indep` (see §3) |
| **b3** | World-measure carries **no observable freedom** (history-observational equivalence) | `BornJoin.ActualEnsemble.history_law_unique`, `history_law_eq_w` | "observable" = exactly actual-history events; does **not** determine the measure on Ω |
| typ | Finite weak LLN: `P(|freq − p k| ≥ ε) ≤ p k(1−p k)/(Nε²)`; union bound `≤ 1/(Nε²)` | `BornTypicalityFinite.chebyshev_freq`, `chebyshev_freq_union_le` | abstract prob vector; Chebyshev |
| u | The product Born measure is the **unique** additive history measure with the Born marginals | `BornMeasureUniqueness.product_born_measure_unique` (+ `_of_independent_trials`) | independence made explicit (cylinder factorization) |

Supporting facts (all axiom-free): `EffectGleason.finite_effect_gleason` (the engine —
normalized/positive/coexistent-additive functional on effects = `tr(ρ·)`); the Goldstein–
Struyve Schur-classification chain; `CapacityModel.capacity_total` (capacity from
orthonormality, Strasberg branch-counting); `SBSBridge` (redundancy ⇒ storage `R·log n`);
`CollisionalGamma` (per-collision `γ<1` from a toy QND Hamiltonian).

---

## 3. What is DERIVED vs ASSUMED (the honest ledger)

**Derived** (machine-checked theorems):
- unique actual record / value from finite capacity + selector (no collapse map anywhere);
- pairwise capacity overflow from orthogonality (distinguishability);
- **the single-trial Born weights** `tr(ρ Pₐ)` from non-contextuality, via effect-Gleason;
- the **product law** `∏ₜ tr(ρ P_{hₜ})` from independence (product structure of the measure);
- Chebyshev typicality of the empirical frequencies;
- uniqueness of the product Born measure; observational irrelevance of the world-measure.

**Assumed** (named, motivated — not Born by hand):
- **non-contextuality** — the outcome assignment is an `EffectMeasure` (a normalized positive
  finitely-additive state on the effect algebra). *Strong premise; honest name with that
  qualifier.* The Born **weights** are derived from it, not posited.
- **product preparation** — the `n` trials are independent copies (the world-measure is a
  product). Irreducible: independence cannot come from no-signaling (which permits
  correlations); product structure is genuinely required.
- the system **is** in state `ρ` (`hp` in the trace-interface theorem) — the irreducible
  premise of "there is a quantum state at all."

**NOT removed** (GPT-5.5-pro verification, candid):
- `BornJoin.ActualEnsemble` still carries `oneSite`/`indep` as *fields*; the reduction
  theorems supply Born-forced `p` and product-derived independence around it, but the abstract
  ensemble interface still names them. (`ensemble_p_isBorn` is the genuine reduction of `p`;
  `finite_noCollapseBorn_trace` is an **interface/specialization**, *circular* as a standalone
  Born derivation — it builds the `EffectMeasure` from ρ via the Born formula.)
- the no-collapse core's value-uniqueness (C1) is, relative to the probability layer, a
  *wrapper*: the typicality math would hold for any `X : Ω → Fin n → Fin m`. What C1 adds is
  the capacity reading (unique value), not a probabilistic constraint.

---

## 4. Non-vacuity witnesses (the hypotheses are satisfiable, not vacuously true)

- `CoreNoCollapse.witnessJointSelection` — a concrete 2-record capacity context with one outcome.
- `OrthogonalCapacity.witness` — two orthogonal macroscopic records on `ℂ²`; `pair_exceeds` fires.
- `BornJoin.iidWitness` — a concrete i.i.d. Born ensemble realizing **both** `oneSite` and
  `indep` (both discharged, not assumed) over worlds = histories with mass `w p`.
- `OneSiteGleason.traceEffectMeasure` — every density matrix is a valid non-contextual measure.

(Per GPT-5.5-pro: `iidWitness` is logically non-vacuous but *degenerate* — `mass := w p` builds
in the product law, trivial one-record `Unit` selections — so it certifies satisfiability, not
explanatory depth.)

---

## 5. What this is NOT (do not write these)

- ✗ "We prove finite `Q_max` alone eliminates collapse / derives Born / solves measurement."
- ✗ "Born is derived from nothing / from counting."  (Born ≠ the uniform/counting measure; a
  typicality measure is needed, and it is the *forced* product Born measure.)
- ✗ "The world-measure is derived from `(Φ,λ)` dynamics."  (Shown observationally free, not
  derived; one cannot derive a specific probability from a deterministic selector.)
- ✗ "`finite_noCollapseBorn_trace` derives Born."  (It is an interface theorem; circular as a
  derivation. Cite `finite_noCollapseBorn_fromNoncontextuality` / `ensemble_p_isBorn` instead.)

---

## 6. Relation to the program's open problems

This finite core is the **realized, finite portion** of the QIQT-H breakthrough target. It does
**not** settle the two breakthrough-defining open problems (see `PROGRAM_STATUS.md`,
`PRIZE_ROADMAP.md`): (1) the **continuum, Lorentz-covariant** construction of the typicality
measure μ (the 33 remaining interface axioms live here, gated by Type III₁ / Tomita–Takesaki
beyond current Mathlib); (2) deriving the scattering / objectivity premises from a realistic
field-theoretic Hamiltonian. The finite result stands on its own as a foundations-of-physics
formalization paper; the continuum is honestly gated.

---

## 7. Suggested paper framing

**Title (finite paper, if pursued standalone):** *Finite no-collapse quantum measurement in
Lean 4: capacity-limited pointer values and Born-typical histories.*

**Abstract core:** "We machine-check, axiom-free, a finite no-collapse representation theorem:
a finite information-capacity bound forces a unique actual pointer value per run with no
collapse map; finite effect-Gleason forces a non-contextual outcome assignment to be the Born
weight of a density matrix; product preparation yields independent trials; and the actual-value
histories carry the Born product law and are Chebyshev-typical. The world-measure is shown to
carry no observable freedom. Born statistics are not assumed — only non-contextuality and
product preparation. The continuum/Lorentz-covariant construction is identified and left open."
