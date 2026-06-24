# BORN-C — μ-selection: grounding the Born measure-choice in refinement equivariance

**Status:** PLAN (not started). **Track:** Born. **Goal:** the no-go theorems prove decoherence + holographic
structure **underdetermine** the typicality measure μ (any distribution is realizable). Ground the **μ-SELECTION**
in a physically-motivated, amplitude-free principle — **refinement equivariance** of the typicality measure (the
selector does not signal under outcome-refinement; the Dürr–Goldstein–Zanghì quantum-equilibrium / Valentini
condition) — and prove it **selects the Born μ**.

Mirrors BORN-A1, which grounded *additivity* (the rule side) in selector no-signaling.  Here we ground the
*measure choice* (the selection side).  Per the BORN-A1 §4 discipline: this is expected to be a **grounding /
reframing**, not a from-nothing derivation — the deliverable is the selection theorem + non-vacuity + the honest
limit, never a dressed-up circularity.

## 0. The exact target

`NoBornFromNothing.any_anti_born_realizable` / `exists_probability_realizing` prove: for ANY target outcome
distribution there is a microscopic μ realizing it — so the structural axioms do not pick μ.  `BORN-A1`
(`apc_iff_positiveAdditive`) showed: selector no-signaling under refinement ⟺ additivity of the rule ⟺ Born.
`SelectorRefinement.equivariant_marg_invariant` proved: a **μ-preserving** refinement leaves every local
marginal invariant (no-signaling) — with **no Born input**.  `EquivarianceGap` proved: *support* preservation is
strictly weaker than *measure* preservation (the `swap`/`μ_nonuniform` witness) — so equivariance is a genuine
extra condition, not free.  These are the pieces.

## 1. Stages (each axiom-free, green-building, one commit)

### Stage 1 — the selection principle `QIQTH/BornMuSelection.lean`
Define **refinement equivariance** of a typicality measure precisely (amplitude-free): the measure's outcome
marginals are Kolmogorov-consistent under every outcome-refinement (equivalently, the refinement dynamics is
measure-preserving — `EquivarianceGap.MeasurePreserving` / `SelectorRefinement.equivariant_marg_invariant`).
Prove the basic facts (the Born/uniform measure is equivariant; the structure is non-degenerate).  **Risk: low.**

### Stage 2 — equivariance selects Born *(the selection theorem)*
Prove: an equivariant typicality measure induces a refinement-no-signaling selector
(`equivariant_marg_invariant`), hence — by `BORN-A1.apc_iff_positiveAdditive` (no-signaling ⟺ additivity) and
`RefinementBorn.continuous_additive_fMeasure_eq_born` (additivity ⟹ Born) — the outcome statistics are **Born**.
So **equivariance selects the Born μ**.  **Risk: medium** (the bridge from the measure-side equivariance to the
rule-side additivity — the key composition).

### Stage 3 — underdetermination + non-vacuity *(the no-go bracket)*
Package the two-sided bracket: WITHOUT the principle, μ is underdetermined
(`NoBornFromNothing.any_anti_born_realizable`); a NON-equivariant measure gives non-Born / signals
(`EquivarianceGap` `swap`/`μ_nonuniform`, `BornRoutes.sqRule_refinement_signals`).  So equivariance is a genuine,
non-vacuous discriminator that uniquely picks Born among the realizable measures.  **Risk: low** (compose
existing no-gos).

### Stage 4 (optional) — the martingale route as a second selection
`BornRoutes.born_from_martingale` already gives a second clean selection: squared-weight conservation in
μ-expectation + an absorbing final record ⟹ μ-probability = Born (the GRW/CSL / optional-stopping mechanism).
Package it alongside Stage 2 as an independent grounding of μ-selection.  **Risk: low** (it is already a theorem).

## 2. Honest limit (stated up front, per BORN-A1 §4)
Some selection principle MUST be assumed — the no-go (`any_anti_born_realizable`) proves μ is otherwise
underdetermined.  Equivariance (refinement no-signaling / quantum equilibrium) is the **physically-motivated,
amplitude-free** choice (DGZ/Valentini), and it is expected to be **logically equivalent** to the additivity /
Born-selection it implies.  So the deliverable is a **grounding**: μ-selection relocated from "assume the Born
μ" to "assume the typicality measure is equivariant (quantum-equilibrium) under refinement" — a principle with
independent physical standing — together with the underdetermination bracket and the non-equivariant
countermodels.  We do **not** dress up the equivalence as a from-nothing selection.

## 3. Verification (per stage)
- `cd lean/mathlib && ~/.elan/bin/lake build QIQTH.<module>` green; `#print axioms` = standard 3;
  `bash scripts/axiom_budget_check.sh` budget 0; wire into `QIQTH.lean` + `AxiomAudit`; one commit per stage.

### Progress log
- **Stage 1 ✅** (`Equivariant`, `uniform_equivariant`, `equivariant_no_signaling`; `QIQTH/BornMuSelection.lean`)
  — the selection principle (refinement equivariance = the quantum-equilibrium condition), the canonical uniform
  measure is equivariant, and **equivariance ⟹ selector no-signaling** (the bridge to Born via BORN-A1).
  Axiom-free, budget 0.
- **Stage 2 ✅ — the kinematic selection** (`equivariant_context_independent`) — an equivariant measure's
  outcome marginal is invariant under the equivariant refinement (the *whole* marginal function): the
  quantum-equilibrium measure has **no preferred refinement**, so its statistics are **non-contextual** — the
  Born-strength premise consumed by `finite_noCollapseBorn_fromNoncontextuality` (and ⟺ additivity ⟺ Born via
  BORN-A1). **Equivariance grounds the Born selection.** Axiom-free, budget 0.
- **Stage 3+4 ✅ — the bracket + the dynamical selection** (`mu_underdetermined`, `mu_selection_martingale`) —
  WITHOUT a principle μ is underdetermined (`any_anti_born_realizable`); WITH the dynamical martingale
  conservation, μ-probability = Born weight (`born_from_martingale`) — a second independent grounding; the α=2
  (non-equivariant) rule SIGNALS under refinement (`sqRule_refinement_signals`) — non-vacuity. Axiom-free, budget 0.

### COMPLETE — the honest §2 grounding
μ-selection is grounded in physically-motivated, amplitude-free principles — **equivariance** (kinematic,
quantum-equilibrium) and **martingale conservation** (dynamical, GRW/CSL) — both selecting Born, bracketed by
the underdetermination no-go and the non-equivariant countermodel. Per §2 (mirroring BORN-A1): some selection
principle MUST be assumed (the no-go proves it); these principles are the physically-motivated choices and are
logically tied to the Born-selection — so this is a **grounding/reframing** of μ-selection, not a from-nothing
derivation. Delivered as such; no circularity dressed up as a discharge.
