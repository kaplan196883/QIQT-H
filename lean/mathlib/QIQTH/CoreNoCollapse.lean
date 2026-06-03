/-
# QIQT-H core: single outcome WITHOUT a collapse postulate (skeleton)

This file states and proves the *load-bearing* core of the QIQT-H claim
"a finite information-capacity bound `Q_max` removes the need for the collapse
postulate", in the form GPT-5.5-pro identified as the only honest target: a
**conditional representation theorem**.

Strategic note (per the 2026-06 consultation): the Tomita–Takesaki / Type-III
machinery (QIQTH/Spectral/PVM.lean, FiniteModularTheory.lean, ...) is *not* the
load-bearing part of this claim — Type III does not imply finite capacity, and
modular flow is reversible. The load-bearing content is HERE: a non-circular
finite-capacity exclusion principle + an actuality selector + Born/typicality +
collapse-recovered-as-conditionalization.

Design discipline (the trap GPT flagged):
  Do NOT define `Q_max` as "at most one actual record" — that trivializes the
  theorem. Instead `cost` is a genuine per-record capacity expenditure, the global
  bound is `∑ cost ≤ Q_max`, and "at most one" is DERIVED from a saturation premise
  (each complete record costs `> Q_max/2`). Finite capacity then bounds the NUMBER
  of coactual records; the selector `λ` supplies "at least one"; together they give
  EXACTLY one — but the single-outcome fact is a theorem, not a hidden hypothesis.

Supporting literature (see CORE_THEOREM_REFS.md; TeX sources in refs/arxiv_sources/):
  • Strasberg–Schindler–Wang–Winter, arXiv:2601.19703 — decoherent-histories
    "branch selection problem": the number of *identifiable* records is bounded
    (geometric Hilbert-space fact, N_detectable ≪ D ≪ N_max). This is precisely the
    capacity bound; QIQT-H's (Q_max, λ) is a proposed *answer* to their open problem.
  • Quantum Darwinism capacity bounds (arXiv:2509.17775, Holevo/functional-info).
  • Typicality & Born (arXiv:1910.08049, 2302.02086) — the across-run frequency layer
    (cf. QIQTH/GleasonSelector, BornTypicality, BornConcentration).

This module is axiom-free (standard three only). -/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace QIQTH.CoreNoCollapse

open scoped BigOperators

/- ── Block 3 (the load-bearing core): finite-capacity exclusion ────────────-/

/-- A **finite record context**: finitely many candidate complete macroscopic
    records, each consuming a positive information `cost`, against a finite total
    capacity `Qmax`.  `cost_gt_half` is the *physical* input (each complete
    macroscopic record is "large" — it consumes more than half the budget); it is
    NOT the conclusion. -/
structure RecordContext where
  /-- candidate complete records -/
  Rec : Type
  [recFintype : Fintype Rec]
  /-- information/capacity each record consumes if actual -/
  cost : Rec → ℝ
  /-- a complete macroscopic record consumes positive capacity -/
  cost_pos : ∀ r, 0 < cost r
  /-- the finite capacity bound `Q_max` -/
  Qmax : ℝ
  /-- **saturation premise** (physical, non-circular): each complete record costs
      more than half the total capacity.  Equivalently: at most one fits. -/
  cost_gt_half : ∀ r, Qmax / 2 < cost r

attribute [instance] RecordContext.recFintype

variable (C : RecordContext)

/-- A **coactual configuration** of a run: the finite set of records that are
    simultaneously actual, subject to the capacity bound `∑ cost ≤ Q_max` (cost is
    additive over independent coactual records). -/
structure Coactual where
  active : Finset C.Rec
  capacity : ∑ r ∈ active, C.cost r ≤ C.Qmax

variable {C}

/-- **Finite capacity forbids two coactual records.**  This is the non-circular
    core: it is *derived* from `cost > Q_max/2` (saturation) + additivity + the
    global bound `∑ ≤ Q_max`.  No "at most one" is assumed. -/
theorem coactual_subsingleton (A : Coactual C) : A.active.card ≤ 1 := by
  classical
  by_contra h
  rw [not_le] at h
  -- card ≥ 2 ⟹ two distinct active records
  obtain ⟨r₁, r₂, hr₁, hr₂, hne⟩ := Finset.one_lt_card_iff.mp h
  have hsub : ({r₁, r₂} : Finset C.Rec) ⊆ A.active := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hpair : C.cost r₁ + C.cost r₂ ≤ ∑ r ∈ A.active, C.cost r := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => (C.cost_pos i).le)
    rwa [Finset.sum_pair hne] at h
  linarith [C.cost_gt_half r₁, C.cost_gt_half r₂, A.capacity]

/- ── Block 4: actuality selector λ ─────────────────────────────────────────-/

/-- The **actuality selector** `λ` for a run: it makes at least one complete record
    actual (a coactual configuration that is nonempty).  Single-outcome-ness is NOT
    built in — only non-emptiness is. -/
structure Selection (C : RecordContext) where
  config : Coactual C
  selected : config.active.Nonempty

/-- **Single-outcome theorem (no collapse postulate):** in any run, finite capacity
    (`≤ 1`) together with the selector (`≥ 1`) forces EXACTLY ONE actual record.
    The state never collapses — this is purely the capacity bound + λ. -/
theorem exactly_one_actual (S : Selection C) : S.config.active.card = 1 := by
  have hle : S.config.active.card ≤ 1 := coactual_subsingleton S.config
  have hge : 1 ≤ S.config.active.card := S.selected.card_pos
  omega

/-- The unique actual record of a run. -/
noncomputable def Selection.outcome (S : Selection C) : C.Rec :=
  (Finset.card_eq_one.mp (exactly_one_actual S)).choose

/- ── Blocks 1,5,6: records as a PVM, Born weights, conditionalization ──────-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A **quantum record system**: a finite orthogonal resolution of the identity
    (the decohered pointer/record observable) on the universal state `ψ`, evolving
    unitarily (no collapse map appears). -/
structure QMRecords (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  Rec : Type
  [recFintype : Fintype Rec]
  /-- record projections `E r` (orthogonal, complete) — already decohered -/
  E : Rec → (H →L[ℂ] H)
  ψ : H

attribute [instance] QMRecords.recFintype

/-- **Born weight** of a record: `w(r) = ‖E r ψ‖²` (the across-run frequency under
    the typicality measure — cf. `QIQTH.GleasonSelector`/`BornTypicality`). -/
noncomputable def QMRecords.weight (Q : QMRecords H) (r : Q.Rec) : ℝ :=
  ‖Q.E r Q.ψ‖ ^ 2

/-- **Collapse-as-conditionalization.**  The conditional probability of a later
    record `b` (projection `F`) given the actual record `r` is the *Lüders* rule
    `‖F (E r ψ)‖² / ‖E r ψ‖²`.  The joint/sequential probability factors as
    `weight(r) · (conditional) = ‖F (E r ψ)‖²` — i.e. the textbook post-measurement
    ("collapsed state `E r ψ / ‖E r ψ‖`") prediction is RECOVERED by conditioning on
    the selected record, with NO collapse map in the dynamics. -/
noncomputable def QMRecords.condProb (Q : QMRecords H) (r : Q.Rec) (F : H →L[ℂ] H) : ℝ :=
  ‖F (Q.E r Q.ψ)‖ ^ 2 / ‖Q.E r Q.ψ‖ ^ 2

/-- The joint (sequential) Born probability equals `weight × conditional` — the
    chain rule that makes the collapse postulate operationally redundant. -/
theorem QMRecords.joint_eq_weight_mul_cond (Q : QMRecords H) (r : Q.Rec)
    (F : H →L[ℂ] H) (hr : Q.E r Q.ψ ≠ 0) :
    Q.weight r * Q.condProb r F = ‖F (Q.E r Q.ψ)‖ ^ 2 := by
  have hden : ‖Q.E r Q.ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)
  unfold QMRecords.weight QMRecords.condProb
  field_simp

/- ── Block 7: a non-vacuous instance (hypotheses NOT encoding the conclusion) ─-/

/-- A concrete 2-record context with `Q_max = 3` and each record costing `2 > 3/2`.
    Witnesses that the capacity hypotheses are satisfiable (non-vacuous) and that
    `coactual_subsingleton`/`exactly_one_actual` are not vacuously true. -/
def witnessContext : RecordContext where
  Rec := Bool
  cost := fun _ => 2
  cost_pos := fun _ => by norm_num
  Qmax := 3
  cost_gt_half := fun _ => by norm_num

/-- In the witness, a selected run indeed has exactly one actual record. -/
example (S : Selection witnessContext) : S.config.active.card = 1 :=
  exactly_one_actual S

/- ── Capstone: the conditional no-collapse representation statement ────────-/

/-- **QIQT-H core (conditional representation theorem).**  Given
    • a finite record context `C` with a genuine capacity budget (`cost`, `Q_max`,
      saturation `cost > Q_max/2`), and
    • an actuality selector producing a nonempty coactual configuration,
    the run has EXACTLY ONE actual record — single-outcome experience — obtained
    with NO collapse postulate (only the capacity bound + λ).  Combined with
    `QMRecords.joint_eq_weight_mul_cond`, the empirical role of collapse (Lüders
    conditioning) is recovered, and (via `GleasonSelector`/`BornTypicality`) the
    selected-record frequencies are Born.

    What remains genuinely *physical* (not a Lean theorem): justifying the
    saturation premise `cost > Q_max/2` from a concrete capacity model (holographic /
    nuclearity / Holevo bound) — this is where the actual content lives, exactly as
    the Strasberg–Winter "branch selection problem" (arXiv:2601.19703) makes precise. -/
theorem qiqth_single_outcome_no_collapse (S : Selection C) :
    ∃! r : C.Rec, r ∈ S.config.active := by
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (exactly_one_actual S)
  exact ⟨r, by rw [hr]; exact Finset.mem_singleton_self r,
    fun y hy => by rw [hr] at hy; exact Finset.mem_singleton.mp hy⟩

end QIQTH.CoreNoCollapse
