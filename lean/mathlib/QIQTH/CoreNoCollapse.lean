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
import Mathlib.Analysis.InnerProductSpace.Adjoint
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

/-- **The honest exact premise.**  `coactual_subsingleton` really only needs that any
    two distinct records together exceed capacity (`Q_max < cost r + cost s`); the
    structure's `cost_gt_half` is a (clean, symmetric) *sufficient condition* for that.
    This makes explicit where the physical content sits — and that it is the genuine
    open target (the capacity model + bridge theorem) rather than a hidden assumption. -/
theorem pair_exceeds_of_cost_gt_half (r s : C.Rec) (h : r ≠ s) :
    C.Qmax < C.cost r + C.cost s := by
  linarith [C.cost_gt_half r, C.cost_gt_half s]

/-- **Honest macroscopic exclusion (no global macroscopicity).**  In ANY capacity-bounded
    active set, at most one *macroscopic* record (`Q_max/2 < cost`) can be present — two
    would exceed capacity.  Unlike `coactual_subsingleton`, this does NOT assume every
    record is macroscopic: SMALL records (`cost ≤ Q_max/2`) may freely coexist.  Stated as
    "any two active macroscopic records are equal".  (Addresses the GPT-5.5-pro worry that
    requiring all records macroscopic excludes small ones by fiat.) -/
theorem active_macroscopic_subsingleton {Rec : Type*} [DecidableEq Rec] {cost : Rec → ℝ}
    {Qmax : ℝ} (hcost : ∀ r, 0 ≤ cost r) {active : Finset Rec}
    (hcap : ∑ r ∈ active, cost r ≤ Qmax) {r₁ r₂ : Rec}
    (h₁ : r₁ ∈ active) (h₂ : r₂ ∈ active)
    (hm₁ : Qmax / 2 < cost r₁) (hm₂ : Qmax / 2 < cost r₂) : r₁ = r₂ := by
  by_contra hne
  have hsub : ({r₁, r₂} : Finset Rec) ⊆ active := by
    intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact h₁
    · exact h₂
  have hpair : cost r₁ + cost r₂ ≤ ∑ r ∈ active, cost r := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hcost i)
    rwa [Finset.sum_pair hne] at h
  linarith

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

/- ── Blocks 1,5,6: a GENUINE PVM, Born normalisation, Lüders conditionalization ──

   Upgraded after the 2026-06 GPT-5.5-pro soundness review: the record observable is
   now an actual resolution of the identity (orthogonal projections summing to `1`), so
   the Born normalisation `∑ ‖E r ψ‖² = 1` and the Lüders post-state are THEOREMS, not
   names.  Requires a Hilbert space (`CompleteSpace`, for the adjoint).  Self-contained:
   the core does NOT depend on the Tomita–Takesaki spectral module. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finite Pythagoras for a pairwise-orthogonal family. -/
private theorem norm_sum_sq_orthogonal {ι : Type*} (t : Finset ι) (g : ι → H)
    (h : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → inner ℂ (g i) (g j) = (0 : ℂ)) :
    ‖∑ i ∈ t, g i‖ ^ 2 = ∑ i ∈ t, ‖g i‖ ^ 2 := by
  have key : inner ℂ (∑ i ∈ t, g i) (∑ i ∈ t, g i) = ∑ i ∈ t, inner ℂ (g i) (g i) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [inner_sum, Finset.sum_eq_single i]
    · intro j hj hji; exact h i hi j hj (Ne.symm hji)
    · intro hni; exact absurd hi hni
  simp only [inner_self_eq_norm_sq_to_K] at key
  exact_mod_cast key

/-- A **finite projective measurement (PVM)** — the decohered record observable as a
    genuine resolution of the identity: orthogonal projections `E r` summing to `1`. -/
structure FinPVM (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  Rec : Type
  [recFintype : Fintype Rec]
  E : Rec → (H →L[ℂ] H)
  selfadj : ∀ r, IsSelfAdjoint (E r)
  idem : ∀ r, IsIdempotentElem (E r)
  orth : ∀ r s, r ≠ s → E r * E s = 0
  complete : ∑ r, E r = 1

attribute [instance] FinPVM.recFintype

namespace FinPVM

variable (M : FinPVM H)

/-- Branch vectors of distinct records are orthogonal. -/
theorem branch_orthogonal (ψ : H) {r s : M.Rec} (h : r ≠ s) :
    inner ℂ (M.E r ψ) (M.E s ψ) = (0 : ℂ) := by
  have hadj : ContinuousLinearMap.adjoint (M.E r) = M.E r := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact M.selfadj r
  rw [← ContinuousLinearMap.adjoint_inner_right, hadj,
    ← ContinuousLinearMap.mul_apply, M.orth r s h]
  simp

/-- **Born weight** of a record: `w(r) = ‖E r ψ‖²`. -/
noncomputable def weight (ψ : H) (r : M.Rec) : ℝ := ‖M.E r ψ‖ ^ 2

/-- **Born normalisation (THEOREM):** for a unit state the record weights sum to `1`.
    This is the resolution of identity (`∑ E r = 1`) + orthogonality (Pythagoras). -/
theorem weight_sum_eq_one (ψ : H) (hψ : ‖ψ‖ = 1) : ∑ r, M.weight ψ r = 1 := by
  have hsum : ∑ r, M.E r ψ = ψ := by
    rw [← ContinuousLinearMap.sum_apply, M.complete, ContinuousLinearMap.one_apply]
  have hp := norm_sum_sq_orthogonal Finset.univ (fun r => M.E r ψ)
    (fun i _ j _ hij => M.branch_orthogonal ψ hij)
  rw [hsum] at hp
  simp only [weight]
  rw [← hp, hψ]; norm_num

/-- Conditional probability of a later effect `F` given record `r` (Lüders rule). -/
noncomputable def condProb (ψ : H) (r : M.Rec) (F : H →L[ℂ] H) : ℝ :=
  ‖F (M.E r ψ)‖ ^ 2 / ‖M.E r ψ‖ ^ 2

/-- The Lüders **post-selected (collapsed) state** `ψ_r = E r ψ / ‖E r ψ‖`. -/
noncomputable def postState (ψ : H) (r : M.Rec) : H :=
  ((‖M.E r ψ‖ : ℂ))⁻¹ • M.E r ψ

/-- **Collapse-as-conditionalization (substantive form):** the conditional probability
    `condProb` is exactly the Born rule applied to the *collapsed* post-selected state
    `ψ_r`.  So "updating to the collapsed state" and "conditioning on the record" give
    the SAME predictions — the collapse map is operationally redundant. -/
theorem condProb_eq_born_postState (ψ : H) (r : M.Rec) (F : H →L[ℂ] H)
    (hr : M.E r ψ ≠ 0) : ‖F (M.postState ψ r)‖ ^ 2 = M.condProb ψ r F := by
  have hn : ‖M.E r ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hnc : ‖(‖M.E r ψ‖ : ℂ)‖ = ‖M.E r ψ‖ := by simp
  unfold postState condProb
  rw [map_smul, norm_smul, norm_inv, hnc, mul_pow, inv_pow]
  field_simp

/-- The joint (sequential) Born probability factors as `weight × conditional`. -/
theorem joint_eq_weight_mul_cond (ψ : H) (r : M.Rec) (F : H →L[ℂ] H)
    (hr : M.E r ψ ≠ 0) : M.weight ψ r * M.condProb ψ r F = ‖F (M.E r ψ)‖ ^ 2 := by
  have hden : ‖M.E r ψ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)
  unfold weight condProb
  field_simp

end FinPVM

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

/-- A concrete **`Selection`** in the witness: record `true` is actual (cost `2 ≤ 3`).
    Witnesses that the FINAL theorem (`exactly_one_actual`) is non-vacuous — the
    hypotheses are jointly satisfiable, not just `RecordContext` alone. -/
def witnessSelection : Selection witnessContext where
  config :=
    { active := {true}
      capacity := by
        show (∑ _r ∈ ({true} : Finset Bool), (2 : ℝ)) ≤ 3
        rw [Finset.sum_const, Finset.card_singleton]; norm_num }
  selected := ⟨true, Finset.mem_singleton_self true⟩

/-- The concrete selected run has exactly one actual record. -/
example : witnessSelection.config.active.card = 1 := exactly_one_actual witnessSelection

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
