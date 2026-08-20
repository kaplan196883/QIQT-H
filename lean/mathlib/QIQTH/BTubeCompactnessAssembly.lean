/-
  BTubeCompactnessAssembly — J4-892: the COMPACTNESS-ASSEMBLY audit of J4-889's b-tube cover route,
  with the DECISIVE boundary obstruction PROVED.  This file attempts the "piece (iv)" assembly that
  would turn the per-point general-centre joint-`C²` inverse-chart results (J4-890/J4-891) into the
  single open, in-gate, chart-`C²` cover `W` of the compact core-graph demanded by
  `onCoreGraphContinuity_of_chartC2_gate_cover` / `hbint_reduced_to_chartC2_gate_cover` (J4-889), and
  finds — and PROVES — that this exact cover is JOINTLY UNSATISFIABLE at boundary base points.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  This file's MAIN theorem is a NO-GO (an obstruction), and its antecedent is proved
  INHABITED (a concrete closed ball) — so it is genuinely non-vacuous.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FINDING — the J4-889 cover route is BOUNDARY-UNSATISFIABLE (a near-miss caught).

  J4-889 reduced `hbint`'s surviving residual to the existence, per a.e. `s`, of an OPEN set `W` that
  (i) COVERS the compact core-graph `(K ×ˢ concreteKx) ∩ jointCore`, (ii) is entirely IN-GATE
  (`p.1 ∈ K` ∧ `S p.1 ∈ 𝓝 p.2` for every `p ∈ W`), and (iii) carries the joint chart
  `ContDiffOn ℝ 2`.  The per-point engines J4-890 (forward joint `C²` at a general velocity centre)
  and J4-891 (`uniformInverseChart_jointContDiffAt_generalCenter`, joint `ContDiffAt ℝ 2` of the
  inverse chart at `(z₀, exp z₀ v₀)` for `z₀ ∈ interior K`, `‖v₀‖ < r₀`) supply the joint chart `C²`
  at each INTERIOR core-graph point.  The compactness assembly was expected to union these into `W`.

  IT CANNOT, for any `K` with a boundary base point.  The obstruction is PURELY topological and needs
  ONLY clause (ii)'s first conjunct `p.1 ∈ K`:

    * `proj_subset_interior_of_open_ingate` — for an OPEN `W` with `p.1 ∈ K` for every `p ∈ W`, the
      base projection `Prod.fst '' W` is an OPEN subset of `K`, hence `⊆ interior K`
      (`isOpenMap_fst` + `interior_maximal`).

    * `coreGraph_mem_diag` — for EVERY base `z₀ ∈ K`, the diagonal point `(z₀, z₀)` is a core-graph
      point (via the zero-velocity image `uniformFlowExp z₀ 0 = z₀`, `uniformFlowExp_zero`).  So the
      core-graph's base projection is ALL of `K`, boundary included.

    * `chartC2_gate_cover_boundary_obstruction` — ★ THE NO-GO.  If `z₀ ∈ K` but `z₀ ∉ interior K`
      (a boundary base point — present in EVERY nonempty proper compact `K ⊆ ℝⁿ`), then there is NO
      open in-gate set `W` covering the core-graph: covering the boundary diagonal point `(z₀, z₀)`
      would force `z₀ ∈ Prod.fst '' W ⊆ interior K`, contradicting `z₀ ∉ interior K`.  A fortiori the
      full J4-889 bundle (which ADDS the chart-`C²` clause) is impossible — `consumer_cover_boundary_obstruction`.

    * `boundary_base_point_exists` — NON-VACUITY: the closed unit ball `K := closedBall 0 1 ⊆
      Point (n+1)` is a concrete compact set with a genuine boundary base point `Pi.single 0 1`
      (`interior (closedBall 0 1) = ball 0 1`), so the obstruction's hypothesis is INHABITED and the
      no-go bites on a real set — it is NOT a vacuous statement.

  ## WHAT THIS MEANS FOR THE CAMPAIGN (precise honest verdict).
  The `hcover` hypothesis of `hbint_reduced_to_chartC2_gate_cover` (J4-889) is satisfiable ONLY when
  the core-graph lies over `interior K` (equivalently: `K` open, hence for compact `K ⊆ ℝⁿ`, `K = ∅`).
  For every genuine (nonempty) confinement set the cover route is UNsatisfiable at the boundary, so it
  cannot discharge `hbint`.  The interior part DOES assemble (J4-890/891 + this file's projection lemma),
  so the boundary is the PRECISE and ONLY residual: the on-core-graph continuity at boundary base points
  must be reached by a route that does NOT require joint chart `C²` on an ambient OPEN neighbourhood of
  boundary points (e.g. the banked FIBERWISE `C²` `flowBall_gateRadius_floor` / `reachableGate_concrete`,
  which holds over ALL of `K`, combined with joint continuity of `exp`).  `hbint` is NOT closed by the
  cover route.  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HbintCollarMatchedCutoffClosed
import QIQTH.FieldHessianJointContinuity
import QIQTH.NearIsometryBudget

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HbintCollarMatchedCutoffClosed
open QIQTH.FieldHessianJointContinuity
open scoped Topology

namespace QIQTH.BTubeCompactnessAssembly

variable {n : ℕ}

/-! ###############################################################################
    ### C0 — the purely-topological projection lemma (open + fiberwise-in-`K` ⟹ base ⊆ interior).
    ############################################################################### -/

/-- **★ `proj_subset_interior_of_open_ingate`.**  For an OPEN set `W ⊆ Point n × Point n` all of whose
    points have base coordinate in `K` (`∀ p ∈ W, p.1 ∈ K`), the base projection `Prod.fst '' W` is an
    OPEN subset of `K`, hence contained in `interior K` (`isOpenMap_fst` + `interior_maximal`).  This
    is the topological core of the boundary obstruction: an OPEN in-gate `W` can only live over
    `interior K`.  NOT `a₁ = R/6`. -/
theorem proj_subset_interior_of_open_ingate {K : Set (Point n)}
    {W : Set (Point n × Point n)} (hWopen : IsOpen W)
    (hWK : ∀ p ∈ W, p.1 ∈ K) :
    Prod.fst '' W ⊆ interior K := by
  refine interior_maximal ?_ (isOpenMap_fst _ hWopen)
  rintro z ⟨p, hp, rfl⟩
  exact hWK p hp

/-! ###############################################################################
    ### C1 — every base point of `K` yields a core-graph diagonal point.
    ############################################################################### -/

/-- **★ `coreGraph_mem_diag`.**  For every base `z₀ ∈ K` and `0 ≤ b`, the diagonal point `(z₀, z₀)`
    lies in the compact core-graph `(K ×ˢ concreteKx) ∩ jointCore`, via the zero-velocity image
    `uniformFlowExp z₀ 0 = z₀` (`uniformFlowExp_zero`) with `(z₀, 0) ∈ K ×ˢ closedBall 0 b`.  So the
    core-graph's base projection is ALL of `K` — including its boundary.  NOT `a₁ = R/6`. -/
theorem coreGraph_mem_diag (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ) (hb : 0 ≤ b)
    {z₀ : Point n} (hz₀ : z₀ ∈ K) :
    ((z₀, z₀) : Point n × Point n) ∈
      (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b := by
  have hexp : uniformFlowExp g gi hC hK z₀ 0 = z₀ := uniformFlowExp_zero g gi hC hK z₀ hz₀
  have hmem0 : ((z₀, (0 : Point n)) : Point n × Point n)
      ∈ K ×ˢ Metric.closedBall (0 : Point n) b := by
    refine ⟨hz₀, ?_⟩
    rw [Metric.mem_closedBall, dist_self]; exact hb
  refine ⟨⟨hz₀, ?_⟩, ?_⟩
  · -- `z₀ ∈ concreteKx` via `(z₀, 0)`.
    exact ⟨(z₀, 0), hmem0, hexp⟩
  · -- `(z₀, z₀) ∈ jointCore` via `(z₀, 0)`.
    refine ⟨(z₀, 0), hmem0, ?_⟩
    show ((z₀, uniformFlowExp g gi hC hK z₀ 0) : Point n × Point n) = (z₀, z₀)
    rw [hexp]

/-! ###############################################################################
    ### C2 — THE NO-GO: no open in-gate cover of the core-graph over a boundary base point.
    ############################################################################### -/

/-- **★★★ `chartC2_gate_cover_boundary_obstruction` — THE BOUNDARY OBSTRUCTION.**  If `z₀ ∈ K` is a
    boundary base point (`z₀ ∉ interior K`), then there is NO open in-gate set `W` covering the compact
    core-graph.  Only clause (ii)'s first conjunct `p.1 ∈ K` is used, so this is the STRONGEST form of
    the no-go: it does not even need the `S`-gate or the chart-`C²`.  Mechanism: covering the boundary
    diagonal core-graph point `(z₀, z₀)` (`coreGraph_mem_diag`) forces
    `z₀ ∈ Prod.fst '' W ⊆ interior K` (`proj_subset_interior_of_open_ingate`), contradicting
    `z₀ ∉ interior K`.  NOT `a₁ = R/6`. -/
theorem chartC2_gate_cover_boundary_obstruction (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ) (hb : 0 ≤ b) (S : Point n → Set (Point n))
    {z₀ : Point n} (hz₀K : z₀ ∈ K) (hz₀int : z₀ ∉ interior K) :
    ¬ ∃ W : Set (Point n × Point n), IsOpen W ∧
      (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b ⊆ W ∧
      (∀ p ∈ W, p.1 ∈ K ∧ S p.1 ∈ nhds p.2) := by
  rintro ⟨W, hWopen, hWcover, hWgate⟩
  have hpW : ((z₀, z₀) : Point n × Point n) ∈ W :=
    hWcover (coreGraph_mem_diag g gi hC hK b hb hz₀K)
  have hz₀int' : z₀ ∈ interior K :=
    proj_subset_interior_of_open_ingate hWopen (fun p hpW => (hWgate p hpW).1)
      ⟨(z₀, z₀), hpW, rfl⟩
  exact hz₀int hz₀int'

/-- **★★ `consumer_cover_boundary_obstruction` — the no-go against the EXACT J4-889 bundle.**  The full
    hypothesis bundle of `onCoreGraphContinuity_of_chartC2_gate_cover` / the `hcover` field of
    `hbint_reduced_to_chartC2_gate_cover` (which ADDS the chart-`ContDiffOn ℝ 2` clause) is ALSO
    impossible at a boundary base point — a fortiori from the stronger
    `chartC2_gate_cover_boundary_obstruction`.  This is the precise statement that the J4-889 cover
    route CANNOT be discharged for any `K` with a boundary base point.  NOT `a₁ = R/6`. -/
theorem consumer_cover_boundary_obstruction (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ) (hb : 0 ≤ b) (S : Point n → Set (Point n))
    {z₀ : Point n} (hz₀K : z₀ ∈ K) (hz₀int : z₀ ∉ interior K) :
    ¬ ∃ W : Set (Point n × Point n), IsOpen W ∧
      (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b ⊆ W ∧
      (∀ p ∈ W, p.1 ∈ K ∧ S p.1 ∈ nhds p.2) ∧
      ContDiffOn ℝ 2
        (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) W := by
  rintro ⟨W, hWopen, hWcover, hWgate, _hWchart⟩
  exact chartC2_gate_cover_boundary_obstruction g gi hC hK b hb S hz₀K hz₀int
    ⟨W, hWopen, hWcover, hWgate⟩

/-! ###############################################################################
    ### C3 — NON-VACUITY: a concrete compact set with a genuine boundary base point.
    ############################################################################### -/

/-- **NON-VACUITY (the obstruction bites on a REAL set).**  The closed unit ball
    `K := Metric.closedBall 0 1 ⊆ Point (n+1)` is compact and has a genuine boundary base point
    `z₀ := Pi.single 0 1`: it lies in `K` (`‖Pi.single 0 1‖ = 1 ≤ 1`) but NOT in
    `interior K = Metric.ball 0 1` (`interior_closedBall`, since `‖z₀‖ = 1 ≮ 1`).  So the hypothesis of
    `chartC2_gate_cover_boundary_obstruction` is INHABITED — the no-go is genuinely non-vacuous, not an
    empty-antecedent trap.  NOT `a₁ = R/6`. -/
theorem boundary_base_point_exists :
    ∃ (K : Set (Point (n + 1))), IsCompact K ∧
      ∃ z₀ : Point (n + 1), z₀ ∈ K ∧ z₀ ∉ interior K := by
  classical
  refine ⟨Metric.closedBall (0 : Point (n + 1)) 1, isCompact_closedBall _ _,
    Pi.single 0 1, ?_, ?_⟩
  · -- `Pi.single 0 1 ∈ closedBall 0 1`.
    rw [Metric.mem_closedBall, dist_zero_right, Pi.norm_single, Real.norm_eq_abs, abs_one]
  · -- `Pi.single 0 1 ∉ interior (closedBall 0 1) = ball 0 1`.
    rw [interior_closedBall (0 : Point (n + 1)) (one_ne_zero), Metric.mem_ball, dist_zero_right,
      Pi.norm_single, Real.norm_eq_abs, abs_one]
    exact lt_irrefl 1

end QIQTH.BTubeCompactnessAssembly

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.BTubeCompactnessAssembly
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms proj_subset_interior_of_open_ingate
#print axioms coreGraph_mem_diag
#print axioms chartC2_gate_cover_boundary_obstruction
#print axioms consumer_cover_boundary_obstruction
#print axioms boundary_base_point_exists
end AxiomChecks
