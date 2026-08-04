/-
  CompactTubeLemma — J4-186: the generic compact open-tube lemma + the F2 gate-radius audit.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is pure
  point-set topology (`compact_tube`, `compact_tube_ball`) plus a geometry audit of the F2 gate-radius
  wall.  It uses NO heat-kernel data in its main lemma.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this delivers (ns `QIQTH.CompactTubeLemma`).

    * (T1) `compact_tube` — THE GENERIC TUBE LEMMA.  For `K` compact in a topological space `X`,
      `O` open in `X × E` (`E` a seminormed group) containing the zero-section over `K`
      (`∀ p ∈ K, (p, 0) ∈ O`), there is a UNIFORM radius `ε > 0` with
          `∀ p ∈ K, ∀ w : E, ‖w‖ < ε → (p, w) ∈ O`.
      Proof: Mathlib's `generalized_tube_lemma` for `K ×ˢ {0}` gives open `u ⊇ K`, `v ∋ 0` with
      `u ×ˢ v ⊆ O`; `Metric.isOpen_iff` extracts a ball `ball 0 ε ⊆ v`; combine.  This is exactly the
      shape Sol proposed for discharging F2 from a JOINTLY-OPEN admissible gate.

    * (T2) `compact_tube_ball` — the same, phrased with `Metric.ball 0 ε` membership.

    * (T3) `admissible_gate_uniform_radius` — the F2 REDUCTION (case (b), satisfiable-by-strengthened-
      spec): given ANY predicate `Adm : X → E → Prop` whose admissible region is jointly open and
      contains the zero-section over `K`, there is a uniform radius on which `Adm p w` holds for all
      `p ∈ K`, `‖w‖ < ε`.  This is the tube lemma packaged as "joint openness ⟹ uniform gate radius".

    * (T4) `flowBall_gateRadius_floor` — THE CONCRETE F2 AUDIT.  For the concrete flow-ball gate the
      uniform positive gate-radius floor is ALREADY banked: `reachableGate_concrete` (equivalently the
      `uniformInverseChart_huniformChart` radius, produced by the quantitative inverse-function theorem
      `ApproximatesLinearOn`) supplies a SINGLE `δ₀ > 0`, uniform over the compact `K`, below which
      every ball radius `c` gives an open / left-invertible / reachable / `C²` gate for every base
      `z ∈ K`.  So F2 (a uniform positive lower bound on the per-base gate radius) does NOT require the
      tube lemma at all — the chart spec is jointly-uniform, not merely fiberwise.  `flowBall_gateRadius_floor`
      re-exposes this floor as an explicit `∃ c₀ > 0` in the F2 slot shape.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## F2 AUDIT VERDICT (the answer to "does F2 fall?").

    The chart spec `HeatResidualBound.uniformInverseChart_huniformChart` banks a SINGLE radius `δ₀ > 0`
    that is UNIFORM over the compact base set `K` — `∃ δ₀ > 0, ∀ q ∈ K, (germ + C² for ‖v‖ < δ₀) ∧
    (open/closure for 0 < c < δ₀)`.  It is therefore case (a) of the task's dichotomy (jointly uniform),
    NOT case (b) (fiberwise-only).  Consequently:

      • The "per-base gate radius `cf`" whose uniform positivity was the feared F2 wall is, in the actual
        E-bound pipeline (`HeatResidualBound.gatedWitness_hEboundW_final_gen`), the UNIFORM constant
        `c = (b + ρc)/2 > b > 0` — the same value for every base `q ∈ K`.  There is no per-base
        `.choose` whose CONTINUITY is needed; the `cf := if hq then (hgood q hq).choose else 0` in
        `gatedWitness_hEboundW_of_good_gen` is bounded below by `b` because every good witness carries
        `b < c`.  F2 is DISCHARGED in that pipeline.

      • `δ₀` from `uniformInverseChart_huniformChart` IS the floor.  The quantitative inverse-function
        theorem (`ApproximatesLinearOn.toOpenPartialHomeomorph`) EXPOSES the source ball `ball 0 δ₀`
        uniformly, which is precisely why the K-uniform radius exists without any continuity-of-`.choose`
        argument (which is genuinely unavailable).

      • The tube lemma (T1/T3) is therefore NOT load-bearing for F2 here; it is banked as the general
        instrument that WOULD discharge F2 from a merely-jointly-open admissible gate (the case (b)
        reduction), and as an independent cross-check of the uniform-radius phenomenon.

    hCover: in the L1 facade (`FlowBallInstantiation.chartGateData_flowBall`) the `hCover` field is
    ALREADY reduced (`reachableGate_concrete` openness + field-`C²`) to the s-independent coverage carry
    `hMemCov` (`∀ᶠ x in 𝓝 x₀, ∀ᵐ z, z ∈ K → x ∈ φ_z '' ball 0 c`).  `hMemCov` is a satisfiable
    measurability CARRY, not a per-base radius floor; it is not the F2 wall and is out of scope of the
    tube argument (it concerns a.e.-`z` coverage of a FIXED field point, not a uniform velocity radius).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConcreteGateAssembly

open Set Filter Metric
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.ConcreteGateAssembly
open scoped Topology

namespace QIQTH.CompactTubeLemma

/-! ### (T1) The generic compact open-tube lemma. -/

/-- **★ T1 — `compact_tube`.**  For `K` compact in a topological space `X` and `O` open in `X × E`
    (`E` a seminormed additive group) that contains the zero-section over `K`, there is a UNIFORM
    radius `ε > 0` such that `(p, w) ∈ O` for every `p ∈ K` and every `w` with `‖w‖ < ε`.

    Proof: the singleton `{0}` is compact, so `generalized_tube_lemma` applied to `K ×ˢ {0} ⊆ O`
    yields open `u ⊇ K`, `v ∋ 0` with `u ×ˢ v ⊆ O`; `v` is an open neighbourhood of `0`, so
    `Metric.isOpen_iff` gives a ball `ball 0 ε ⊆ v`; then `p ∈ u` and `w ∈ ball 0 ε ⊆ v` place
    `(p, w) ∈ u ×ˢ v ⊆ O`.  NOT `a₁ = R/6`. -/
theorem compact_tube {X : Type*} [TopologicalSpace X] {E : Type*} [SeminormedAddCommGroup E]
    {K : Set X} (hK : IsCompact K) {O : Set (X × E)} (hO : IsOpen O)
    (hzero : ∀ p ∈ K, (p, (0 : E)) ∈ O) :
    ∃ ε > (0 : ℝ), ∀ p ∈ K, ∀ w : E, ‖w‖ < ε → (p, w) ∈ O := by
  -- `K ×ˢ {0} ⊆ O`.
  have hsub : K ×ˢ ({0} : Set E) ⊆ O := by
    rintro ⟨p, w⟩ ⟨hp, hw⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hzero p hp
  obtain ⟨u, v, hu, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hO hsub
  -- `v` is an open neighbourhood of `0`; extract a ball.
  have h0v' : (0 : E) ∈ v := h0v (Set.mem_singleton _)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hv 0 h0v'
  refine ⟨ε, hε, ?_⟩
  intro p hp w hw
  have hwv : w ∈ v := hball (by simpa [Metric.mem_ball, dist_zero_right] using hw)
  exact huv ⟨hKu hp, hwv⟩

/-! ### (T2) The ball-membership form. -/

/-- **T2 — `compact_tube_ball`.**  The tube lemma phrased with `Metric.ball 0 ε` membership. -/
theorem compact_tube_ball {X : Type*} [TopologicalSpace X] {E : Type*} [SeminormedAddCommGroup E]
    {K : Set X} (hK : IsCompact K) {O : Set (X × E)} (hO : IsOpen O)
    (hzero : ∀ p ∈ K, (p, (0 : E)) ∈ O) :
    ∃ ε > (0 : ℝ), ∀ p ∈ K, ∀ w ∈ Metric.ball (0 : E) ε, (p, w) ∈ O := by
  obtain ⟨ε, hε, htube⟩ := compact_tube hK hO hzero
  refine ⟨ε, hε, ?_⟩
  intro p hp w hw
  exact htube p hp w (by simpa [Metric.mem_ball, dist_zero_right] using hw)

/-! ### (T3) The F2 reduction: joint openness ⟹ uniform gate radius. -/

/-- **T3 — `admissible_gate_uniform_radius`.**  The F2 REDUCTION (case (b), satisfiable-by-strengthened-
    spec).  Given an admissibility predicate `Adm : X → E → Prop` whose region `{(p, w) | Adm p w}` is
    jointly OPEN and holds along the zero-section over `K`, there is a uniform velocity radius `ε > 0`
    on which `Adm p w` holds for every `p ∈ K`, `‖w‖ < ε`.  This is exactly "a jointly-open admissible
    gate yields a uniform positive gate radius" — the shape a merely-fiberwise chart spec would need,
    and which the repo's `uniformInverseChart_huniformChart` already supplies UNCONDITIONALLY (see
    `flowBall_gateRadius_floor`).  NOT `a₁ = R/6`. -/
theorem admissible_gate_uniform_radius {X : Type*} [TopologicalSpace X] {E : Type*}
    [SeminormedAddCommGroup E] {K : Set X} (hK : IsCompact K) (Adm : X → E → Prop)
    (hOpen : IsOpen {q : X × E | Adm q.1 q.2}) (hzero : ∀ p ∈ K, Adm p (0 : E)) :
    ∃ ε > (0 : ℝ), ∀ p ∈ K, ∀ w : E, ‖w‖ < ε → Adm p w := by
  obtain ⟨ε, hε, htube⟩ := compact_tube hK hOpen (fun p hp => hzero p hp)
  exact ⟨ε, hε, fun p hp w hw => htube p hp w hw⟩

/-! ### (T4) The concrete F2 audit: the flow-ball gate-radius floor is already banked. -/

/-- **★ T4 — `flowBall_gateRadius_floor`.**  THE CONCRETE F2 AUDIT.  For the concrete flow-ball gate
    `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, the uniform positive gate-radius floor is
    ALREADY banked: there is a SINGLE `c₀ > 0`, uniform over the compact base set `K`, such that for
    EVERY ball radius `0 < c < c₀` and EVERY base `z ∈ K`, the gate is open, the inverse chart is a
    left inverse on the ball, and every gate point is reachable with the inverse chart `C²` there.

    This is a thin re-exposure of `ConcreteGateAssembly.reachableGate_concrete` in the "∃ c₀ > 0"
    F2-slot shape, DOCUMENTING that F2 does not need the tube lemma: the chart spec
    (`uniformInverseChart_huniformChart`, via the quantitative inverse-function theorem
    `ApproximatesLinearOn`) is jointly uniform, so the floor `c₀` exists unconditionally.  NOT
    `a₁ = R/6`. -/
theorem flowBall_gateRadius_floor {n : ℕ} (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ c₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < c₀ → ∀ z ∈ K,
      IsOpen (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
      ∧ (∀ v ∈ Metric.ball (0 : Point n) c,
          uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
      ∧ (∀ x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c,
          (∃ v : Point n, ‖v‖ < c₀ ∧ x = uniformFlowExp g gi hC hK z v)
          ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x) :=
  reachableGate_concrete g gi hC hK

/-! ### `section AxiomChecks` — `#print axioms` for the mains. -/

section AxiomChecks

#print axioms compact_tube
#print axioms compact_tube_ball
#print axioms admissible_gate_uniform_radius
#print axioms flowBall_gateRadius_floor

end AxiomChecks

end QIQTH.CompactTubeLemma
