/-
  ThetaChartContDiff — J4-1148: dispatch 2 of Sol's 4-dispatch plan to close `hWmeas`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  transports the existing `ContDiffAt ℝ 2` germ fact for the OLD `uniformInverseChart` (proved in
  `UniformChartRadius.lean`, `uniformInverseChart_huniformChart`) onto the NEW canonical chart
  `uniformInverseChart'` (built in `ThetaMeasurableEmbedding.lean`, J4-1147) at every point in the flow
  image.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no existing
  file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `uniformInverseChart'_eqOn_uniformInverseChart` — on the (open) tube image
      `φ_q '' Metric.ball 0 c`, the two charts `uniformInverseChart'` and `uniformInverseChart` agree
      POINTWISE (both recover the same velocity `v'` at `p = φ_q v'`, one via
      `uniformInverseChart'_flow_eq`, the other via the germ left-inverse packaged inside
      `uniformInverseChart_huniformChart`).

    * `uniformInverseChart'_eventuallyEq_uniformInverseChart` — since the tube image is `IsOpen` (this
      openness clause is already part of `uniformInverseChart_huniformChart`'s output — NOT re-derived
      here), pointwise agreement on the image upgrades to `Filter.EventuallyEq` in `𝓝 (φ_q v)` for any
      `v` in the tube ball.

    * ★ `uniformInverseChart'_contDiffAt` — ★★ THE PAYOFF: `ContDiffAt ℝ 2 (uniformInverseChart' … c q)
      (φ_q v)` for every `q ∈ K` and `‖v‖ < c` (uniformly, single radius `δ₀ = min` of the two source
      radii), transported from the OLD chart's `ContDiffAt` fact via
      `ContDiffAt.congr_of_eventuallyEq`.  This is the `C²` germ half of the `huniformChart` shape that
      `gatedWitness_hEboundW_final_gen` consumes, now discharged for `uniformInverseChart'`.

  ## WHAT REMAINS (dispatches 27/28, NOT this dispatch).
    * dispatch 27 — instantiate `gatedWitness_hEboundW_final_gen` at `W := uniformInverseChart' … c`,
      combining this file's `ContDiffAt` half with `ThetaMeasurableEmbedding`'s measurability half and
      the (still-needed) open/closure clause for `uniformInverseChart'` itself (transportable the same
      way from `(hchart q hq).2`, not yet packaged as a standalone lemma here).
    * dispatch 28 — the parallel residualization theorem for `uniformInverseChart'` (mirroring J4-1143).

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ThetaMeasurableEmbedding

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.FlowJointContinuity
open QIQTH.ThetaMeasurableEmbedding
open scoped Topology BigOperators ContDiff

namespace QIQTH.ThetaChartContDiff

variable {n : ℕ}

/-! ###############################################################################
    ### THE POINTWISE AGREEMENT — both charts recover the same velocity on the tube image.
    ############################################################################### -/

/-- **`uniformInverseChart'_eqOn_uniformInverseChart`.**  For `0 < c < min δg δθ` (`δg` the
    `uniformInverseChart_huniformChart` radius, `δθ` the `theta_measurableEmbedding` radius) and
    `q ∈ K`, the NEW chart `uniformInverseChart'` and the OLD chart `uniformInverseChart` agree
    POINTWISE on the tube image `φ_q '' Metric.ball 0 c`: both recover the velocity `v'` at
    `p = φ_q v'`. NOT `a₁ = R/6`. -/
theorem uniformInverseChart'_eqOn_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {δg : ℝ}
    (hchart : ∀ q ∈ K,
      (∀ v : Point n, ‖v‖ < δg →
        (fun z => uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z))
            =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v)) ∧
      (∀ cc : ℝ, 0 < cc → cc < δg →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 cc) ∧
        closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 cc)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 cc))
    {c : ℝ} (hc0 : 0 < c) (hcg : c < δg)
    (hemb : MeasurableEmbedding ((ThetaMeasurableEmbedding.TubeDomain K c).restrict
      (ThetaMeasurableEmbedding.thetaMap g gi hC hK)))
    {q : Point n} (hq : q ∈ K) :
    Set.EqOn (uniformInverseChart' g gi hC hK c q) (uniformInverseChart g gi hC hK q)
      (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c) := by
  rintro p ⟨v', hv', rfl⟩
  rw [mem_ball_zero_iff] at hv'
  have h1 := uniformInverseChart'_flow_eq g gi hC hK hemb hq hv'
  have h2 := ((hchart q hq).1 v' (lt_trans hv' hcg)).1
  have h2' : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v') = v' := by
    simpa using h2.eq_of_nhds
  rw [h1, h2']

/-! ###############################################################################
    ### THE EVENTUAL-EQUALITY UPGRADE — via openness of the tube image.
    ############################################################################### -/

/-- **`uniformInverseChart'_eventuallyEq_uniformInverseChart`.**  For `0 < c < min δg δθ` and
    `q ∈ K`, `‖v‖ < c`: since the tube image `φ_q '' Metric.ball 0 c` is `IsOpen` (from `hchart`'s own
    output — not re-derived) and contains `φ_q v`, the pointwise agreement upgrades to
    `Filter.EventuallyEq` in `𝓝 (φ_q v)`. NOT `a₁ = R/6`. -/
theorem uniformInverseChart'_eventuallyEq_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {δg : ℝ}
    (hchart : ∀ q ∈ K,
      (∀ v : Point n, ‖v‖ < δg →
        (fun z => uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z))
            =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v)) ∧
      (∀ cc : ℝ, 0 < cc → cc < δg →
        IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 cc) ∧
        closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 cc)
          ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 cc))
    {c : ℝ} (hc0 : 0 < c) (hcg : c < δg)
    (hemb : MeasurableEmbedding ((ThetaMeasurableEmbedding.TubeDomain K c).restrict
      (ThetaMeasurableEmbedding.thetaMap g gi hC hK)))
    {q : Point n} (hq : q ∈ K) {v : Point n} (hv : ‖v‖ < c) :
    uniformInverseChart' g gi hC hK c q
      =ᶠ[nhds (uniformFlowExp g gi hC hK q v)] uniformInverseChart g gi hC hK q := by
  have hOC := ((hchart q hq).2 c hc0 hcg).1
  have hmemU : uniformFlowExp g gi hC hK q v ∈
      uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c :=
    ⟨v, mem_ball_zero_iff.mpr hv, rfl⟩
  exact (uniformInverseChart'_eqOn_uniformInverseChart g gi hC hK hchart hc0 hcg hemb hq)
    |>.eventuallyEq_of_mem (hOC.mem_nhds hmemU)

/-! ###############################################################################
    ### ★★ THE PAYOFF — `ContDiffAt ℝ 2` for the new chart, transported from the old one.
    ############################################################################### -/

/-- **★★ `uniformInverseChart'_contDiffAt` — the `C²` germ half of the `huniformChart` shape, for the
    NEW chart.**  A single `δ₀ > 0` (`= min` of the `uniformInverseChart_huniformChart` radius and the
    `theta_measurableEmbedding` radius) such that for every `0 < c < δ₀`, `q ∈ K`, `‖v‖ < c`:
    `ContDiffAt ℝ 2 (uniformInverseChart' … c q) (φ_q v)`.  Transported from the OLD chart's
    `ContDiffAt` fact (`uniformInverseChart_huniformChart`) via
    `uniformInverseChart'_eventuallyEq_uniformInverseChart` and `ContDiffAt.congr_of_eventuallyEq`.
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart'_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < c →
      ContDiffAt ℝ 2 (uniformInverseChart' g gi hC hK c q) (uniformFlowExp g gi hC hK q v) := by
  obtain ⟨δg, hδg, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δθ, hδθ, hembR⟩ := theta_measurableEmbedding g gi hC hK
  refine ⟨min δg δθ, lt_min hδg hδθ, ?_⟩
  intro c hc0 hcr q hq v hv
  have hcg : c < δg := lt_of_lt_of_le hcr (min_le_left _ _)
  have hcθ : c < δθ := lt_of_lt_of_le hcr (min_le_right _ _)
  have hemb := hembR c hc0 hcθ
  have hEq := uniformInverseChart'_eventuallyEq_uniformInverseChart g gi hC hK hchart hc0 hcg
    hemb hq hv
  have hCD : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK q) (uniformFlowExp g gi hC hK q v) :=
    ((hchart q hq).1 v (lt_trans hv hcg)).2
  exact hCD.congr_of_eventuallyEq hEq

end QIQTH.ThetaChartContDiff

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ThetaChartContDiff
#print axioms uniformInverseChart'_eqOn_uniformInverseChart
#print axioms uniformInverseChart'_eventuallyEq_uniformInverseChart
#print axioms uniformInverseChart'_contDiffAt
end AxiomChecks
