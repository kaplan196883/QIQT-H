/-
  ThetaChartGatedInstantiation — J4-1149: dispatch 3 of Sol's 4-dispatch plan to close `hWmeas`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  instantiates the existing chart-generic summit `UniformChartRadius.gatedWitness_hEboundW_final_gen`
  at the NEW canonical chart `uniformInverseChart'` (built in `ThetaMeasurableEmbedding.lean`, J4-1147,
  with its `C²` germ half transported in `ThetaChartContDiff.lean`, J4-1148).  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `uniformInverseChart'_huniformChart` — ★★ THE PAYOFF: for the FIXED tube radius
      `c₀ := min δg δθ / 2` (`δg` = `uniformInverseChart_huniformChart`'s radius, `δθ` =
      `theta_measurableEmbedding`'s radius), the chart `W := uniformInverseChart' g gi hC hK c₀`
      satisfies the exact `huniformChart` shape consumed by `gatedWitness_hEboundW_final_gen`, at
      radius `δ₀ := c₀` itself:
        - the GERM clause (`(fun z => W q (φ_q z)) =ᶠ[nhds v] id` + `ContDiffAt ℝ 2 (W q) (φ_q v)`)
          is assembled from `uniformInverseChart'_flow_eq` (J4-1147, upgraded to eventual equality via
          openness of `Metric.ball 0 c₀`) and `uniformInverseChart'_contDiffAt` (J4-1148);
        - the OPEN/CLOSURE clause is `W`-INDEPENDENT (it only mentions the flow `φ_q`, never the
          chart), so it is reused VERBATIM from `uniformInverseChart_huniformChart`'s own output.

    * `gatedWitness_hEboundW_unconditional'` — the direct instantiation of
      `gatedWitness_hEboundW_final_gen` at `W := uniformInverseChart' g gi hC hK c₀`: the SAME
      `hEboundW` primitive shape as `gatedWitness_hEboundW_unconditional`
      (`UniformChartRadius.lean`), now for the NEW, jointly-measurable-in-p chart.

  ## WHAT REMAINS (dispatch 28, NOT this dispatch).
    * dispatch 28 — the parallel residualization theorem for `uniformInverseChart'` (mirroring
      J4-1143), i.e. actually discharging `hWmeas` end-to-end using
      `uniformInverseChart'_joint_measurable` (J4-1147) together with this file's
      `gatedWitness_hEboundW_unconditional'`.

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ThetaChartContDiff

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.FlowJointContinuity
open QIQTH.ThetaMeasurableEmbedding
open QIQTH.ThetaChartContDiff
open QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open QIQTH.HeatParametrixOrder
open QIQTH.PullbackMetric QIQTH.TrueHeatKernel
open QIQTH.RadialDistance QIQTH.RNCDecay
open scoped Topology BigOperators NNReal ContDiff

namespace QIQTH.ThetaChartGatedInstantiation

variable {n : ℕ}

/-! ###############################################################################
    ### ★★ THE PAYOFF — `uniformInverseChart'` satisfies the `huniformChart` shape.
    ############################################################################### -/

/-- **★★ `uniformInverseChart'_huniformChart` — the `huniformChart` shape for the NEW chart.**  For the
    fixed tube radius `c₀ := min δg δθ / 2` (`δg` = `uniformInverseChart_huniformChart`'s radius,
    `δθ` = `theta_measurableEmbedding`'s radius, so `0 < c₀ < min δg δθ`), the chart
    `W := uniformInverseChart' g gi hC hK c₀` satisfies `huniformChart` at radius `δ₀ := c₀`: the germ +
    `ContDiffAt ℝ 2` clause is assembled from `uniformInverseChart'_flow_eq`/`_contDiffAt`; the
    open/closure clause is `W`-independent and reused from `uniformInverseChart_huniformChart`.
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart'_huniformChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ c₀ > (0 : ℝ), ∃ W : Point n → Point n → Point n, W = uniformInverseChart' g gi hC hK c₀ ∧
      ∀ q ∈ K,
        (∀ v : Point n, ‖v‖ < c₀ →
          (fun z => W q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (W q) (uniformFlowExp g gi hC hK q v)) ∧
        (∀ c : ℝ, 0 < c → c < c₀ →
          IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
          closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
            ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c) := by
  obtain ⟨δg, hδg, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δθ, hδθ, hembR⟩ := theta_measurableEmbedding g gi hC hK
  obtain ⟨δC, hδC, hCD⟩ := uniformInverseChart'_contDiffAt g gi hC hK
  set c₀ : ℝ := min δg (min δθ δC) / 2 with hc₀def
  have hc₀lt : c₀ < min δg (min δθ δC) := by
    rw [hc₀def]; linarith [lt_min hδg (lt_min hδθ hδC)]
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]; positivity
  refine ⟨c₀, hc₀pos, uniformInverseChart' g gi hC hK c₀, rfl, ?_⟩
  have hc₀g : c₀ < δg := lt_of_lt_of_le hc₀lt (min_le_left _ _)
  have hc₀θ : c₀ < δθ := lt_of_lt_of_le hc₀lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc₀C : c₀ < δC := lt_of_lt_of_le hc₀lt (le_trans (min_le_right _ _) (min_le_right _ _))
  have hemb := hembR c₀ hc₀pos hc₀θ
  intro q hq
  refine ⟨?_, ?_⟩
  · intro v hv
    refine ⟨?_, hCD c₀ hc₀pos hc₀C q hq v hv⟩
    have hballOpen : IsOpen (Metric.ball (0 : Point n) c₀) := Metric.isOpen_ball
    have hvmem : v ∈ Metric.ball (0 : Point n) c₀ := mem_ball_zero_iff.mpr hv
    have hnhds : Metric.ball (0 : Point n) c₀ ∈ nhds v := hballOpen.mem_nhds hvmem
    filter_upwards [hnhds] with z hz
    have hz' : ‖z‖ < c₀ := mem_ball_zero_iff.mp hz
    exact uniformInverseChart'_flow_eq g gi hC hK hemb hq hz'
  · intro c hc0 hcc
    exact (hchart q hq).2 c hc0 (lt_trans hcc hc₀g)

/-! ###############################################################################
    ### ★★ THE CAPSTONE — `hEboundW` for the NEW, jointly-measurable-in-p chart.
    ############################################################################### -/

/-- **★★ `gatedWitness_hEboundW_unconditional'` — the `hEboundW` primitive for `uniformInverseChart'`.**
    Direct instantiation of `gatedWitness_hEboundW_final_gen` at
    `W := uniformInverseChart' g gi hC hK c₀` via `uniformInverseChart'_huniformChart`: delivers the
    SAME width-2 `hEboundW` primitive shape as `gatedWitness_hEboundW_unconditional`
    (`UniformChartRadius.lean`), now for the chart with DERIVED joint measurability in `p`
    (`uniformInverseChart'_joint_measurable`, J4-1147) rather than an opaque `Exists.choose` chart.
    NOT `a₁ = R/6`. -/
theorem gatedWitness_hEboundW_unconditional' (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitness Θ u a b (uniformInverseChart' g gi hC hK c₀))) τ p q|
          ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨c₀, hc₀pos, W, hWeq, hchart⟩ := uniformInverseChart'_huniformChart g gi hC hK
  refine ⟨c₀, hc₀pos, ?_⟩
  have hres := gatedWitness_hEboundW_final_gen g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
    hw0smooth hw0flat W ⟨c₀, hc₀pos, hchart⟩
  rw [hWeq] at hres
  exact hres

end QIQTH.ThetaChartGatedInstantiation

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ThetaChartGatedInstantiation
#print axioms uniformInverseChart'_huniformChart
#print axioms gatedWitness_hEboundW_unconditional'
end AxiomChecks
