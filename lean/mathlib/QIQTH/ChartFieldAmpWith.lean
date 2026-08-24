/-
  ChartFieldAmpWith — J4-1156: Phase 1, Task B of the chart-parametric rebuild campaign (dispatch 1
  of the newly-authorized full rebuild; per `gpt-5.6-sol`'s 33rd consult, 2026-08-24).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes `NormalFormDischarge.chartFieldAmp` — one of the exactly TWO root definitions in the
  whole campaign that call the concrete chart `uniformInverseChart` DIRECTLY (not transitively) — over
  an ABSTRACT chart argument `W : Point n → Point n → Point n`, then instantiates the generic version
  twice: once at the OLD chart (bridged back to the existing `chartFieldAmp` via a `rfl`-level
  compatibility theorem, so nothing existing is broken or reproven) and once at the NEW,
  jointly-measurable chart `uniformInverseChart'` (`ThetaMeasurableEmbedding.lean`, J4-1147).  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `chartFieldAmpWith` — the chart-generic sibling of `chartFieldAmp`: LITERALLY the same body
      (`radialCutoff`, `vanVleck ^ (-1/2)`, the two `transportCoeff` terms), with every occurrence of
      `uniformInverseChart g gi hC hK z x'` replaced by the abstract `W z x'`.

    * `chartFieldAmpWith_uniformInverseChart` — ★ THE COMPATIBILITY BRIDGE: instantiating the generic
      definition at `W := uniformInverseChart g gi hC hK` recovers the EXISTING `chartFieldAmp`
      literally (`rfl` — pure unfolding, no new mathematics, confirms the genericization is faithful).

    * `chartFieldAmp'` — the NEW-chart instantiation: `chartFieldAmpWith` at
      `W := uniformInverseChart' g gi hC hK c` (the derived-measurable chart, J4-1147/1148/1149).

  ## WHAT THIS DOES NOT DO.
  This file does NOT prove any relationship between `chartFieldAmp'` and `chartFieldAmp` beyond what
  the generic definition trivially gives (both are the SAME formula in different chart-arguments) — in
  particular it does NOT claim `chartFieldAmp' = chartFieldAmp` (false in general: the two charts
  agree only on a bounded tube image, per `ThetaChartContDiff.uniformInverseChart'_eqOn_uniformInverseChart`,
  NOT globally). It also does not yet build the derivative-chain analogues (`witnessFieldDeriv`-shaped
  siblings) — that is Phase 2 of the rebuild plan (see `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`).

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.NormalFormDischarge
import QIQTH.ThetaChartGatedInstantiation

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.ThetaMeasurableEmbedding
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ###############################################################################
    ### THE CHART-GENERIC SIBLING — `chartFieldAmpWith`.
    ############################################################################### -/

/-- **`chartFieldAmpWith` — the chart-generic sibling of `chartFieldAmp`.**  Literally the same body
    as `chartFieldAmp` (`radialCutoff a b (W z x')`, times `vanVleck g (W z x') ^ (-1/2)`, times the
    order-0/order-1 `transportCoeff` sum at `W z x'`), with the concrete `uniformInverseChart g gi hC
    hK z x'` replaced by an ABSTRACT chart evaluation `W z x'`.  Pure data — no chart-property
    hypotheses attached; those are supplied at the theorem level downstream.  NOT `a₁ = R/6`. -/
noncomputable def chartFieldAmpWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (W : Point n → Point n → Point n) (τ : ℝ) (z : Point n) (x' : Point n) : ℝ :=
  radialCutoff a b (W z x')
    * (vanVleck g (W z x') ^ (-(1 : ℝ) / 2)
        * (transportCoeff (transportOp (vanVleck g) g gi) 0 (W z x')
          + transportCoeff (transportOp (vanVleck g) g gi) 1 (W z x') * τ))

/-! ###############################################################################
    ### ★ THE COMPATIBILITY BRIDGE — old-chart instantiation recovers `chartFieldAmp` verbatim.
    ############################################################################### -/

/-- **★ `chartFieldAmpWith_uniformInverseChart` — the compatibility bridge.**  Instantiating the
    generic `chartFieldAmpWith` at the OLD concrete chart `uniformInverseChart g gi hC hK` recovers the
    EXISTING `chartFieldAmp` literally.  Pure `rfl` (definitional unfolding) — confirms the
    genericization changed nothing about the existing, banked definition. NOT `a₁ = R/6`. -/
theorem chartFieldAmpWith_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z : Point n) (x' : Point n) :
    chartFieldAmpWith g gi hC hK a b (uniformInverseChart g gi hC hK) τ z x'
      = chartFieldAmp g gi hC hK a b τ z x' := rfl

/-! ###############################################################################
    ### THE NEW-CHART INSTANTIATION — `chartFieldAmp'`.
    ############################################################################### -/

/-- **`chartFieldAmp'` — the NEW-chart instantiation.**  `chartFieldAmpWith` at
    `W := uniformInverseChart' g gi hC hK c` (the derived-jointly-measurable chart, J4-1147/1148/1149),
    for a fixed tube radius `c`.  NOT globally equal to `chartFieldAmp` (the two charts agree only on a
    bounded tube image; see `ThetaChartContDiff.uniformInverseChart'_eqOn_uniformInverseChart`).
    NOT `a₁ = R/6`. -/
noncomputable def chartFieldAmp' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (c : ℝ)
    (τ : ℝ) (z : Point n) (x' : Point n) : ℝ :=
  chartFieldAmpWith g gi hC hK a b (uniformInverseChart' g gi hC hK c) τ z x'

end QIQTH.HeatResidualBound

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms chartFieldAmpWith
#print axioms chartFieldAmpWith_uniformInverseChart
#print axioms chartFieldAmp'
end AxiomChecks
