/-
  VanVleckGatedWitnessWith — J4-1156: Phase 1, Task A of the chart-parametric rebuild campaign
  (dispatch 1 of the newly-authorized full rebuild; per `gpt-5.6-sol`'s 33rd consult, 2026-08-24).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes `ConvApproximants.vanVleckGatedWitness` — the SECOND of the exactly TWO root definitions
  in the whole campaign that call the concrete chart `uniformInverseChart` DIRECTLY (not transitively)
  — over an ABSTRACT chart argument `W : Point n → Point n → Point n`, then instantiates the generic
  version twice: once at the OLD chart (bridged back to the existing `vanVleckGatedWitness` via a
  `rfl`-level compatibility theorem) and once at the NEW, jointly-measurable chart
  `uniformInverseChart'` (`ThetaMeasurableEmbedding.lean`, J4-1147).  `vanVleckGatedWitness` is
  UNUSUALLY CHEAP to genericize: `globalCutoffParametrixWitnessN` (its own callee) is ALREADY
  chart-generic — it takes the chart as an explicit `Vmap : Point n → Point n → Point n` argument, with
  no `uniformInverseChart` reference anywhere in its own body (confirmed by direct read,
  `OrderNResidual.lean:148-150`) — so genericizing `vanVleckGatedWitness` is a one-argument threading,
  not a rebuild.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no
  existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `vanVleckGatedWitnessWith` — the chart-generic sibling of `vanVleckGatedWitness`: the SAME
      `gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g) (transportCoeff …) a b …)` body,
      with the trailing `Vmap` argument threaded as the abstract `W` instead of the concrete
      `uniformInverseChart g gi hC hK`.

    * `vanVleckGatedWitnessWith_uniformInverseChart` — ★ THE COMPATIBILITY BRIDGE: instantiating the
      generic definition at `W := uniformInverseChart g gi hC hK` recovers the EXISTING
      `vanVleckGatedWitness` literally (`rfl`).

    * `vanVleckGatedWitness'` — the NEW-chart instantiation: `vanVleckGatedWitnessWith` at
      `W := uniformInverseChart' g gi hC hK c`.

  ## WHAT THIS DOES NOT DO.
  This file does NOT prove any relationship between `vanVleckGatedWitness'` and `vanVleckGatedWitness`
  beyond what the generic definition trivially gives — it does NOT claim global equality (false in
  general; the two charts agree only on a bounded tube image). It does not build the derivative-chain
  analogues (`witnessFieldDeriv`/`witnessFieldDeriv2`-shaped siblings, Phase 2 of the rebuild plan; see
  `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`) and does not touch the measurability/audit chain
  (Phase 4) — this file is Phase 1 only.

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.ConvApproximants
import QIQTH.ThetaChartGatedInstantiation

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ThetaMeasurableEmbedding
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ###############################################################################
    ### THE CHART-GENERIC SIBLING — `vanVleckGatedWitnessWith`.
    ############################################################################### -/

/-- **`vanVleckGatedWitnessWith` — the chart-generic sibling of `vanVleckGatedWitness`.**  Literally
    the same body, with the `Vmap` argument of `globalCutoffParametrixWitnessN` threaded as an ABSTRACT
    chart `W : Point n → Point n → Point n` instead of the concrete `uniformInverseChart g gi hC hK`.
    Pure data — no chart-property hypotheses attached. NOT `a₁ = R/6`. -/
noncomputable def vanVleckGatedWitnessWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (W : Point n → Point n → Point n) :
    ℝ → Point n → Point n → ℝ :=
  gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) a b W)

/-! ###############################################################################
    ### ★ THE COMPATIBILITY BRIDGE — old-chart instantiation recovers `vanVleckGatedWitness` verbatim.
    ############################################################################### -/

/-- **★ `vanVleckGatedWitnessWith_uniformInverseChart` — the compatibility bridge.**  Instantiating
    the generic `vanVleckGatedWitnessWith` at the OLD concrete chart `uniformInverseChart g gi hC hK`
    recovers the EXISTING `vanVleckGatedWitness` literally.  Pure `rfl`.  NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitnessWith_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) :
    vanVleckGatedWitnessWith g gi hC hK S a b (uniformInverseChart g gi hC hK)
      = vanVleckGatedWitness g gi hC hK S a b := rfl

/-! ###############################################################################
    ### THE NEW-CHART INSTANTIATION — `vanVleckGatedWitness'`.
    ############################################################################### -/

/-- **`vanVleckGatedWitness'` — the NEW-chart instantiation.**  `vanVleckGatedWitnessWith` at
    `W := uniformInverseChart' g gi hC hK c` (the derived-jointly-measurable chart, J4-1147/1148/1149),
    for a fixed tube radius `c`.  NOT globally equal to `vanVleckGatedWitness`.  NOT `a₁ = R/6`. -/
noncomputable def vanVleckGatedWitness' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (c : ℝ) :
    ℝ → Point n → Point n → ℝ :=
  vanVleckGatedWitnessWith g gi hC hK S a b (uniformInverseChart' g gi hC hK c)

end QIQTH.HeatResidualBound

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms vanVleckGatedWitnessWith
#print axioms vanVleckGatedWitnessWith_uniformInverseChart
#print axioms vanVleckGatedWitness'
end AxiomChecks
