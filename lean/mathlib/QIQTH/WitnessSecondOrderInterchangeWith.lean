/-
  WitnessSecondOrderInterchangeWith — J4-1159: Phase 3 (opening dispatch) of the chart-parametric
  rebuild campaign, closing the item J4-1158 deliberately deferred from Phase 2 Task B.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes `EngineInstantiation.witness_secondOrder_interchange` (E3, "THE ENGINE INSTANTIATION")
  over an ABSTRACT chart `W`, per `docs/qg_roadmap/CHART_PARAMETRIC_REBUILD_PLAN.md`, threading through
  `WitnessFieldDerivWith.lean` (J4-1157) and `WitnessFieldDerivConsumersWith.lean` (J4-1158).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY NO `heatConvFrozenWith` WAS NEEDED (correcting J4-1158's own forward note).

  J4-1158 flagged `witness_secondOrder_interchange` as needing "a `heatConvFrozenWith`, Phase 3/4
  territory", reasoning that its statement threads `heatConvFrozen (vanVleckGatedWitness …) F u b x 0`
  DIRECTLY. Direct re-inspection of `heatConvFrozen` (`HeatDuhamel.lean:135`) and its consumer
  `pd_pd_heatConvFrozen_interchange` (`SecondOrderInterchange.lean:227`) shows BOTH are ALREADY fully
  chart-generic: `heatConvFrozen` is `noncomputable def heatConvFrozen (A B : ℝ → Point n → Point n →
  ℝ) (τ₀ t : ℝ) (x y : Point n) : ℝ := ∫ s in (0)..t, (∫ z, A (τ₀ - s) x z * B s z y)` — it takes an
  ARBITRARY function `A`, never calling `uniformInverseChart` (or any chart) in its own body, and
  `pd_pd_heatConvFrozen_interchange` likewise quantifies over arbitrary `H dH dHH F : ℝ → Point n →
  Point n → ℝ`. The chart-hardwiring in `witness_secondOrder_interchange` lives ENTIRELY in the
  CONCRETE ARGUMENTS fed into these generic engines (`vanVleckGatedWitness`, `witnessFieldDeriv`,
  `witnessFieldDeriv2`, `witnessSecondXDeriv`), not in the engines themselves. So no new `...With`
  definition for `heatConvFrozen` is needed at all — substituting the ALREADY-BUILT
  `vanVleckGatedWitnessWith`/`witnessFieldDerivWith`/`witnessFieldDeriv2With`/`witnessSecondXDerivWith`
  (J4-1156/1157/1158) for the concrete roots suffices. This closes the Task B item as pure mechanical
  threading, one layer up the chain — matching the pattern of the other six Task B theorems (the
  ingredients the proof leans on were already chart-independent).

  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `witness_secondOrder_interchangeWith` — chart-generic sibling of
      `EngineInstantiation.witness_secondOrder_interchange` (E3), at the ABSTRACT chart `W`: feeds
      `witnessFieldDerivWith`/`witnessFieldDeriv2With` into `pd_pd_heatConvFrozen_interchange`, then
      identifies the center via `witnessFieldDeriv2With_center` (J4-1158). Proof mirrors the old one
      EXACTLY, `W` substituted for `uniformInverseChart g gi hC hK` throughout.

    * `witness_secondOrder_interchange'` — the PRIMED instantiation at
      `W := uniformInverseChart' g gi hC hK c` (J4-1147/1148/1149): the second-order interchange for
      the NEW, jointly-measurable chart, concluding about `witnessSecondXDerivWith … W'`.

  This closes Phase 2 Task B's deferred item 7 in full (all 7 `EngineInstantiation.lean` consumer
  theorems whose statement names `witnessFieldDeriv`/`witnessFieldDeriv2` are now genericized+primed)
  and is itself Phase 3 material (rebuilding a local analytic/derivative supplier — the second-order
  interchange chain — purely in terms of generic/primed objects, per the plan's Phase 3 Task C).

  ## WHAT THIS DOES NOT DO.
  Does NOT claim `witness_secondOrder_interchange' = witness_secondOrder_interchange` or any global
  old/new chart equality (false in general). Does not touch the measurability/audit chain (Phase 4).
  Does not attempt Canary C2 (`FirstHWMConsumerPrime`) — this file supplies no `hWmeas` discharge.

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.WitnessFieldDerivConsumersWith
import QIQTH.SecondOrderInterchange

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel
open QIQTH.ThetaMeasurableEmbedding
open scoped Interval Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### `witness_secondOrder_interchangeWith` — chart-generic sibling of E3.
    ############################################################################### -/

/-- **`witness_secondOrder_interchangeWith`.**  Chart-generic sibling of
    `EngineInstantiation.witness_secondOrder_interchange`: feeding `witnessFieldDerivWith`/
    `witnessFieldDeriv2With` (built from `vanVleckGatedWitnessWith` at the ABSTRACT chart `W`) into
    `pd_pd_heatConvFrozen_interchange` (already fully chart-generic), the second-order coordinate
    differentiation passes under the double space-time integral, at any gap `b`. NOT `a₁ = R/6`. -/
theorem witness_secondOrder_interchangeWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut : ℝ)
    (W : Point n → Point n → Point n)
    (F : ℝ → Point n → Point n → ℝ) (u b : ℝ) (i : Fin n)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (hQ1 : ∀ y ∈ V,
      pd (fun x => heatConvFrozen (vanVleckGatedWitnessWith g gi hC hK S acut bcut W) F u b x 0) i y
        = ∫ s in (0)..b, ∫ z, witnessFieldDerivWith g gi hC hK S acut bcut i (u - s) y z W * F s z 0)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 ((0 : Point n) i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDerivWith g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z W * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, witnessFieldDerivWith g gi hC hK S acut bcut i (u - s) (0 : Point n) z W * F s z 0)
      volume 0 b)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv2With g gi hC hK S acut bcut i (u - s) (0 : Point n) z W * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 b)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      ‖∫ z, witnessFieldDeriv2With g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z W * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, witnessFieldDerivWith g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z W * F s z 0)
        (∫ z, witnessFieldDeriv2With g gi hC hK S acut bcut i (u - s)
          (Function.update (0 : Point n) i w) z W * F s z 0) w) :
    pd (fun y => pd
        (fun x => heatConvFrozen (vanVleckGatedWitnessWith g gi hC hK S acut bcut W) F u b x 0) i y) i 0
      = ∫ s in (0)..b, ∫ z, witnessSecondXDerivWith g gi hC hK S acut bcut i (u - s) z W * F s z 0 := by
  have h := pd_pd_heatConvFrozen_interchange (vanVleckGatedWitnessWith g gi hC hK S acut bcut W)
    (fun τ x z => witnessFieldDerivWith g gi hC hK S acut bcut i τ x z W)
    (fun τ x z => witnessFieldDeriv2With g gi hC hK S acut bcut i τ x z W) F
    u b i V hVopen hV0 hQ1 snb hsnb hFmeas hFint hF'meas bound hbdd hbound hdiff
  rw [h]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  show witnessFieldDeriv2With g gi hC hK S acut bcut i (u - s) 0 z W * F s z 0
      = witnessSecondXDerivWith g gi hC hK S acut bcut i (u - s) z W * F s z 0
  rw [witnessFieldDeriv2With_center]

/-! ###############################################################################
    ### `witness_secondOrder_interchange'` — the PRIMED instantiation.
    ############################################################################### -/

/-- **`witness_secondOrder_interchange'`.**  Instantiating `witness_secondOrder_interchangeWith` at
    `W := uniformInverseChart' g gi hC hK c`: the second-order interchange for the NEW,
    jointly-measurable chart. NOT `a₁ = R/6`. -/
theorem witness_secondOrder_interchange' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (acut bcut c : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u b : ℝ) (i : Fin n)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (hQ1 : ∀ y ∈ V,
      pd (fun x => heatConvFrozen
          (vanVleckGatedWitnessWith g gi hC hK S acut bcut (uniformInverseChart' g gi hC hK c))
          F u b x 0) i y
        = ∫ s in (0)..b, ∫ z, witnessFieldDeriv' g gi hC hK S acut bcut c i (u - s) y z * F s z 0)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 ((0 : Point n) i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv' g gi hC hK S acut bcut c i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, witnessFieldDeriv' g gi hC hK S acut bcut c i (u - s) (0 : Point n) z * F s z 0)
      volume 0 b)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, witnessFieldDeriv2' g gi hC hK S acut bcut c i (u - s) (0 : Point n) z * F s z 0)
      (volume.restrict (Set.uIoc 0 b)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 b)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      ‖∫ z, witnessFieldDeriv2' g gi hC hK S acut bcut c i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, witnessFieldDeriv' g gi hC hK S acut bcut c i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0)
        (∫ z, witnessFieldDeriv2' g gi hC hK S acut bcut c i (u - s)
          (Function.update (0 : Point n) i w) z * F s z 0) w) :
    pd (fun y => pd
        (fun x => heatConvFrozen
          (vanVleckGatedWitnessWith g gi hC hK S acut bcut (uniformInverseChart' g gi hC hK c))
          F u b x 0) i y) i 0
      = ∫ s in (0)..b, ∫ z, witnessSecondXDerivWith g gi hC hK S acut bcut i (u - s) z
          (uniformInverseChart' g gi hC hK c) * F s z 0 := by
  unfold witnessFieldDeriv' at hQ1 hFmeas hFint hdiff
  unfold witnessFieldDeriv2' at hF'meas hbound hdiff
  exact witness_secondOrder_interchangeWith g gi hC hK S acut bcut
    (uniformInverseChart' g gi hC hK c) F u b i V hVopen hV0 hQ1 snb hsnb hFmeas hFint hF'meas
    bound hbdd hbound hdiff

end QIQTH.HeatResidualBound

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms witness_secondOrder_interchangeWith
#print axioms witness_secondOrder_interchange'
end AxiomChecks
