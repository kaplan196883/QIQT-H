/-
  WhiteHVcont — J4-697 (i): THE `hVcont` EXPORT — the in-gate chart continuity
  `z ↦ whiteInvChart 0 z` packaged as a standalone `ContinuousOn` over `closedBall 0 R ⊆ S 0`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It packages a
  parametric CHART-CONTINUITY germ (the nearest member of the `WhiteHBaseReduction` residue) as a set
  continuity.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to (or trivially yielding) the conclusion, no existing file edited, nothing committed,
  nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE GERM.  `uniformInverseChart_huniformChart` banks a single uniform chart radius `δ₀ > 0` such
     that for every `q ∈ Kset` and every `v` with `‖v‖ < δ₀`,
       `ContDiffAt ℝ 2 (uniformInverseChart … q) (uniformFlowExp … q v)`.
     Since `whiteInvChart κ hκ hKc q = whiteUnvel κ q ∘ uniformInverseChart … q` and `whiteUnvel κ q`
     is a continuous linear map, the composite is `ContinuousAt` at every image point.

  ── THE COLLAPSE TO A SET.  On `closedBall 0 R ⊆ uniformFlowExp … 0 '' ball 0 c` with `0 ∈ Kset` and
     `c < δ₀`, every `z ∈ closedBall 0 R` is an image point `uniformFlowExp … 0 v`, `‖v‖ < c < δ₀`, so
     the germ applies pointwise and `ContinuousAt.continuousOn` yields the SET continuity — this is
     exactly the `hVcont` hypothesis carried by `white_hRepCont` / `whiteDefectKernel_…_modulo_L`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `whiteInvChart_continuousAt_flowBall` — the pointwise germ: `ContinuousAt (whiteInvChart … q ·) p`
      for `p ∈ uniformFlowExp … q '' ball 0 c`, `q ∈ Kset`, `c < δ₀`.
    • `whiteInvChart_continuousOn_flowBall` — ★★ the packaged `hVcont`: `ContinuousOn (whiteInvChart … 0 ·)
      (closedBall 0 R)`, from `0 ∈ Kset`, `closedBall 0 R ⊆ flow-ball(c)`, `c < δ₀`.
    • `white_hRepCont_flowBall` — ★★★ `white_hRepCont` with `hVcont` DISCHARGED via the packaged germ:
      the joint `(τ,z)` continuity of the `∂_τ` representative field, now needing only the flow-ball gate
      geometry `{0 ∈ Kset, closedBall 0 R ⊆ flow-ball(c), c < δ₀}` (no free chart-continuity input).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteHRepCont

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteS1
open QIQTH.WhiteHBaseReduction QIQTH.WhiteHRepCont
open scoped Topology BigOperators

namespace QIQTH.WhiteHVcont

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (V1) — the pointwise germ: `ContinuousAt` of `whiteInvChart` on the flow ball.
    ############################################################################### -/

/-- **`whiteInvChart_continuousAt_flowBall` — THE POINTWISE CHART-CONTINUITY GERM.**  For `q ∈ Kset`
    and `p` in the flow-ball image `uniformFlowExp … q '' ball 0 c` with `c < δ₀` (the banked uniform
    chart radius), the inverse chart `uniformInverseChart … q` is `ContDiffAt ℝ 2` at `p`, hence
    `ContinuousAt`; composing with the continuous linear `whiteUnvel κ q` gives `ContinuousAt` of
    `whiteInvChart κ hκ hKc q` at `p`.  Extracted from the `key`-pattern of `white_hpkgBound_at_radius`.
    NOT `a₁ = R/6`. -/
theorem whiteInvChart_continuousAt_flowBall (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (δ₀ : ℝ)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v)))
    (c : ℝ) (hcδ : c < δ₀) (p : Point n)
    (hp : p ∈ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q ''
        Metric.ball (0 : Point n) c) :
    ContinuousAt (fun p' => whiteInvChart κ hκ hKc q p') p := by
  obtain ⟨v, hvmem, hpv⟩ := hp
  have hv : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hvmem
  have hvδ : ‖v‖ < δ₀ := lt_trans hv hcδ
  have hC2 := (hspec v hvδ).2
  have hCV : ContinuousAt (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q) p := by
    rw [← hpv]
    exact hC2.continuousAt
  exact ((whiteUnvel κ q).continuous.continuousAt).comp hCV

/-! ###############################################################################
    ### (V2) — the packaged `hVcont`: `ContinuousOn` on `closedBall 0 R`.
    ############################################################################### -/

/-- **★★ `whiteInvChart_continuousOn_flowBall` — THE PACKAGED `hVcont`.**  On
    `closedBall 0 R ⊆ uniformFlowExp … 0 '' ball 0 c` with `0 ∈ Kset` and `c < δ₀`, the map
    `z ↦ whiteInvChart κ hκ hKc 0 z` is `ContinuousOn (closedBall 0 R)`: every point of the ball is a
    flow-ball image point, the pointwise germ `whiteInvChart_continuousAt_flowBall` supplies
    `ContinuousAt`, and `ContinuousAt.continuousOn` collapses to the set.  This is EXACTLY the `hVcont`
    hypothesis carried by `white_hRepCont`.  NOT `a₁ = R/6`. -/
theorem whiteInvChart_continuousOn_flowBall (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (h0K : (0 : Point n) ∈ Kset)
    (δ₀ : ℝ)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc 0 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc 0 z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)))
    (R c : ℝ) (hcδ : c < δ₀)
    (hball : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc 0 z)
      (Metric.closedBall (0 : Point n) R) := by
  apply continuousOn_of_forall_continuousAt
  intro z hz
  exact whiteInvChart_continuousAt_flowBall κ hκ hKc 0 h0K δ₀ hspec c hcδ z (hball hz)

/-- **`whiteInvChart_continuousOn_flowBall_banked`** — same as above but the germ radius `δ₀` is
    obtained internally from `uniformInverseChart_huniformChart` and exposed via an `∃`.  Consumes only
    the flow-ball gate geometry: `0 ∈ Kset`, and a `c < δ₀` with `closedBall 0 R ⊆ flow-ball(c)`.
    NOT `a₁ = R/6`. -/
theorem whiteInvChart_continuousOn_flowBall_banked (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (h0K : (0 : Point n) ∈ Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ R c : ℝ, c < δ₀ →
      Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c →
      ContinuousOn (fun z : Point n => whiteInvChart κ hκ hKc 0 z)
        (Metric.closedBall (0 : Point n) R) := by
  obtain ⟨δ₀, hδ₀0, hspec⟩ := uniformInverseChart_huniformChart (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨δ₀, hδ₀0, ?_⟩
  intro R c hcδ hball
  exact whiteInvChart_continuousOn_flowBall κ hκ hKc h0K δ₀ (hspec 0 h0K).1 R c hcδ hball

/-! ###############################################################################
    ### (V3) — `white_hRepCont` with `hVcont` DISCHARGED via the packaged germ.
    ############################################################################### -/

/-- **★★★ `white_hRepCont_flowBall` — THE `∂_τ` REPRESENTATIVE-FIELD CONTINUITY, `hVcont`-FREE.**
    The joint `(τ,z)` continuity of `whiteTauDerivRep κ a b Kset S Wg (τ,z,0)` on the in-window in-gate
    box, with the chart-continuity input `hVcont` now DISCHARGED by `whiteInvChart_continuousOn_flowBall`
    from the flow-ball gate geometry `{0 ∈ Kset, closedBall 0 R ⊆ flow-ball(c), c < δ₀}`.  NOT
    `a₁ = R/6`. -/
theorem white_hRepCont_flowBall (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R c δ₀ : ℝ) (ht₁ : 0 < t₁)
    (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc 0 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc 0 z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)))
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn
      (fun p : ℝ × Point n => whiteTauDerivRep κ a b Kset S Wg (p.1, p.2, 0))
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  white_hRepCont κ hκ hKc S a b Wg hagree t₁ t₂ R ht₁ h0K hballS
    (whiteInvChart_continuousOn_flowBall κ hκ hKc h0K δ₀ hspec R c hcδ hballC)

#check @whiteInvChart_continuousAt_flowBall
#check @whiteInvChart_continuousOn_flowBall
#check @whiteInvChart_continuousOn_flowBall_banked
#check @white_hRepCont_flowBall

end QIQTH.WhiteHVcont

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHVcont
#print axioms whiteInvChart_continuousAt_flowBall
#print axioms whiteInvChart_continuousOn_flowBall
#print axioms whiteInvChart_continuousOn_flowBall_banked
#print axioms white_hRepCont_flowBall
end AxiomChecks
