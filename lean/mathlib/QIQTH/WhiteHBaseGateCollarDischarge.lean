/-
  WhiteHBaseGateCollarDischarge — J4-718: THE ON-GATE COLLAR RESIDUAL, DISCHARGED to the flow-reach
  near-isometry + a named satisfiable radii hypothesis.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` is a
  labelled carrier, untouched).  It closes the ON-GATE collar residual `hgateCollar` of J4-717
  (`WhiteHBaseGateCollar.white_hInnerCont_closed_final5`) down to the banked flow-reach near-isometry
  data plus ONE explicit satisfiable radii inequality `b·(1 + C_D·c) < R`.  No `sorry`, no `admit`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no existing file edited, nothing
  committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE GEOMETRIC VERDICT (why the on-gate residual is now dischargeable, unlike the plain collar).
    On the gate, `p ∈ closure (S 0) ⊆ flowExp₀ '' closedBall 0 c`, so `p = flowExp₀ v` with `‖v‖ ≤ c`,
    and there `whiteInvChart 0 p = v` is the GENUINE inverse (`whiteInvChart_center_eq` + the banked
    uniform-chart germ), NOT junk.  The banked EXP-side displacement `‖flowExp₀ v − v‖ ≤ C_D·‖v‖²`
    (`uniformFlowExp_displacement_bound`, base `0`) gives, via the reverse triangle inequality and
    `‖v‖ ≤ c`, the reach lower bound `‖v‖·(1 + C_D·c) ≥ ‖p‖ ≥ R`.  With the satisfiable
    `b·(1 + C_D·c) < R` this yields the STRICT `b < ‖v‖`, hence `b² < ‖v‖² ≤ rncRadialSq v =
    rncRadialSq (whiteInvChart 0 p)` (`norm_sq_le_rncRadialSq`).  Continuity of the genuine inverse on
    the reach (`ContDiffAt`) upgrades the strict pointwise bound to a NEIGHBOURHOOD via
    `isOpen_Ioi`.  This is EXACTLY the annulus mechanism the banked cover machinery uses
    (`gatedWitness_hEboundW_of_good_gen`), now specialised to base `0` and the on-gate residual.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `white_gate_reach_bundle` — from the base-`0` inverse-chart germ + `C²` package (final5's
      `hspec 0`) and `c < δ₀`: the LEFT-INVERSE `whiteInvChart 0 (flowExp₀ v) = v` and the CONTINUITY
      `ContinuousAt (whiteInvChart 0) (flowExp₀ v)` on the reach `‖v‖ ≤ c`.
    * `closure_gate_subset_image_closedBall` — `closure (S 0) ⊆ flowExp₀ '' closedBall 0 c` from the
      gate reach `S 0 ⊆ flowExp₀ '' ball 0 c` + the banked flow-image closure clause.
    * `white_hgateCollar_of_reach` — ★★ THE MAIN BRICK: the ON-GATE collar `hgateCollar` from the
      left-inverse + continuity + displacement (all on the reach) + `closure (S 0) ⊆ image` + the
      satisfiable `b·(1 + C_D·c) < R`.
    * `white_hgateCollar_numeric_satisfiable` — the radii inequality is INHABITED (non-vacuous).
    * `white_hInnerCont_closed_final6` — ★★★ THE TERMINAL FEED: `white_hInnerCont_closed_final5` with
      `hgateCollar` DISCHARGED in-line.  Surviving analytic residual: `{hnull}` ONLY (+ the standard
      co-instantiated carries) — the on-gate collar is replaced by the banked reach data + the radii
      inequality.

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHBaseGateCollar

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteHJetCont QIQTH.WhiteHBaseExtend
open QIQTH.WhiteHInnerContLegADischarged
open QIQTH.WhiteHBaseCollar
open QIQTH.WhiteHBaseGateCollar
open scoped Topology BigOperators

namespace QIQTH.WhiteHBaseGateCollarDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the reach bundle: left-inverse + continuity of the genuine center chart.
    ############################################################################### -/

/-- **★ `white_gate_reach_bundle`.**  From the base-`0` inverse-chart germ + `C²` package (final5's
    `hspec 0`) and `c < δ₀`, the genuine center chart `whiteInvChart 0` is BOTH a left inverse of the
    flow exp AND continuous on the reach `‖v‖ ≤ c`.  Uses the center grounding
    `whiteInvChart_center_eq` (whitening is trivial at the center).  NOT `a₁ = R/6`. -/
theorem white_gate_reach_bundle (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (c δ₀ : ℝ) (hcδ : c < δ₀)
    (hspec0 : ∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc 0 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc 0 z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)) :
    (∀ v : Point n, ‖v‖ ≤ c →
        whiteInvChart κ hκ hKc 0
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v) = v)
    ∧ (∀ v : Point n, ‖v‖ ≤ c →
        ContinuousAt (whiteInvChart κ hκ hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)) := by
  have hfun : whiteInvChart κ hκ hKc 0
      = uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 :=
    funext (fun p => whiteInvChart_center_eq κ hκ hKc p)
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨hgerm, _⟩ := hspec0 v (lt_of_le_of_lt hv hcδ)
    rw [hfun]; exact hgerm.eq_of_nhds
  · intro v hv
    obtain ⟨_, hC2⟩ := hspec0 v (lt_of_le_of_lt hv hcδ)
    rw [hfun]; exact hC2.continuousAt

/-! ###############################################################################
    ### §B — closure of the gate ⊆ closed flow-ball image.
    ############################################################################### -/

/-- **`closure_gate_subset_image_closedBall`.**  From the gate reach `S 0 ⊆ flowExp₀ '' ball 0 c` and
    the banked flow-image closure clause `closure (flowExp₀ '' ball 0 c) ⊆ flowExp₀ '' closedBall 0 c`,
    `closure (S 0) ⊆ flowExp₀ '' closedBall 0 c`.  NOT `a₁ = R/6`. -/
theorem closure_gate_subset_image_closedBall (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (c : ℝ)
    (hSreach0 : S 0 ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc 0 '' Metric.ball 0 c)
    (hclosclause : closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0 '' Metric.ball 0 c)
      ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.closedBall 0 c) :
    closure (S 0) ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc 0 '' Metric.closedBall 0 c :=
  fun p hp => hclosclause (closure_mono hSreach0 hp)

/-! ###############################################################################
    ### §C — ★★ THE MAIN BRICK: the on-gate collar from the reach near-isometry.
    ############################################################################### -/

/-- **★★ `white_hgateCollar_of_reach`.**  The ON-GATE collar `hgateCollar` of J4-717 — for every
    `p ∈ closure (S 0)` with `R ≤ ‖p‖`, the cutoff collar
    `{p' | b² ≤ rncRadialSq (whiteInvChart 0 p')} ∈ 𝓝 p` — from the banked flow-reach data:
      * `hleft`  : `whiteInvChart 0 (flowExp₀ v) = v`  on `‖v‖ ≤ c`  (genuine inverse on the reach);
      * `hcont`  : `ContinuousAt (whiteInvChart 0) (flowExp₀ v)`  on `‖v‖ ≤ c`;
      * `hdisp`  : `‖flowExp₀ v − v‖ ≤ C_D·‖v‖·‖v‖`  on `‖v‖ ≤ c`  (EXP-side displacement, base 0);
      * `hclos`  : `closure (S 0) ⊆ flowExp₀ '' closedBall 0 c`;
      * `hbR`    : `b·(1 + C_D·c) < R`  (the SATISFIABLE radii inequality — cutoff small vs reach).
    On `p = flowExp₀ v` (`‖v‖ ≤ c`), `whiteInvChart 0 p = v`; the reverse triangle + displacement give
    `‖v‖·(1 + C_D·c) ≥ ‖p‖ ≥ R > b·(1 + C_D·c)`, hence `b < ‖v‖`, so `b² < ‖v‖² ≤ rncRadialSq v`;
    continuity upgrades the strict bound to the neighbourhood.  NOT `a₁ = R/6`. -/
theorem white_hgateCollar_of_reach (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (b R c C_D : ℝ)
    (hb0 : 0 ≤ b) (hCD0 : 0 ≤ C_D)
    (hleft : ∀ v : Point n, ‖v‖ ≤ c →
        whiteInvChart κ hκ hKc 0
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v) = v)
    (hcont : ∀ v : Point n, ‖v‖ ≤ c →
        ContinuousAt (whiteInvChart κ hκ hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v))
    (hdisp : ∀ v : Point n, ‖v‖ ≤ c →
        ‖uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v - v‖
          ≤ C_D * ‖v‖ * ‖v‖)
    (hclos : closure (S 0) ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc 0 '' Metric.closedBall 0 c)
    (hbR : b * (1 + C_D * c) < R) :
    ∀ p : Point n, R ≤ ‖p‖ → p ∈ closure (S 0) →
      {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p := by
  intro p hRp hpcl
  obtain ⟨v, hvmem, hEv⟩ := hclos hpcl
  rw [Metric.mem_closedBall, dist_zero_right] at hvmem
  have hc0 : 0 ≤ c := le_trans (norm_nonneg v) hvmem
  -- the genuine inverse pins `whiteInvChart 0 p = v`.
  have hV0p : whiteInvChart κ hκ hKc 0 p = v := by rw [← hEv]; exact hleft v hvmem
  -- displacement at `v`, transported to `p`.
  have hd := hdisp v hvmem
  rw [hEv] at hd
  -- reverse triangle: `‖p‖ ≤ ‖v‖ + ‖p − v‖`.
  have heq : v + (p - v) = p := by abel
  have hrev : ‖p‖ ≤ ‖v‖ + ‖p - v‖ := by
    calc ‖p‖ = ‖v + (p - v)‖ := by rw [heq]
      _ ≤ ‖v‖ + ‖p - v‖ := norm_add_le _ _
  -- `C_D·‖v‖² ≤ C_D·c·‖v‖` from `‖v‖ ≤ c`.
  have hCDsq : C_D * ‖v‖ * ‖v‖ ≤ C_D * c * ‖v‖ := by
    nlinarith [hvmem, hCD0, norm_nonneg v, mul_nonneg hCD0 (norm_nonneg v)]
  -- reach lower bound: `R ≤ ‖v‖·(1 + C_D·c)`.
  have hRle : R ≤ ‖v‖ * (1 + C_D * c) := by nlinarith [hRp, hrev, hd, hCDsq]
  have hpos : (0 : ℝ) < 1 + C_D * c := by
    have : (0 : ℝ) ≤ C_D * c := mul_nonneg hCD0 hc0; linarith
  -- STRICT `b < ‖v‖`.
  have hblt : b * (1 + C_D * c) < ‖v‖ * (1 + C_D * c) := lt_of_lt_of_le hbR hRle
  have hbv : b < ‖v‖ := lt_of_mul_lt_mul_right hblt hpos.le
  -- `b² < rncRadialSq (whiteInvChart 0 p)`.
  have hbsq : b ^ 2 < ‖v‖ ^ 2 := by nlinarith [hbv, hb0, norm_nonneg v]
  have hnormsq : ‖v‖ ^ 2 ≤ rncRadialSq v := norm_sq_le_rncRadialSq v
  have hstrict : b ^ 2 < rncRadialSq (whiteInvChart κ hκ hKc 0 p) := by
    rw [hV0p]; linarith [hbsq, hnormsq]
  -- continuity upgrades the strict bound to a neighbourhood.
  have hcp : ContinuousAt (whiteInvChart κ hκ hKc 0) p := by rw [← hEv]; exact hcont v hvmem
  have hgcont : ContinuousAt
      (fun p' => rncRadialSq (whiteInvChart κ hκ hKc 0 p')) p :=
    (rncRadialSq_contDiff.continuous.continuousAt).comp hcp
  have hnhds : {p' : Point n | b ^ 2 < rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p :=
    hgcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hstrict)
  apply Filter.mem_of_superset hnhds
  intro p' hp'
  simp only [Set.mem_setOf_eq] at hp' ⊢
  exact le_of_lt hp'

/-- **`white_hgateCollar_numeric_satisfiable`** (cp466 discipline).  The radii inequality of the main
    brick is INHABITED: `b = 1, c = 2, C_D = 0, R = 2` gives `0 ≤ b`, `0 ≤ C_D`, `b < c` and
    `b·(1 + C_D·c) = 1 < 2 = R`.  So the discharge is NOT a vacuously-false regime.  NOT `a₁ = R/6`. -/
theorem white_hgateCollar_numeric_satisfiable :
    ∃ b c C_D R : ℝ, 0 ≤ b ∧ 0 ≤ C_D ∧ b < c ∧ b * (1 + C_D * c) < R := by
  refine ⟨1, 2, 0, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ###############################################################################
    ### §D — ★★★ THE TERMINAL FEED — final5 with `hgateCollar` DISCHARGED.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_closed_final6` (THE TERMINAL FEED).**  Same conclusion as
    `WhiteHBaseGateCollar.white_hInnerCont_closed_final5`, but the ON-GATE collar `hgateCollar` is
    BUILT in-line from `white_hgateCollar_of_reach`: the reach left-inverse + continuity come from
    `white_gate_reach_bundle` (using the base-`0` germ `hspec 0` and `c < δ₀`), the gate-closure ⊆
    image from `closure_gate_subset_image_closedBall`, and the near-isometry from the banked base-`0`
    displacement `hdisp0` + the satisfiable radii inequality `hbR`.
    ⚠ CONDITIONAL on the certificate list; the SURVIVING analytic residual is `hnull` (the flow-gate
    null-frontier cert) — the on-gate collar is now the banked reach data + `hbR`.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final6 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    -- A. co-instantiated width-`whiteLam` pkg / S1 / value data
    (C : ℝ) (hC0 : 0 ≤ C)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (whiteLam κ hκ hKc) 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (hWmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      whiteGatedWitness κ hκ hKc S a b w.1 w.2.1 w.2.2))
    (wA Cpre A₀ A₁ : ℝ) (hwA0 : 0 < wA) (hCpre0 : 0 ≤ Cpre) (hA₀0 : 0 ≤ A₀) (hA₁0 : 0 ≤ A₁)
    (hval : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |whiteGatedWitness κ hκ hKc S a b τ p q|
        ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q))
    -- B. the null-frontier cert
    (hnull : ∀ z₀ : Point n, volume {w : Point n | z₀ ∈ frontier (S w)} = 0)
    -- C. the `hlegA` DISCHARGE cert (reach substrate inputs)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (c δ₀ : ℝ) (hcδ : c < δ₀)
    (hSopen : ∀ w : Point n, w ∈ Kset → IsOpen (S w))
    (hSreach : ∀ w : Point n, w ∈ Kset →
        S w ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w ''
          Metric.ball (0 : Point n) c)
    (hspec : ∀ w : Point n, w ∈ Kset →
        (∀ v : Point n, ‖v‖ < δ₀ →
          (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc w (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) hKc w z)) =ᶠ[nhds v] (fun z => z) ∧
          ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc w)
            (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc w v)))
    -- D. the `hbase` COMBINED-PRODUCER certs (base-0 flow-ball reach)
    (R : ℝ) (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    -- D'. the ON-GATE collar DISCHARGE certs (reach near-isometry + closure clause + radii)
    (C_D : ℝ) (hCD0 : 0 ≤ C_D)
    (hdisp0 : ∀ v : Point n, ‖v‖ ≤ c →
        ‖uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v - v‖
          ≤ C_D * ‖v‖ * ‖v‖)
    (hclosclause : closure (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0 '' Metric.ball 0 c)
      ⊆ uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.closedBall 0 c)
    (hbR : b * (1 + C_D * c) < R)
    -- E. window
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) := by
  have hb0 : 0 ≤ b := le_of_lt (lt_trans ha hab)
  have hbundle := white_gate_reach_bundle κ hκ hKc c δ₀ hcδ (hspec 0 h0K)
  have hclos := closure_gate_subset_image_closedBall κ hκ hKc S c (hSreach 0 h0K) hclosclause
  have hgateCollar := white_hgateCollar_of_reach κ hκ hKc S b R c C_D hb0 hCD0
    hbundle.1 hbundle.2 hdisp0 hclos hbR
  exact white_hInnerCont_closed_final5 hn κ hκ hKc S a b ha hab C hC0 hpkg hEmeas hWmeas
    wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval hnull Wg hagree c δ₀ hcδ hSopen hSreach hspec
    R h0K hballS hballC hgateCollar Uwin hU1

#check @white_gate_reach_bundle
#check @closure_gate_subset_image_closedBall
#check @white_hgateCollar_of_reach
#check @white_hgateCollar_numeric_satisfiable
#check @white_hInnerCont_closed_final6

end QIQTH.WhiteHBaseGateCollarDischarge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHBaseGateCollarDischarge
#print axioms white_gate_reach_bundle
#print axioms closure_gate_subset_image_closedBall
#print axioms white_hgateCollar_of_reach
#print axioms white_hgateCollar_numeric_satisfiable
#print axioms white_hInnerCont_closed_final6
end AxiomChecks
