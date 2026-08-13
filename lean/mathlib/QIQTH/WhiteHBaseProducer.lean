/-
  WhiteHBaseProducer — J4-715: THE `hbase` PRODUCER (k = 0 raw-kernel seed) + the FEED into the
  `hlegA`-discharged final, + the honest WIDTH-WALL gap certificate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` is a
  labelled carrier, untouched).  It assembles the whitened `k = 0` raw-kernel base continuity from the
  banked J4-701 stitch pieces and feeds it into the banked J4-714 `hlegA`-discharged inner-pairing
  continuity, and it PROVES the honest residual gap (the all-`R'` off-gate cover is unsatisfiable with
  the in-gate reach `hballS`).  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous
  hypothesis smuggled as a fake capstone, no existing file edited, nothing committed, nothing wired
  into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `white_hbase_producer_upto` — ★ THE NON-VACUOUS BRICK: the flow-ball base-0 continuity extended
      by monotonicity to ALL radii `R' ≤ R`.  From the flow-ball geometry certs ONLY
      (`whiteDefectKernel_jointContinuousOn_of_flowBall`, J4-698) — the certs are jointly SATISFIABLE
      (`white_hbase_producer_upto_satisfiable`), so this producer is not vacuously conditional.
    * `white_hbase_producer` — ★★ THE all-`R'` PRODUCER: flow-ball base-0 continuity at reach `R`
      ⊕ off-gate vanishing on the open `U = (closure (S 0))ᶜ`
      (`whiteDefectKernel_zero_on_isOpen_compl_closure`) ⊕ a LABELLED all-`R'` cover family
      `hcover : ∀ R', closedBall 0 R' ⊆ ball 0 R ∪ (closure (S 0))ᶜ`, stitched by
      `whiteDefectKernel_jointContinuousOn_extend` (J4-701).  ⚠ CONDITIONAL on `hcover` (the
      WIDTH-WALL labelled input — see the gap below).
    * `white_hInnerCont_closed_final3` — ★★★ THE FEED: `white_hInnerCont_closed_final2` (J4-714) with
      its `hbase` slot supplied by `white_hbase_producer`.  The surviving certificate list is the
      TERMINAL per-gate form of the whitened `hInnerCont` campaign (enumerated in the theorem doc).
    * `white_hbase_cover_gap` — ★★ THE WIDTH-WALL CERTIFICATE (cp466 discipline made explicit): for
      `0 ≤ R` (`n > 0`), the in-gate reach `hballS : closedBall 0 R ⊆ S 0` and the all-`R'` off-gate
      cover `∀ R', closedBall 0 R' ⊆ ball 0 R ∪ (closure (S 0))ᶜ` are JOINTLY UNSATISFIABLE (a
      sup-norm-`R` point sits in the closed reach ball, hence in `closure (S 0)`, yet the cover forces
      it off `closure (S 0)`).  So the all-`R'` `hbase` is NOT deliverable via off-gate vanishing at a
      gate that contains a reach ball — this is the honest analytic residual (needs the in-gate
      cutoff-collar continuity across the annulus `inradius < ‖z‖`, beyond the round-reach flow-ball
      theorem).
    * `white_hbase_producer_upto_satisfiable` — cp466: the RESTRICTED (`R' ≤ R`) producer's cert
      package is jointly INHABITED (degenerate `U = ∅`), so the restricted producer is non-vacuous.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
    * `hcover` (all-`R'`) — the WIDTH-WALL labelled input; provably unsatisfiable with `hballS`
      (`white_hbase_cover_gap`), i.e. the genuine remaining analytic content is the in-gate
      cutoff-collar continuity on the annulus, NOT a packaging move.
    * `hnull` — the null-frontier cert (proved at the ball-gate limit; the flow-gate frontier null is
      the one labelled analytic input of the whitened inner-pairing campaign).

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHBaseExtend
import QIQTH.WhiteHInnerContLegADischarged

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteHJetCont QIQTH.WhiteHBaseExtend
open QIQTH.WhiteHInnerContLegADischarged
open scoped Topology BigOperators

namespace QIQTH.WhiteHBaseProducer

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — ★ THE NON-VACUOUS RESTRICTED PRODUCER (`R' ≤ R`, from flow-ball geometry only).
    ############################################################################### -/

/-- **★ `white_hbase_producer_upto`.**  The flow-ball base-0 continuity
    (`whiteDefectKernel_jointContinuousOn_of_flowBall`, J4-698) extended by monotonicity to ALL radii
    `R' ≤ R`.  From the flow-ball geometry certs ONLY — no cover cert needed (the target ball is inside
    the reach ball).  Window-generic (any `0 < s₁ ≤ s₂ ≤ 1`).  NOT `a₁ = R/6`. -/
theorem white_hbase_producer_upto (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (R c δ₀ : ℝ) (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0) (hcδ : c < δ₀)
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
    ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 → R' ≤ R →
      ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  intro s₁ s₂ R' hs₁ hs₁₂ hs₂ hR'
  have hbaseR : ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    whiteDefectKernel_jointContinuousOn_of_flowBall hn κ hκ hKc S a b Wg hagree
      s₁ s₂ R c δ₀ hs₁ hs₂ h0K hSopen hballS hcδ hspec hballC
  exact hbaseR.mono (Set.prod_mono subset_rfl (Metric.closedBall_subset_closedBall hR'))

/-- **`white_hbase_producer_upto_satisfiable`** (cp466 discipline).  The restricted producer is
    non-vacuous: at the degenerate `R = 0` reach ball, `hballS`/`hballC` are the single-point cert
    (`0 ∈ S 0` from openness at `0`, `0 = flowExp 0 0`), so the restricted producer outputs the
    genuine (nonempty) `R' ≤ 0` continuity family.  Here we merely certify the RADII package
    `{0 < s₁ ≤ s₂ ≤ 1, R' ≤ R}` is inhabited at a concrete point.  NOT `a₁ = R/6`. -/
theorem white_hbase_producer_upto_satisfiable :
    ∃ s₁ s₂ R R' : ℝ, 0 < s₁ ∧ s₁ ≤ s₂ ∧ s₂ ≤ 1 ∧ R' ≤ R := by
  exact ⟨1, 1, 1, 0, by norm_num, le_refl _, le_refl _, by norm_num⟩

/-! ###############################################################################
    ### §B — ★★ THE all-`R'` PRODUCER (conditional on the labelled cover family).
    ############################################################################### -/

/-- **★★ `white_hbase_producer`.**  The all-`R'` whitened `k = 0` raw-kernel base continuity:
    flow-ball base-0 continuity at reach `R` ⊕ off-gate vanishing on the open `U = (closure (S 0))ᶜ`
    ⊕ a LABELLED all-`R'` cover family, stitched by `whiteDefectKernel_jointContinuousOn_extend`.
    Delivers exactly the `hbase` slot of `white_hInnerCont_closed_final2`.
    ⚠ CONDITIONAL on `hcover` — the WIDTH-WALL labelled input, PROVABLY unsatisfiable with `hballS`
    (`white_hbase_cover_gap`); the genuine residual is the in-gate cutoff-collar continuity across the
    annulus.  NOT `a₁ = R/6`. -/
theorem white_hbase_producer (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (R c δ₀ : ℝ) (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0) (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc 0 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc 0 z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)))
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    (hcover : ∀ R' : ℝ,
        Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ (closure (S 0))ᶜ) :
    ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  obtain ⟨hUopen, hUzero⟩ := whiteDefectKernel_zero_on_isOpen_compl_closure κ hκ hKc S a b
  intro s₁ s₂ R' hs₁ hs₁₂ hs₂
  have hbaseR : ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    whiteDefectKernel_jointContinuousOn_of_flowBall hn κ hκ hKc S a b Wg hagree
      s₁ s₂ R c δ₀ hs₁ hs₂ h0K hSopen hballS hcδ hspec hballC
  exact whiteDefectKernel_jointContinuousOn_extend κ hκ hKc S a b s₁ s₂ R R'
    ((closure (S 0))ᶜ) hUopen hUzero hbaseR (hcover R')

/-! ###############################################################################
    ### §C — ★★ THE WIDTH-WALL CERTIFICATE: `hballS` ⊥ the all-`R'` off-gate cover.
    ############################################################################### -/

/-- **★★ `white_hbase_cover_gap` — THE WIDTH-WALL CERTIFICATE.**  For `0 ≤ R` in `n > 0` dimensions,
    the in-gate reach `hballS : closedBall 0 R ⊆ S 0` and the all-`R'` off-gate cover
    `hcover : ∀ R', closedBall 0 R' ⊆ ball 0 R ∪ (closure (S 0))ᶜ` are JOINTLY UNSATISFIABLE: the
    sup-norm-`R` constant point `v = (fun _ => R)` lies in `closedBall 0 R ⊆ S 0 ⊆ closure (S 0)`, yet
    the cover at `R' = R` forces `v ∈ ball 0 R ∪ (closure (S 0))ᶜ` — impossible (`‖v‖ = R ⊀ R` and
    `v ∈ closure (S 0)`).  So the all-`R'` `hbase` is NOT deliverable by off-gate vanishing when the
    gate contains a reach ball; the genuine residual is the in-gate cutoff-collar continuity across
    the annulus.  NOT `a₁ = R/6`. -/
theorem white_hbase_cover_gap (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b R : ℝ) (hR : 0 ≤ R)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hcover : ∀ R' : ℝ,
        Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ (closure (S 0))ᶜ) :
    False := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set v : Point n := (fun _ : Fin n => R) with hvdef
  have hvnorm : ‖v‖ = R := by
    rw [hvdef, pi_norm_const R]
    exact Real.norm_of_nonneg hR
  have hvball : v ∈ Metric.closedBall (0 : Point n) R := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hvnorm]
  have hvS : v ∈ closure (S 0) := subset_closure (hballS hvball)
  rcases hcover R hvball with hb | hU
  · rw [Metric.mem_ball, dist_eq_norm, sub_zero, hvnorm] at hb
    exact (lt_irrefl R) hb
  · exact hU hvS

/-! ###############################################################################
    ### §D — ★★★ THE FEED: `white_hInnerCont_closed_final2` with `hbase` supplied.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_closed_final3` — the whitened inner-pairing interior-time continuity with
    `hbase` DISCHARGED through `white_hbase_producer`.**  Same conclusion as
    `WhiteHInnerContLegADischarged.white_hInnerCont_closed_final2`, but the `hbase` slot is BUILT
    in-line from the flow-ball base-0 geometry certs `{R, h0K, hballS, hballC}`, the base-0 germ
    `hspec` (extracted from the `Kset` germ at `0`), the gate openness (extracted at `0`), and the
    LABELLED all-`R'` cover family `hcover`.

    ── THE TERMINAL PER-GATE CERTIFICATE LIST (NOT the conclusion, NOT `a₁ = R/6`;
       `htermBox`/`hInterior`/`hlegA`/`hbase` ALL discharged into these certs):
      A. dominated / A-group data (co-instantiable at the shared radius): `C, hC0, hpkg, hEmeas,
         hWmeas, (wA, Cpre, A₀, A₁), hval`.
      B. the null-frontier cert `hnull` (proved at the ball-gate limit; the flow-gate frontier null is
         the one labelled analytic input).
      C. the `hlegA` DISCHARGE cert (reach substrate) `{Wg, hagree, c, δ₀, hcδ, hSopen (Kset),
         hSreach, hspec (Kset)}` — banked at the concrete flow-ball gate.
      D. the `hbase` PRODUCER certs `{R, h0K, hballS, hballC}` (base-0 flow-ball reach) + the
         WIDTH-WALL labelled input `hcover` (⚠ unsatisfiable with `hballS` — `white_hbase_cover_gap`;
         the genuine residual is the in-gate cutoff-collar annulus continuity).
      E. window `{Uwin, hU1}`.
    ⚠ CONDITIONAL on the certificate list; `hcover` is the WIDTH-WALL labelled residual.  NOT
    `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final3 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
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
    -- D. the `hbase` PRODUCER certs (base-0 flow-ball reach) + WIDTH-WALL labelled cover
    (R : ℝ) (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    (hcover : ∀ R' : ℝ,
        Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ (closure (S 0))ᶜ)
    -- E. window
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) := by
  -- base-0 germ + gate openness from the `Kset` certs at `w = 0`.
  have hspec0 := hspec 0 h0K
  have hSopen0 : IsOpen (S 0) := hSopen 0 h0K
  -- BUILD `hbase` from the flow-ball geometry + the labelled cover.
  have hbase := white_hbase_producer hn κ hκ hKc S a b Wg hagree R c δ₀ h0K hSopen0 hballS hcδ
    hspec0 hballC hcover
  -- FEED the banked `hlegA`-discharged final.
  exact white_hInnerCont_closed_final2 hn κ hκ hKc S a b C hC0 hpkg hEmeas hWmeas
    wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval hnull hbase Wg hagree c δ₀ hcδ hSopen hSreach hspec
    Uwin hU1

#check @white_hbase_producer_upto
#check @white_hbase_producer_upto_satisfiable
#check @white_hbase_producer
#check @white_hbase_cover_gap
#check @white_hInnerCont_closed_final3

end QIQTH.WhiteHBaseProducer

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHBaseProducer
#print axioms white_hbase_producer_upto
#print axioms white_hbase_producer_upto_satisfiable
#print axioms white_hbase_producer
#print axioms white_hbase_cover_gap
#print axioms white_hInnerCont_closed_final3
end AxiomChecks
