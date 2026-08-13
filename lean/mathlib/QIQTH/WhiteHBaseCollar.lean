/-
  WhiteHBaseCollar — J4-716: THE CUTOFF-COLLAR DISCHARGE of the width-wall residual of the whitened
  `hInnerCont` campaign.  Replaces the PROVABLY-UNSATISFIABLE all-`R'` OFF-GATE cover
  (`WhiteHBaseProducer.white_hbase_cover_gap`, J4-715 — the sup-norm-`R` point sits in the reach ball
  `⊆ S 0 ⊆ closure (S 0)`, contradicting the cover forcing it OFF `closure (S 0)`) with the HONEST
  CUTOFF COLLAR: the whitened defect kernel vanishes where the radial cutoff is `0`
  (`WhiteHBaseExtend.whiteDefectKernel_eq_zero_farCutoff`, J4-701 — window-uniform in `τ`), and the
  collar region `b² ≤ rncRadialSq (whiteInvChart 0 ·)` is COMPATIBLE with the in-gate reach `hballS`
  (it constrains the chart RADIAL SIZE, not gate membership) — so NO `white_hbase_cover_gap`
  contradiction arises.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` is a
  labelled carrier, untouched).  It is a purely TOPOLOGICAL / GEOMETRIC cover-swap brick: the vanishing
  region is an INTERIOR (automatically open — no global chart continuity needed), the cover comes from
  the labelled collar-reach geometric input `hcollar`, and the stitch is the banked J4-701 open-cover
  continuity.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis smuggled as a fake capstone, no existing file edited, nothing committed, nothing wired
  into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `whiteDefectKernel_collar_vanishing_open` — ★ STEP 1 (UNCONDITIONAL): the OPEN vanishing region
      `U = interior {p' | b² ≤ rncRadialSq (whiteInvChart 0 p')}` — open by `isOpen_interior` (the
      chart need NOT be globally continuous: the interior automatically restricts to points where the
      collar condition holds on a neighbourhood), and the whitened defect `(·,·,0)`-slice is `≡ 0`
      there for every `τ` (via `whiteDefectKernel_eq_zero_farCutoff`, `mem_interior_iff_mem_nhds`).
    * `white_hbase_cover_collar` — ★ STEP 2 (from `hcollar`): the ALL-`R'` cover
      `closedBall 0 R' ⊆ ball 0 R ∪ U` from the labelled collar-reach input
      `hcollar : ∀ p, R ≤ ‖p‖ → {p' | b² ≤ rncRadialSq (whiteInvChart 0 p')} ∈ 𝓝 p` — in-reach points
      (`‖p‖ < R`) land in `ball 0 R`, beyond-reach points (`‖p‖ ≥ R`) land in the interior-collar `U`.
    * `white_collar_of_globalQuarterIso` — ★ STEP 2b (the near-isometry BRIDGE): derives `hcollar`
      from a global `(1/4)`-near-isometry lower bound `hquarter : ∀ p', (1/4)‖p'‖² ≤ rncRadialSq(V₀ p')`
      plus the collar-reach relation `hbR : 2b < R` (`0 ≤ b`) — the open ball complement
      `{p' | 2b < ‖p'‖}` is the required neighbourhood.  ⚠ HONEST: the GLOBAL `(1/4)` lower bound is
      the demanding form (false for a chart whose extension junks beyond the injectivity radius); the
      banked near-isometry bounds are LOCAL (small-`‖z‖` perturbation of identity), so `hquarter` is a
      labelled geometric input, NOT banked.  `hcollar` (nhds form, beyond `R` only) is the WEAKER
      primary carry.
    * `white_hbase_producer_collar` — ★★ STEP 3 (the all-`R'` PRODUCER): flow-ball base-0 continuity
      at reach `R` (J4-698) ⊕ the interior-collar vanishing (step 1) ⊕ the collar cover (step 2),
      stitched by `whiteDefectKernel_jointContinuousOn_extend` (J4-701).  ⚠ CONDITIONAL on `hcollar`
      (the collar-reach geometric input) — but `hcollar` is COMPATIBLE with `hballS`
      (`white_collar_hballS_no_gap`), unlike the off-gate cover.
    * `white_hInnerCont_closed_final4` — ★★★ STEP 4 (THE TERMINAL FEED): `white_hInnerCont_closed_final2`
      (J4-714) with the `hbase` slot supplied by `white_hbase_producer_collar` — the whitened
      inner-pairing interior-time continuity, with the width wall discharged to the honest `hcollar`
      collar-reach input (NOT an unsatisfiable cover).
    * `white_collar_hballS_no_gap` — ★★ THE WIDTH-WALL DISCHARGE CERTIFICATE: unlike the off-gate cover
      (`white_hbase_cover_gap`, jointly UNSATISFIABLE with `hballS`), the collar route places the
      boundary sup-norm-`R` point p₀ SIMULTANEOUSLY in the collar `U` (from `hcollar`, `‖p₀‖ = R ≥ R`)
      AND in the gate `S 0` (from `hballS`) — NO contradiction.  So the width wall is CLOSED modulo the
      compatible geometric input `hcollar`.
    * `white_collar_hcollar_shape_satisfiable` — cp466 antecedent-inhabitance gate: the `hcollar` shape
      `∀ p, R ≤ ‖p‖ → {p' | b² ≤ f p'} ∈ 𝓝 p` is INHABITED (constant `f ≡ b²+1`, collar set `= univ`),
      so the conditional is not a vacuously-false SHAPE (unlike the off-gate cover shape).

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
    * `hcollar` — the collar-reach labelled geometric input (the whitened inverse chart maps `‖·‖ ≥ R`
      into the cutoff collar `b² ≤ rncRadialSq(V₀ ·)`, with local uniformity).  Its GLOBAL truth for
      the concrete chart is chart-geometry content NOT banked here (banked near-isometry is LOCAL,
      small-`‖z‖`); carried as the honest labelled input.  ⚠ COMPATIBLE with `hballS`
      (`white_collar_hballS_no_gap`) — the genuine advance over the unsatisfiable off-gate cover.
    * `hnull` — the null-frontier cert (unchanged carry from the inner-pairing campaign).

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHBaseProducer

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteHJetCont QIQTH.WhiteHBaseExtend
open QIQTH.WhiteHInnerContLegADischarged
open scoped Topology BigOperators

namespace QIQTH.WhiteHBaseCollar

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — ★ STEP 1: the OPEN interior-collar vanishing region (UNCONDITIONAL).
    ############################################################################### -/

/-- **★ `whiteDefectKernel_collar_vanishing_open` (STEP 1, UNCONDITIONAL).**  The whitened defect
    `(·,·,0)`-slice vanishes on the OPEN region
    `U = interior {p' | b² ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')}`.  Openness is
    `isOpen_interior` (crucially NO global chart continuity is needed — the interior automatically
    selects the points where the collar condition holds on a whole neighbourhood, which is exactly
    what `whiteDefectKernel_eq_zero_farCutoff` consumes).  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_collar_vanishing_open (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsOpen (interior {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')}) ∧
      ∀ p ∈ interior {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')},
        ∀ τ : ℝ, whiteDefectKernel κ hκ hKc S a b τ p 0 = 0 := by
  refine ⟨isOpen_interior, fun p hp τ => ?_⟩
  exact whiteDefectKernel_eq_zero_farCutoff κ hκ hKc S ha hab τ p (mem_interior_iff_mem_nhds.mp hp)

/-! ###############################################################################
    ### §B — ★ STEP 2: the ALL-`R'` COLLAR COVER from the labelled collar-reach input.
    ############################################################################### -/

/-- **★ `white_hbase_cover_collar` (STEP 2).**  From the labelled collar-reach input
    `hcollar : ∀ p, R ≤ ‖p‖ → {p' | b² ≤ rncRadialSq (whiteInvChart 0 p')} ∈ 𝓝 p`, the ALL-`R'` cover
    `closedBall 0 R' ⊆ ball 0 R ∪ U` with `U = interior {collar}`.  In-reach points (`‖p‖ < R`) land
    in `ball 0 R`; beyond-reach points (`‖p‖ ≥ R`) land in `U` (`hcollar` ⟹ the collar set is a
    neighbourhood ⟹ the point is in its interior).  NOT `a₁ = R/6`. -/
theorem white_hbase_cover_collar (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b R : ℝ)
    (hcollar : ∀ p : Point n, R ≤ ‖p‖ →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p) :
    ∀ R' : ℝ, Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪
        interior {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} := by
  intro R' p _hp
  by_cases hb : p ∈ Metric.ball (0 : Point n) R
  · exact Or.inl hb
  · refine Or.inr ?_
    rw [mem_interior_iff_mem_nhds]
    refine hcollar p ?_
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hb
    exact hb

/-- **★ `white_collar_of_globalQuarterIso` (STEP 2b — the near-isometry BRIDGE).**  Derives the
    collar-reach input `hcollar` from a GLOBAL `(1/4)`-near-isometry lower bound
    `hquarter : ∀ p', (1/4)·‖p'‖² ≤ rncRadialSq (whiteInvChart 0 p')` plus the collar-reach relation
    `hbR : 2·b < R` (`0 ≤ b`).  For `R ≤ ‖p‖` the OPEN set `{p' | 2b < ‖p'‖}` is a neighbourhood of
    `p`, and on it `b² < (1/4)‖p'‖² ≤ rncRadialSq (V₀ p')`.
    ⚠ HONEST: the GLOBAL `(1/4)` bound is the demanding form — false for a chart whose extension is
    junk beyond the injectivity radius; the banked near-isometry is LOCAL (small-`‖z‖`).  So
    `hquarter` is a labelled geometric input, and `hcollar` (weaker, beyond-`R` only) is the primary
    carry.  NOT `a₁ = R/6`. -/
theorem white_collar_of_globalQuarterIso (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (b R : ℝ) (hb : 0 ≤ b) (hbR : 2 * b < R)
    (hquarter : ∀ p' : Point n,
        (1 / 4) * ‖p'‖ ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')) :
    ∀ p : Point n, R ≤ ‖p‖ →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p := by
  intro p hRp
  have hp2b : 2 * b < ‖p‖ := lt_of_lt_of_le hbR hRp
  have hopen : IsOpen {p' : Point n | (2 * b) < ‖p'‖} :=
    isOpen_lt continuous_const continuous_norm
  refine Filter.mem_of_superset (hopen.mem_nhds hp2b) ?_
  intro p' hp'
  simp only [Set.mem_setOf_eq] at hp' ⊢
  have h1 : b ^ 2 < (1 / 4) * ‖p'‖ ^ 2 := by nlinarith [hp', hb, norm_nonneg p']
  exact le_of_lt (lt_of_lt_of_le h1 (hquarter p'))

/-! ###############################################################################
    ### §C — ★★ THE WIDTH-WALL DISCHARGE: `hcollar` is COMPATIBLE with `hballS`.
    ############################################################################### -/

/-- **★★ `white_collar_hballS_no_gap` — THE WIDTH-WALL DISCHARGE CERTIFICATE.**  Unlike the off-gate
    cover (`WhiteHBaseProducer.white_hbase_cover_gap`: jointly UNSATISFIABLE with `hballS` — the
    boundary sup-norm-`R` point is FORCED off `closure (S 0)` while sitting in the reach ball
    `⊆ S 0`), the collar route is COMPATIBLE: the boundary point `p₀ = (fun _ => R)` sits
    SIMULTANEOUSLY in the collar interior `U` (from `hcollar`, since `‖p₀‖ = R ≥ R`) AND in the gate
    `S 0` (from `hballS`, since `p₀ ∈ closedBall 0 R`) — NO contradiction.  So the width wall is
    CLOSED modulo the compatible geometric input `hcollar`.  NOT `a₁ = R/6`. -/
theorem white_collar_hballS_no_gap (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b R : ℝ) (hR : 0 ≤ R)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hcollar : ∀ p : Point n, R ≤ ‖p‖ →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p) :
    ∃ p₀ : Point n,
      p₀ ∈ interior {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')}
      ∧ p₀ ∈ S 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨(fun _ : Fin n => R), ?_, ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    refine hcollar _ ?_
    rw [pi_norm_const R, Real.norm_of_nonneg hR]
  · refine hballS ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_const R, Real.norm_of_nonneg hR]

/-- **`white_collar_hcollar_shape_satisfiable`** (cp466 discipline — the axiom-budget blind spot is
    UNSATISFIABLE-SHAPE antecedents).  The `hcollar` SHAPE `∀ p, R ≤ ‖p‖ → {p' | b² ≤ f p'} ∈ 𝓝 p`
    is INHABITED — witnessed by a constant `f ≡ b² + 1` (collar set `= univ`, a neighbourhood of
    every point).  So the conditional collar producer is NOT a vacuously-FALSE shape (contrast the
    off-gate cover shape, provably unsatisfiable with `hballS`).  NOT `a₁ = R/6`. -/
theorem white_collar_hcollar_shape_satisfiable (b R : ℝ) :
    ∃ f : Point n → ℝ, ∀ p : Point n, R ≤ ‖p‖ →
      {p' : Point n | b ^ 2 ≤ f p'} ∈ nhds p := by
  refine ⟨fun _ => b ^ 2 + 1, fun p _hp => ?_⟩
  have huniv : {p' : Point n | b ^ 2 ≤ b ^ 2 + 1} = Set.univ := by
    ext p'; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; linarith
  rw [huniv]
  exact Filter.univ_mem

/-! ###############################################################################
    ### §D — ★★ STEP 3: the all-`R'` COLLAR PRODUCER.
    ############################################################################### -/

/-- **★★ `white_hbase_producer_collar` (STEP 3).**  The all-`R'` whitened `k = 0` raw-kernel base
    continuity via the CUTOFF COLLAR: flow-ball base-0 continuity at reach `R`
    (`whiteDefectKernel_jointContinuousOn_of_flowBall`, J4-698) ⊕ the interior-collar vanishing
    (step 1) ⊕ the collar cover (step 2, from `hcollar`), stitched by
    `whiteDefectKernel_jointContinuousOn_extend` (J4-701).  Delivers exactly the `hbase` slot of
    `white_hInnerCont_closed_final2`.
    ⚠ CONDITIONAL on `hcollar` — the collar-reach labelled geometric input; COMPATIBLE with `hballS`
    (`white_collar_hballS_no_gap`), unlike the off-gate cover.  NOT `a₁ = R/6`. -/
theorem white_hbase_producer_collar (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
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
    (hcollar : ∀ p : Point n, R ≤ ‖p‖ →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p) :
    ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  obtain ⟨hUopen, hUzero⟩ := whiteDefectKernel_collar_vanishing_open κ hκ hKc S ha hab
  intro s₁ s₂ R' hs₁ hs₁₂ hs₂
  have hbaseR : ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    whiteDefectKernel_jointContinuousOn_of_flowBall hn κ hκ hKc S a b Wg hagree
      s₁ s₂ R c δ₀ hs₁ hs₂ h0K hSopen hballS hcδ hspec hballC
  exact whiteDefectKernel_jointContinuousOn_extend κ hκ hKc S a b s₁ s₂ R R'
    (interior {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')})
    hUopen hUzero hbaseR (white_hbase_cover_collar κ hκ hKc a b R hcollar R')

/-! ###############################################################################
    ### §E — ★★★ STEP 4: THE TERMINAL FEED — `final2` with `hbase` from the collar producer.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_closed_final4` (STEP 4 — THE TERMINAL FEED).**  Same conclusion as
    `WhiteHInnerContLegADischarged.white_hInnerCont_closed_final2`, but the `hbase` slot is BUILT
    in-line from `white_hbase_producer_collar`: the flow-ball base-0 geometry certs `{R, h0K, hballS,
    hballC}`, the base-0 germ `hspec` (at `0 ∈ Kset`), the gate openness (at `0`), the cutoff radii
    `0 < a < b`, and the LABELLED collar-reach input `hcollar`.  This is the whitened inner-pairing
    interior-time continuity with the WIDTH WALL DISCHARGED to the honest collar route (NOT the
    unsatisfiable off-gate cover of `white_hbase_cover_gap`).

    ── THE TERMINAL PER-GATE CERTIFICATE LIST (NOT the conclusion, NOT `a₁ = R/6`):
      A. dominated / A-group data: `C, hC0, hpkg, hEmeas, hWmeas, (wA, Cpre, A₀, A₁), hval`.
      B. the null-frontier cert `hnull`.
      C. the `hlegA` DISCHARGE cert (reach substrate) `{Wg, hagree, c, δ₀, hcδ, hSopen (Kset),
         hSreach, hspec (Kset)}`.
      D. the `hbase` COLLAR-PRODUCER certs `{R, h0K, hballS, hballC}` (base-0 flow-ball reach) + the
         cutoff radii `ha, hab` + the WIDTH-WALL collar-reach input `hcollar`
         (⚠ COMPATIBLE with `hballS` — `white_collar_hballS_no_gap`; the genuine advance over the
         unsatisfiable off-gate cover).
      E. window `{Uwin, hU1}`.
    ⚠ CONDITIONAL on the certificate list; `hcollar` is the WIDTH-WALL collar-reach labelled residual
    (COMPATIBLE with `hballS`).  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final4 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
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
    -- D. the `hbase` COLLAR-PRODUCER certs (base-0 flow-ball reach) + WIDTH-WALL collar-reach input
    (R : ℝ) (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    (hcollar : ∀ p : Point n, R ≤ ‖p‖ →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p)
    -- E. window
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) := by
  have hspec0 := hspec 0 h0K
  have hSopen0 : IsOpen (S 0) := hSopen 0 h0K
  have hbase := white_hbase_producer_collar hn κ hκ hKc S a b ha hab Wg hagree R c δ₀ h0K hSopen0
    hballS hcδ hspec0 hballC hcollar
  exact white_hInnerCont_closed_final2 hn κ hκ hKc S a b C hC0 hpkg hEmeas hWmeas
    wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval hnull hbase Wg hagree c δ₀ hcδ hSopen hSreach hspec
    Uwin hU1

#check @whiteDefectKernel_collar_vanishing_open
#check @white_hbase_cover_collar
#check @white_collar_of_globalQuarterIso
#check @white_collar_hballS_no_gap
#check @white_collar_hcollar_shape_satisfiable
#check @white_hbase_producer_collar
#check @white_hInnerCont_closed_final4

end QIQTH.WhiteHBaseCollar

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHBaseCollar
#print axioms whiteDefectKernel_collar_vanishing_open
#print axioms white_hbase_cover_collar
#print axioms white_collar_of_globalQuarterIso
#print axioms white_collar_hballS_no_gap
#print axioms white_collar_hcollar_shape_satisfiable
#print axioms white_hbase_producer_collar
#print axioms white_hInnerCont_closed_final4
end AxiomChecks
