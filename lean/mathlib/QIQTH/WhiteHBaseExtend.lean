/-
  WhiteHBaseExtend — J4-701: THE GATE-VANISHING EXTENSION of the whitened `hbase` from the
  reach-limited flow-ball radius to ALL radii `R'`.  Removes the "REACH ALIGNMENT" residual of
  `white_htermBox_of_flowBall_hcont` (WhiteHTermBoxWire.lean, J4-700): the consumer
  (`WhiteLeviMajorWire.white_leviJoint_window_modulo_termBox`) needs `htermBox` at ALL radii, but the
  flow-ball `hbase` covers only `R ≤ chart reach`.  Beyond the reach the whitened defect kernel is
  LOCALLY CONSTANT `0` — the gated witness's `heatOp` vanishes where the spatial gate is locally off
  (`whiteGated_heatOp_zero_offGate`) OR where the radial cutoff is in its zero collar
  (`whiteGated_heatOp_zero_farCutoff`) — so joint continuity there is trivial.  Stitching the
  flow-ball continuity (on `closedBall 0 R`) with the vanishing region via an OPEN cover
  (`ball 0 R ∪ U`, `U` the open locally-zero region) delivers joint continuity on `closedBall 0 R'`
  for ANY `R'`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a purely
  TOPOLOGICAL stitching brick (open-cover continuity of a function that is locally continuous on one
  piece and locally `0` on the other).  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `whiteDefectKernel_eq_zero_offGate` — the whitened defect vanishes at `q = 0` when the spatial
      gate `S 0` is locally off `p` (window-uniform in `τ`; via `whiteGated_heatOp_zero_offGate`).
    * `whiteDefectKernel_eq_zero_farCutoff` — the whitened defect vanishes at `q = 0` when the whitened
      chart image of a neighbourhood of `p` lies in the cutoff zero collar `b² ≤ rncRadialSq (V₀ ·)`
      (window-uniform in `τ`; via `whiteGated_heatOp_zero_farCutoff`).
    * `whiteDefectKernel_zero_on_isOpen_compl_closure` — the concrete OFF-GATE open vanishing region
      `U = (closure (S 0))ᶜ`: open, and the kernel is `≡ 0` there.
    * `whiteDefectKernel_jointContinuousOn_extend` — ★★ THE STITCH: given the flow-ball base continuity
      on `Icc t₁ t₂ ×ˢ closedBall 0 R`, an OPEN region `U` on which the whitened defect `(·,·,0)`-slice
      is identically `0`, and the cover `closedBall 0 R' ⊆ ball 0 R ∪ U`, the base continuity holds on
      `Icc t₁ t₂ ×ˢ closedBall 0 R'` — for ANY `R'`.  Pure `ContinuousWithinAt` open-cover argument.
    * `white_htermBox_of_flowBall_extend_hcont` — ★★★ the all-`R'` `htermBox`: composes the extend with
      `WhiteHJetCont.whiteDefectKernel_jointContinuousOn_of_flowBall` (flow-ball geometry at `R`) and
      `WhiteHTermBoxWire.white_htermBox_of_hbase_hcont` (at radius `R'`), delivering the ALL-`k`
      termwise joint continuity of `iterE (whiteDefectKernel …) (k+1)` on `Icc t₁ t₂ ×ˢ closedBall 0 R'`
      — reach-UNRESTRICTED — the SOLE surviving carries being `hcont` (at `R'`) and the labelled
      vanishing-cover certificate `{U, hUopen, hUzero, hcover}`.
    * `whiteDefectKernel_extend_cover_satisfiable` — cp466 antecedent-inhabitance gate: the extend's
      vanishing-cover package `{U, hUopen, hUzero, hcover}` is jointly inhabited (at `U = ∅`, `R' < R`),
      so the conditional stitch is not vacuously conditional.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
    * The `R' > R` cover `closedBall 0 R' ⊆ ball 0 R ∪ U` at a NONEMPTY `U` is a labelled GEOMETRIC
      certificate (the whitened chart maps `‖·‖ ≥ R` into the cutoff zero collar / off-gate region) —
      the whitened analogue of the flow-ball reach containment; supplied, not proved here.
    * `hcont` — the recursive inner convolution-step joint continuity, at radius `R'` (unchanged carry).

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHTermBoxWire
import QIQTH.WhiteHJetCont
import QIQTH.WhiteGated
import QIQTH.WhiteBridge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge
open QIQTH.InnerEngineRecursion QIQTH.IterEEngineWiring
open QIQTH.WhiteHJetCont QIQTH.WhiteHTermBoxWire
open scoped Topology BigOperators

namespace QIQTH.WhiteHBaseExtend

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — THE VANISHING SUPPLIERS: the whitened defect is `0` off-gate / in the cutoff collar.
    ############################################################################### -/

/-- **`whiteDefectKernel_eq_zero_offGate`.**  Where the spatial gate `S 0` is locally OFF `p`
    (`{p' | p' ∉ S 0} ∈ 𝓝 p`), the whitened defect kernel at base `q = 0` vanishes — for EVERY `τ`
    (on the window it is the gated `heatOp`, which vanishes by `whiteGated_heatOp_zero_offGate`; off
    the window it is `0` by definition). -/
theorem whiteDefectKernel_eq_zero_offGate (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (τ : ℝ) (p : Point n)
    (h : {p' : Point n | p' ∉ S 0} ∈ nhds p) :
    whiteDefectKernel κ hκ hKc S a b τ p 0 = 0 := by
  by_cases hw : 0 < τ ∧ τ ≤ 1
  · rw [whiteDefectKernel_eq κ hκ hKc S a b hw.1 hw.2 p 0]
    exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b τ p 0 (Or.inr h)
  · simp only [whiteDefectKernel, if_neg hw]

/-- **`whiteDefectKernel_eq_zero_farCutoff`.**  Where the whitened chart image of a neighbourhood of
    `p` lies in the cutoff zero collar (`{p' | b² ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ 𝓝 p`),
    the whitened defect kernel at base `q = 0` vanishes — for EVERY `τ` (via
    `whiteGated_heatOp_zero_farCutoff`). -/
theorem whiteDefectKernel_eq_zero_farCutoff (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (τ : ℝ) (p : Point n)
    (hfar : {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p) :
    whiteDefectKernel κ hκ hKc S a b τ p 0 = 0 := by
  by_cases hw : 0 < τ ∧ τ ≤ 1
  · rw [whiteDefectKernel_eq κ hκ hKc S a b hw.1 hw.2 p 0]
    exact whiteGated_heatOp_zero_farCutoff κ hκ hKc S ha hab τ p 0 hfar
  · simp only [whiteDefectKernel, if_neg hw]

/-- **`whiteDefectKernel_zero_on_isOpen_compl_closure`.**  The concrete OFF-GATE open vanishing region
    `U = (closure (S 0))ᶜ`: it is open, and the whitened defect `(·,·,0)`-slice is identically `0`
    there (any point of the open `(closure (S 0))ᶜ` has that set as a neighbourhood contained in
    `{p' | p' ∉ S 0}`, so `whiteDefectKernel_eq_zero_offGate` applies). -/
theorem whiteDefectKernel_zero_on_isOpen_compl_closure (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) :
    IsOpen ((closure (S 0))ᶜ) ∧
      ∀ p ∈ (closure (S 0))ᶜ, ∀ τ : ℝ, whiteDefectKernel κ hκ hKc S a b τ p 0 = 0 := by
  refine ⟨isClosed_closure.isOpen_compl, fun p hp τ => ?_⟩
  refine whiteDefectKernel_eq_zero_offGate κ hκ hKc S a b τ p ?_
  refine Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hp) ?_
  intro x hx hxs
  exact hx (subset_closure hxs)

/-! ###############################################################################
    ### §B — ★★ THE STITCH: extend the flow-ball base continuity to ALL radii `R'`.
    ############################################################################### -/

/-- **★★ `whiteDefectKernel_jointContinuousOn_extend`.**  Given:
      • `hR` — the flow-ball base continuity of the whitened defect `(·,·,0)`-slice on
        `Icc t₁ t₂ ×ˢ closedBall 0 R`;
      • an OPEN region `U` on which that slice is identically `0` (`hUopen`, `hUzero`);
      • the cover `closedBall 0 R' ⊆ ball 0 R ∪ U`;
    the base continuity holds on `Icc t₁ t₂ ×ˢ closedBall 0 R'` for ANY `R'`.  Pure open-cover
    `ContinuousWithinAt` argument: at a ball point either `p.2 ∈ ball 0 R` (transport `hR` through the
    open `univ ×ˢ ball 0 R` neighbourhood) or `p.2 ∈ U` (the slice is `≡ 0` on the open
    `Icc t₁ t₂ ×ˢ U` neighbourhood, hence continuous there).  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_extend (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (t₁ t₂ R R' : ℝ)
    (U : Set (Point n)) (hUopen : IsOpen U)
    (hUzero : ∀ p ∈ U, ∀ τ : ℝ, whiteDefectKernel κ hκ hKc S a b τ p 0 = 0)
    (hR : ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hcover : Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ U) :
    ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  intro p hp
  obtain ⟨hpτ, hpz⟩ := hp
  rcases hcover hpz with hball | hU
  · -- p.2 ∈ ball 0 R: transport `hR` through the open `univ ×ˢ ball 0 R` neighbourhood.
    have hcw : ContinuousWithinAt
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.ball (0 : Point n) R) p := by
      exact (hR p ⟨hpτ, Metric.ball_subset_closedBall hball⟩).mono
        (Set.prod_mono subset_rfl Metric.ball_subset_closedBall)
    refine hcw.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ Metric.ball (0 : Point n) R, isOpen_univ.prod Metric.isOpen_ball,
      ⟨Set.mem_univ _, hball⟩, ?_⟩
    rintro q ⟨hqu, hqs⟩
    exact ⟨hqs.1, hqu.2⟩
  · -- p.2 ∈ U: the slice is ≡ 0 on the open `Icc t₁ t₂ ×ˢ U` neighbourhood.
    have hcw : ContinuousWithinAt
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ U) p := by
      have hzero : ContinuousWithinAt (fun _ : ℝ × Point n => (0 : ℝ))
          (Set.Icc t₁ t₂ ×ˢ U) p := continuousWithinAt_const
      exact hzero.congr (fun q hq => hUzero q.2 hq.2 q.1) (hUzero p.2 hU p.1)
    refine hcw.mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ U, isOpen_univ.prod hUopen, ⟨Set.mem_univ _, hU⟩, ?_⟩
    rintro q ⟨hqu, hqs⟩
    exact ⟨hqs.1, hqu.2⟩

/-! ###############################################################################
    ### §C — ★★★ THE ALL-`R'` `htermBox`: flow-ball geometry ⊕ vanishing cover ⊕ `hcont`.
    ############################################################################### -/

/-- **★★★ `white_htermBox_of_flowBall_extend_hcont` — the whitened `htermBox` at ALL radii `R'`.**
    Composes:
      • `whiteDefectKernel_jointContinuousOn_of_flowBall` — the flow-ball base continuity at radius
        `R` (chart germ `hspec`, gate openness `hSopen`, reach `hballC`, gate `hballS`);
      • `whiteDefectKernel_jointContinuousOn_extend` — stitch it up to `R'` across the open vanishing
        region `U` (`hUopen`, `hUzero`), given the cover `hcover : closedBall 0 R' ⊆ ball 0 R ∪ U`;
      • `white_htermBox_of_hbase_hcont` at radius `R'` — feed the extended base continuity plus the
        recursive `hcont` (at `R'`), width-`lam` bound `hpkg`, and S1 measurability `hEmeas`.
    Delivers the ALL-`k` termwise joint `(τ,z)`-continuity of `iterE (whiteDefectKernel …) (k+1)` on
    `Icc t₁ t₂ ×ˢ closedBall 0 R'` — REACH-UNRESTRICTED — killing the reach-alignment residual of
    `white_htermBox_of_flowBall_hcont`.
    ⚠ CONDITIONAL on: `hpkg`, `hEmeas`, the flow-ball geometry (at `R`), the labelled vanishing-cover
    certificate `{U, hUopen, hUzero, hcover}` (the `R' > R` residual — the whitened chart maps
    `‖·‖ ≥ R` into the cutoff-zero / off-gate region), and `hcont` at `R'`.  NOT `a₁ = R/6`. -/
theorem white_htermBox_of_flowBall_extend_hcont (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R R' c δ₀ : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
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
          Metric.ball (0 : Point n) c)
    (U : Set (Point n)) (hUopen : IsOpen U)
    (hUzero : ∀ p ∈ U, ∀ τ : ℝ, whiteDefectKernel κ hκ hKc S a b τ p 0 = 0)
    (hcover : Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ U)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b))
    (hcont : ∀ k : ℕ, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
          * iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R')) :
    ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => iterE (whiteDefectKernel κ hκ hKc S a b) (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  have hbaseR : ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    whiteDefectKernel_jointContinuousOn_of_flowBall hn κ hκ hKc S a b Wg hagree
      t₁ t₂ R c δ₀ ht₁ ht₂ h0K hSopen hballS hcδ hspec hballC
  have hbaseR' : ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R') :=
    whiteDefectKernel_jointContinuousOn_extend κ hκ hKc S a b t₁ t₂ R R' U hUopen hUzero
      hbaseR hcover
  exact white_htermBox_of_hbase_hcont κ hκ hKc S a b C lam hC hlam2 t₁ t₂ R' ht₁ hpkg hEmeas
    hbaseR' hcont

/-! ###############################################################################
    ### §D — cp466 antecedent-inhabitance gate for the extend's vanishing-cover package.
    ############################################################################### -/

/-- **`whiteDefectKernel_extend_cover_satisfiable`** (cp466 discipline — the axiom-budget blind spot
    is UNSATISFIABLE antecedents).  The extend's vanishing-cover package
    `{U, IsOpen U, ∀ p ∈ U …, closedBall 0 R' ⊆ ball 0 R ∪ U}` is jointly INHABITED — witnessed at
    `U = ∅` for any `R' < R` (openness trivially, the vanishing leg vacuously over the empty region,
    the cover by `closedBall_subset_ball`).  So the conditional stitch is not vacuously conditional.
    ⚠ HONEST: at `U = ∅` the extend degenerates to `hR` restricted to `closedBall 0 R'` (`R' < R`);
    the genuine `R' > R` closure needs a NONEMPTY `U` (the labelled cutoff-collar/off-gate cover). -/
theorem whiteDefectKernel_extend_cover_satisfiable (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (R R' : ℝ) (hR' : R' < R) :
    ∃ U : Set (Point n), IsOpen U ∧
      (∀ p ∈ U, ∀ τ : ℝ, whiteDefectKernel κ hκ hKc S a b τ p 0 = 0) ∧
      Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪ U := by
  refine ⟨(∅ : Set (Point n)), isOpen_empty, fun p hp => absurd hp (Set.notMem_empty p), ?_⟩
  rw [Set.union_empty]
  exact Metric.closedBall_subset_ball hR'

#check @whiteDefectKernel_eq_zero_offGate
#check @whiteDefectKernel_eq_zero_farCutoff
#check @whiteDefectKernel_zero_on_isOpen_compl_closure
#check @whiteDefectKernel_jointContinuousOn_extend
#check @white_htermBox_of_flowBall_extend_hcont
#check @whiteDefectKernel_extend_cover_satisfiable

end QIQTH.WhiteHBaseExtend

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHBaseExtend
#print axioms whiteDefectKernel_eq_zero_offGate
#print axioms whiteDefectKernel_eq_zero_farCutoff
#print axioms whiteDefectKernel_zero_on_isOpen_compl_closure
#print axioms whiteDefectKernel_jointContinuousOn_extend
#print axioms white_htermBox_of_flowBall_extend_hcont
#print axioms whiteDefectKernel_extend_cover_satisfiable
end AxiomChecks
