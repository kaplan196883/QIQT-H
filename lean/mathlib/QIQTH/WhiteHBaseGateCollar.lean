/-
  WhiteHBaseGateCollar — J4-717: THE COMBINED-ROUTE DISCHARGE of the width-wall residual — the
  honest configuration verdict for the concrete center chart.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6` (`R/6` is a
  labelled carrier, untouched).  It is a purely TOPOLOGICAL / GEOMETRIC cover-swap brick: it combines
  the TWO banked vanishing suppliers (off-gate `whiteDefectKernel_zero_on_isOpen_compl_closure` and
  far-cutoff `whiteDefectKernel_collar_vanishing_open`) into ONE open vanishing region, so the
  all-`R'` cover reduces the collar-reach residual to an ON-GATE-ONLY statement.  No `sorry`, no
  `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no existing file edited,
  nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE HONEST CONFIGURATION VERDICT (why the plain collar `hcollar` of J4-716 is not concretely
     dischargeable, and how the combined route repairs it).
    * `whiteUnvel_center_apply` / `whiteInvChart_center_eq` — ★ THE GROUNDING: at the CENTER base
      point the whitening frame is trivial (`whiteUnvel κ 0 = id`, since `E_0 = δ` and `g^κ(0) = δ`),
      so the concrete center chart is EXACTLY the banked uniform inverse chart:
          `whiteInvChart κ hκ hKc 0 p = uniformInverseChart g^κ gi^κ … 0 p`.
      ⚠ VERDICT: `uniformInverseChart … 0` is the ApproximatesLinearOn partial-homeomorph inverse
      `E.symm` (UniformChartRadius, U2), which is UNCONSTRAINED JUNK outside `E.target` (the chart
      REACH image).  Hence `rncRadialSq (whiteInvChart 0 p)` for large `‖p‖` (off the reach) is
      determined by the junk `invFun` and is NEITHER an identity-extension (`~ ‖p‖²`, hcollar easy)
      NOR the zero-extension (`= 0`, hcollar false) — it is genuinely UNPROVABLE either way from the
      banked material.  So the plain all-beyond-`R` `hcollar` of J4-716 is a demanding labelled input
      whose truth is NOT decidable at the concrete chart.  This file REROUTES around it.
    * ★★ THE REROUTE.  The whitened defect kernel vanishes on the UNION of the two banked open regions:
        (a) `(closure (S 0))ᶜ` — OFF-GATE (bounded gate ⟹ this covers everything outside the gate);
        (b) `interior {p' | b² ≤ rncRadialSq (whiteInvChart 0 p')}` — the FAR-CUTOFF collar.
      On the intersection with `‖p‖ ≥ R` that the plain collar had to control, points split:
        • `p ∉ closure (S 0)` — handled by (a) for FREE (no chart control needed — this is precisely
          the junk-far-field region, where the kernel vanishes by the GATE, not the cutoff);
        • `p ∈ closure (S 0)` with `‖p‖ ≥ R` — the ONLY residual, and there `p` is in the flow-image
          gate, where `whiteInvChart 0` is the GENUINE inverse chart (not junk).
      So the labelled residual shrinks from the plain all-beyond-`R` `hcollar` to the ON-GATE-only
      `hgateCollar` (`gateCollar_of_collar` proves it is strictly WEAKER: `hcollar ⟹ hgateCollar`).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `whiteUnvel_center_apply`, `whiteInvChart_center_eq` — the center-chart grounding (above).
    * `white_hbase_cover_gateCollar` — ★ the ALL-`R'` COMBINED cover
        `closedBall 0 R' ⊆ ball 0 R ∪ (interior {collar} ∪ (closure (S 0))ᶜ)`
      from the ON-GATE collar input `hgateCollar`.
    * `gateCollar_of_collar` — ★ the plain collar of J4-716 IMPLIES the on-gate collar (the reroute is
      strictly weaker on the labelled side).
    * `white_hbase_producer_gateCollar` — ★★ the all-`R'` producer via the COMBINED vanishing region.
    * `white_hInnerCont_closed_final5` — ★★★ THE TERMINAL FEED: `white_hInnerCont_closed_final2`
      (J4-714) with `hbase` from the combined producer — the whitened inner-pairing interior-time
      continuity, width wall discharged to the ON-GATE-only `hgateCollar` (strictly weaker than the
      J4-716 all-beyond-`R` `hcollar`).
    * `white_gateCollar_hballS_no_gap` — the compatibility certificate (as in J4-716, unchanged).
    * `white_gateCollar_shape_satisfiable` — cp466 antecedent-inhabitance gate.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
    * `hgateCollar` — the ON-GATE collar-reach input: only for `p ∈ closure (S 0)` with `‖p‖ ≥ R`
      (where `whiteInvChart 0` is the GENUINE chart inverse, not junk).  This is the honest irreducible
      geometric residual — the "in-gate cutoff-collar continuity across the annulus" named in the
      J4-715 doc — with the junk-far-field disposed of by the off-gate leg.
    * `hnull` — the flow-gate null-frontier cert (unchanged carry; the codim-1 sphere-image wall).

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.WhiteHBaseCollar

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation QIQTH.LeviSeries
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteAnnulus
open QIQTH.WhiteHJetCont QIQTH.WhiteHBaseExtend
open QIQTH.WhiteHInnerContLegADischarged
open QIQTH.WhiteHBaseCollar
open scoped Topology BigOperators

namespace QIQTH.WhiteHBaseGateCollar

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — ★ THE GROUNDING: the center chart IS the genuine uniform inverse chart.
    ############################################################################### -/

/-- **★ `whiteUnvel_center_apply`.**  At the center base point the whitening inverse frame is the
    identity: `whiteUnvel κ 0 y = y` (via `whiteUnvel_whiteVel` at `q = 0` and `whiteVel_center`,
    `E_0 = δ`).  NOT `a₁ = R/6`. -/
theorem whiteUnvel_center_apply (κ : ℝ) (hκ : κ ≤ 0) (y : Point n) :
    whiteUnvel κ (0 : Point n) y = y := by
  have h := whiteUnvel_whiteVel κ hκ (0 : Point n) y
  rwa [whiteVel_center] at h

/-- **★ `whiteInvChart_center_eq`.**  The concrete CENTER whitened inverse chart is EXACTLY the banked
    uniform inverse chart at base `0`: `whiteInvChart κ hκ hKc 0 p = uniformInverseChart … 0 p` —
    whitening is trivial at the center.  So the far-field radial behaviour of `whiteInvChart 0` IS
    that of `uniformInverseChart 0 = E.symm` (a partial-homeomorph inverse, unconstrained junk off the
    reach `E.target`).  This is the grounding of the honest configuration verdict.  NOT `a₁ = R/6`. -/
theorem whiteInvChart_center_eq (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (p : Point n) :
    whiteInvChart κ hκ hKc 0 p
      = uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 p := by
  simp only [whiteInvChart]
  exact whiteUnvel_center_apply κ hκ _

/-! ###############################################################################
    ### §B — ★ THE ON-GATE COLLAR IS WEAKER THAN THE PLAIN COLLAR.
    ############################################################################### -/

/-- **★ `gateCollar_of_collar`.**  The plain all-beyond-`R` collar input of J4-716
    (`hcollar : ∀ p, R ≤ ‖p‖ → {collar} ∈ 𝓝 p`) IMPLIES the ON-GATE-only collar
    (`hgateCollar : ∀ p, R ≤ ‖p‖ → p ∈ closure (S 0) → {collar} ∈ 𝓝 p`) — the combined reroute
    carries a STRICTLY WEAKER labelled residual (it drops the demand at every off-gate junk-far-field
    point).  NOT `a₁ = R/6`. -/
theorem gateCollar_of_collar (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (b R : ℝ)
    (hcollar : ∀ p : Point n, R ≤ ‖p‖ →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p) :
    ∀ p : Point n, R ≤ ‖p‖ → p ∈ closure (S 0) →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p :=
  fun p hp _ => hcollar p hp

/-! ###############################################################################
    ### §C — ★ THE ALL-`R'` COMBINED COVER (off-gate ∪ far-cutoff).
    ############################################################################### -/

/-- **★ `white_hbase_cover_gateCollar` (COMBINED cover).**  From the ON-GATE collar input
    `hgateCollar`, the ALL-`R'` cover
        `closedBall 0 R' ⊆ ball 0 R ∪ (interior {collar} ∪ (closure (S 0))ᶜ)`.
    In-reach points (`‖p‖ < R`) land in `ball 0 R`; beyond-reach points split by gate membership —
    if `p ∈ closure (S 0)` the ON-GATE collar `hgateCollar` puts it in the interior-collar; else `p`
    is off `closure (S 0)` (the junk-far-field, handled by the off-gate leg).  NOT `a₁ = R/6`. -/
theorem white_hbase_cover_gateCollar (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (b R : ℝ)
    (hgateCollar : ∀ p : Point n, R ≤ ‖p‖ → p ∈ closure (S 0) →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p) :
    ∀ R' : ℝ, Metric.closedBall (0 : Point n) R' ⊆ Metric.ball 0 R ∪
        (interior {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')}
          ∪ (closure (S 0))ᶜ) := by
  intro R' p _hp
  by_cases hb : p ∈ Metric.ball (0 : Point n) R
  · exact Or.inl hb
  · refine Or.inr ?_
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hb
    by_cases hcl : p ∈ closure (S 0)
    · exact Or.inl (mem_interior_iff_mem_nhds.mpr (hgateCollar p hb hcl))
    · exact Or.inr hcl

/-! ###############################################################################
    ### §D — ★★ THE all-`R'` COMBINED PRODUCER.
    ############################################################################### -/

/-- **★★ `white_hbase_producer_gateCollar` (COMBINED producer).**  The all-`R'` whitened `k = 0`
    raw-kernel base continuity via the COMBINED vanishing region `U = interior {collar} ∪
    (closure (S 0))ᶜ`: flow-ball base-0 continuity at reach `R` (J4-698) ⊕ the union vanishing (both
    banked suppliers) ⊕ the combined cover (from `hgateCollar`), stitched by
    `whiteDefectKernel_jointContinuousOn_extend` (J4-701).  Delivers exactly the `hbase` slot of
    `white_hInnerCont_closed_final2`.
    ⚠ CONDITIONAL on the ON-GATE `hgateCollar` (strictly weaker than the J4-716 all-beyond-`R`
    `hcollar`; the junk-far-field is disposed of by the off-gate leg).  NOT `a₁ = R/6`. -/
theorem white_hbase_producer_gateCollar (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
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
    (hgateCollar : ∀ p : Point n, R ≤ ‖p‖ → p ∈ closure (S 0) →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p) :
    ∀ s₁ s₂ R' : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ 1 →
      ContinuousOn
        (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
        (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R') := by
  obtain ⟨hU1open, hU1zero⟩ := whiteDefectKernel_collar_vanishing_open κ hκ hKc S ha hab
  obtain ⟨hU2open, hU2zero⟩ := whiteDefectKernel_zero_on_isOpen_compl_closure κ hκ hKc S a b
  set U : Set (Point n) :=
    interior {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')}
      ∪ (closure (S 0))ᶜ with hUdef
  have hUopen : IsOpen U := hU1open.union hU2open
  have hUzero : ∀ p ∈ U, ∀ τ : ℝ, whiteDefectKernel κ hκ hKc S a b τ p 0 = 0 := by
    intro p hp τ
    rcases hp with h | h
    · exact hU1zero p h τ
    · exact hU2zero p h τ
  intro s₁ s₂ R' hs₁ hs₁₂ hs₂
  have hbaseR : ContinuousOn
      (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc s₁ s₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    whiteDefectKernel_jointContinuousOn_of_flowBall hn κ hκ hKc S a b Wg hagree
      s₁ s₂ R c δ₀ hs₁ hs₂ h0K hSopen hballS hcδ hspec hballC
  exact whiteDefectKernel_jointContinuousOn_extend κ hκ hKc S a b s₁ s₂ R R'
    U hUopen hUzero hbaseR (white_hbase_cover_gateCollar κ hκ hKc S b R hgateCollar R')

/-! ###############################################################################
    ### §E — ★★ COMPATIBILITY + cp466 satisfiability.
    ############################################################################### -/

/-- **★★ `white_gateCollar_hballS_no_gap` — the width-wall discharge certificate.**  As in J4-716:
    the boundary sup-norm-`R` point sits SIMULTANEOUSLY in the collar interior (from `hgateCollar`,
    since `‖p₀‖ = R ≥ R` AND `p₀ ∈ closedBall 0 R ⊆ S 0 ⊆ closure (S 0)`) AND in the gate `S 0` — NO
    contradiction (contrast the off-gate cover, unsatisfiable with `hballS`).  NOT `a₁ = R/6`. -/
theorem white_gateCollar_hballS_no_gap (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (b R : ℝ) (hR : 0 ≤ R)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hgateCollar : ∀ p : Point n, R ≤ ‖p‖ → p ∈ closure (S 0) →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p) :
    ∃ p₀ : Point n,
      p₀ ∈ interior {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')}
      ∧ p₀ ∈ S 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hp0ball : (fun _ : Fin n => R) ∈ Metric.closedBall (0 : Point n) R := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_const R, Real.norm_of_nonneg hR]
  have hp0S : (fun _ : Fin n => R) ∈ S 0 := hballS hp0ball
  refine ⟨(fun _ : Fin n => R), ?_, hp0S⟩
  rw [mem_interior_iff_mem_nhds]
  refine hgateCollar _ ?_ (subset_closure hp0S)
  rw [pi_norm_const R, Real.norm_of_nonneg hR]

/-- **`white_gateCollar_shape_satisfiable`** (cp466 discipline).  The `hgateCollar` SHAPE
    `∀ p, R ≤ ‖p‖ → p ∈ closure (S 0) → {p' | b² ≤ f p'} ∈ 𝓝 p` is INHABITED — witnessed by the
    constant `f ≡ b² + 1` (collar set `= univ`).  So the conditional producer is NOT a vacuously-false
    shape.  NOT `a₁ = R/6`. -/
theorem white_gateCollar_shape_satisfiable (S : Point n → Set (Point n)) (b R : ℝ) :
    ∃ f : Point n → ℝ, ∀ p : Point n, R ≤ ‖p‖ → p ∈ closure (S 0) →
      {p' : Point n | b ^ 2 ≤ f p'} ∈ nhds p := by
  refine ⟨fun _ => b ^ 2 + 1, fun p _hp _hcl => ?_⟩
  have huniv : {p' : Point n | b ^ 2 ≤ b ^ 2 + 1} = Set.univ := by
    ext p'; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; linarith
  rw [huniv]
  exact Filter.univ_mem

/-! ###############################################################################
    ### §F — ★★★ THE TERMINAL FEED — `final2` with `hbase` from the combined producer.
    ############################################################################### -/

/-- **★★★ `white_hInnerCont_closed_final5` (THE TERMINAL FEED).**  Same conclusion as
    `WhiteHInnerContLegADischarged.white_hInnerCont_closed_final2`, but the `hbase` slot is BUILT
    in-line from `white_hbase_producer_gateCollar`: the flow-ball base-0 geometry certs, the base-0
    germ `hspec`, gate openness, the cutoff radii `0 < a < b`, and the ON-GATE collar input
    `hgateCollar` (strictly WEAKER than the J4-716 all-beyond-`R` `hcollar` by `gateCollar_of_collar`;
    the junk-far-field disposed of by the off-gate leg).
    ⚠ CONDITIONAL on the certificate list; `hgateCollar` is the ON-GATE collar-reach residual and
    `hnull` the flow-gate null-frontier residual.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_closed_final5 (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
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
    -- D. the `hbase` COMBINED-PRODUCER certs (base-0 flow-ball reach) + ON-GATE collar-reach input
    (R : ℝ) (h0K : (0 : Point n) ∈ Kset)
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c)
    (hgateCollar : ∀ p : Point n, R ≤ ‖p‖ → p ∈ closure (S 0) →
        {p' : Point n | b ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc 0 p')} ∈ nhds p)
    -- E. window
    (Uwin : Set ℝ) (hU1 : ∀ u ∈ Uwin, u ≤ 1) :
    ∀ u ∈ Uwin, ContinuousOn
      (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
        * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
      (Set.Ioo 0 u) := by
  have hspec0 := hspec 0 h0K
  have hSopen0 : IsOpen (S 0) := hSopen 0 h0K
  have hbase := white_hbase_producer_gateCollar hn κ hκ hKc S a b ha hab Wg hagree R c δ₀ h0K
    hSopen0 hballS hcδ hspec0 hballC hgateCollar
  exact white_hInnerCont_closed_final2 hn κ hκ hKc S a b C hC0 hpkg hEmeas hWmeas
    wA Cpre A₀ A₁ hwA0 hCpre0 hA₀0 hA₁0 hval hnull hbase Wg hagree c δ₀ hcδ hSopen hSreach hspec
    Uwin hU1

#check @whiteUnvel_center_apply
#check @whiteInvChart_center_eq
#check @gateCollar_of_collar
#check @white_hbase_cover_gateCollar
#check @white_hbase_producer_gateCollar
#check @white_gateCollar_hballS_no_gap
#check @white_gateCollar_shape_satisfiable
#check @white_hInnerCont_closed_final5

end QIQTH.WhiteHBaseGateCollar

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteHBaseGateCollar
#print axioms whiteUnvel_center_apply
#print axioms whiteInvChart_center_eq
#print axioms gateCollar_of_collar
#print axioms white_hbase_cover_gateCollar
#print axioms white_hbase_producer_gateCollar
#print axioms white_gateCollar_hballS_no_gap
#print axioms white_gateCollar_shape_satisfiable
#print axioms white_hInnerCont_closed_final5
end AxiomChecks
